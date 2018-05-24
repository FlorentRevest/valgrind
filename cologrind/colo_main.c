
//--------------------------------------------------------------------*/
//--- Cologrind: a Cool Colors Collector               colo_main.c ---*/
//--------------------------------------------------------------------*/

/*
   This file is part of Cologrind, a Valgrind tool for plotting the
   memory accesses of programs.

   Copyright (C) 2018 Florent Revest

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h" 
#include "pub_tool_mallocfree.h"
#include "pub_tool_options.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_oset.h"
#include "pub_tool_vki.h"

static VgFile *output;
static VgFile *graphsize;

//------------------------------------------------------------//
//--- Pages accesses storage                               ---//
//------------------------------------------------------------//
//

#define PAGE_SIZE   4096
static Addr prev_page;
static VgHashTable* visited_nodes = NULL;

static UInt nodes_count = 0;

typedef
   struct {
      void*       next;
      Addr        key;
      UInt        node;
   }
   PageToNode;

UInt nodeNbForPage(Addr page)
{
    PageToNode *p2n = VG_(HT_lookup)(visited_nodes, page);
    if(!p2n) {
        p2n = VG_(malloc)("pagetonode", sizeof(PageToNode));
        p2n->key = page;
        p2n->node = nodes_count;
        VG_(HT_add_node)(visited_nodes, p2n);
        nodes_count = nodes_count + 1;
    }

    return p2n->node;
}

typedef
   struct { 
      Addr src;
      Addr dst;
   }
   Edge;
static OSet* visited_edges = NULL;

static Word edgesCmp( const void* key, const void* elem )
{
    const Edge *e_key = (const Edge *)key;
    const Edge *e_elem = (const Edge *)elem;

    Word diffSrc = e_key->src - e_elem->src;

    if(diffSrc != 0)
        return diffSrc;
    else {
        Word diffDst = e_key->dst - e_elem->dst;

        return diffDst;
    }
}

//------------------------------------------------------------//
//--- memory references                                    ---//
//------------------------------------------------------------//
//

static
void handle_mem_access ( Addr addr )
{
    Addr page = addr / PAGE_SIZE;

    Edge e;
    e.src = prev_page;
    e.dst = page;

    if(prev_page && page != prev_page && !VG_(OSetGen_Contains)( visited_edges, &e)) {
        Edge *new_elem = (Edge*) VG_(OSetGen_AllocNode)( visited_edges, sizeof(Edge) );
        *new_elem = e;        

        VG_(fprintf)(output, "    %ld -> %ld;\n", nodeNbForPage(prev_page), nodeNbForPage(page));
        VG_(OSetGen_Insert)( visited_edges, new_elem );
    }

    prev_page = page;
}

static VG_REGPARM(2)
void colo_handle_write ( Addr addr, UWord szB )
{
    handle_mem_access(addr);
}

static VG_REGPARM(2)
void colo_handle_read ( Addr addr, UWord szB )
{
    handle_mem_access(addr);
}

// Handle reads and writes by syscalls (read == kernel
// reads user space, write == kernel writes user space).
// Assumes no such read or write spans a heap block
// boundary and so we can treat it just as one giant
// read or write.
static void colo_handle_noninsn_read ( CorePart part, ThreadId tid, const HChar* s,
        Addr base, SizeT size )
{
    switch (part) {
        case Vg_CoreSysCall:
            colo_handle_read(base, size);
            break;
        case Vg_CoreSysCallArgInMem:
            break;
        case Vg_CoreTranslate:
            break;
        default:
            tl_assert(0);
    }
}

static void colo_handle_noninsn_write ( CorePart part, ThreadId tid,
        Addr base, SizeT size )
{
    switch (part) {
        case Vg_CoreSysCall:
            colo_handle_write(base, size);
            break;
        case Vg_CoreSignal:
            break;
        default:
            tl_assert(0);
    }
}


//------------------------------------------------------------//
//--- Instrumentation                                      ---//
//------------------------------------------------------------//

#define binop(_op, _arg1, _arg2) IRExpr_Binop((_op),(_arg1),(_arg2))
#define mkexpr(_tmp)             IRExpr_RdTmp((_tmp))
#define mkU32(_n)                IRExpr_Const(IRConst_U32(_n))
#define mkU64(_n)                IRExpr_Const(IRConst_U64(_n))
#define assign(_t, _e)           IRStmt_WrTmp((_t), (_e))

static void addMemEvent(IRSB* sbOut, Bool isWrite, Int szB, IRExpr* addr,
        Int goff_sp)
{
    IRType   tyAddr   = Ity_INVALID;
    const HChar* hName= NULL;
    void*    hAddr    = NULL;
    IRExpr** argv     = NULL;
    IRDirty* di       = NULL;

    const Int THRESH = 4096 * 4; // somewhat arbitrary
    const Int rz_szB = VG_STACK_REDZONE_SZB;

    tyAddr = typeOfIRExpr( sbOut->tyenv, addr );
    tl_assert(tyAddr == Ity_I32 || tyAddr == Ity_I64);

    if (isWrite) {
        hName = "colo_handle_write";
        hAddr = &colo_handle_write;
    } else {
        hName = "colo_handle_read";
        hAddr = &colo_handle_read;
    }

    argv = mkIRExprVec_2( addr, mkIRExpr_HWord(szB) );

    /* Add the helper. */
    tl_assert(hName);
    tl_assert(hAddr);
    tl_assert(argv);
    di = unsafeIRDirty_0_N( 2/*regparms*/,
            hName, VG_(fnptr_to_fnentry)( hAddr ),
            argv );

    /* Generate the guard condition: "(addr - (SP - RZ)) >u N", for
       some arbitrary N.  If that fails then addr is in the range (SP -
       RZ .. SP + N - RZ).  If N is smallish (a page?) then we can say
       addr is within a page of SP and so can't possibly be a heap
       access, and so can be skipped. */

    IRTemp sp = newIRTemp(sbOut->tyenv, tyAddr);
    addStmtToIRSB( sbOut, assign(sp, IRExpr_Get(goff_sp, tyAddr)));

    IRTemp sp_minus_rz = newIRTemp(sbOut->tyenv, tyAddr);
    addStmtToIRSB(
            sbOut,
            assign(sp_minus_rz,
                tyAddr == Ity_I32
                ? binop(Iop_Sub32, mkexpr(sp), mkU32(rz_szB))
                : binop(Iop_Sub64, mkexpr(sp), mkU64(rz_szB)))
            );

    IRTemp diff = newIRTemp(sbOut->tyenv, tyAddr);
    addStmtToIRSB(
            sbOut,
            assign(diff,
                tyAddr == Ity_I32 
                ? binop(Iop_Sub32, addr, mkexpr(sp_minus_rz))
                : binop(Iop_Sub64, addr, mkexpr(sp_minus_rz)))
            );

    IRTemp guard = newIRTemp(sbOut->tyenv, Ity_I1);
    addStmtToIRSB(
            sbOut,
            assign(guard,
                tyAddr == Ity_I32 
                ? binop(Iop_CmpLT32U, mkU32(THRESH), mkexpr(diff))
                : binop(Iop_CmpLT64U, mkU64(THRESH), mkexpr(diff)))
            );
    di->guard = mkexpr(guard);

    addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
}

static IRSB* colo_instrument ( VgCallbackClosure* closure,
        IRSB* sbIn,
        const VexGuestLayout* layout,
        const VexGuestExtents* vge,
        const VexArchInfo* archinfo_host,
        IRType gWordTy, IRType hWordTy )
{
    Int   i;
    IRSB* sbOut;
    IRTypeEnv* tyenv = sbIn->tyenv;

    const Int goff_sp = layout->offset_SP;

    // We increment the instruction count in two places:
    // - just before any Ist_Exit statements;
    // - just before the IRSB's end.
    // In the former case, we zero 'n' and then continue instrumenting.

    sbOut = deepCopyIRSBExceptStmts(sbIn);

    // Copy verbatim any IR preamble preceding the first IMark
    i = 0;
     while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
         addStmtToIRSB( sbOut, sbIn->stmts[i] );
         i++;
    }

    for (/*use current i*/; i < sbIn->stmts_used; i++) {
        IRStmt* st = sbIn->stmts[i];

        if (!st || st->tag == Ist_NoOp) continue;

        switch (st->tag) {
            case Ist_WrTmp: {
                IRExpr* data = st->Ist.WrTmp.data;
                if (data->tag == Iex_Load) {
                    IRExpr* aexpr = data->Iex.Load.addr;
                    // Note also, endianness info is ignored.  I guess
                    // that's not interesting.
                    addMemEvent( sbOut, False/*!isWrite*/,
                            sizeofIRType(data->Iex.Load.ty),
                            aexpr, goff_sp );
                }
                break;
            }

            case Ist_Store: {
                IRExpr* data  = st->Ist.Store.data;
                IRExpr* aexpr = st->Ist.Store.addr;
                addMemEvent( sbOut, True/*isWrite*/, 
                        sizeofIRType(typeOfIRExpr(tyenv, data)),
                        aexpr, goff_sp );
                break;
            }

            case Ist_Dirty: {
                Int      dataSize;
                IRDirty* d = st->Ist.Dirty.details;
                if (d->mFx != Ifx_None) {
                    /* This dirty helper accesses memory.  Collect the details. */
                    tl_assert(d->mAddr != NULL);
                    tl_assert(d->mSize != 0);
                    dataSize = d->mSize;
                    // Large (eg. 28B, 108B, 512B on x86) data-sized
                    // instructions will be done inaccurately, but they're
                    // very rare and this avoids errors from hitting more
                    // than two cache lines in the simulation.
                    if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify)
                        addMemEvent( sbOut, False/*!isWrite*/,
                                dataSize, d->mAddr, goff_sp );
                    if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify)
                        addMemEvent( sbOut, True/*isWrite*/,
                                dataSize, d->mAddr, goff_sp );
                } else {
                    tl_assert(d->mAddr == NULL);
                    tl_assert(d->mSize == 0);
                }
                break;
            }

            case Ist_CAS: {
                /* We treat it as a read and a write of the location.  I
                think that is the same behaviour as it was before IRCAS
                was introduced, since prior to that point, the Vex
                front ends would translate a lock-prefixed instruction
                into a (normal) read followed by a (normal) write. */
                Int    dataSize;
                IRCAS* cas = st->Ist.CAS.details;
                tl_assert(cas->addr != NULL);
                tl_assert(cas->dataLo != NULL);
                dataSize = sizeofIRType(typeOfIRExpr(tyenv, cas->dataLo));
                if (cas->dataHi != NULL)
                    dataSize *= 2; /* since it's a doubleword-CAS */
                addMemEvent( sbOut, False/*!isWrite*/,
                        dataSize, cas->addr, goff_sp );
                addMemEvent( sbOut, True/*isWrite*/,
                        dataSize, cas->addr, goff_sp );
                break;
            }

            case Ist_LLSC: {
                IRType dataTy;
                if (st->Ist.LLSC.storedata == NULL) {
                    /* LL */
                    dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
                    addMemEvent( sbOut, False/*!isWrite*/,
                            sizeofIRType(dataTy),
                            st->Ist.LLSC.addr, goff_sp );
                } else {
                    /* SC */
                    dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
                    addMemEvent( sbOut, True/*isWrite*/,
                            sizeofIRType(dataTy),
                            st->Ist.LLSC.addr, goff_sp );
                }
                break;
            }

            default:
               break;
        }

        addStmtToIRSB( sbOut, st );
    }

    return sbOut;
}

//------------------------------------------------------------//
//--- Finalisation                                         ---//
//------------------------------------------------------------//

static void colo_fini(Int exit_status)
{
    VG_(OSetGen_Destroy)(visited_edges);

    VG_(fprintf)(output, "}");
    VG_(fclose)(output);

    VG_(fprintf)(graphsize, "%d\n", nodes_count);
    VG_(fclose)(graphsize);

    VG_(HT_destruct)(visited_nodes, VG_(free));
}

//------------------------------------------------------------//
//--- Arguments                                            ---//
//------------------------------------------------------------//

static Bool colo_process_cmd_line_option(const HChar* arg)
{
    const HChar* tmp_str;
    if(VG_STR_CLO(arg, "--cologrind-out-file", tmp_str)) {
        output = VG_(fopen)(tmp_str, VKI_O_CREAT|VKI_O_WRONLY|VKI_O_TRUNC, VKI_S_IRUSR|VKI_S_IWUSR);
        VG_(fprintf)(output, "digraph {\n");
    }
    return True;
}

static void colo_print_usage(void)
{
    VG_(printf)(
"    --cologrind-out-file=path       generates a dot file in path\n"
    );
}

static void colo_print_debug_usage(void)
{
    VG_(printf)(
"    (none)\n"
    );
}

//------------------------------------------------------------//
//--- Initialisation                                       ---//
//------------------------------------------------------------//

static void colo_post_clo_init(void) {}

static void colo_pre_clo_init(void)
{
    VG_(details_name)            ("Cologrind");
    VG_(details_version)         (NULL);
    VG_(details_description)     ("a cool colors collector");
    VG_(details_copyright_author)(
            "Copyright (C) 2018, and GNU GPL'd, by Sigmoid");
    VG_(details_bug_reports_to)  (VG_BUGS_TO);

    VG_(basic_tool_funcs)          (colo_post_clo_init,
            colo_instrument,
            colo_fini);
    VG_(needs_command_line_options)(colo_process_cmd_line_option,
                                    colo_print_usage,
                                    colo_print_debug_usage);
//    VG_(track_pre_mem_read)        ( colo_handle_noninsn_read );
//    VG_(track_post_mem_write)      ( colo_handle_noninsn_write );

    visited_nodes = VG_(HT_construct)("visited_nodes");
    visited_edges = VG_(OSetGen_Create)(/*keyOff*/0,
                                        edgesCmp,
                                        VG_(malloc), "ve.1", VG_(free));

    graphsize = VG_(fopen)("graphsize", VKI_O_CREAT|VKI_O_WRONLY, VKI_S_IRUSR|VKI_S_IWUSR);
}

VG_DETERMINE_INTERFACE_VERSION(colo_pre_clo_init)

//--------------------------------------------------------------------//
//--- end                                              colo_main.c ---//
//--------------------------------------------------------------------//
