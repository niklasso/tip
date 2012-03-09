/***************************************************************************************[Unroll.cc]
Copyright (c) 2011, Niklas Sorensson
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "tip/unroll/Unroll.h"

namespace Tip {


UnrollCirc::UnrollCirc(const TipCirc& t, vec<IFrame>& ui, Circ& uc, bool reset) 
    : tip(t), unroll_circ(uc), unroll_inps(ui), last_gate(t.main.lastGate())
{ 
    if (reset)
        initReset();
    else
        initRandom();
}


void UnrollCirc::initReset()
{
    GMap<Sig> init_map;
    copyCirc(tip.init, unroll_circ, init_map);

    unroll_inps.push();
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd() ; ++iit)
        if (tip.init.number(*iit) != UINT32_MAX){
            Gate inp = *iit;
            assert(!sign(init_map[*iit]));
            unroll_inps.last().growTo(tip.init.number(inp)+1, gate_Undef);
            unroll_inps.last()[tip.init.number(inp)] = gate(init_map[*iit]);
        }

    for (int i = 0; i < tip.flps.size(); i++)
        flop_front.push(tip.flps.init(tip.flps[i]));
    map(init_map, flop_front);
}


void UnrollCirc::initRandom()
{
    // TODO: traces for unrollings rooted in a random state does not yet make much sense. How to
    // handle that? 1) move trace handling out of this class 2) somehow also capture the initial
    // values of flops. Let's see what makes most sense later.
    unroll_inps.push();
    for (int i = 0; i < tip.flps.size(); i++)
        flop_front.push(unroll_circ.mkInp());
}


void UnrollCirc::operator()(GMap<Sig>& unroll_map){
    unroll_map.clear();
    unroll_map.growTo(tip.main.lastGate(), sig_Undef);
    for (int i = 0; i < numFlops(); i++)
        unroll_map[tip.flps[i]] = flop_front[i];
    copyCirc(tip.main, unroll_circ, unroll_map, last_gate);

    unroll_inps.push();
    for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
        if (tip.main.number(*iit) != UINT32_MAX){
            Gate inp = *iit;
            assert(!sign(unroll_map[*iit]));
            unroll_inps.last().growTo(tip.main.number(inp)+1, gate_Undef);
            unroll_inps.last()[tip.main.number(inp)] = gate(unroll_map[*iit]);
        }

    for (int i = 0; i < numFlops(); i++){
        Gate flop     = tip.flps[i];
        Sig  next     = tip.flps.next(flop);
        flop_front[i] = unroll_map[gate(next)] ^ sign(next);
    }
}

//=================================================================================================
// UnrollCirc2 (new attempt):


UnrollCirc2::UnrollCirc2(const TipCirc& t, Circ& uc, GMap<Sig>& imap)
    : tip(t), ucirc(uc)
{ 
    imap.clear();
    copyCirc(tip.init, ucirc, imap);
    for (int i = 0; i < tip.flps.size(); i++)
        flop_front.push(tip.flps.init(tip.flps[i]));
    map(imap, flop_front);
}


UnrollCirc2::UnrollCirc2(const TipCirc& t, Circ& uc)
    : tip(t), ucirc(uc)
{ 
    for (int i = 0; i < tip.flps.size(); i++)
        flop_front.push(ucirc.mkInp());
}


void UnrollCirc2::operator()(GMap<Sig>& umap){
    umap.clear();
    umap.growTo(tip.main.lastGate(), sig_Undef);
    for (int i = 0; i < tip.flps.size(); i++)
        umap[tip.flps[i]] = flop_front[i];
    copyCirc(tip.main, ucirc, umap);

    for (int i = 0; i < tip.flps.size(); i++){
        Gate flop     = tip.flps[i];
        Sig  next     = tip.flps.next(flop);
        flop_front[i] = umap[gate(next)] ^ sign(next);
    }
}

//=================================================================================================
// UnrolledCirc:

UnrolledCirc::UnrolledCirc(const TipCirc& t, bool ri) 
    : tip(t), random_init(ri){}

Sig UnrolledCirc::unroll(Gate g, unsigned cycle)
{
    // printf(" ... unrollGate (cycle=%d): ", cycle);
    // printGate(g);
    // printf("\n");
    
    umap.growTo(cycle+1);
    umap[cycle].growTo(g, sig_Undef);
    if (umap[cycle][g] != sig_Undef){
        //printf(" ... got here cycle=%d (cache)\n", cycle);
        return umap[cycle][g];
    }

    Sig ret = sig_Undef;
    if (type(g) == gtype_And){
        //printf(" ... got here cycle=%d (and)\n", cycle);
        Sig xl = tip.main.lchild(g);
        Sig xr = tip.main.rchild(g);
        ret = mkAnd(unroll(xl, cycle), unroll(xr, cycle));
//     }else if (type(g) == gtype_Inp && cycle > 0 && tip.flps.isFlop(g)){
//         //printf(" ... got here cycle=%d (flop-next)\n", cycle);
//         ret = unrollSig(tip.flps.next(g), cycle-1);
    }else if (tip.flps.isFlop(g)){
        if (cycle > 0)
            ret = unroll(tip.flps.next(g), cycle-1);
        else if (random_init)
            ret = mkInp();
        else
            ret = copySig(tip.init, *this, tip.flps.init(g), imap);
    }else if (type(g) == gtype_Inp){
        ret = mkInp();
        //printf(" ... got here cycle=%d (input)\n", cycle);
        // if (tip.flps.isFlop(g))
        //     inputs.push(mkSig(g));
    }else{
        //printf(" ... got here cycle=%d (const)\n", cycle);
        assert(type(g) == gtype_Const);
        ret = sig_True;
    }

    umap[cycle][g] = ret;
    return ret;
}

void UnrolledCirc::extractUsedInputs(unsigned cycle, vec<Sig>& xs) const
{
    for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
        Sig inp = lookup(*iit, cycle);
        if (inp != sig_Undef)
            xs.push(inp);
    }
}

void UnrolledCirc::extractUsedInitInputs(vec<Sig>& xs) const
{
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit){
        Sig inp = lookupInit(*iit);
        if (inp != sig_Undef)
            xs.push(inp);
    }
}


void UnrolledCirc::extractUsedFlops(unsigned cycle, vec<Sig>& xs) const
{
    for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
        Sig flp = lookup(*flit, cycle);
        if (flp != sig_Undef)
            xs.push(flp);
    }
}


void UnrolledCirc::unrollProperties(unsigned cycle, vec<Sig>& xs)
{
    unrollSafeProps(cycle, xs);
    unrollLiveProps(cycle, xs);
}


void UnrolledCirc::unrollSafeProps(unsigned cycle, vec<Sig>& xs)
{
    for (SafeProp p = 0; p < tip.safe_props.size(); p++)
        if (tip.safe_props[p].stat == pstat_Unknown)
            xs.push(unroll(tip.safe_props[p].sig, cycle));
}


void UnrolledCirc::unrollLiveProps(unsigned cycle, vec<Sig>& xs)
{
    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown){
            assert(tip.live_props[p].sigs.size() == 1);
            xs.push(unroll(tip.live_props[p].sigs[0], cycle));
        }
}


void UnrolledCirc::unrollConstraints(unsigned cycle, vec<vec<Sig> >& xs)
{
    for (unsigned i = 0; i < tip.cnstrs.size(); i++){
        xs.push();
        for (int j = 0; j < tip.cnstrs[i].size(); j++)
            xs.last().push(unroll(tip.cnstrs[i][j], cycle));
    }
}


void UnrolledCirc::unrollFlops(unsigned cycle, vec<Sig>& xs)
{
    for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
        xs.push(unroll(*flit, cycle));
}


void UnrolledCirc::unrollFlopsNext(unsigned cycle, vec<Sig>& xs)
{
    for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
        xs.push(unroll(tip.flps.next(*flit), cycle));
}


//=================================================================================================
// UnrollCnf: (sketch)

void UnrollCnf::pinGate(Gate g)
{
    pinned.growTo(g, 0);
    pinned[g] = 1;
}


bool UnrollCnf::isPinned(Gate g)
{
    return pinned.has(g) && pinned[g];
}


UnrollCnf::UnrollCnf(const TipCirc& t, SimpSolver& us, GMap<Lit>& imap)
    : tip(t), usolver(us)
{
}


UnrollCnf::UnrollCnf(const TipCirc& t, SimpSolver& us)
    : tip(t), usolver(us)
{
}


void UnrollCnf::operator()(GMap<Sig>& umap)
{
}


//=================================================================================================
} // namespace Tip
