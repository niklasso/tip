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
    : tip(t), unroll_circ(uc), unroll_inps(ui)
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
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd() ; ++iit){
        Gate inp = *iit;
        assert(!sign(init_map[*iit]));
        assert(tip.init.number(inp) != UINT32_MAX);
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
    for (int i = 0; i < tip.flps.size(); i++)
        unroll_map[tip.flps[i]] = flop_front[i];
    copyCirc(tip.main, unroll_circ, unroll_map);

    unroll_inps.push();
    for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
        Gate inp = *iit;
        assert(!sign(unroll_map[*iit]));
        assert(tip.main.number(inp) != UINT32_MAX);
        unroll_inps.last().growTo(tip.main.number(inp)+1, gate_Undef);
        unroll_inps.last()[tip.main.number(inp)] = gate(unroll_map[*iit]);
    }

    for (int i = 0; i < tip.flps.size(); i++){
        Gate flop     = tip.flps[i];
        Sig  next     = tip.flps.next(flop);
        flop_front[i] = unroll_map[gate(next)] ^ sign(next);
    }
}


//=================================================================================================
} // namespace Tip
