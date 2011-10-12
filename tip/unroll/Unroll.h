/****************************************************************************************[Unroll.h]
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

#ifndef Tip_Unroll_h
#define Tip_Unroll_h

#include "minisat/simp/SimpSolver.h"
#include "mcl/CircPrelude.h"
#include "tip/TipCirc.h"

namespace Tip {

class UnrollCirc {
    const TipCirc& tip;
    Circ&          unroll_circ;
    vec<IFrame>&   unroll_inps;
    vec<Sig>       flop_front;

    void initReset ();
    void initRandom();
public:

    UnrollCirc(const TipCirc& t, vec<IFrame>& ui, Circ& uc, bool reset);
    void operator()(GMap<Sig>& unroll_map);
    Sig  front   (int i) const { return flop_front[i]; }
};


class UnrollCirc2
{
    const TipCirc& tip;
    Circ&          ucirc;
    vec<Sig>       flop_front;
public:

    UnrollCirc2(const TipCirc& t, Circ& uc, GMap<Sig>& imap);  // Initialize with reset circuit.
    UnrollCirc2(const TipCirc& t, Circ& uc);                   // Initialize with random flops.

    void operator()(GMap<Sig>& umap);
};


class UnrollCnf
{
public:
    void pinGate(Gate g);

    UnrollCnf(const TipCirc& t, SimpSolver& us, GMap<Lit>& imap);  // Initialize with reset circuit.
    UnrollCnf(const TipCirc& t, SimpSolver& us);                   // Initialize with random flops.

    void operator()(GMap<Sig>& umap);

private:
    const TipCirc& tip;
    SimpSolver&    usolver;
    GMap<char>     pinned;

    bool isPinned(Gate g);
};


//=================================================================================================
// Convenience helpers:


template<class T>
void extractResetInput(const TipCirc& tip, const GMap<T>& m, vec<vec<T> >& frames, T undef)
{
    frames.push();
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
        if (tip.init.number(*iit) != UINT32_MAX){
            Gate inp = *iit;
            frames.last().growTo(tip.init.number(inp)+1, undef);
            frames.last()[tip.init.number(inp)] = m[*iit];
        }
}


template<class T>
void extractInput(const TipCirc& tip, const GMap<T>& m, vec<vec<T> >& frames, T undef)
{
    frames.push();
    for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
        if (tip.main.number(*iit) != UINT32_MAX){
            Gate inp = *iit;
            frames.last().growTo(tip.main.number(inp)+1, undef);
            frames.last()[tip.main.number(inp)] = m[*iit];
        }
}


//=================================================================================================
} // namespace Tip
#endif
