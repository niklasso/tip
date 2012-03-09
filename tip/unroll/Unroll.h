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

    // Remember the original state of the circuit to allow limited addition to the circuit without
    // disturbing the unrolling. Ok to add: unnamed inputs, gates, flops, but NOT named inputs or
    // properties.
    Gate           last_gate;

    void initReset ();
    void initRandom();
public:

    UnrollCirc(const TipCirc& t, vec<IFrame>& ui, Circ& uc, bool reset);
    void operator()(GMap<Sig>& unroll_map);
    Sig  front   (int i) const { return flop_front[i]; }
    int  numFlops()      const { return flop_front.size(); }
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


class UnrolledCirc : public Circ
{
    const TipCirc&  tip;
    GMap<Sig>       imap;
    vec<GMap<Sig> > umap;
    bool            random_init;

 public:
    UnrolledCirc(const TipCirc& t, bool random_init = true);

    Sig  unroll            (Sig  x, unsigned cycle);
    Sig  unroll            (Gate g, unsigned cycle);

    void unrollProperties  (unsigned cycle, vec<Sig>& xs);
    void unrollSafeProps   (unsigned cycle, vec<Sig>& xs);
    void unrollLiveProps   (unsigned cycle, vec<Sig>& xs);
    void unrollConstraints (unsigned cycle, vec<vec<Sig> >& xs);
    void unrollFlops       (unsigned cycle, vec<Sig>& xs);
    void unrollFlopsNext   (unsigned cycle, vec<Sig>& xs);

    Sig  lookup            (Sig  x, unsigned cycle) const;
    Sig  lookup            (Gate g, unsigned cycle) const;
    void extractUsedInputs (unsigned cycle, vec<Sig>& xs) const;
    void extractUsedFlops  (unsigned cycle, vec<Sig>& xs) const;

    Sig  lookupInit        (Sig x)  const;
    Sig  lookupInit        (Gate g) const;

    void extractUsedInitInputs
                           (vec<Sig>& xs) const;
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
// Inline implementations:

inline Sig UnrolledCirc::unroll(Sig  x, unsigned cycle){ return unroll(gate(x), cycle) ^ sign(x); }

inline Sig UnrolledCirc::lookup(Gate g, unsigned cycle) const {
    return g == gate_True ? sig_True :
        (cycle < (unsigned)umap.size() && umap[cycle].has(g)) ? umap[cycle][g] : sig_Undef; }

inline Sig UnrolledCirc::lookup(Sig  x, unsigned cycle) const {
    Sig ret = lookup(gate(x), cycle);
    return ret != sig_Undef ? ret ^ sign(x) : sig_Undef; }

inline Sig UnrolledCirc::lookupInit(Gate g) const { return imap.has(g) ? imap[g] : sig_Undef; }
inline Sig UnrolledCirc::lookupInit(Sig x)  const {
    Sig ret = lookupInit(gate(x));
    return ret != sig_Undef ? ret ^ sign(x) : sig_Undef; }


//=================================================================================================
} // namespace Tip
#endif
