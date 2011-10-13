/*************************************************************************************[Liveness.cc]
Copyright (c) 2011, Niklas Sorensson, Koen Claessen

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

#include "minisat/core/Solver.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "tip/liveness/Liveness.h"
#include "tip/induction/Induction.h"
#include "tip/reductions/RemoveUnused.h"
#include "tip/unroll/Bmc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Liveness Checking:
//

void embedLivenessBiere(TipCirc& tip, int kind)
{
    Sig just = sig_Undef;
    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown){
            if (just != sig_Undef)
                printf("ERROR! 'checkLiveness()' only works with a single liveness property."), exit(1);
            printf("=== Biere-trick for property %d, kind=%d ===\n", p, kind);
            assert(tip.live_props[p].sigs.size() == 1);
            just = tip.live_props[p].sigs[0];
        }

#if 0
    if ( tip.cnstrs.size() > 0 ) {
        printf("Preparing for %d constraints.\n", tip.cnstrs.size());
        Sig conj = sig_True;
        for ( uint32_t i = 0; i < tip.cnstrs.size(); i++ ) {
            ;
            if ( tip.cnstrs[i].size() > 0 )
                for ( int j = 0; j < tip.cnstrs[i].size(); j++ )
                    conj = tip.main.mkAnd(conj, tip.main.mkOr(~(j > 0 ? tip.cnstrs[i][j-1] : tip.cnstrs[i].last()), tip.cnstrs[i][j]));
        }

        Gate next_conj = gate(tip.main.mkInp());
        Sig conj_ = tip.main.mkAnd(mkSig(next_conj), conj);
        tip.flps.define(next_conj, conj_, sig_True);
        just = tip.main.mkAnd(just, conj_);
        tip.cnstrs.clear();
    }
#endif
    
    // implementing Biere circuit
    Sig bad = sig_False;
    if ( kind == 0 ) {
        // Biere trick with save signal that can save multiple times
        Sig save = tip.main.mkInp();
        
        // copying flops
        vec<Gate> s_orig;
        vec<Gate> s_copy;
        int nflops = tip.flps.size(); // important to save this, since it will change in the loop!
        for (int i = 0; i < nflops; i++) {
            Gate s_o = tip.flps[i];
            Gate s_c = gate(tip.main.mkInp());
            s_orig.push(s_o);
            s_copy.push(s_c);
            tip.flps.define(s_c, tip.main.mkMux(save, mkSig(s_o), mkSig(s_c)), tip.flps.init(s_o));
        }
        
        // triggered
        Gate triggered = gate(tip.main.mkInp());
        tip.flps.define(triggered, tip.main.mkOr(just, tip.main.mkAnd(~save, mkSig(triggered))));

        // comparing saved state and outgoing state
        Sig eq = sig_True;
        for (int i = 0; i < s_orig.size(); i++) {
            Sig a = tip.flps.next(s_orig[i]);
            Sig b = tip.flps.next(s_copy[i]);
            eq = tip.main.mkAnd(eq, ~tip.main.mkXor(a,b));
        }
        
        // bad
        bad = tip.main.mkAnd(eq, tip.flps.next(triggered));
    } else if ( kind == 1 ) {
        // Biere trick with constant flops and no extra inputs
        
        // static flops
        vec<Gate> s_orig;
        vec<Gate> s_comp;
        int nflops = tip.flps.size(); // important to save this, since it will change in the loop!
        for (int i = 0; i < nflops; i++) {
            Gate s_o = tip.flps[i];
            Gate s_c = gate(tip.main.mkInp());
            s_orig.push(s_o);
            s_comp.push(s_c);
            tip.flps.define(s_c, mkSig(s_c), tip.init.mkInp());
        }
        
        // seen becomes true when we discover our incoming state is the static state
        Gate seen = gate(tip.main.mkInp());
        Sig eq_in = sig_True;
        for (int i = 0; i < s_orig.size(); i++) {
            Sig a = mkSig(s_orig[i]);
            Sig b = mkSig(s_comp[i]);
            eq_in = tip.main.mkAnd(eq_in, ~tip.main.mkXor(a,b));
        }
        Sig seen_ = tip.main.mkOr(eq_in, mkSig(seen));
        tip.flps.define(seen, seen_);

        // triggered becomes true when seen is true and just is true
        Gate triggered = gate(tip.main.mkInp());
        Sig triggered_ = tip.main.mkOr(tip.main.mkAnd(just,seen_), mkSig(triggered));
        tip.flps.define(triggered, triggered_);

        // comparing saved state and outgoing state
        Sig eq_out = sig_True;
        for (int i = 0; i < s_orig.size(); i++) {
            Sig a = tip.flps.next(s_orig[i]);
            Sig b = mkSig(s_comp[i]); // same as next(s_comp[i])
            eq_out = tip.main.mkAnd(eq_out, ~tip.main.mkXor(a,b));
        }
        
        // bad
        bad = tip.main.mkAnd(eq_out, triggered_);
    } else {
        printf("*** kind=%d not recognized!\n",kind);
        return;
    }
    tip.newSafeProp(~bad);
    tip.live_props.clear();
    removeUnusedLogic(tip);
    printf("After Biere trick and removing unused logic...\n");
    tip.stats();
}


void checkLivenessBiere(TipCirc& tip, int kind)
{
    embedLivenessBiere(tip,kind);
    // safety verification
    printf("--- calling safety checker ---\n");
    relativeInduction(tip);
}


void bmcLivenessBiere(TipCirc& tip, int kind)
{
    embedLivenessBiere(tip,kind);
    // safety verification
    printf("--- calling BMC ---\n");
    tip.bmc(0,UINT32_MAX);
}

//=================================================================================================
// Liveness Checking:
//

void checkLiveness(TipCirc& tip, int k)
{
    Sig just = sig_Undef;
    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown){
            if (just != sig_Undef)
                printf("ERROR! 'checkLiveness()' only works with a single liveness property."), exit(1);
            printf("=== Liveness checking of property #%d with k=%d ===\n", p, k);
            assert(tip.live_props[p].sigs.size() == 1);
            just = tip.live_props[p].sigs[0];
        }

#if 0
    if ( tip.cnstrs.size() > 0 ) {
        printf("Preparing for %d constraints.\n", tip.cnstrs.size());
        Sig conj = sig_True;
        for ( uint32_t i = 0; i < tip.cnstrs.size(); i++ ) {
            ;
            if ( tip.cnstrs[i].size() > 0 )
                for ( int j = 0; j < tip.cnstrs[i].size(); j++ )
                    conj = tip.main.mkAnd(conj, tip.main.mkOr(~(j > 0 ? tip.cnstrs[i][j-1] : tip.cnstrs[i].last()), tip.cnstrs[i][j]));
        }

        Gate next_conj = gate(tip.main.mkInp());
        Sig conj_ = tip.main.mkAnd(mkSig(next_conj), conj);
        tip.flps.define(next_conj, conj_, sig_True);
        just = tip.main.mkAnd(just, conj_);
        tip.cnstrs.clear();
    }
#endif
    
    Sig x = sig_True;
    for ( int i = 0; i < k; i++ ) {
        Gate y = gate(tip.main.mkInp());
        Sig justx = tip.main.mkAnd(just,x);
        tip.flps.define(y, tip.main.mkOr(justx,mkSig(y)));
        x = mkSig(y);
        tip.newSafeProp(~x);
    }
    tip.live_props.clear();
    printf("--- calling safety checker ---\n");
    relativeInduction(tip);
}


};

