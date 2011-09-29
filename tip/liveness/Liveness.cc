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

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Liveness Checking:
//

void checkLiveness(TipCirc& tip, LiveProp p, int k)
{
    printf("=== Liveness checking of property #%d with k=%d ===\n", p, k);
    Sig just = tip.live_props[p].sigs[0];
    Sig x = sig_True;
    for ( int i = 0; i < k; i++ ) {
        Gate y = gate(tip.main.mkInp());
        Sig justx = tip.main.mkAnd(just,x);
        tip.flps.define(y, tip.main.mkOr(justx,mkSig(y)));
        x = mkSig(y);
        tip.newSafeProp(~x);
    }
    printf("--- calling safety checker ---\n");
    relativeInduction(tip);
}

void checkLiveness(TipCirc& tip, LiveProp p)
{
    Solver solver;
    Lit lit_False = mkLit(solver.newVar());
    solver.addClause(~lit_False);
    assert(tip.live_props[p].sigs.size() == 1);
    
    // initialize state
    vec<Lit> state;
    for( int i = 0; i < tip.flps.size(); i++ )
        state.push(lit_False);
    
    // unroll
    vec<Lit> props;
    for( int t = 0; t < 100; t++ ) {
        Clausifyer<Solver> cl(tip.main, solver);

        // prev state
        for( int i = 0; i < tip.flps.size(); i++ )
            cl.clausifyAs(tip.flps[i], state[i]);
        
        // next state
        for( int i = 0; i < tip.flps.size(); i++ )
            state[i] = cl.clausify(tip.flps.next(tip.flps[i]));
        
        // prop
        props.push(cl.clausify(tip.live_props[p].sigs[0]));
    }
    
    // maximizing
    printf("Maximizing (%d props)...\n", props.size());
    int opt = 0;
    while ( 1 ) {
        // at least one of the (remaining) props should be true
        solver.addClause(props);

        // solve!
        if ( !solver.solve() )
            break;

        // find all true props
        for ( int i = 0; i < props.size(); i++ )
          if ( solver.modelValue(props[i]) != l_False ) {
              props[i] = props.last();
              props.pop();
          }
          else
              i++;
    }
    printf("True: %d (%d left)\n", opt, props.size());
}

void checkLiveness(TipCirc& tip)
{
    for( LiveProp p = 0; p < tip.live_props.size(); p++ ) {
        printf("=== liveness property #%d\n", p);
        checkLiveness(tip, p);
    }
}

};

