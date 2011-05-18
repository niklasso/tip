/*************************************************************************************[BasicBmc.cc]
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

#include "minisat/core/Solver.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "tip/bmc/Bmc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Some helpers:
//

class Unroller {
    const TipCirc& tip;
    Circ&          unroll_circ;
    vec<Sig>       flop_front;

    void initialize();
public:
    Unroller(const TipCirc& t, vec<IFrame>& ui, Circ& uc);
    void operator()(GMap<Sig>& unroll_map);

    vec<IFrame>&   unroll_inps;
};


Unroller::Unroller(const TipCirc& t, vec<IFrame>& ui, Circ& uc) 
    : tip(t), unroll_circ(uc), unroll_inps(ui){ initialize(); }


void Unroller::initialize()
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


void Unroller::operator()(GMap<Sig>& unroll_map){
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
// Implementation of Basic BMC:
//

void basicBmc(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle)
{
    Circ               uc;                  // Unrolled circuit.
    vec<IFrame>        ui;                  // Unrolled set of input frames.
    Unroller           unroll(tip, ui, uc); // Unroller-helper object.
    Solver             s;                   // SAT-solver and clausifyer for unrolled circuit.
    Clausifyer<Solver> cl(uc, s);
    GMap<Sig>          umap;                // Reusable unroll-map.

    //s.verbosity = 1;
    for (uint32_t i = 0; i < stop_cycle; i++){
        unroll(umap);
        //printf(" ... unrolling cycle %d\n", i);

        if (i < begin_cycle)
            continue;

        // Do SAT-tests:
        int unresolved_safety = 0;
        for (int j = 0; j < tip.all_props.size(); j++){
            Property p = tip.all_props[j];
            if (tip.properties.propType(p) != ptype_Safety || tip.properties.propStatus(p) != pstat_Unknown)
                continue;
            
            Sig psig_orig   = tip.properties.propSig(p);
            Sig psig_unroll = umap[gate(psig_orig)] ^ sign(psig_orig);
            assert(psig_unroll != sig_Undef);
            Lit plit = cl.clausify(psig_unroll);

            printf(" --- cycle=%3d, vars=%8.3g, clauses=%8.3g, conflicts=%8.3g\n", i, (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);

            //printf(" ... testing property %d\n", p);
            if (s.solve(~plit)){
                // Property falsified, create and extract trace:
                Trace             cex    = tip.traces.newTrace();
                vec<vec<lbool> >& frames = tip.traces.getFrames(cex);
                for (int k = 0; k < unroll.unroll_inps.size(); k++){
                    frames.push();
                    for (int l = 0; l < unroll.unroll_inps[k].size(); l++)
                        frames.last().push(cl.modelValue(unroll.unroll_inps[k][l]));
                }
                //printf (" ... property falsified.\n");
                tip.properties.setPropFalsified(p, cex);
            }else{
                unresolved_safety++;
                //printf (" ... property true.\n");
            }
        }

        // Terminate if all safety properties resolved:
        if (unresolved_safety == 0)
            break;
    }
    printf(" --- done, vars=%8.3g, clauses=%8.3g, conflicts=%8.3g\n", (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);
    s.printStats();
}

};
