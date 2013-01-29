/**************************************************************************************[SimpBmc.cc]
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

#include "minisat/simp/SimpSolver.h"
#include "minisat/utils/System.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "tip/unroll/Bmc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Some helpers:
//

typedef vec<Var> LIFrame;

class SimpUnroller {
    const TipCirc& tip;
    SimpSolver&    solver;
    vec<Lit>       flop_front;

    void initialize();
public:
    SimpUnroller(const TipCirc& t, vec<LIFrame>& ui, SimpSolver& solver);
    void operator()(Clausifyer<SimpSolver>& unroll_cl);

    vec<LIFrame>&  unroll_inps;
};


SimpUnroller::SimpUnroller(const TipCirc& t, vec<LIFrame>& ui, SimpSolver& s) 
    : tip(t), solver(s), unroll_inps(ui) { initialize(); }


void SimpUnroller::initialize()
{
    // Clausify initial circuit:
    Clausifyer<SimpSolver> cl(tip.init, solver);
    for (int i = 0; i < tip.flps.size(); i++){
        Lit l = cl.clausify(tip.flps.init(tip.flps[i]));
        // solver.setFrozen(var(l), true);
        solver.freezeVar(var(l));
        flop_front.push(l);
    }

    // Extract input variables:
    unroll_inps.push();
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd() ; ++iit)
        if (tip.init.number(*iit) != UINT32_MAX){
            Gate     inp = *iit;
            uint32_t num = tip.init.number(inp);
            Lit      l   = cl.lookup(inp);
            assert(!sign(l));
            unroll_inps.last().growTo(num+1, var_Undef);
            unroll_inps.last()[num] = var(l);
        }
}


void SimpUnroller::operator()(Clausifyer<SimpSolver>& unroll_cl){
    unroll_cl.clear();
    // Bind old flop outputs to new flop inputs:
    for (int i = 0; i < tip.flps.size(); i++){
        assert(!solver.isEliminated(var(flop_front[i])));
        //solver.setFrozen(var(flop_front[i]), false);
        unroll_cl.clausifyAs(tip.flps[i], flop_front[i]);
    }

    // Clausify flop definitions:
    for (int i = 0; i < tip.flps.size(); i++){
        Lit l = unroll_cl.clausify(tip.flps.next(tip.flps[i]));
        //solver.setFrozen(var(l), true);
        solver.freezeVar(var(l));
        flop_front[i] = l;
    }

    // Assert constraints:
    for (unsigned j = 0; j < tip.cnstrs.size(); j++){
        Sig cx = tip.cnstrs[j][0];
        Lit lx = unroll_cl.clausify(cx);
        for (int k = 1; k < tip.cnstrs[j].size(); k++){
            Sig cy = tip.cnstrs[j][k];
            Lit ly = unroll_cl.clausify(cy);
            solver.addClause(~lx, ly);
            solver.addClause(~ly, lx);
        }
    }

    // Clausify safety properties:
    for (SafeProp p = 0; p < tip.safe_props.size(); p++){
        if (tip.safe_props[p].stat != pstat_Unknown)
            continue;
        Lit l = unroll_cl.clausify(tip.safe_props[p].sig);
        solver.freezeVar(var(l));
    }

    // Extract input variables:
    unroll_inps.push();
    for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
        if (tip.main.number(*iit) != UINT32_MAX){
            Gate     inp = *iit;
            uint32_t num = tip.main.number(inp);
            Lit      l   = unroll_cl.lookup(inp);
            assert(!sign(l));
            unroll_inps.last().growTo(num+1, var_Undef);
            unroll_inps.last()[num] = var(l);
        }
}


//=================================================================================================
// Implementation of Simplifying BMC:
//

void simpBmc(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle)
{
    double                 time_before = cpuTime();
    double                 solve_time  = 0;
    double                 simp_time   = 0;
    vec<LIFrame>           ui;                  // Unrolled set of input frames.
    SimpSolver             s;                   // SAT-solver.
    SimpUnroller           unroll(tip, ui, s);  // Unroller-helper object.
    Clausifyer<SimpSolver> ucl(tip.main, s);    // Reusable clausifyer.
    vec<Var>               frozen_vars;         // Reusable list of frozen variables.

    //s.verbosity = 1;
    for (uint32_t i = 0; i < stop_cycle; i++){
        unroll(ucl);

        if (i < begin_cycle)
            continue;

        // Do CNF-level simplification:
        double simp_time_before = cpuTime();
        s.eliminate();
        simp_time += cpuTime() - simp_time_before;

        // Do SAT-tests:
        int unresolved_safety = 0;
        for (SafeProp p = 0; p < tip.safe_props.size(); p++){
            if (tip.safe_props[p].stat != pstat_Unknown)
                continue;
            
            Lit    plit       = ucl.lookup(tip.safe_props[p].sig);
            double total_time = cpuTime() - time_before;
            if (tip.verbosity >= 1){
                printf(" --- k=%3d, vrs=%8.3g, cls=%8.3g, con=%8.3g",
                       i, (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);
                if (tip.verbosity >= 2)
                    printf(", time(solve=%6.1f s, simp=%6.1f s, total=%6.1f s)\n",
                           solve_time, simp_time, total_time);
                else
                    printf("\n");
                fflush(stdout);
            }

            double solve_time_before = cpuTime();
            bool ret = s.solve(~plit, false, false);
            solve_time += cpuTime() - solve_time_before;

            if (ret){
                // Property falsified, create and extract trace:
                Trace             cex    = tip.newTrace();
                vec<vec<lbool> >& frames = tip.traces[cex].frames;
                for (int k = 0; k < unroll.unroll_inps.size(); k++){
                    frames.push();
                    for (int l = 0; l < unroll.unroll_inps[k].size(); l++)
                        if (unroll.unroll_inps[k][l] != var_Undef)
                            frames.last().push(s.modelValue(unroll.unroll_inps[k][l]));
                        else
                            frames.last().push(l_Undef);
                }
                tip.adaptTrace(frames);
                tip.setFalsifiedSafe(p, cex, "sbmc");
            }else{
                unresolved_safety++;
                assert(s.value(plit) == l_True);
                tip.setRadiusSafe(p, i+1, "sbmc");
            }
        }

        // Thaw all frozen variables:
        s.thaw();

        // Terminate if all safety properties resolved:
        if (unresolved_safety == 0)
            break;
    }

    if (tip.verbosity >= 1){
        double total_time = cpuTime() - time_before;
        printf(" --- done,  vrs=%8.3g, cls=%8.3g, con=%8.3g",
               (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);
        if (tip.verbosity >= 2)
            printf(", time(solve=%6.1f s, simp=%6.1f s, total=%6.1f s)\n",
                   solve_time, simp_time, total_time);
        else
            printf("\n");
        s.printStats();
        fflush(stdout);
    }
}

};
