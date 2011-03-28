/*************************************************************************************[SimpBmc2.cc]
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

#include "minisat/mtl/Sort.h"
#include "minisat/simp/SimpSolver.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "mcl/DagShrink.h"
#include "mcl/Equivs.h"
#include "tip/bmc/Bmc.h"

namespace Tip {

using namespace Minisat;

namespace {

//=================================================================================================
// Some helpers:
//

struct CircInstance {
    Circ      circ;
    GMap<Sig> map;
};


struct FrontPair {
    Gate flop;
    Sig  sig;
    bool operator<(const FrontPair& fp){ return sig < fp.sig; }
};


void instantiateCirc(const TipCirc& t, const Equivs& eq, CircInstance& inst)
{
    // Create substitution from 'Equivs':
    GMap<Sig> subst; mkSubst(t.main, eq, subst);

    copyCircWithSubst(t.main, inst.circ, subst, inst.map);
    map(inst.map, subst);
    subst.moveTo(inst.map);

    // Debug (check that all gates in 'inst.map' is withing bounds for 'inst.circ':
    for (Gate g = t.main.firstGate(); g != gate_Undef; g = t.main.nextGate(g)){
        Sig x  = inst.map[g];
        assert(x <= ~mkSig(inst.circ.lastGate())); }

    // Remove redundant logic in instance:
    Circ        reduced_inst;
    GMap<Sig>   reduced_map(inst.circ.lastGate(), sig_Undef);
    CircMatcher cm;
    double      rnd_seed = 1234;

    // Copy all flop-definitions:
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_def_t    = t.flps.next(t.flps[i]);
        assert(flop_def_t != sig_Undef);
        Sig flop_def_inst = inst.map[gate(flop_def_t)] ^ sign(flop_def_t);
        assert(flop_def_inst != sig_Undef);
        dagShrink(inst.circ, reduced_inst, gate(flop_def_inst), cm, reduced_map, rnd_seed);
    }

    // Copy all property signals:
    for (int i = 0; i < t.all_props.size(); i++){
        Property p    = t.all_props[i];
        Sig prop_t    = t.properties.propSig(p);
        Sig prop_inst = inst.map[gate(prop_t)] ^ sign(prop_t);
        dagShrink(inst.circ, reduced_inst, gate(prop_inst), cm, reduced_map, rnd_seed);
    }

    // Fix the output circuit/map:
    reduced_inst.moveTo(inst.circ);
    map(reduced_map, inst.map);

    // Debug:
    printf(" ... clausifyInstance(): circuit-size=%d, main-size=%d\n", inst.circ.size(), t.main.size());

    // Check that all gates in 'inst.map' is withing bounds for 'inst.circ' or undefined:
    for (Gate g = t.main.firstGate(); g != gate_Undef; g = t.main.nextGate(g))
        assert(inst.map[g] == sig_Undef || inst.map[g] <= ~mkSig(inst.circ.lastGate()));
}


void clausifyInstance(const TipCirc& t, const CircInstance& inst, 
                      SimpSolver& s, GMap<Lit>& lit_map /* t.main => s */)
{
#if 1
    Clausifyer<SimpSolver> cl(inst.circ, s);

    // Clausify flop-definitions:
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_next_t            = t.flps.next(t.flps[i]);
        Sig flop_next_inst         = inst.map[gate(flop_next_t)] ^ sign(flop_next_t);
        Lit l                      = cl.clausify(flop_next_inst);
    }

    // Clausify properties:
    for (int i = 0; i < t.all_props.size(); i++){
        Property p            = t.all_props[i];
        Sig prop_t            = t.properties.propSig(p);
        Sig prop_inst         = inst.map[gate(prop_t)] ^ sign(prop_t);
        Lit l                 = cl.clausify(prop_inst);
    }

    // Extract references to all clausified gates:
    lit_map.clear();
    lit_map.growTo(t.main.lastGate(), lit_Undef);
    for (Gate g = t.main.firstGate(); g != gate_Undef; g = t.main.nextGate(g))
        if (inst.map.has(g) && inst.map[g] != sig_Undef){
            Lit l = cl.lookup(inst.map[g]);
            if (l != lit_Undef)
                lit_map[g] = l;
        }

    // TODO: freeze vars and simplify.
#else
    printf("ERROR! 'clausifyInstance()' Unimplemented!\n");
    exit(0);
#endif
}


void clausifyInit(const TipCirc& t,
                  SimpSolver& s, GMap<Lit>& lit_map /* t.main => s */)
{
    Clausifyer<SimpSolver> cl(t.init, s);
    lit_map.growTo(t.main.lastGate(), lit_Undef);
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_init = t.flps.init(t.flps[i]);
        lit_map[t.flps[i]] = cl.clausify(flop_init);
    }
}


void plugClausifiedInstance(const TipCirc& t, const SimpSolver& one, const GMap<Lit>& one_lit_map /* t.main => one */,
                            SimpSolver& s, GMap<Lit>& s_lit_map /* t.main => s */)
{
    printf("ERROR! 'plugClausifiedInstance()' Unimplemented!\n");
    exit(0);
}


void extractEquivsFromFront(const TipCirc& t, const vec<Sig>& front, Equivs& eqs)
{
    printf(" ... Called 'extractEquivsFromFront()':\n");
    eqs.clear();

    vec<FrontPair> front_pairs;
    for (int i = 0; i < t.flps.size(); i++){
        FrontPair fp = { t.flps[i], front[i] };
        front_pairs.push(fp);
    }
    sort(front_pairs);

    // printf(" ... front_pairs: ");
    // for (int i = 1; i < front_pairs.size(); i++){
    //     printf(" (i%d, ", index(front_pairs[i].flop));
    //     printSig(front_pairs[i].sig);
    //     printf(") ");
    // }
    // printf("\n");
    
    if (t.flps.size() > 0){
        if (type(front_pairs[0].sig) == gtype_Const)
            eqs.merge(mkSig(front_pairs[0].flop), front_pairs[0].sig);

        for (int i = 1; i < front_pairs.size(); i++)
            if (front_pairs[i-1].sig == front_pairs[i].sig)
                eqs.merge(mkSig(front_pairs[i-1].flop),  mkSig(front_pairs[i].flop));
            else if (front_pairs[i-1].sig == ~front_pairs[i].sig)
                eqs.merge(mkSig(front_pairs[i-1].flop), ~mkSig(front_pairs[i].flop));
    }

    // Print resulting equivalences:
    for (int i = 0; i < eqs.size(); i++){
        printf(" ... class %d: ", i);
        for (int j = 0; j < eqs[i].size(); j++){
            printSig(eqs[i][j]);
            printf(" ");
        }
        printf("\n");
    }
}


void extractEquivsFromInstance(const TipCirc& t, CircInstance& inst, Equivs& eqs)
{
    vec<Sig> front;
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_next_t = t.flps.next(t.flps[i]);
        Sig flop_inst   = inst.map[gate(flop_next_t)] ^ sign(flop_next_t);
        front.push(flop_inst);
    }
    extractEquivsFromFront(t, front, eqs);
}


void extractEquivsFromInit(const TipCirc& t, Equivs& eqs)
{
    vec<Sig> front;
    for (int i = 0; i < t.flps.size(); i++)
        front.push(t.flps.init(t.flps[i]));
    extractEquivsFromFront(t, front, eqs);
}


void extractEquivsFromSolver(const TipCirc& t, SimpSolver& s, Equivs& eqs)
{
    printf("ERROR! 'extractEquivsFromSolver()' Unimplemented!\n");
    exit(0);
}


//=================================================================================================

typedef vec<Var> LIFrame;

class SimpUnroller {
    const TipCirc& tip;
    SimpSolver&    solver;
    Equivs         front_eqs;
    vec<LIFrame>&  unroll_inps;
    vec<Lit>       flop_front; // Only non-constant, 'leader' flops are not equal to 'lit_Undef'.

    void initialize();
public:
    SimpUnroller(const TipCirc& t, vec<LIFrame>& ui, SimpSolver& solver);
    void operator()(GMap<Lit>& cl_map);
};


SimpUnroller::SimpUnroller(const TipCirc& t, vec<LIFrame>& ui, SimpSolver& s) 
    : tip(t), solver(s), unroll_inps(ui){ initialize(); }


void SimpUnroller::initialize()
{
    GMap<Lit> cl_map;
    clausifyInit(tip, solver, cl_map);

    // TODO investigate alternatives here ...
    extractEquivsFromInit(tip, front_eqs);
        
    // Extract initial input-variables from solver:
    for (int i = 0; i < tip.inps_init.size(); i++){
        unroll_inps.push();
        for (int j = 0; j < tip.inps_init[i].size(); j++){
            Lit l = cl_map[tip.inps_init[i][j]];
            assert(!sign(l));
            unroll_inps.last().push(var(l));
        }
    }

    // Extract & freeze initial flop-front-variables from solver:
    for (int i = 0; i < tip.flps.size(); i++){
        Sig flop = mkSig(tip.flps[i]);
        if (front_eqs.leader(flop) == flop){
            Sig flop_init = tip.flps.init(tip.flps[i]);
            Lit l         = cl_map[gate(flop_init)] ^ sign(flop_init);
            solver.setFrozen(var(l), true);
            flop_front.push(l);
        }else
            flop_front.push(lit_Undef);
    }
}


void SimpUnroller::operator()(GMap<Lit>& lit_map){
    CircInstance inst;
    SimpSolver   inst_solver;
    GMap<Lit>    inst_cl_map;

    instantiateCirc       (tip, front_eqs, inst);
    clausifyInstance      (tip, inst, inst_solver, inst_cl_map);
    plugClausifiedInstance(tip, inst_solver, inst_cl_map, solver, lit_map);

    // Unfreeze previous flop-front-variables:
    for (int i = 0; i < flop_front.size(); i++)
        if (flop_front[i] != lit_Undef)
            solver.setFrozen(var(flop_front[i]), false);

    // TODO investigate alternatives here ...
    extractEquivsFromInstance(tip, inst, front_eqs);

    // Extract input-variables from solver:
    for (int i = 0; i < tip.inps_main.size(); i++){
        unroll_inps.push();
        for (int j = 0; j < tip.inps_main[i].size(); j++){
            Lit l = inst_cl_map[tip.inps_main[i][j]];
            assert(!sign(l));
            unroll_inps.last().push(var(l));
        }
    }

    // Extract & freeze flop-front-variables from solver:
    for (int i = 0; i < tip.flps.size(); i++){
        Sig flop = mkSig(tip.flps[i]);
        if (front_eqs.leader(flop) == flop){
            Sig flop_next = tip.flps.next(tip.flps[i]);
            Lit l         = inst_cl_map[gate(flop_next)] ^ sign(flop_next);
            solver.setFrozen(var(l), true);
            flop_front[i] = l;
        }else
            flop_front[i] = lit_Undef;
    }
}


}

//=================================================================================================
// Implementation of Simplifying BMC:
//

void simpBmc2(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle)
{
    vec<LIFrame>           ui;                  // Unrolled set of input frames.
    SimpSolver             s;                   // SAT-solver.
    SimpUnroller           unroll(tip, ui, s);  // Unroller-helper object.
    GMap<Lit>              cl_map;              // Reusable map from 't.main' to literals in 's'.
    vec<Var>               frozen_vars;         // Reusable list of frozen variables.

    //s.verbosity = 1;
    for (uint32_t i = 0; i < stop_cycle; i++){
        unroll(cl_map);
        //printf(" ... unrolling cycle %d\n", i);

        if (i < begin_cycle)
            continue;

        // Clausify and freeze all properties:
        frozen_vars.clear();
        for (int j = 0; j < tip.all_props.size(); j++){
            Property p = tip.all_props[j];
            if (tip.properties.propType(p) != ptype_Safety || tip.properties.propStatus(p) != pstat_Unknown)
                continue;
            Sig psig = tip.properties.propSig(p);
            Lit l    = cl_map[gate(psig)] ^ sign(psig);
            s.setFrozen(var(l), true);
            frozen_vars.push(var(l));
        }

        // Do CNF-level simplification:
        s.eliminate();

        // Do SAT-tests:
        int unresolved_safety = 0;
        for (int j = 0; j < tip.all_props.size(); j++){
            Property p = tip.all_props[j];
            if (tip.properties.propType(p) != ptype_Safety || tip.properties.propStatus(p) != pstat_Unknown)
                continue;
            
            Sig psig = tip.properties.propSig(p);
            Lit plit = cl_map[gate(psig)] ^ sign(psig);
            printf(" --- cycle=%3d, vars=%8.3g, clauses=%8.3g\n", i, (double)s.nFreeVars(), (double)s.nClauses());

            //printf(" ... testing property %d\n", p);
            if (s.solve(~plit, false, false)){
                //printf (" ... property falsified.\n");
                tip.properties.setPropFalsified(p, /* FIXME */ trace_Undef);
            }else{
                unresolved_safety++;
                //printf (" ... property true.\n");
                assert(s.value(plit) == l_True);
            }
        }

        // Unfreeze all properties:
        for (int j = 0; j < frozen_vars.size(); j++)
            s.setFrozen(frozen_vars[j], false);

        // Terminate if all safety properties resolved:
        if (unresolved_safety == 0)
            break;
    }
}

};
