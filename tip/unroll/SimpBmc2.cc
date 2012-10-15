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
#include "minisat/utils/System.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "mcl/DagShrink.h"
#include "mcl/Equivs.h"
#include "tip/unroll/Bmc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "SIMPBMC2";

static IntOption     opt_local_grow  (_cat, "local-grow",  "Use grow value for local preprocessing in SimpBmc2", 0, IntRange(0, INT32_MAX));
static BoolOption    opt_local_asymm (_cat, "local-asymm", "Use local asymmetric brancing in SimpBmc2", false);

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


    void printMap(const Circ& c, const GMap<Sig>& m, const char* map_name){
        for (GateIt git = c.begin(); git != c.end(); ++git){
            printf("  %s[", map_name);
            printGate(*git);
            printf("] = ");
            printSig(m[*git]);
            printf("\n");
        }
    }

    template<class Lits>
    void printLits(const Lits& cs){
        for (int i = 0; i < cs.size(); i++)
            printf("%s%d ", sign(cs[i])?"-":"", var(cs[i]));
    }


void instantiateCirc(const TipCirc& t, const Equivs& eq, CircInstance& inst)
{
    // Create substitution from 'Equivs':
    GMap<Sig> subst; mkSubst(t.main, eq, subst);

    copyCircWithSubst(t.main, inst.circ, subst, inst.map);
    map(inst.map, subst);
    subst.moveTo(inst.map);

    // Debug (check that all gates in 'inst.map' is withing bounds for 'inst.circ':
    for (GateIt git = t.main.begin(); git != t.main.end(); ++git){
        Sig x  = inst.map[*git];
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

    // Copy all safety property signals:
    for (SafeProp p = 0; p < t.safe_props.size(); p++){
        Sig prop_t    = t.safe_props[p].sig;
        Sig prop_inst = inst.map[gate(prop_t)] ^ sign(prop_t);
        dagShrink(inst.circ, reduced_inst, gate(prop_inst), cm, reduced_map, rnd_seed);

        // printf(" ... prop_t = "); printSig(prop_t); printf("\n");
        // printf(" ... reduced_map[gate(prop_inst)] ^ sign(prop_inst) = "); printSig(reduced_map[gate(prop_inst)] ^ sign(prop_inst)); printf("\n");
    }

    // printMap(t.main, inst.map, "inst.map");
    // printMap(inst.circ, reduced_map, "reduced_map");
    
    // Fix the output circuit/map:
    reduced_inst.moveTo(inst.circ);
    map(reduced_map, inst.map);

    // printMap(t.main, inst.map, "inst.map");

    // Debug:
    // printf(" ... instanciateCirc(): inst-size { ands=%d, inps=%d }, main-size { ands=%d, inps=%d }\n", 
    //        inst.circ.nGates(), inst.circ.nInps(), t.main.nGates(), t.main.nInps());

    // Check that all gates in 'inst.map' is withing bounds for 'inst.circ' or undefined:
    for (GateIt git = t.main.begin(); git != t.main.end(); ++git){
        // if (!(inst.map[g] == sig_Undef || inst.map[g] <= ~mkSig(inst.circ.lastGate()))){
        //     printf(" --- g = ");printGate(g);printf("\n");
        //     printf(" --- inst_map[g] = ");printSig(inst.map[g]);printf("\n");
        //     Gate last = inst.circ.lastGate();
        //     printf(" --- inst.circ.lastGate() = ");printGate(inst.circ.lastGate());printf("\n");
        //     printf(" --- last = ");printGate(last);printf("\n");
        //     printf(" --- last.x = %d\n", last.x);
        //     printf(" --- gate_True = ");printGate(gate_True);printf("\n");
        //     printf(" --- ~mkSig(inst.circ.lastGate()) = ");printSig(~mkSig(inst.circ.lastGate()));printf("\n");
        // }
        assert(inst.map[*git] == sig_Undef || inst.map[*git] <= ~mkSig(inst.circ.lastGate()));
    }
}


void clausifyInstance(const TipCirc& t, const CircInstance& inst, 
                      SimpSolver& s, GMap<Lit>& lit_map /* t.main => s */)
{
    Clausifyer<SimpSolver> cl(inst.circ, s);

    // Clausify & freeze flop-definitions:
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_next_t            = t.flps.next(t.flps[i]);
        Sig flop_next_inst         = inst.map[gate(flop_next_t)] ^ sign(flop_next_t);
        assert(flop_next_inst != sig_Undef);
        Lit l                      = cl.clausify(flop_next_inst);
        // printf(" ... froze (flop-def) %d\n", var(l));
        s.freezeVar(var(l));
    }

    // Clausify & freeze safety properties:
    for (SafeProp p = 0; p < t.safe_props.size(); p++){
        Sig prop_t            = t.safe_props[p].sig;
        Sig prop_inst         = inst.map[gate(prop_t)] ^ sign(prop_t);
        assert(prop_inst != sig_Undef);
        Lit l                 = cl.clausify(prop_inst);
        // printf(" ... froze (property) %d\n", var(l));
        s.freezeVar(var(l));
    }

    // Freeze all (used) inputs:
    for (TipCirc::InpIt iit = t.inpBegin(); iit != t.inpEnd(); ++iit){
        Gate inp      = *iit;
        Sig  inp_inst = inst.map[inp];
        if (inp_inst != sig_Undef){
            Lit l = cl.lookup(inp_inst);
            if (l != lit_Undef){
                // printf(" ... froze (input) "); printGate(inp);
                // printf(" => "); printSig(inp_inst);
                // printf(" => %s%d\n", sign(l)?"-":"", var(l));
                s.freezeVar(var(l));
            }
        }
    }

    // Freeze all (used) flops:
    for (int i = 0; i < t.flps.size(); i++){
        Gate flop      = t.flps[i];
        Sig  flop_inst = inst.map[flop];
        if (flop_inst != sig_Undef){
            Lit l = cl.lookup(flop_inst);
            if (l != lit_Undef){
                // printf(" ... froze (flop) "); printGate(flop);
                // printf(" => "); printSig(flop_inst);
                // printf(" => %s%d\n", sign(l)?"-":"", var(l));
                s.freezeVar(var(l));
            }
        }
    }    

#if 0
    {
        Lit true_lit  = cl.lookup(gate_True);
        printf("  CNF["); printGate(gate_True); 
        printf("] => "); printSig(sig_True);
        if (true_lit != lit_Undef)
            printf(" => %s%d\n", sign(true_lit)?"-":"", var(true_lit));
        else
            printf(" => x\n");
    }
    for (Gate g = t.main.firstGate(); g != gate_Undef; g = t.main.nextGate(g)){
        Sig g_inst = inst.map[g];
        if (g_inst != sig_Undef){
            Lit g_lit  = cl.lookup(g_inst);
            printf("  CNF["); printGate(g); printf("] => "); printSig(g_inst);
            if (g_lit != lit_Undef)
                printf(" => %s%d\n", sign(g_lit)?"-":"", var(g_lit));
            else
                printf(" => x\n");
        }else{
            printf("  CNF["); printGate(g); printf("] => x\n");
        }
    }
    for (TrailIterator ti = s.trailBegin(); ti != s.trailEnd(); ++ti)
        printf("  unit: %s%d\n", sign(*ti)?"-":"", var(*ti));
        
    for (ClauseIterator ci = s.clausesBegin(); ci != s.clausesEnd(); ++ci){
        printf("  clause: ");
        printLits(*ci);
        printf("\n");
    }

    for (int i = 0; i < t.props.size(); i++){
        Property p            = t.props[i];
        Sig prop_t            = t.property_set.propSig(p);
        Sig prop_inst         = inst.map[gate(prop_t)] ^ sign(prop_t);
        Lit prop_lit          = cl.lookup(prop_inst);
        printf("  prop %d", i);
        printf(" => "); printSig(prop_inst);
        printf(" => ");
        if (prop_lit != lit_Undef)
            printf("%s%d\n", sign(prop_lit)?"-":"", var(prop_lit));
        else
            printf("x\n");
    }        
#endif

    int num_vrs_before = s.nFreeVars();
    int num_cls_before = s.nClauses();

    // Simplify & unfreeze variables:
    s.grow      = opt_local_grow;
    s.use_asymm = opt_local_asymm;
    s.eliminate();

    // TODO: not sure if it matters to unfreeze variables as this is a throw-away SAT instance
    // anyway.
    s.thaw();

    if (t.verbosity >= 3)
        printf(" ... clausify: circ-ands(%d => %d), circ-inps(%d => %d), cnf-vars(%d => %d), cnf-cls(%d => %d)\n",
               t.main.nGates(), inst.circ.nGates(),
               t.main.nInps(), inst.circ.nInps(),
               num_vrs_before, s.nFreeVars(),
               num_cls_before, s.nClauses());

    // Extract references to all clausified gates:
    lit_map.clear();
    lit_map.growTo(t.main.lastGate(), lit_Undef);
    for (GateIt git = t.main.begin(); git != t.main.end(); ++git)
        if (inst.map.has(*git) && inst.map[*git] != sig_Undef){
            Lit l = cl.lookup(inst.map[*git]);
            if (l != lit_Undef && !s.isEliminated(var(l)))
                lit_map[*git] = l;
        }
    // Also extract the constant true if referred to:
    if (cl.lookup(sig_True) != lit_Undef)
        lit_map[gate_True] = cl.lookup(sig_True);

#ifndef NDEBUG
    // Check that all inputs that exists in circuit instance, are also in clausified instance:
    for (TipCirc::InpIt iit = t.inpBegin(); iit != t.inpEnd(); ++iit)
            if (inst.map[*iit] != sig_Undef)
                assert(lit_map[*iit] != lit_Undef);
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


Lit plugLit(Lit l, SimpSolver& to, vec<Lit>& lit_remap)
{
    if (lit_remap[var(l)] == lit_Undef)
        lit_remap[var(l)] = mkLit(to.newVar());

    return lit_remap[var(l)] ^ sign(l);
}


void plugClause(const Clause& c, SimpSolver& to, vec<Lit>& lit_remap)
{
    vec<Lit> clause;
    for (int i = 0; i < c.size(); i++)
        clause.push(plugLit(c[i], to, lit_remap));
    to.addClause(clause);
    //printf(" ... plugged-clause: "); printLits(clause); printf("\n");
}


void plugClausifiedInstance(const TipCirc& t, const SimpSolver& one, const GMap<Lit>& one_lit_map /* t.main => one */,
                            const vec<Lit>& flop_front,
                            SimpSolver& s, GMap<Lit>& s_lit_map /* t.main => s */)
{
    // printf(" >>> 'plugClausifiedInstance()':\n");
    vec<Lit> lit_remap(one.nVars(), lit_Undef); // Store variable mapping between solvers ('one' => 's').

    // Connect previous unrolling with new CNF instance:
    for (int i = 0; i < t.flps.size(); i++){
        Gate flop     = t.flps[i];
        Lit  lit_prev = flop_front[i];
        Lit  lit_one  = one_lit_map[flop];

        if (!(lit_prev != lit_Undef || lit_one == lit_Undef || one.value(lit_one) != l_Undef)){
            printf(" --- oops: flop=");
            printGate(flop);
            printf(", lit_one=%s%d, value(lit_one)=%c\n", 
                   sign(lit_one)?"-":"", var(lit_one),
                   one.value(lit_one)==l_Undef?'x':one.value(lit_one)==l_True?'1':'0'
                   );
        }
        // NOTE: the assert below does not hold for flops that are equal to some other flop
        // (non-leaders). Would be nice to fix the assertion, but that requires that the
        // equivalence information is passed here or that less values are defined in the map
        // 'one_lit_map'.
        // assert(lit_prev != lit_Undef || lit_one == lit_Undef || one.value(lit_one) != l_Undef);

        // If literal exists on both sides, connect them:
        if (lit_prev != lit_Undef && lit_one != lit_Undef){
            // printf(" +++ connect flop: "); printGate(flop); 
            // printf(", lit_prev=%s%d, lit_one=%s%d\n", 
            //        sign(lit_prev)?"-":"", var(lit_prev),
            //        sign(lit_one)?"-":"", var(lit_one)
            //        );
            assert(lit_remap[var(lit_one)] == lit_Undef || lit_remap[var(lit_one)] == lit_prev ^ sign(lit_one));
            lit_remap[var(lit_one)] = lit_prev ^ sign(lit_one);
        }
    }

    // Copy all clauses:
    for (ClauseIterator ci = one.clausesBegin(); ci != one.clausesEnd(); ++ci)
        plugClause(*ci, s, lit_remap);

    // Copy all assignments:
    for (TrailIterator ti = one.trailBegin(); ti != one.trailEnd(); ++ti){
        Lit l = plugLit(*ti, s, lit_remap);
        s.addClause(l);
        //printf(" ... plugged-unit: %s%d\n", sign(l)?"-":"", var(l)); 
    }

    // Copy all external references (flop-defs and properties):
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_def     = t.flps.next(t.flps[i]);
        Lit flop_def_one = one_lit_map[gate(flop_def)] ^ sign(flop_def);
        assert(flop_def_one != lit_Undef);
        Lit flop_plugged = plugLit(flop_def_one, s, lit_remap);
        // printf(" ... plugged-flop-def "); printGate(t.flps[i]);
        // printf(" : %s%d\n", sign(flop_plugged)?"-":"", var(flop_plugged));
    }
    for (SafeProp p = 0; p < t.safe_props.size(); p++){
        Sig prop_t   = t.safe_props[p].sig;
        Lit prop_one = one_lit_map[gate(prop_t)] ^ sign(prop_t);
        assert(prop_one != lit_Undef);
        Lit prop_plugged = plugLit(prop_one, s, lit_remap);
        // printf(" ... plugged-property %d", i);
        // printf(" : %s%d\n", sign(prop_plugged)?"-":"", var(prop_plugged));
    }    

    // Check that all inputs that exists in circuit instance, are also in plugged instance: 
    // NOTE: this may happen because CNF-level simplification reduced the CNF to a single constant
    // (for the output property). Then the inputs may be anything, and we just assign them free
    // variables.
    for (TipCirc::InpIt iit = t.inpBegin(); iit != t.inpEnd(); ++iit){
            Lit l = one_lit_map[*iit];
            if (l != lit_Undef)
                plugLit(l, s, lit_remap);
        }

    // Construct map from main to copied CNF instance:
    s_lit_map.clear();
    s_lit_map.growTo(t.main.lastGate(), lit_Undef);
    for (GateIt git = t.main.begin(); git != t.main.end(); ++git){
        Lit one_lit = one_lit_map[*git];
        if (one_lit != lit_Undef){
            Lit s_lit = lit_remap[var(one_lit)] ^ sign(one_lit);
            // if (s_lit == lit_Undef){
            //     printf("  oops: ");
            //     printGate(g);
            //     printf(" => one_lit=%s%d", sign(one_lit)?"-":"", var(one_lit));
            //     printf(" => s_lit=%s%d\n", sign(s_lit)?"-":"", var(s_lit));
            // }
            assert(s_lit != lit_Undef);
            s_lit_map[*git] = s_lit;

            // if (type(g) == gtype_Inp && !t.flps.isFlop(g)){
            //     printf (" === input %d => (one) lit %s%d => (s) lit %s%d\n",
            //             index(g), sign(one_lit)?"-":"", var(one_lit),
            //             sign(s_lit)?"-":"", var(s_lit));
            // }
        }
    }

    // Also make a reference to the constant true:
    if (one_lit_map[gate_True] != lit_Undef){
        Lit lit_true = lit_Undef;
        if (s.trailBegin() == s.trailEnd()){
            // No previous assignments:
            lit_true = mkLit(s.newVar());
            s.addClause(lit_true);
        }else
            lit_true = *s.trailBegin();
        s_lit_map[gate_True] = lit_true;
    }
}


void extractEquivsFromFront(const TipCirc& t, const vec<Sig>& front, Equivs& eqs)
{
    // printf(" >>> 'extractEquivsFromFront()':\n");
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
#if 0
    for (uint32_t i = 0; i < eqs.size(); i++){
        printf(" ... class %d: ", i);
        for (int j = 0; j < eqs[i].size(); j++){
            printSig(eqs[i][j]);
            printf(" ");
        }
        printf("\n");
    }
#else
    uint32_t n_consts = 0;
    for (uint32_t i = 0; i < eqs.size(); i++)
        if (eqs[i][0] == sig_True){
            n_consts = eqs[i].size()-1;
            break; }

    // printf(" ... front equivalences: #const=%d, #classes=%d\n", n_consts, eqs.size());
#endif
}


void extractEquivsFromInstance(const TipCirc& t, CircInstance& inst, Equivs& eqs)
{
    vec<Sig> front;
    for (int i = 0; i < t.flps.size(); i++){
        Sig flop_next_t = t.flps.next(t.flps[i]);
        Sig flop_inst   = inst.map[gate(flop_next_t)] ^ sign(flop_next_t);
        // printf(" >>> flop: "); printGate(t.flps[i]); 
        // printf(" => "); printSig(flop_next_t); printf(" => "); printSig(flop_inst); printf("\n");
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


void extractEquivsFromSolver(const TipCirc& /*t*/, SimpSolver& /*s*/, Equivs& /*eqs*/)
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

    void extractTrace(const SimpSolver& s, vec<vec<lbool> >& tr);

    void printFront();
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
    unroll_inps.push();
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
        if (tip.init.number(*iit) != UINT32_MAX){
            Gate     inp = *iit;
            uint32_t num = tip.init.number(inp);
            Lit      l   = cl_map[inp];
            assert(!sign(l));
            unroll_inps.last().growTo(num+1, var_Undef);
            unroll_inps.last()[num] = var(l);
        }

    // Extract & freeze initial flop-front-variables from solver:
    for (int i = 0; i < tip.flps.size(); i++){
        Sig flop = mkSig(tip.flps[i]);
        if (front_eqs.leader(flop) == flop){
            Sig flop_init = tip.flps.init(tip.flps[i]);
            Lit l         = cl_map[gate(flop_init)] ^ sign(flop_init);
            assert(l != lit_Undef);
            solver.freezeVar(var(l));
            flop_front.push(l);
        }else
            flop_front.push(lit_Undef);
    }
}


void SimpUnroller::operator()(GMap<Lit>& lit_map){
    CircInstance inst;
    SimpSolver   inst_solver;
    GMap<Lit>    inst_cl_map;

    // printf(" +++ Unrolling ...\n");
    // printFront();

    instantiateCirc       (tip, front_eqs, inst);
    clausifyInstance      (tip, inst, inst_solver, inst_cl_map);
    plugClausifiedInstance(tip, inst_solver, inst_cl_map, flop_front, solver, lit_map);

    // Unfreeze previous flop-front-variables:
    // for (int i = 0; i < flop_front.size(); i++)
    //     if (flop_front[i] != lit_Undef){
    //         assert(var(flop_front[i]) >= 0);
    //         assert(var(flop_front[i]) < solver.nVars());
    //         assert(!solver.isEliminated(var(flop_front[i])));
    //         solver.setFrozen(var(flop_front[i]), false);
    //     }

    // TODO investigate alternatives here ...
    extractEquivsFromInstance(tip, inst, front_eqs);

    // Extract input-variables from solver:
    unroll_inps.push();
    for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
        if (tip.main.number(*iit) != UINT32_MAX){
            Gate     inp = *iit;
            uint32_t num = tip.main.number(inp);
            Lit      l   = lit_map[inp];
            
            // TODO: investigate this assert.
            // assert(l == lit_Undef || !sign(l));
            assert(l != lit_Undef);
            
            assert(!sign(l));
            unroll_inps.last().growTo(num+1, var_Undef);
            unroll_inps.last()[num] = var(l);
        }

    // Extract & freeze flop-front-variables from solver:
    for (int i = 0; i < tip.flps.size(); i++){
        Sig flop = mkSig(tip.flps[i]);
        if (front_eqs.leader(flop) == flop){
            Sig flop_next = tip.flps.next(tip.flps[i]);
            Lit l         = lit_map[gate(flop_next)] ^ sign(flop_next);
            assert(l != lit_Undef);
            assert(var(l) >= 0);
            assert(var(l) < solver.nVars());
            assert(!solver.isEliminated(var(l)));
            solver.freezeVar(var(l));
            flop_front[i] = l;
        }else
            flop_front[i] = lit_Undef;
    }
}


void SimpUnroller::extractTrace(const SimpSolver& s, vec<vec<lbool> >& tr)
{
    for (int i = 0; i < unroll_inps.size(); i++){
        tr.push();
        for (int j = 0; j < unroll_inps[i].size(); j++)
            if (unroll_inps[i][j] != var_Undef)
                tr.last().push(s.modelValue(unroll_inps[i][j]));
            else
                tr.last().push(l_Undef);
    }            
}


void SimpUnroller::printFront()
{
    // front_eqs
    // flop_front
    printf(" <<< Current Equivalences:\n");
    for (uint32_t i = 0; i < front_eqs.size(); i++){
        printf(" ... class %d: ", i);
        for (int j = 0; j < front_eqs[i].size(); j++){
            printSig(front_eqs[i][j]);
            printf(" ");
        }
        printf("\n");
    }
    printf(" <<< Current Front:\n");
    for (int i = 0; i < flop_front.size(); i++){
        Gate g = tip.flps[i];
        Lit  l = flop_front[i];
        printf(" ... flop "); printGate(g); 
        if (l == lit_Undef)
            printf(" = x");
        else
            printf(" = %s%d", sign(l)?"-":"", var(l)); 
        printf("\n");
    }
}

}


//=================================================================================================
// Implementation of Simplifying BMC:
//

void simpBmc2(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle)
{
    double                 time_before   = cpuTime();
    double                 solve_time    = 0;
    double                 simp_time     = 0;
    double                 clausify_time = 0;
    vec<LIFrame>           ui;                  // Unrolled set of input frames.
    SimpSolver             s;                   // SAT-solver.
    SimpUnroller           unroll(tip, ui, s);  // Unroller-helper object.
    GMap<Lit>              cl_map;              // Reusable map from 't.main' to literals in 's'.

    //tip.printCirc();
    //s.verbosity = 1;
    for (uint32_t i = 0; i < stop_cycle; i++){
        double clausify_time_begin = cpuTime();
        unroll(cl_map);
        clausify_time += cpuTime() - clausify_time_begin;

        if (i < begin_cycle)
            continue;

        // Clausify and freeze all properties:
        for (SafeProp p = 0; p < tip.safe_props.size(); p++){
            if (tip.safe_props[p].stat != pstat_Unknown)
                continue;
            Sig psig = tip.safe_props[p].sig;
            Lit l    = cl_map[gate(psig)] ^ sign(psig);
            assert(l != lit_Undef);
            s.freezeVar(var(l));
        }

        // Do CNF-level simplification:
        double simp_time_before = cpuTime();
        s.eliminate();
        simp_time += cpuTime() - simp_time_before;

        // Do SAT-tests:
        int unresolved_safety = 0;
        for (SafeProp p = 0; p < tip.safe_props.size(); p++){
            if (tip.safe_props[p].stat != pstat_Unknown)
                continue;
            Sig psig = tip.safe_props[p].sig;
            Lit plit = cl_map[gate(psig)] ^ sign(psig);
            assert(plit != lit_Undef);

            if (tip.verbosity >= 1){
                double total_time = cpuTime() - time_before;
                printf(" --- k=%3d, vrs=%8.3g, cls=%8.3g, con=%8.3g",
                       i, (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);
                if (tip.verbosity >= 2)
                    printf(", time(solve=%6.1f s, simp=%6.1f s, claus=%6.1f s, total=%6.1f s)\n",
                           solve_time, simp_time, clausify_time, total_time);
                else
                    printf("\n");
            }

            double solve_time_before = cpuTime();
            bool ret = s.solve(~plit, false, false);
            solve_time += cpuTime() - solve_time_before;

            if (ret){
                Trace cex = tip.newTrace();
                unroll.extractTrace(s, tip.traces[cex].frames);
                tip.adaptTrace(tip.traces[cex].frames);
                tip.setFalsifiedSafe(p, cex, "sbmc2");
            }else{
                unresolved_safety++;
                assert(s.value(plit) == l_True);
            }
        }

        // Unfreeze everything:
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
            printf(", time(solve=%6.1f s, simp=%6.1f s, claus=%6.1f s, total=%6.1f s)\n",
                   solve_time, simp_time, clausify_time, total_time);
        else
            printf("\n");
        s.printStats();
    }
}

};
