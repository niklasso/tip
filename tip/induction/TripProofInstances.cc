/***************************************************************************[TripProofInstances.cc]
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
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/induction/TripProofInstances.h"

namespace Tip {

    namespace {

        void extractResetInputs(const TipCirc& tip, const GMap<Sig>& umap, 
                                Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit){
                Sig inp = umap[*iit];
                Lit lit = cl.clausify(inp);
                umapl[*iit] = lit;
                solver.freezeVar(var(lit));
                xs.push(lit);
            }
        }

        void extractInputs(const TipCirc& tip, const GMap<Sig>& umap,
                           Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
                Sig inp = umap[*iit];
                Lit lit = cl.clausify(inp);
                umapl[*iit] = lit;
                solver.freezeVar(var(lit));
                xs.push(lit);
            }
        }

        void extractFlopIns(const TipCirc& tip, const GMap<Sig>& umap,
                            Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Gate flp_in   = *flit;
                Lit  lit_in   = cl.clausify(umap[flp_in]);
                umapl[flp_in] = lit_in;
                solver.freezeVar(var(lit_in));
                xs.push(lit_in);
            }
        }

        void extractFlopOuts(const TipCirc& tip, const GMap<Sig>& umap,
                             Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Sig  flp_out         = tip.flps.next(*flit);
                Lit  lit_out         = cl.clausify(umap[gate(flp_out)] ^ sign(flp_out));
                umapl[gate(flp_out)] = lit_out ^ sign(flp_out);
                solver.freezeVar(var(lit_out));
                xs.push(lit_out);
            }
        }


        void extractProps(const TipCirc& tip, const GMap<Sig>& umap,
                          Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Unknown){
                    Sig prop          = tip.safe_props[p].sig;
                    Lit lit           = cl.clausify(umap[gate(prop)] ^ sign(prop));
                    umapl[gate(prop)] = lit ^ sign(prop);
                    solver.freezeVar(var(lit));
                    xs.push(lit);
                }
        }


        // Minimize the last conflicting assumption set:
        void shrinkConflict(SimpSolver& s)
        {
            vec<Lit> ass;
            vec<Lit> smaller;
            bool     must_hold;
            // printf("[shrinkConflict] init = ");
            // for (int i = 0; i < s.conflict.size(); i++)
            //     printf("%s%d ", sign(~s.conflict[i])?"-":"", var(s.conflict[i]));
            // printf("\n");
            for (;;){
                ass.clear();
                for (int i = 0; i < s.conflict.size(); i++)
                    ass.push(~s.conflict[i]);

                for (int i = 0; i < ass.size(); i++){
                    smaller.clear();
                    for (int j = 0; j < ass.size(); j++)
                        if (i != j)
                            smaller.push(ass[j]);
                    // printf("[shrinkConflict] trying to remove %s%d ", sign(ass[i])?"-":"", var(ass[i]));
                    if (!s.solve(smaller)){
                        // printf(" (succeeded)\n");
                        goto retry;
                    }else{
                        // printf(" (failed)\n");
                    }
                }
                must_hold = !s.solve(ass);
                assert(must_hold);
                break;
            retry:;
            }
        }


        void shrinkModelOnce(SimpSolver& s, LitSet& xs, const vec<Lit>& top)
        {
            for (int i = 0; i < xs.size(); i++)
                assert(s.modelValue(xs[i]) == l_True);

            for (int i = 0; i < top.size(); i++)
                assert(s.modelValue(top[i]) == l_True);

            // Simple variant for now:
            Lit      trigg = mkLit(s.newVar());
            vec<Lit> clause;
            for (int i = 0; i < top.size(); i++)
                clause.push(~top[i]);
            clause.push(~trigg);
            s.addClause(clause);

            vec<Lit> assume;
            xs.copyTo(assume);
            assume.push(trigg);
            check(!s.solve(assume));

            //s.addClause(~trigg);
            s.releaseVar(~trigg);

            // Check 's.conflict' and remove literals not present there:
            vec<Lit> out;
            for (int i = 0; i < s.conflict.size(); i++)
                if (xs.has(~s.conflict[i]))
                    out.push(~s.conflict[i]);
            xs.fromVec(out);
        }


        void traceResetInputs(const TipCirc& tip, const LitSet& lset, const GMap<Lit>& umapl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit){
                Gate inp = *iit;
                Lit  l   = umapl[inp];
                assert(tip.init.number(inp) != UINT32_MAX); // Inputs must be numbered.
                frames.last().growTo(tip.init.number(inp)+1, l_Undef);
                frames.last()[tip.init.number(inp)] = lset.has(var(l)) ^ sign(l);
            }
        }


        void traceInputs(const TipCirc& tip, const LitSet& lset, const GMap<Lit>& umapl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
                Gate inp = *iit;
                Lit  l   = umapl[inp];
                assert(tip.main.number(inp) != UINT32_MAX); // Inputs must be numbered.
                frames.last().growTo(tip.main.number(inp)+1, l_Undef);
                frames.last()[tip.main.number(inp)] = lset.has(var(l)) ^ sign(l);
            }
        }


        void getClause(const TipCirc& tip, const LitSet& lset, const GMap<Lit>& umapl, vec<Sig>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Lit   l   = umapl[*flit];
                lbool val = lset.has(var(l)) ^ sign(l);
                if (val != l_Undef)
                    xs.push(mkSig(*flit, val == l_True));
            }
        }
    }

    //===================================================================================================
    // Implementation of InitInstance:

    void InitInstance::reset()
    {
        // Clear solver & gate to solver maps:
        delete solver;
        solver = new SimpSolver();
        umapl[0].clear();
        umapl[0].growTo(tip.init.lastGate(), lit_Undef);
        umapl[1].clear();
        umapl[1].growTo(tip.main.lastGate(), lit_Undef);
        inputs.clear();

        // Unroll proper number of steps:
        Circ                   uc;                       // Unrolled circuit.
        GMap<Sig>              umap[2];                  // Map for circuit unrollings.
        UnrollCirc2            unroll(tip, uc, umap[0]); // Unroller-helper object.
        Clausifyer<SimpSolver> cl(uc, *solver);
        unroll(umap[1]);

        // Extract all needed references:
        extractResetInputs(tip, umap[0], cl, *solver, umapl[0], inputs);
        extractInputs     (tip, umap[1], cl, *solver, umapl[1], inputs);
        extractFlopOuts   (tip, umap[1], cl, *solver, umapl[1], inputs);

        // Simplify CNF:
#if 0
        solver->use_asymm = true;
        solver->grow = 2;
#endif
        solver->eliminate(true);
        solver->thaw();
    }

    struct SigLitPair {
        Sig x;
        Lit l;
    };

    struct SigLitCmp {
        bool operator()(SigLitPair p1, SigLitPair p2) const {
            return p1.l < p2.l;
        }
    };

    bool InitInstance::prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next)
    {
        assert(next == NULL || &c == (Clause*)next);

        vec<Lit> assumes;
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
            Lit l = umapl[1][gate(x)] ^ sign(x);
            assert(l != lit_Undef);
            assumes.push(~l);
        }

        if (solver->solve(assumes)){
            // Found a counter-example:
            if (next != NULL){
                lset.fromModel(inputs, *solver);
                shrinkModelOnce(*solver, lset, assumes);

                vec<vec<lbool> > frames;
                vec<Sig>         clause;
                traceResetInputs(tip, lset, umapl[0], frames);
                traceInputs     (tip, lset, umapl[1], frames);

                vec<Sig>         dummy;
                ScheduledClause* pred0    = new ScheduledClause(dummy, 0, frames[1], next);
                ScheduledClause* pred_rst = new ScheduledClause(dummy, 0, frames[0], pred0);
                //printf("[InitInstance::prove] pred0 = %p, pred_rst = %p\n", pred0, pred_rst);
                no = pred_rst;
            }

            return false;
        }else{
            // Proved the clause:

            // Minimize reason more:
            int n_before = solver->conflict.size();
            shrinkConflict(*solver);
            if (tip.verbosity >= 3 && solver->conflict.size() < n_before)
                printf("[InitInstance::prove] expensive conflict shrink: %d => %d\n",
                       n_before, solver->conflict.size());

            vec<SigLitPair> slits;
            for (unsigned i = 0; i < c.size(); i++){
                SigLitPair p;
                p.x   = c[i];
                Sig x = tip.flps.next(gate(p.x)) ^ sign(p.x);
                p.l   = umapl[1][gate(x)] ^ sign(x);
                slits.push(p);
            }

            sort(slits, SigLitCmp());

            // printf(" .. slits-before = ");
            // for (int i = 0; i < slits.size(); i++)
            //     printf("%s%d:%s%d ", 
            //            sign(slits[i].x)?"~":"", index(gate(slits[i].x)),
            //            sign(slits[i].l)?"~":"", var(slits[i].l));
            // printf("\n");
            
            int i,j;
            for (i = j = 1; i < slits.size(); i++)
                if (slits[i].l != slits[j-1].l)
                    slits[j++] = slits[i];
            slits.shrink(i-j);

            // if (i - j > 0)
            //     printf("[InitInstance::prove] potential reason shrunk with: %d\n", i - j);
            
            // printf(" .. slits-after = ");
            // for (int i = 0; i < slits.size(); i++)
            //     printf("%s%d:%s%d ", 
            //            sign(slits[i].x)?"~":"", index(gate(slits[i].x)),
            //            sign(slits[i].l)?"~":"", var(slits[i].l));
            // printf("\n");

            vec<Sig> subset;
            for (int i = 0; i < slits.size(); i++)
                if (find(solver->conflict, slits[i].l))
                    subset.push(slits[i].x);
            yes = Clause(subset, 0);

            return true;
        }
    }


    bool InitInstance::prove(const Clause& c, Clause& yes)
    {
        ScheduledClause* dummy;
        return prove(c, yes, dummy);
    }


    InitInstance::InitInstance(const TipCirc& t) : tip(t), solver(NULL)
    {
        reset();
    }


    InitInstance::~InitInstance(){ delete solver; }

    void InitInstance::printStats()
    {
        printf("[init-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver->nVars(), (double)solver->nClauses(), (double)solver->conflicts);
    }
    
    //===================================================================================================
    // Implementation of PropInstance:

    void PropInstance::clearClauses()
    {
        //solver->addClause(~trigg);
        solver->releaseVar(~trigg);
        trigg = mkLit(solver->newVar());
    }

    void PropInstance::addClause(const Clause& c)
    {
        // Add the clause if it is an invariant, or if it belongs to the last cycle:
        if (c.cycle == (unsigned)F.size()-1 || c.cycle == cycle_Undef){
            vec<Lit> xs;
            if (c.cycle != cycle_Undef)
                xs.push(~trigg);
            for (unsigned i = 0; i < c.size(); i++)
                xs.push(umapl[0][gate(c[i])] ^ sign(c[i]));
            solver->addClause(xs);
        }
    }


    void PropInstance::reset()
    {
        // Clear solver & gate to solver maps:
        delete solver;
        solver = new SimpSolver();
        umapl[0].clear();
        umapl[0].growTo(tip.main.lastGate(), lit_Undef);
        umapl[1].clear();
        umapl[1].growTo(tip.main.lastGate(), lit_Undef);
        inputs.clear();

        // Unroll proper number of steps:
        Circ                   uc;              // Unrolled circuit.
        GMap<Sig>              umap[2];         // Map for circuit unrollings.
        UnrollCirc2            unroll(tip, uc); // Unroller-helper object.
        Clausifyer<SimpSolver> cl(uc, *solver);
        vec<Lit>               outputs;         // Unused;
        unroll(umap[0]);
        unroll(umap[1]);

        // Extract all needed references:
        extractFlopIns    (tip, umap[0], cl, *solver, umapl[0], inputs);
        extractInputs     (tip, umap[0], cl, *solver, umapl[0], inputs);
        extractInputs     (tip, umap[1], cl, *solver, umapl[1], inputs);
        extractProps      (tip, umap[1], cl, *solver, umapl[1], outputs);

        // Simplify CNF:
        solver->eliminate(true);
        solver->thaw();
        trigg = mkLit(solver->newVar());
    }


    template<class Lits>
    void printLits(const Lits& cs){
        for (int i = 0; i < cs.size(); i++)
            printf("%s%d ", sign(cs[i])?"-":"", var(cs[i]));
    }


    #if 0
    lbool PropInstance::evaluate(const LitSet& lset, Sig p)
    {
        // FIXME: yuck!
        GMap<lbool> value(tip.main.lastGate(), l_Undef);

        for (TrailIterator ti = solver->trailBegin(); ti != solver->trailEnd(); ++ti)
            printf("  unit: %s%d\n", sign(*ti)?"-":"", var(*ti));
        
        for (ClauseIterator ci = solver->clausesBegin(); ci != solver->clausesEnd(); ++ci){
            printf("  clause: ");
            printLits(*ci);
            printf("\n");
        }
        
        for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git){
            printGate(*git);
            Lit l = umapl[0][*git];
            if (l != lit_Undef){
                lbool v = solver->value(l);
                printf(" = %c\n", v == l_Undef ? 'x' : v == l_False ? '0' : '1');
            }else
                printf(" = ?\n");
        }

        // Evaluate cycle 0:
        for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git){
            if (value[*git] == l_Undef){
                if (*git == gate_True)
                    value[*git] = l_True;
                else if (type(*git) == gtype_Inp){
                    value[*git] = model.value(*git, umapl[0]);
                    // For unknown inputs, we'll only check that there
                    // is one value that falsifies 'p':
                    if (value[*git] == l_Undef && !tip.flps.isFlop(*git))
                        value[*git] = l_False;
                }else{
                    assert(type(*git) == gtype_And);
                    Sig x = tip.main.lchild(*git);
                    Sig y = tip.main.rchild(*git);
                    value[*git] = (value[gate(x)] ^ sign(x)) && (value[gate(y)] ^ sign(y));
                }
            }
            printGate(*git);
            Lit l = umapl[0][*git];
            if (l != lit_Undef)
                printf(" (%s%d) ", sign(l)?"-":"", var(l));
            else
                printf(" (x) ");
            
            printf(" = %c\n", value[*git] == l_Undef ? 'x' : value[*git] == l_False ? '0' : '1');
        }

        // Copy values of flops to next cycle:
        GMap<lbool> value_next(tip.main.lastGate(), l_Undef);
        for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
            Sig x = tip.flps.next(*flit);
            value_next[*flit] = value[gate(x)] ^ sign(x);
        }
        value_next.moveTo(value);

        // Evaluate cycle 1:
        for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git){
            if (value[*git] == l_Undef){
                if (*git == gate_True)
                    value[*git] = l_True;
                else if (type(*git) == gtype_Inp){
                    value[*git] = model.value(*git, umapl[1]);
                    // For unknown inputs, we'll only check that there
                    // is one value that falsifies 'p':
                    if (value[*git] == l_Undef && !tip.flps.isFlop(*git))
                        value[*git] = l_False;
                }else{
                    assert(type(*git) == gtype_And);
                    Sig x = tip.main.lchild(*git);
                    Sig y = tip.main.rchild(*git);
                    value[*git] = (value[gate(x)] ^ sign(x)) && (value[gate(y)] ^ sign(y));
                }
            }
            printGate(*git); 
            Lit l = umapl[1][*git];
            if (l != lit_Undef)
                printf(" (%s%d) ", sign(l)?"-":"", var(l));
            else
                printf(" (x) ");
            printf(" = %c\n", value[*git] == l_Undef ? 'x' : value[*git] == l_False ? '0' : '1');
        }
        //printf(" ... got here:\n");
        lbool result = value[gate(p)] ^ sign(p);
        printf("result = %c\n", result == l_Undef ? 'x' : result == l_False ? '0' : '1');
        assert(result == l_False);
        return result;
    }
    #endif


    lbool PropInstance::prove(Sig p, ScheduledClause*& no, unsigned cycle)
    {
        Lit l = umapl[1][gate(p)] ^ sign(p);
        if (solver->solve(~l, trigg)){
            assert(solver->modelValue(l) == l_False);
            // Found predecessor state to a bad state:
            vec<Lit> outputs;
            outputs.push(~l);
            lset.fromModel(inputs, *solver);
            shrinkModelOnce(*solver, lset, outputs);

            vec<vec<lbool> > frames;
            vec<Sig>         clause;
            traceInputs(tip, lset, umapl[0], frames);
            traceInputs(tip, lset, umapl[1], frames);
            getClause  (tip, lset, umapl[0], clause);

            // TODO: It is hard to specify the actual property
            // here. The SAT-based query used here is stronger than
            // 3-valued simulation and can thus not be verified with
            // that.

            // assert(evaluate(shrunk_model, p) == l_False);

            vec<Sig> dummy;
            ScheduledClause* last = new ScheduledClause(dummy,  cycle+1, frames[1], NULL);
            ScheduledClause* pred = new ScheduledClause(clause, cycle,   frames[0], last);
            //printf("[PropInstance::prove] last = %p, pred = %p\n", last, pred);
            no = pred;

            return l_False;
        }else if (!solver->solve(~l))
            // Property is implied already by invariants:
            return l_True;
        else
            return l_Undef;
    }

    PropInstance::PropInstance(const TipCirc& t, const vec<vec<Clause*> >& F_)
        : tip(t), F(F_), solver(NULL)
    {
        reset();
    }


    PropInstance::~PropInstance(){ delete solver; }

    void PropInstance::printStats()
    {
        printf("[prop-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver->nVars(), (double)solver->nClauses(), (double)solver->conflicts);
    }

    //===================================================================================================
    // Implementation of StepInstance:


    void StepInstance::addClause(const Clause& c)
    {
        vec<Lit> xs;
        // Add the unconditionally if it is an invariant, or else triggered by the cycles
        // activation literal:
        if (c.cycle != cycle_Undef){
            activate.growTo(c.cycle+1, lit_Undef);
            if (activate[c.cycle] == lit_Undef)
                activate[c.cycle] = mkLit(solver->newVar());
            xs.push(~activate[c.cycle]);

            cycle_clauses.growTo(c.cycle+1, 0);
            cycle_clauses[c.cycle]++;
        }

        for (unsigned i = 0; i < c.size(); i++)
            xs.push(umapl[gate(c[i])] ^ sign(c[i]));
        solver->addClause(xs);
    }


    void StepInstance::resetCycle(unsigned cycle, unsigned num_clauses)
    {
        assert(cycle != cycle_Undef);
        if ((int)cycle < cycle_clauses.size() && (cycle_clauses[cycle] / 2) > num_clauses){
            // Disable all clauses added to this cycle:
            //solver->addClause(~activate[cycle]);
            solver->releaseVar(~activate[cycle]);
            cycle_clauses[cycle] = 0;

            // Introduce new trigger literal:
            activate[cycle] = mkLit(solver->newVar());

            // Re-add all clauses from this cycle:
            for (int i = 0; i < F[cycle].size(); i++)
                if (F[cycle][i]->isActive())
                    addClause(*F[cycle][i]);

            // Force a solver simplify:
            solver->simplify();
        }
    }


    void StepInstance::reset()
    {
        // Clear solver & gate to solver maps:
        delete solver;
        solver = new SimpSolver();
        umapl.clear();
        umapl.growTo(tip.main.lastGate(), lit_Undef);
        inputs.clear();
        outputs.clear();
        activate.clear();

        // Unroll proper number of steps:
        Clausifyer<SimpSolver> cl(tip.main, *solver);

        // FIXME: ugly, but will do for now.
        GMap<Sig> id(tip.main.lastGate(), sig_Undef);
        for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git)
            id[*git] = mkSig(*git);

        // Extract all needed references:
        extractFlopIns (tip, id, cl, *solver, umapl, inputs);
        extractInputs  (tip, id, cl, *solver, umapl, inputs);
        extractFlopOuts(tip, id, cl, *solver, umapl, outputs);

#if 0
        solver->use_asymm = true;
        solver->grow = 2;
#endif

        // Simplify CNF:
        solver->eliminate(true);
        solver->thaw();
    }


    void StepInstance::evaluate(vec<Sig>& clause)
    {
        GMap<lbool> value(tip.main.lastGate(), l_Undef);
        for (GateIt git = tip.main.begin(); git != tip.main.end(); ++git)
            if (type(*git) == gtype_Inp){
                Lit l = umapl[*git];
                value[*git] = lset.has(var(l)) ^ sign(l);
            }else{
                assert(type(*git) == gtype_And);
                Sig x = tip.main.lchild(*git);
                Sig y = tip.main.rchild(*git);
                value[*git] = (value[gate(x)] ^ sign(x)) && (value[gate(y)] ^ sign(y));
            }

        for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
            Sig   x = tip.flps.next(*flit);
            lbool v = value[gate(x)] ^ sign(x);
            if (v != l_Undef)
                clause.push(mkSig(*flit, v == l_True));
        }
    }


    bool StepInstance::prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next)
    {
        assert(next == NULL || &c == (Clause*)next);
        assert(c.cycle > 0);
        vec<Lit> outputs;
        vec<Lit> inputs;
        vec<Lit> assumes;
        this->inputs.copyTo(inputs);

        // Assume proved clauses:
        if (c.cycle != cycle_Undef)
            for (int i = c.cycle-1; i < activate.size(); i++)
                if (activate[i] != lit_Undef){
                    assumes.push(activate[i]);
                    inputs .push(activate[i]);
                }

        // These clauses must be satisfiable:
        // assert(solver->solve(assumes));

        // Assume negation of clause 'c' (outgoing):
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
            Lit l = umapl[gate(x)] ^ sign(x);
            assert(l != lit_Undef);
            outputs.push(~l);
            assumes.push(~l);
        }

        // Try to satisfy clause 'c' (incoming):
        vec<Lit> cls;
        for (unsigned i = 0; i < c.size(); i++){
            Lit l = umapl[gate(c[i])] ^ sign(c[i]);
            assert(l != lit_Undef);
            solver->setPolarity(var(l), lbool(!sign(l)));
            cls.push(l);
        }

        bool sat = solver->solve(assumes);

        // Undo polarity preference:
        for (int i = 0; i < cls.size(); i++)
            solver->setPolarity(var(cls[i]), l_Undef);

        if (sat){
            // Check if incoming clause was satisfied:
            bool clause_sat = false;
            for (int i = 0; i < cls.size() && !clause_sat; i++)
                if (solver->modelValue(cls[i]) == l_True)
                    clause_sat = true;

            if (!clause_sat){
                // Look for a new model where the clause is guaranteed to be true:
                Lit trigg = mkLit(solver->newVar());
                cls.push(~trigg);
                solver->addClause(cls);
                assumes.push(trigg);
                sat = solver->solve(assumes);
                //solver->addClause(~trigg);
                solver->releaseVar(~trigg);
                // printf("[StepInstance::prove] needed to add induction hypothesis => sat=%d\n", sat);
            }else{
                // printf("[StepInstance::prove] did NOT need to add induction hypothesis.\n");
            }
        }

        bool result;
        if (sat){
            // Found a counter-example:
            if (next != NULL){
                lset.fromModel(inputs, *solver);
                shrinkModelOnce(*solver, lset, outputs);

                vec<vec<lbool> > frames;
                vec<Sig>         clause;
                traceInputs     (tip, lset, umapl, frames);
                getClause       (tip, lset, umapl, clause);

                ScheduledClause* pred = new ScheduledClause(clause, c.cycle-1, frames[0], next);
                //printf("[StepInstance::prove] pred = %p\n", pred);
                no = pred;

                // { //TMP-debug:
                //     vec<Sig> xs;
                //     evaluate(shrunk_model, xs);
                //     Clause   eval(xs, c.cycle);
                //     printf("[StepInstance::prove] c    = ");
                //     printClause(tip, c);
                //     printf("\n");
                //     printf("[StepInstance::prove] eval = ");
                //     printClause(tip, eval);
                //     printf("\n");
                //     assert(subsumes(c, eval));
                // }

            }

            result = false;
        }else{
            // Proved the clause:
            vec<Sig> subset;
            for (unsigned i = 0; i < c.size(); i++){
                Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
                Lit l = umapl[gate(x)] ^ sign(x);
                if (find(solver->conflict, l))
                    subset.push(c[i]);
            }
            assert(subset.size() > 0);

            // What level was sufficient?
            unsigned k = cycle_Undef;
            for (int i = c.cycle-1; i < activate.size(); i++)
                if (find(solver->conflict, ~activate[i])){
                    k = i+1;
                    break;
                }

            // printf("[StepInstance::prove] c.cycle = %d, k = %d\n", c.cycle, k);
            yes = Clause(subset, k);
            //printf("[StepInstance::prove] &yes = %p\n", &yes);
            result = true;
        }

        return result;
    }

    bool StepInstance::prove(const Clause& c, Clause& yes)
    {
        ScheduledClause* dummy;
        return prove(c, yes, dummy);
    }

    StepInstance::StepInstance(const TipCirc& t, const vec<vec<Clause*> >& F_)
        : tip(t), F(F_), solver(NULL)
    {
        reset();
    }


    StepInstance::~StepInstance(){ delete solver; }


    void StepInstance::printStats()
    {
        printf("[step-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver->nVars(), (double)solver->nClauses(), (double)solver->conflicts);
    }


//=================================================================================================
} // namespace Tip
