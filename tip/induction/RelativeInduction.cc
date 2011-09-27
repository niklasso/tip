/****************************************************************************[RelativeInduction.cc]
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

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "tip/induction/Induction.h"
#include "tip/induction/TripTypes.h"
#include "tip/induction/TripProofInstances.h"

#define GENERALIZE_THEN_PUSH

namespace Tip {

    namespace {

        //===================================================================================================
        // Temporal Relative Induction Prover:
        class Trip {
            TipCirc&             tip;

            // Solver independent data:
            vec<vec<Clause*> >   F;             // Proved clauses (by cycle).
            vec<unsigned>        F_size;        // Number of active clauses in each cycle.
            vec<Clause*>         F_inv;         // Invariant clauses.
            unsigned             n_inv;         // Number of active invariants.
            unsigned             n_total;       // Total number of active clauses.

            vec<vec<ScheduledClause*> > 
                                 clause_queue;
            SMap<vec<Clause*> >  bwd_occurs;
            SMap<vec<Clause*> >  fwd_occurs;

            // Solver data: Should be rederivable from only independent data at any time:
            InitInstance         init;
            PropInstance         prop;
            StepInstance         step;

            // PROVE:   Init ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in cycle 1,
            //       or False and the starting point of a counter-example trace.
            bool             proveInit(const ScheduledClause* c, Clause& yes, ScheduledClause*& no);
            bool             proveInit(const Clause& c, Clause& yes);

            // PROVE:   let k = c.cycle: F_inv ^ F[k-1] ^ c ^ Trans => c'
            // RETURNS: True and a minimal stronger clause d (subset of c) that holds in a maximal cycle >= k,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveAndGeneralize(const ScheduledClause* c, Clause& yes, ScheduledClause*& no);

            // PROVE:   let k = c.cycle: F_inv ^ F[k-1] ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in some cycle >= k,
            //       or False if c does not hold in cycle k.
            bool             proveStep(const Clause& c, Clause& yes);

            // Find a maximal generalization of c that still is subsumed by init.
            void             generalize(const Clause& init, Clause& c);

            // PROVE:   let k = F.size()-1: F_inv ^ F[k] ^ Trans => p'
            // RETURNS: l_True if the property is implied by the invariants alone,
            //       or l_False and a new clause predecessor to be proved in cycle k,
            //       or l_Undef when the propery 'p' holds in cycle k+1.
            lbool            proveProp(Sig p, ScheduledClause*& no);

            // Prove scheduled clause "recursively". Returns true if the clause was proved, and
            // false if it was falsified.
            bool             proveRec(ScheduledClause* sc, SafeProp p);

            // Try to push clauses forwards, particularily push clauses forward into the newly opened last
            // frame. Returns true if an invariant is found and false otherwise.
            bool             pushClauses  ();

            // Add a proved clause 'c'. Returns true if this causes an invariant to be found, and false
            // otherwise.
            bool             addClause    (const Clause& c);

            // When some set of invariants have been found, extract and add the clauses to
            // 'F_inv'. Also perform backward subsumption to remove redundant clauses.
            void             extractInvariant();

            // Remove a proved clause 'c'. Returns true if this causes an invariant to be found,
            // and false otherwise.
            bool             removeClause (Clause* c);

            void             clearInactive();

            // Check if clause 'c' is subsumed by any previously proved clause. Returns true if it is and
            // false otherwise.
            bool             fwdSubsumed  (const Clause* c);

            // Find and remove all previously proved claues that are subsumed by the new clause 'c'. If an
            // invariant is found true is returned, otherwise false.
            bool             bwdSubsume   (Clause* c, bool verify = false);
            void             verifySubsumption();

            void             enqueueClause(ScheduledClause* sc);
            ScheduledClause* getMinClause ();

            // Extracts the trace that leads to the failure, and removes all scheduled clauses.
            void             extractTrace (const ScheduledClause* sc, vec<vec<lbool> >& frames);



            // Returns number of states in unrolling.
            unsigned         size() const;

            // DEBUG:
            void             printClause (const Clause& c);

            
        public:
            void             printInvariant  ();
            void             verifyInvariant ();

            Trip(TipCirc& t) : tip(t), n_inv(0), n_total(0), init(t), prop(t, F), step(t, F)
            {
                F.push();
                F_size.push(0);
            }

            // Prove or disprove all properties using depth k. Returns true if all properties are decided, and
            // false if there are still some unresolved property.
            bool decideCycle();

            // Prove that the necessary number of initial cycles are bug free. Returns true if all properties
            // are resolved (i.e. all properties were falsifiable), and false otherwise.
            bool baseCase();

            void printStats(unsigned curr_cycle = cycle_Undef, bool newline = true);
        };

        bool Trip::proveInit(const ScheduledClause* c, Clause& yes, ScheduledClause*& no){ 
            return init.prove(*c, yes, no, c);
        }

        bool Trip::proveInit(const Clause& c, Clause& yes){
            return init.prove(c, yes);
        }


        void Trip::generalize(const Clause& ic, Clause& c)
        {
            Clause try_remove = c - ic;
            Clause d,e;

            c = ic + c;
            for (unsigned i = 0; i < try_remove.size(); i++)
                if (find(c, try_remove[i]))
                    if (step.prove(c - try_remove[i], d))
                        c = ic + d;
        }


        bool Trip::proveAndGeneralize(const ScheduledClause* c, Clause& yes, ScheduledClause*& no)
        {
            Clause yes_init, yes_step;
            if (c->cycle == 0){
                if (!init.prove(*c, yes_init, no, c))
                    return false;
                yes_step = yes_init;
            }else{
                if (!step.prove(*c, yes_step, no, c))
                    return false;
                
                check(proveInit(*c, yes_init));
#ifdef GENERALIZE_THEN_PUSH
                generalize(yes_init, yes_step);
#else
                yes_step = yes_init + yes_step;
#endif
            }

            if (tip.verbosity >= 3 && c->cycle < yes_step.cycle)
                printf("[proveStep] clause was proved in the future: %d -> %d\n",
                       c->cycle, yes_step.cycle);

            // Push clause forwards as much as possible:
            while (yes_step.cycle < size()-1){
                Clause d = yes_step;
                d.cycle++;
                if (!step.prove(d, yes_step))
                    break;
                yes_step = yes_init + yes_step;
            }

#ifndef GENERALIZE_THEN_PUSH
            generalize(yes_init, yes_step);
#endif

            yes = yes_step;
            // TODO: assert something based on subsumtion instead.
            // assert(proveInit(yes, yes_step));
            return true;
        }


        bool Trip::proveStep(const Clause& c, Clause& yes)
        {
            // FIXME: code duplication ...
            Clause yes_init, yes_step;

            if (!step.prove(c, yes_step))
                return false;

            if (tip.verbosity >= 3 && c.cycle < yes_step.cycle)
                printf("[proveStep] clause was proved in the future: %d -> %d\n",
                       c.cycle, yes_step.cycle);

            check(proveInit(c, yes_init));

            // Calculate union of the two strengthened clauses:
            yes = yes_init + yes_step;
            return true;
        }


        lbool Trip::proveProp(Sig p, ScheduledClause*& no){ return prop.prove(p, no, size()-1); }


        bool Trip::baseCase()
        {
            // Run BMC for the necessary number of initial cycles:
            tip.bmc(0,2);

            // Check if all properties are resolved:
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Unknown)
                    return false;
            return true;
        }


        void Trip::extractTrace(const ScheduledClause* sc, vec<vec<lbool> >& frames)
        {
            // Extract trace:
            for (const ScheduledClause* scan = sc; scan != NULL; scan = scan->next){
                // printf("[extractTrace] scan = %p, cycle = %d\n", scan, scan->cycle);
                frames.push();
                for (unsigned i = 0; i < scan->inputs.size(); i++)
                    frames.last().push(scan->inputs[i]);
            }

            // TODO: this leaks memory due to the fact that snippets from the property instance,
            // and the init instance don't appear in the clause queue.
            for (int i = 0; i < clause_queue.size(); i++)
                for (int j = 0; j < clause_queue[i].size(); j++)
                    delete clause_queue[i][j];
            clause_queue.clear();
        }

        void Trip::enqueueClause(ScheduledClause* sc)
        {
            if (tip.verbosity >= 4){
                printf("[enqueueClause] clause = ");
                printClause(*sc);
                printf("\n"); }
            clause_queue.growTo(sc->cycle+1);
            clause_queue[sc->cycle].push(sc);
        }


        ScheduledClause* Trip::getMinClause()
        {
            // Naive implementation:
            int i;
            for (i = 0; i < clause_queue.size() && clause_queue[i].size() == 0; i++)
                ;

            if (i == clause_queue.size())
                return NULL;

            ScheduledClause* result = clause_queue[i].last();
            clause_queue[i].pop();

            if (tip.verbosity >= 4){
                printf("[getMinClause] clause = ");
                printClause(*result);
                printf("\n"); }

            return result;
        }


        void Trip::clearInactive()
        {
            // Remove all references to inactive clauses:
            for (GateIt git = tip.main.begin(); git != tip.main.end(); ++git)
                for (unsigned s = 0; s < 2; s++)
                    for (unsigned bwd = 0; bwd < 2; bwd++){
                        Sig x = mkSig(*git, s);
                        SMap<vec<Clause*> >& occ = bwd ? bwd_occurs : fwd_occurs;
                        if (!occ.has(x))
                            continue;

                        int i,j;
                        for (i = j = 0; i < occ[x].size(); i++)
                            if (occ[x][i]->isActive())
                                occ[x][j++] = occ[x][i];
                        occ[x].shrink(i - j);
                    }
            
            // Delete inactive clauses:
            int n_removed = 0;
            for (int k = 0; k < F.size(); k++){
                int i,j;
                for (i = j = 0; i < F[k].size(); i++)
                    if (F[k][i]->isActive())
                        F[k][j++] = F[k][i];
                    else
                        n_removed++, delete F[k][i];
                F[k].shrink(i - j);
            }
            if (tip.verbosity >= 2)
                printf("[clearInactive] removed %d inactive clauses\n", n_removed);
        }


        bool Trip::removeClause(Clause* c)
        {
            // It was not already removed:
            assert(c->isActive());

            c->deactivate();

            if (tip.verbosity >= 3){
                printf("[removeClause] clause removed:");
                printClause(*c);
                if (c->cycle != cycle_Undef)
                    printf("(#clauses=%d at cycle %d)\n", F_size[c->cycle], c->cycle);
                else
                    printf("(inv)\n");
            }

            if (c->cycle == cycle_Undef){
                n_inv--;
                return false;
            }
            n_total--;
            step.resetCycle(c->cycle, F_size[c->cycle]);

            // While removing from the last cycle, the set can not become empty:
            assert(c->cycle < (unsigned)size());

            // FIXME: what to check here instead?
            // assert(c->cycle < size()-1 || F_size[c->cycle] > 1);

            F_size[c->cycle]--;
            c->deactivate();

            // FIXME: what to check here instead?
            // Assume that there was no empty set before:
            // assert(F_size[c->cycle] > 0 || F_size[c->cycle+1] > 0);

            return F_size[c->cycle] == 0;
        }

        unsigned Trip::size() const { assert(F.size() == F_size.size()); return F.size(); }


        bool Trip::addClause(const Clause& c_)
        {
            unsigned cycle = c_.cycle;
            if (c_.cycle != cycle_Undef){
                assert(cycle <= size());
                // Clause that hold up-to and including 'cycle':
                // FIXME: how to handle the case when 'cycle == size()'
                if (cycle == size())
                    cycle--;
                F[cycle].push(new Clause(c_));
                F_size[cycle]++;
                F[cycle].last()->cycle = cycle;
            }else{
                // Invariant clause:
                F_inv.push(new Clause(c_));
                n_inv++;
            }
            Clause& c = cycle != cycle_Undef ? *F[cycle].last() : *F_inv.last();
            assert(c.size() > 0);
            assert(!fwdSubsumed(&c_));
            n_total++;

            if (tip.verbosity >= 3){
                printf("[addClause] clause proved:");
                printClause(c);
                if (c.cycle != cycle_Undef)
                    printf("(#clauses=%d at cycle %d)\n", F_size[c.cycle], c.cycle);
                else
                    printf("(inv)\n");
            }

            prop.addClause(c);
            step.addClause(c);

            // Attach to backward subsumption index:
            for (unsigned i = 0; i < c.size(); i++){
                bwd_occurs.growTo(c[i]);
                bwd_occurs[c[i]].push(&c);
            }

            // Attach to forward subsumption index:
            int min_index = 0;
            int min_size  = fwd_occurs.has(c[0]) ? fwd_occurs[c[0]].size() : 0;
            for (unsigned i = 1; i < c.size(); i++){
                Sig x    = c[i];
                int size = fwd_occurs.has(x) ? fwd_occurs[x].size() : 0;
                if (size < min_size){
                    min_size  = size;
                    min_index = i;
                }
            }
            fwd_occurs.growTo(c[min_index]);
            fwd_occurs[c[min_index]].push(&c);

            return bwdSubsume(&c);
        }


        // FIXME: it can happen that the last cycle becoming empty triggers this, and no invariant
        // can be extracted. Should we just let that happen maybe? It does not seem like an error.

        // There is some cycles i,j such that i < j, F[i] == 0 and F[j] > 0. Then the invariant is
        // equal to the union of F[l] for l such that i < l < size().
        void Trip::extractInvariant()
        {
            Clause c;
            for (int i = 0; i < F.size(); i++)
                if (F_size[i] == 0){
                    assert((unsigned)i < size()-1);
                    int inv_size = 0;
                    for (unsigned j = i+1; j < size(); j++)
                        for (int k = 0; k < F[j].size(); k++)
                            if (F[j][k]->isActive()){
                                c = *F[j][k];
                                c.cycle = cycle_Undef;
                                addClause(c);
                                inv_size++;
                            }
                    printf("[extractInvariant] extracted invariant of size %d\n", inv_size);
            
                    // Check that the invariant is non-empty:
                    assert(inv_size > 0);

                    return;
                }

            // Check that some F[i] was empty:
            assert(false);
        }
        

        // PRECONDITION: (incomplete?) 'c' must not already exist in the forward subsumption index.
        bool Trip::fwdSubsumed(const Clause* c)
        {
            for (unsigned i = 0; i < c->size(); i++){
                Sig x = (*c)[i];
                if (!fwd_occurs.has(x))
                    continue;

                for (int j = 0; j < fwd_occurs[x].size(); j++)
                    if (fwd_occurs[x][j]->isActive() && subsumes(*fwd_occurs[x][j], *c)){
                        if (tip.verbosity >= 3){
                            printf("[fwdSubsumed] c = ");
                            printClause(*fwd_occurs[x][j]);
                            printf("\n");
                            printf("[fwdSubsumed] d = ");
                            printClause(*c);
                            printf("\n");
                        }

                        return true;
                    }
            }
            return false;
        }

        
        void Trip::verifySubsumption()
        {
            for (int i = 0; i < F.size(); i++)
                for (int j = 0; j < F[i].size(); j++)
                    if (F[i][j]->isActive())
                        bwdSubsume(F[i][j], true);
        }


        bool Trip::bwdSubsume(Clause* c, bool verify)
        {
            assert(bwd_occurs.has((*c)[0]));
            int min_index = 0;
            int min_size  = bwd_occurs[(*c)[0]].size();
            for (unsigned i = 1; i < c->size(); i++){
                assert(bwd_occurs.has((*c)[i]));
                Sig x    = (*c)[i];
                int size = bwd_occurs[x].size();
                if (size < min_size){
                    min_size  = size;
                    min_index = i;
                }
            }

            const vec<Clause*>& occ = bwd_occurs[(*c)[min_index]];

            bool inv_found = false;
            for (int i = 0; i < occ.size(); i++)
                if (occ[i] != c && occ[i]->isActive() && subsumes(*c, *occ[i]))
                    if (removeClause(occ[i])){
                        if (verify){
                            printf("[bwdSubsume] spurious subsumption\n");
                            printf("[bwdSubsume] c = ");
                            printClause(*c);
                            printf("\n");
                            printf("[bwdSubsume] d = ");
                            printClause(*occ[i]);
                            printf("\n");
                            assert(false);
                        }
                        inv_found = true;
                    }

            return inv_found;
        }


        void Trip::printInvariant(){
            for (int i = 0; i < F_inv.size(); i++)
                if (F_inv[i]->isActive()){
                    const Clause& c = *F_inv[i];
                    printf(" >> ");
                    printClause(c);
                    printf("\n");
                }
        }


        bool Trip::pushClauses()
        {
            Clause c,d;
            assert(F.size() > 0);

            clearInactive();

            // Somewhat weird special case that currently needs to be taken care of:
            for (int i = 0; i < F_size.size()-1; i++)
                if (F_size[i] == 0)
                    return true;

            // TMP: check that no subsumptions were missed.
            verifySubsumption();
            
            for (int i = 0; i < F.size()-1; i++)
                for (int j = 0; j < F[i].size(); j++)
                    if (F[i][j]->isActive()){
                        c = *F[i][j];
                        c.cycle++;
                        if (proveStep(c, d)){
                            if (tip.verbosity >= 3) {
                                printf(  "[pushClauses] pushed = ");
                                printClause(*F[i][j]);
                                printf("\n[pushClauses] to     = ");
                                printClause(d);
                                printf("\n"); }
                            
                            // NOTE: the clause F[i][j] will be removed by backward subsumption.
                            if (addClause(d)){
                                extractInvariant();
                                return true;
                            }
                        }
                    }

            return false;
        }


        static bool findClause(const ScheduledClause* x, const ScheduledClause* xs)
        {
            return xs->next != NULL && (xs->next == x || findClause(x, xs->next));
        }


        bool Trip::proveRec(ScheduledClause* sc, SafeProp p)
        {
            enqueueClause(sc);
            for (;;){
                // if (tip.verbosity >= 2) printf("[proveRec] property = %d\n", p);

                ScheduledClause* sc = getMinClause();

                if (sc == NULL)
                    break;

                if (fwdSubsumed((Clause*)sc)){
                    // NOTE: there may still be live references to 'sc'. Need some kind of
                    // reference counting?
                    // delete sc;

                    // FIXME: 'sc' should be scheduled in the future, +1 from the clause that
                    // subsumed it.

                    continue;
                }

                ScheduledClause* pred;
                Clause           minimized;

                static unsigned iters = 0;

                if (proveAndGeneralize(sc, minimized, pred)){
                    if ((iters++ % 10) == 0) printStats(sc->cycle, false);
                    // TODO: plug memory leak of scheduled clauses if invariant is found.
                    if (addClause(minimized)){
                        // FIXME: reference counting?
                        // delete sc;
                        extractInvariant();
                    }else if (minimized.cycle != cycle_Undef && minimized.cycle+1 < size()){
                        sc->cycle = minimized.cycle+1;
                        enqueueClause(sc);
                    }else
                        ;
                    // FIXME: reference counting?
                    // delete sc;
                }else if (sc->cycle == 0){
                    Trace             cex    = tip.newTrace();
                    vec<vec<lbool> >& frames = tip.traces[cex].frames;
                    extractTrace(pred, frames);
                    tip.safe_props[p].stat   = pstat_Falsified;
                    tip.safe_props[p].cex    = cex;
                    delete sc;
                    delete pred;
                    return false;
                }else{
                    enqueueClause(pred);
                    enqueueClause(sc);
                }
            }

            return true;
        }


        bool Trip::decideCycle()
        {
            ScheduledClause* pred;
            int unresolved = 0;
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Unknown){
                    lbool prop_res = l_False;
                    do {
                        prop_res = proveProp(tip.safe_props[p].sig, pred);
                        if (prop_res == l_False){
                            if (!proveRec(pred, p))
                                // 'p' was falsified.
                                break;
                        }else if (prop_res == l_True){
                            // 'p' is implied by the invariants.
                            tip.safe_props[p].stat = pstat_Proved;
                        }else if (prop_res == l_Undef){
                            // Done with 'p' for this cycle:
                            unresolved++;
                        }
                    }while (prop_res == l_False);
                }

            // Check if all properties were resolved:
            if (unresolved == 0)
                return true;

            // At this point we know that all remaining properties are implied in cycle k+1. Expand
            // a new frame and push clauses forward as much as possible:
            F.push();
            F_size.push(0);
            prop.clearClauses();

            if (pushClauses()){
                printStats();
                // All remaining properties proved:
                for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                    if (tip.safe_props[p].stat == pstat_Unknown)
                        tip.safe_props[p].stat = pstat_Proved;
                
                return true;
            }else
                return false;
        }


        void Trip::printStats(unsigned curr_cycle, bool newline)
        {
            if (tip.verbosity >= 2){
                printf("[trip-stats] #clauses=%d, depth=%d\n", n_total, size());
                init.printStats();
                prop.printStats();
                step.printStats();
            }
            printf("%d:", size());
            for (int i = 0; i < F.size(); i++){
                printf("%c%d", i == (int)curr_cycle ? '*' : ' ', F_size[i]);
            }
            printf(" (%d)", n_inv);
            printf(newline || tip.verbosity >= 2 ? "\n" : "\r");
            fflush(stdout);
        }


        void Trip::printClause(const Clause& c)
        {
            Tip::printClause(tip, c);
        }
    };


    void relativeInduction(TipCirc& tip)
    {
        double time_before = cpuTime();
        Trip   trip(tip);

        if (!trip.baseCase())
            while (!trip.decideCycle())
                trip.printStats();

        if (tip.verbosity >= 2){
            // If some property was proved, print the invariant:
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Proved){
                    printf("[relativeInduction] invariant:\n");
                    trip.printInvariant();
                    break;
                }
        }

        if (tip.verbosity >= 1)
            printf("CPU Time: %6.2f s\n", cpuTime() - time_before);
    }


//=================================================================================================
} // namespace Tip
