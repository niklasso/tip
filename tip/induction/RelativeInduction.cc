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

#include "minisat/simp/SimpSolver.h"
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/induction/Induction.h"
#include "tip/induction/TripTypes.h"
#include "tip/induction/TripProofInstances.h"

namespace Tip {

    namespace {

        template<class Vec>
        void mkUnion(const Vec& c, const Vec& d, vec<Sig>& out)
        {
            // FIXME: clean up.
            unsigned i,j;
            for (i = j = 0; i < c.size() || j < d.size();){
                if (i < c.size() && (j == d.size() || c[i] < d[j]))
                    out.push(c[i++]);
                else if (i == c.size() || d[j] < c[i])
                    out.push(d[j++]);
                else{
                    out.push(c[i++]);
                    j++;
                }
            }
        }

        //===================================================================================================
        // Temporal Relative Induction Prover:
        class Trip {
            TipCirc&             tip;

            // Solver independent data:
            vec<Clause*>         proved;     // All proved clauses.
            vec<unsigned>        cycle_size; // Number of proved clauses in each cycle.

            vec<vec<ScheduledClause*> > 
                                 clause_queue;
            SMap<vec<Clause*> >  bwd_occurs;
            SMap<vec<Clause*> >  fwd_occurs;

            // Solver data: Should be rederivable from only independent data at any time:
            InitInstance         init;
            PropInstance         prop;
            StepInstance         step;

            // PROVE:   Init ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in cycle 1,
            //       or False and the starting point of a counter-example trace.
            bool             proveInit(const ScheduledClause* c, Clause& yes, ScheduledClause*& no);
            bool             proveInit(const Clause& c, Clause& yes);

            // PROVE:   let k = c.cycle: F[k-1] ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in some cycle >= k,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveStep(const ScheduledClause* c, Clause& yes, ScheduledClause*& no);
            bool             proveStep(const Clause& c, Clause& yes);

            // PROVE:   let k = F.size()-1: F[k] ^ Trans => prop'
            // RETURNS: True and a new frame F[k+1] can be opened,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveProp(Sig p, ScheduledClause*& no);

            // Prove scheduled clause "recursively". Returns true if proved and false if falsified.
            bool             propagate    (ScheduledClause* sc, SafeProp p);

            // Try to push clauses forwards, particularily push clauses forward into the newly opened last
            // frame. Returns true if an invariant is found and false otherwise.
            bool             pushClauses  ();

            // Add a proved clause 'c'. Returns true if this causes an invariant to be found, and false
            // otherwise.
            bool             addClause    (const Clause& c);

            // Remove a proved clause 'c'. Returns true if this causes an invariant to be found,
            // and false otherwise.
            bool             removeClause (Clause* c);

            // Check if clause 'c' is subsumed by any previously proved clause. Returns true if it is and
            // false otherwise.
            bool             fwdSubsumed  (const Clause* c);

            // Find and remove all previously proved claues that are subsumed by the new clause 'c'. If an
            // invariant is found true is returned, otherwise false.
            bool             bwdSubsume   (Clause* c);

            void             enqueueClause(ScheduledClause* sc);
            ScheduledClause* getMinClause ();

            // Extracts the trace that leads to the failure, and removes all scheduled clauses.
            void             extractTrace (const ScheduledClause* sc, vec<vec<lbool> >& frames);

            // Returns number of states in unrolling.
            unsigned         size() const;

            // Fill all active clauses such that the clause 'c' is in out[c.cycle].
            void             clausesByCycle(vec<vec<Clause*> >& out);
            
            // DEBUG:
            void             printClause(const Clause& c);

        public:
            Trip(TipCirc& t) : tip(t), init(t), prop(t, proved), step(t, proved)
            {
                cycle_size.push(0);
            }

            // Prove or disprove all properties using depth k. Returns true if all properties are decided, and
            // false if there are still some unresolved property.
            bool decideCycle();

            // Prove that the necessary number of initial cycles are bug free. Returns true if all properties
            // are resolved (i.e. all properties were falsifiable), and false otherwise.
            bool baseCase();

            void printStats();
        };

        bool Trip::proveInit(const ScheduledClause* c, Clause& yes, ScheduledClause*& no){ 
            return init.prove(*c, yes, no, c);
        }

        bool Trip::proveInit(const Clause& c, Clause& yes){ 
            ScheduledClause* dummy;
            return init.prove(c, yes, dummy);
        }

        bool Trip::proveStep(const ScheduledClause* c, Clause& yes, ScheduledClause*& no)
        {
            Clause yes_step;
            Clause yes_init;

            if (!step.prove(*c, yes_step, no, c)){
                // printf("[proveStep] no = ");
                // printClause(*no);
                // printf("\n");
                return false;
            }

            bool must_hold = proveInit(*c, yes_init);
            assert(must_hold);

            if (tip.verbosity >= 4){
                printf("[proveStep] yes_step = ");
                printClause(yes_step);
                printf("\n");
                printf("[proveStep] yes_init = ");
                printClause(yes_init);
                printf("\n");
            }

            // Calculate union of the two strengthened clauses:
            vec<Sig> yes_union;
            mkUnion(yes_step, yes_init, yes_union);
            yes = Clause(yes_union, yes_step.cycle);
            return true;
        }


        bool Trip::proveStep(const Clause& c, Clause& yes)
        {
            // FIXME: code duplication ...
            Clause           yes_step;
            Clause           yes_init;
            ScheduledClause* dummy;

            if (!step.prove(c, yes_step, dummy))
                return false;

            bool must_hold = proveInit(c, yes_init);
            assert(must_hold);

            // Calculate union of the two strengthened clauses:
            vec<Sig> yes_union;
            mkUnion(yes_step, yes_init, yes_union);
            yes = Clause(yes_union, yes_step.cycle);
            return true;
        }


        bool Trip::proveProp(Sig p, ScheduledClause*& no){ return prop.prove(p, no, size()-1); }


        bool Trip::baseCase()
        {
            // Run BMC for the necessary number of initial cycles:
            tip.bmc(0,1);

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


        bool Trip::removeClause(Clause* c)
        {
            // FIXME: inactivating this assert for now.
            // Don't remove clauses from the last frame. The last frame is not yet completed and if
            // it becomes empty this does not indicate that an invariant has been found.
            // assert(c->cycle < size()-1);

            --cycle_size[c->cycle];
            c->deactivate();

            // Assume that there was no empty set before:
            assert(cycle_size[c->cycle] > 0 || cycle_size[c->cycle+1] > 0);

            return cycle_size[c->cycle] == 0;
        }

        unsigned Trip::size() const { return cycle_size.size(); }


        bool Trip::addClause(const Clause& c_)
        {
            assert(!fwdSubsumed(&c_));

            proved.push(new Clause(c_));
            const Clause& c = *proved.last();
            cycle_size[c.cycle]++;

            if (tip.verbosity >= 3){
                printf("[addClause] clause proved:");
                printClause(c);
                printf("\n"); 
            }

            if (c.cycle == size()-1){
                if (tip.verbosity >= 4) printf("[addClause] adding to prop-instance.\n");
                prop.addClause(c);
            }
            step.addClause(c);

            // Attach to backward subsumption index:
            for (unsigned i = 0; i < c.size(); i++){
                bwd_occurs.growTo(c[i]);
                bwd_occurs[c[i]].push(proved.last());
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
            fwd_occurs[c[min_index]].push(proved.last());

            return bwdSubsume(proved.last());
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
        

        bool Trip::bwdSubsume(Clause* c)
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

            for (int i = 0; i < occ.size(); i++)
                if (occ[i] != c && occ[i]->isActive() && subsumes(*c, *occ[i]))
                    removeClause(occ[i]);

            return false;
        }


        bool Trip::pushClauses()
        {
            vec<vec<Clause*> > F; clausesByCycle(F);
            Clause c,d;
            assert(F.size() > 0);

            printf("[pushClauses]\n");
            for (int i = 0; i < F[0].size(); i++){
                c = *F[0][i];
                c.cycle++;
                if (proveStep(c, d)){
                    printf("[pushClauses] pushed = ");
                    printClause(*F[0][i]);
                    printf("\n[pushClauses] to = ");
                    printClause(d);
                    printf("\n");
                    
                    if (addClause(d))
                        return true;
                    if (removeClause(F[0][i]))
                        return true;
                }
            }

            for (int i = 1; i < F.size(); i++)
                for (int j = 0; j < F[i].size(); j++)
                    if (proveStep(*F[i][j], d)){
                        printf("[pushClauses] pushed = ");
                        printClause(*F[i][j]);
                        printf("\n[pushClauses] to = ");
                        printClause(d);
                        printf("\n");
                        if (addClause(d))
                            return true;
                        if (removeClause(F[i][j]))
                            return true;
                    }

            return false;
        }


        bool Trip::propagate(ScheduledClause* sc, SafeProp p)
        {
            enqueueClause(sc);

            for (;;){
                ScheduledClause* sc = getMinClause();

                if (sc == NULL)
                    break;

                if (fwdSubsumed((Clause*)sc)){
                    delete sc;
                    continue;
                }

                ScheduledClause* pred;
                Clause           minimized;

                if (sc->cycle == 0){
                    // Handle initial cycle:
                    if (proveInit(sc, minimized, pred)){
                        addClause(minimized);
                        sc->cycle = minimized.cycle+1;
                        if (sc->cycle < size())
                            enqueueClause(sc);
                        else
                            delete sc;
                    }else{
                        Trace             cex    = tip.newTrace();
                        vec<vec<lbool> >& frames = tip.traces[cex].frames;
                        extractTrace(pred, frames);
                        tip.safe_props[p].stat   = pstat_Falsified;
                        tip.safe_props[p].cex    = cex;
                        delete sc;
                        delete pred;

                        return false;
                    }

                }else{
                    // Handle arbitrary non-initial cycle:
                    if (proveStep(sc, minimized, pred)){
                        addClause(minimized);
                        sc->cycle = minimized.cycle+1;
                        if (sc->cycle < size())
                            enqueueClause(sc);
                        else
                            delete sc;
                    }else{
                        enqueueClause(pred);
                        enqueueClause(sc);
                    }
                }
            }

            return true;
        }


        bool Trip::decideCycle()
        {
            ScheduledClause* pred;
            int unresolved = 0;
            for (SafeProp p = 0; p < tip.safe_props.size(); p++){
                if (tip.safe_props[p].stat == pstat_Unknown){
                    while (!proveProp(tip.safe_props[p].sig, pred)){
                        if (tip.verbosity >= 3)
                            printf("[decideCycle] cycle=%d, property=%d\n", size(), p);
                        if (!propagate(pred, p))
                            goto next_prop;
                    }
                    unresolved++;
                }
            next_prop:;
            }

            // Check if all properties were resolved (should mean all falsified at the moment):
            if (unresolved == 0)
                return true;

            // At this point we know that all properties are implied in cycle k+1. Expand a new frame and push
            // clauses forward as much as possible:
            cycle_size.push(0);
            prop.clearClauses();
            return pushClauses();
        }


        void Trip::printStats()
        {
            vec<vec<Clause*> > F; clausesByCycle(F);
            printf("%d: ", size());
            for (int i = 0; i < F.size(); i++)
                printf("%d ", F[i].size());
            printf("\n");
        }


        void Trip::printClause(const Clause& c)
        {
            printf("{ ");
            for (unsigned i = 0; i < c.size(); i++){
                if (i > 0) printf(", ");
                if (sign(c[i])) printf("~");
                if (tip.flps.isFlop(gate(c[i])))
                    printf("f");
                else if (type(c[i]) == gtype_Inp)
                    printf("i");
                else
                    assert(false);
                printf("%d", tip.main.number(gate(c[i])));
            }
            printf(" }@%d", c.cycle);
        }



        void Trip::clausesByCycle(vec<vec<Clause*> >& out)
        {
            for (int i = 0; i < proved.size(); i++){
                if (tip.verbosity >= 4){
                    printf("[clausesByCycle]: proved[%d] =", i);
                    printClause(*proved[i]);
                    printf(" (%s)\n", proved[i]->isActive() ? "active" : "inactive");
                }
                if (proved[i]->isActive()){
                    out.growTo(proved[i]->cycle+1);
                    out[proved[i]->cycle].push(proved[i]);
                }
            }
        }

    };


    void relativeInduction(TipCirc& tip)
    {
        Trip trip(tip);

        if (!trip.baseCase())
            while (!trip.decideCycle())
                trip.printStats();
    }


//=================================================================================================
} // namespace Tip
