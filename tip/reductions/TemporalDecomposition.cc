/************************************************************************[TemporalDecomposition.cc]
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

#include "minisat/mtl/Map.h"
#include "mcl/Equivs.h"
#include "mcl/CircPrelude.h"
#include "tip/unroll/Bmc.h"
#include "tip/reductions/Substitute.h"
#include "tip/reductions/TemporalDecomposition.h"
#include "tip/reductions/RemoveUnused.h"

using namespace Minisat;

namespace Tip {

    namespace {

        class TempDecompAdaptor : public TraceAdaptor
        {
            unsigned       init_frame_size;
            vec<vec<int> > init_num_map;

            void patchRadius(unsigned& radius)
            {
                radius += init_num_map.size();
            }

            void patch(vec<vec<lbool> >& frames)
            {
                vec<vec<lbool> > new_frames;

                // Copy initial portion of frame 0:
                new_frames.push();
                frames[0].copyTo(new_frames.last());
                new_frames[0].shrink(new_frames[0].size() - init_frame_size);

                // Expand the previously unrolled frames:
                for (int i = 0; i < init_num_map.size(); i++){
                    new_frames.push();
                    new_frames.last().growTo(init_num_map[i].size(), l_Undef);
                    for (int j = 0; j < init_num_map[i].size(); j++)
                        if (init_num_map[i][j] >= 0)
                            new_frames.last()[j] = frames[0][init_num_map[i][j]];
                }

                // Move the remaining frames:
                for (int i = 1; i < frames.size(); i++){
                    new_frames.push();
                    frames[i].moveTo(new_frames.last());
                }
                new_frames.moveTo(frames);
            }
            
        public:
            TempDecompAdaptor(unsigned init_frame_size_, vec<vec<int> >& init_num_map_, TraceAdaptor* chain) :
                TraceAdaptor(chain), init_frame_size(init_frame_size_) { init_num_map_.moveTo(init_num_map); }
        };


        void simulateInit(const TipCirc& tip, vec<lbool>& out)
        {
            GMap<lbool> val(tip.init.lastGate(), l_Undef);
            for (GateIt git = tip.init.begin0(); git != tip.init.end(); ++git)
                if (*git == gate_True)
                    val[*git] = l_True;
                else if (type(*git) == gtype_And){
                    Sig x = tip.init.lchild(*git);
                    Sig y = tip.init.rchild(*git);
                    val[*git] = (val[gate(x)] ^ sign(x)) && (val[gate(y)] ^ sign(y));
                }

            out.clear();
            for (int i = 0; i < tip.flps.size(); i++){
                Sig f_init = tip.flps.init(tip.flps[i]);
                out.push(val[gate(f_init)] ^ sign(f_init));
            }
        }


        void simulateStep(const TipCirc& tip, const vec<lbool>& prev, vec<lbool>& out)
        {
            assert(prev.size() == tip.flps.size());
            GMap<lbool> val(tip.main.lastGate(), l_Undef);

            for (int i = 0; i < tip.flps.size(); i++)
                val[tip.flps[i]] = prev[i];

            for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git)
                if (val[*git] == l_Undef){
                    if (*git == gate_True)
                        val[*git] = l_True;
                    else if (type(*git) == gtype_And){
                        Sig x = tip.main.lchild(*git);
                        Sig y = tip.main.rchild(*git);
                        val[*git] = (val[gate(x)] ^ sign(x)) && (val[gate(y)] ^ sign(y));
                    }
                }

            // printf("circuit: ");
            // for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git)
            //     printf("%c", val[*git] == l_Undef ? 'x' : val[*git] == l_True ? '1' : '0');
            // printf("\n");

            out.clear();
            for (int i = 0; i < tip.flps.size(); i++){
                Sig f_next = tip.flps.next(tip.flps[i]);
                out.push(val[gate(f_next)] ^ sign(f_next));
            }
        }


        void printState(const vec<lbool>& xs)
        {
            for (int i = 0; i < xs.size(); i++)
                printf("%c", xs[i] == l_Undef ? 'x' : xs[i] == l_True ? '1' : '0');
        }

        void printEquivs(const Equivs& eqs)
        {
            for (unsigned i = 0; i < eqs.size(); i++){
                printf("{ ");
                for (int j = 0; j < eqs[i].size(); j++){
                    if (j > 0) printf(", ");
                    printSig(eqs[i][j]);
                }
                printf(" }");
            }
        }


        void stateEquivs(const TipCirc& tip, const vec<lbool>& xs, Equivs& eqs)
        {
            eqs.clear();
            for (int i = 0; i < tip.flps.size(); i++)
                if (xs[i] == l_True)
                    eqs.merge(sig_True, mkSig(tip.flps[i]));
                else if (xs[i] == l_False)
                    eqs.merge(sig_False, mkSig(tip.flps[i]));
        }


        bool equivsHolds(const TipCirc& tip, const vec<lbool>& xs, const Equivs& eqs)
        {
            Equivs curr, inters;
            stateEquivs(tip, xs, curr);
            for (unsigned i = 0; i < eqs.size(); i++){
                Sig x = eqs[i][0];
                for (int j = 0; j < eqs[i].size(); j++)
                    if (!curr.equals(x, eqs[i][j]))
                        return false;
            }
            return true;
        }


        struct StateEq {
            const vec<vec<lbool> >& states;
            StateEq(vec<vec<lbool> >& sts) : states(sts){}

            bool operator()(unsigned s, unsigned t) const
            {
                const vec<lbool>& xs = states[s];
                const vec<lbool>& ys = states[t];

                assert(xs.size() == ys.size());
                for (int i = 0; i < xs.size(); i++)
                    if (xs[i] != ys[i])
                        return false;
                return true;
            }
        };


        struct StateHash {
            const vec<vec<lbool> >& states;
            StateHash(vec<vec<lbool> >& sts) : states(sts){}

            uint32_t operator()(unsigned s) const
            {
                const vec<lbool>& xs = states[s];

                uint32_t x = 0;
                for (int i = 0; i < xs.size(); i++){
                    uint32_t y = toInt(xs[i]);
                    x = x * 313 + (y & ~(y&2 >> 1));
                }
                return x;
            }
        };


        void detectEquivalentFlops(const TipCirc& tip, unsigned max_cycle, Equivs& eqs, unsigned& cycle)
        {
            vec<vec<lbool> > states;
            states.push();
            simulateInit(tip, states.last());
            
            // printf(" 0: ");
            // printState(states.last());
            // printf("\n");
            
            StateHash                                   hsh(states);
            StateEq                                     heq(states);
            Map<unsigned, unsigned, StateHash, StateEq> map(hsh, heq);
            
            map.insert(states.size()-1, states.size()-1);
            
            // TODO: make a parameter of this constant.
            for (int i = 1; i < 2048; i++){
                states.push();
                simulateStep(tip, states[states.size()-2], states.last());
                
                unsigned c;
                if (map.peek(states.size()-1, c)){
                    printf("[detectEquivalentFlops] found loop from cycle %d to %d!\n", i, c);
                    
                    stateEquivs(tip, states[c], eqs);
                    
                    // printf("%d: ", i);
                    // printState(states[i]);
                    // printf("\n");
                    // 
                    // printf("equivs %d: ", c);
                    // printEquivs(eqs);
                    // printf("\n");

                    for (int j = c+1; j < i; j++){
                        Equivs curr;
                        stateEquivs(tip, states[j], curr);
                        Equivs inters;
                        equivsIntersection(eqs, curr, inters);
                        inters.moveTo(eqs);
                        
                        // printf("state %d: ", j);
                        // printState(states[j]);
                        // printf("\n");
                        // 
                        // printf("curr %d: ", j);
                        // printEquivs(curr);
                        // printf("\n");
                        // 
                        // printf("equivs %d: ", j);
                        // printEquivs(eqs);
                        // printf("\n");
                        
                    }
                    
                    printf("[detectEquivalentFlops] equivs %d: ", c);
                    printEquivs(eqs);
                    printf("\n");
                    
                    unsigned j = c;
                    while (j > 0 && equivsHolds(tip, states[j-1], eqs))
                        j--;
                    if (j < c){
                        c = j;
                        printf("[detectEquivalentFlops] equivs holds at an earlier time point: %d\n", c);
                    }

                    // TODO: make a parameter of this constant.
                    while (c > max_cycle){
                        Equivs curr;
                        stateEquivs(tip, states[--c], curr);
                        Equivs inters;
                        equivsIntersection(eqs, curr, inters);
                        inters.moveTo(eqs);
                        printf("pulling back equivs %d: ", c);
                        printEquivs(eqs);
                        printf("\n");
                    }                        

                    cycle = c;
                    break;
                }

                map.insert(states.size()-1, states.size()-1);
                // map.insert(&states.last(), i);
                // printf("%2d: ", i);
                // printState(states.last());
                // printf("\n");
            }
        }



    }



void temporalDecompositionSmart(TipCirc& tip, unsigned min_cycles, unsigned max_cycles)
{
    Equivs   eqs;
    unsigned cycle = 0;

    detectEquivalentFlops(tip, max_cycles, eqs, cycle);

    if (eqs.size() > 0 || min_cycles > 0){
        if (min_cycles > cycle)
            cycle = min_cycles;

        printf("[temporalDecomposition] unrolling %d cycles.\n", cycle);
        temporalDecomposition(tip, cycle);

        if (eqs.size() > 0){
            substitute(tip, eqs);
            tip.stats(); }
        removeUnusedLogic(tip);
        tip.stats();
    }
}


void temporalDecomposition(TipCirc& tip, unsigned cycles)
{
    basicBmc(tip, 0, cycles, /* no liveness */false);

    // Figure out the current maximal input-number in the reset circuit:
    vec<vec<int> > init_num_map;
    unsigned       init_frame_size = 0;
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
        if (tip.init.number(*iit) != UINT32_MAX && tip.init.number(*iit)+1 > init_frame_size)
            init_frame_size = tip.init.number(*iit)+1;
    unsigned       next_number = init_frame_size;

    Sig init_constr = sig_True;
    for (unsigned i = 0; i < cycles; i++){
        GMap<Sig> cmap(tip.main.lastGate(), sig_Undef);
        for (int i = 0; i < tip.flps.size(); i++){
            Gate f  = tip.flps[i];
            cmap[f] = tip.flps.init(f);
        }

        copyCirc(tip.main, tip.init, cmap);
        init_num_map.push();
        for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
            if (tip.main.number(*iit) != UINT32_MAX){
                assert(cmap[*iit] != sig_Undef);
                assert(!sign(cmap[*iit]));
                tip.init.number(gate(cmap[*iit])) = next_number++;
                init_num_map.last().growTo(tip.main.number(*iit)+1, -1);
                init_num_map.last()[tip.main.number(*iit)] = tip.init.number(gate(cmap[*iit]));
            }

        Flops flps;
        for (int i = 0; i < tip.flps.size(); i++){
            Gate f      = tip.flps[i];
            Sig  f_next = tip.flps.next(f);
            Sig  f_init = cmap[gate(f_next)] ^ sign(f_next);
            flps.define(f, f_next, f_init);
        }
        flps.moveTo(tip.flps);

        // Build constraint logic:
        for (unsigned i = 0; i < tip.cnstrs.size(); i++){
            Sig x = cmap[gate(tip.cnstrs[i][0])] ^ sign(tip.cnstrs[i][0]);
            for (int j = 1; j < tip.cnstrs[i].size(); j++){
                Sig y = cmap[gate(tip.cnstrs[i][j])] ^ sign(tip.cnstrs[i][j]);
                init_constr = tip.init.mkAnd(init_constr, ~tip.init.mkXor(x, y));
                // printf("x = ");
                // printSig(x);
                // printf("\n");
                // printf("y = ");
                // printSig(y);
                // printf("\n");
            }
        }
    }

#if 0
    for (int i = 0; i < init_num_map.size(); i++)
        for (int j = 0; j < init_num_map[i].size(); j++)
            printf(" ... mapping input-number %d cycle %d to %d\n", j, i, init_num_map[i][j]);
#endif

    tip.tradaptor = new TempDecompAdaptor(init_frame_size, init_num_map, tip.tradaptor);

    if (init_constr != sig_True){
        printf("[temporalDecomposition] Adding a constraint flop.\n");
        Sig f = tip.main.mkInp();
        tip.flps.define(gate(f), sig_True, init_constr);
        tip.cnstrs.merge(sig_True, f);
    }
}


//=================================================================================================
} // namespace Tip
