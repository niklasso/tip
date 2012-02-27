/*********************************************************************************[RemoveUnused.cc]
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

#include "mcl/CircPrelude.h"
#include "tip/reductions/RemoveUnused.h"

namespace Tip {

    namespace {

        // Redundant logic removal may remove some inputs, which will change the size of input
        // frames when inputs with maximal numberings are removed. This trace adaptor inserts the
        // proper amount of 'x's at the end of each frame to correct the trace.
        class LostInputAdaptor : public TraceAdaptor
        {
            unsigned init_frame_size;
            unsigned frame_size;
            void patch(vec<vec<lbool> >& frames){
                frames[0].growTo(init_frame_size, l_Undef);
                for (int i = 1; i < frames.size(); i++)
                    frames[i].growTo(frame_size, l_Undef);
            }
            
        public:
            LostInputAdaptor(unsigned init_frame_size_, unsigned frame_size_, TraceAdaptor* chain) : 
                TraceAdaptor(chain), init_frame_size(init_frame_size_), frame_size(frame_size_){}
        };
    };


void removeUnusedLogic(TipCirc& tip)
{
    vec<Sig> xs;

    //--------------------------------------------------------------------------
    // Figure out the current input frame size:

    unsigned max_input = 0;
    for (SeqCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
        if (tip.main.number(*iit) != UINT32_MAX && tip.main.number(*iit)+1 > max_input)
            max_input = tip.main.number(*iit)+1;

    unsigned max_init_input = 0;
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
        if (tip.init.number(*iit) != UINT32_MAX && tip.init.number(*iit)+1 > max_init_input)
            max_init_input = tip.init.number(*iit)+1;

    //--------------------------------------------------------------------------
    // Collect starting referenses (active properties + constraints + fairness):

    tip.extractRoots(xs);
    xs.push(sig_True);

    //--------------------------------------------------------------------------
    // Calculate all gates reachable from some active property or constraint:

    GSet used;
    while (xs.size() > 0){
        Gate g = gate(xs.last()); xs.pop();

        if (used.has(g))
            continue;
        used.insert(g);

        if (type(g) == gtype_And){
            xs.push(tip.main.lchild(g));
            xs.push(tip.main.rchild(g));
        }else if (tip.flps.isFlop(g))
            xs.push(tip.flps.next(g));
    }

    SeqCirc   copy;
    GMap<Sig> mmap;
    GMap<Sig> imap;

    //--------------------------------------------------------------------------
    // Copy all used gates:

    mmap.growTo(tip.main.lastGate(), sig_Undef);
    for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git)
        if (used.has(*git)){
            if (type(*git) == gtype_Const)
                mmap[*git] = mkSig(*git);
            else if (type(*git) == gtype_And){
                assert(used.has(gate(tip.main.lchild(*git))));
                Sig x = mmap[gate(tip.main.lchild(*git))] ^ sign(tip.main.lchild(*git));
                Sig y = mmap[gate(tip.main.rchild(*git))] ^ sign(tip.main.rchild(*git));
                mmap[*git] = copy.main.mkAnd(x, y);
            }else{
                assert(type(*git) == gtype_Inp);
                mmap[*git] = copy.main.mkInp(tip.main.number(*git));
            }
        }

    //--------------------------------------------------------------------------
    // Copy used parts of reset circuit and used flops:

    for (SeqCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
        if (used.has(*flit)){
            Gate f      = gate(mmap[*flit]); assert(!sign(mmap[*flit]));
            Sig  f_init = copySig(tip.init, copy.init, tip.flps.init(*flit), imap);
            Sig  f_next = mmap[gate(tip.flps.next(*flit))] ^ sign(tip.flps.next(*flit));
            copy.flps.define(f, f_next, f_init);
            // TODO: this should happen in 'define()' but can't at the moment.
            copy.main.number(f) =  tip.main.number(f);
        }

    copy.init.moveTo(tip.init);
    copy.main.moveTo(tip.main);
    copy.flps.moveTo(tip.flps);
    
    //--------------------------------------------------------------------------
    // Move references to circuit copy:

    tip.updateRoots(mmap);

    //--------------------------------------------------------------------------
    // Figure out the new input frame size:

    unsigned new_max_input = 0;
    for (SeqCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
        if (tip.main.number(*iit) != UINT32_MAX && tip.main.number(*iit)+1 > new_max_input)
            new_max_input = tip.main.number(*iit)+1;

    unsigned new_max_init_input = 0;
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
        if (tip.init.number(*iit) != UINT32_MAX && tip.init.number(*iit)+1 > new_max_init_input)
            new_max_init_input = tip.init.number(*iit)+1;

    if (new_max_input < max_input || new_max_init_input < max_init_input){
        if (tip.verbosity >= 2)
            printf("[removeUnusedLogic] lost some inputs that need to be corrected: %d -> %d (init), %d -> %d (main)\n",
                   max_init_input, new_max_init_input, max_input, new_max_input);

        tip.tradaptor = new LostInputAdaptor(max_init_input, max_input, tip.tradaptor);
    }
}


//=================================================================================================
} // namespace Tip
