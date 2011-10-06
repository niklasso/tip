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

void removeUnusedLogic(TipCirc& tip)
{
    vec<Sig> xs;

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
        if (used.has(*git))
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

    //--------------------------------------------------------------------------
    // Copy used parts of reset circuit and used flops:

    for (SeqCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
        if (used.has(*flit)){
            Gate f      = gate(mmap[*flit]); assert(!sign(mmap[*flit]));
            Sig  f_init = copySig(tip.init, copy.init, tip.flps.init(*flit), imap);
            Sig  f_next = mmap[gate(tip.flps.next(*flit))] ^ sign(tip.flps.next(*flit));
            copy.flps.define(f, f_next, f_init);
        }

    copy.init.moveTo(tip.init);
    copy.main.moveTo(tip.main);
    copy.flps.moveTo(tip.flps);
    
    //--------------------------------------------------------------------------
    // Move references to circuit copy:

    tip.updateRoots(mmap);
}


//=================================================================================================
} // namespace Tip
