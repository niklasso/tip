/***********************************************************************************[Substitute.cc]
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
#include "tip/reductions/Substitute.h"

namespace Tip {

// TODO: specify when this is ok to use w.r.t constraints and such.
void substitute(TipCirc& tip, const Equivs& eqs)
{
    Circ      copy;
    Flops     cflps;
    GMap<Sig> cmap;
    copyCircWithSubst(tip.main, copy, eqs, cmap);

    for (SeqCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
        assert(!sign(cmap[*flit]));
        Gate f      = gate(cmap[*flit]);
        Sig  f_next = cmap[gate(tip.flps.next(*flit))] ^ sign(tip.flps.next(*flit));
        cflps.define(f, f_next, tip.flps.init(*flit));
        // TODO: this should happen in 'define()' but can't at the moment.
        copy.number(f) = tip.main.number(f);
    }
    copy .moveTo(tip.main);
    cflps.moveTo(tip.flps);

    tip.updateRoots(cmap);
}


void substituteConstraints(TipCirc& tip)
{
    Circ      copy;
    Flops     cflps;
    GMap<Sig> cmap;
    copyCircWithSubst(tip.main, copy, tip.cnstrs, cmap);

    for (SeqCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
        assert(!sign(cmap[*flit]));
        Gate f      = gate(cmap[*flit]);
        Sig  f_next = cmap[gate(tip.flps.next(*flit))] ^ sign(tip.flps.next(*flit));
        cflps.define(f, f_next, tip.flps.init(*flit));
        // TODO: this should happen in 'define()' but can't at the moment.
        copy.number(f) = tip.main.number(f);
    }
    copy .moveTo(tip.main);
    cflps.moveTo(tip.flps);

    tip.updateRoots(cmap);
}

//=================================================================================================
} // namespace Tip
