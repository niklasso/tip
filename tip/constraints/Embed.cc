/****************************************************************************************[Embed.cc]
Copyright (c) 2011, Niklas Sorensson, Koen Claessen
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

#include "tip/constraints/Embed.h"
#include "mcl/CircTypes.h"

namespace Tip {

void embedConstraints(TipCirc &tip)
{
    if ( tip.cnstrs.size() > 0 ) {
        // creating the flop that holds all the constraints
        Sig pre_constr = tip.main.mkInp();
        Sig constr     = pre_constr;
        for ( unsigned int i = 0; i < tip.cnstrs.size(); i++ ) {
            Sig rep = tip.cnstrs[i][0];
            for ( int j = 1; j < tip.cnstrs[i].size(); j++ )
                // TODO: investigate the need for other codings
                constr = tip.main.mkAnd(constr,~tip.main.mkXor(rep,tip.cnstrs[i][j]));
        }
        tip.flps.define(gate(pre_constr),constr,sig_True);
    
        // clearing the constraints
        tip.cnstrs.clear();
    
        // embedding the flop in safety properties
        for ( SafeProp p = 0; p < tip.safe_props.size(); p++ )
            tip.safe_props[p].sig = tip.main.mkOr(~constr, tip.safe_props[p].sig);
    
        // add the flop as a fairness property (!)
        // TODO: investigate if we should bake the constraint into the justify signals directly
        if ( tip.live_props.size() > 0 )
            tip.fairs.push(constr);
    }
}

//=================================================================================================
} // namespace Tip
