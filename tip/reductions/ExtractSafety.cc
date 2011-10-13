/********************************************************************************[ExtractSafety.cc]
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

#include "tip/reductions/ExtractSafety.h"
#include "tip/reductions/RemoveUnused.h"
#include "mcl/Circ.h"

namespace Tip {

void extractSafety(TipCirc& tip)
{
    printf("== extracting extra safety signals ==\n");
    tip.stats();

    int num = 0;    
    SafeProp p = 0;
    while ( p < tip.safe_props.size() ) {
        Sig s = tip.safe_props[p].sig;
        
        // check if this signal not already exists
        int exists = 0;
        for ( SafeProp q = 0; q < p; q++ )
            if ( tip.safe_props[q].sig == s ) {
                exists = 1;
                break;
            }
        
        if ( exists ) {
            tip.safe_props[p].sig = tip.safe_props.last().sig;
            tip.safe_props.pop();
        } else if ( !sign(s) && type(s) == gtype_And ) {
            tip.safe_props[p].sig = tip.main.lchild(s);
            tip.newSafeProp(tip.main.rchild(s));
            num++;
        } else
            p++;
    }

    printf("-- expanded %d safety signals\n", num);
    removeUnusedLogic(tip);
    tip.stats();
}

//=================================================================================================
} // namespace Tip
