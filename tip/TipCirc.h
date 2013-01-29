/***************************************************************************************[TipCirc.h]
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

#ifndef Tip_TipCirc_h
#define Tip_TipCirc_h

#include "mcl/Equivs.h"
#include "mcl/SeqCirc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Basic types:

typedef enum { pstat_Proved = 0, pstat_Falsified = 1, pstat_Unknown = 2, pstat_Discarded = 3 } PropStatus;
typedef enum { ripbmc_None = 0, ripbmc_Safe = 1, ripbmc_Live = 2 } RipBmcMode;

typedef vec<Gate> IFrame;
typedef int       Trace;
typedef int       SafeProp;
typedef int       LiveProp;

enum { trace_Undef = -1 };
enum { prop_Undef  = -1 };
enum { loop_none   = UINT32_MAX };

struct TraceData {
    vec<vec<lbool> > frames;
    uint32_t         loop;
    TraceData() : loop(loop_none){}
};

struct SafePropData {
    Sig        sig;
    PropStatus stat;
    unsigned   radius;
    Trace      cex;
    SafePropData(Sig s) : sig(s), stat(pstat_Unknown), radius(0), cex(trace_Undef){}
};

struct LivePropData {
    vec<Sig>   sigs;
    PropStatus stat;
    Trace      cex;
};

class TraceAdaptor
{
    TraceAdaptor* chain;
public:
    typedef uint32_t InputId;

    TraceAdaptor(TraceAdaptor* chain_ = NULL) : chain(chain_){}
    virtual ~TraceAdaptor(){ delete chain; }

    void adapt(vec<vec<lbool> >& frames){
        patch(frames);
        if (chain != NULL) chain->adapt(frames);
    }

    void adaptRadius(unsigned& radius){
        patchRadius(radius);
        if (chain != NULL) chain->adaptRadius(radius);
    }

private:
    virtual void patch(vec<vec<lbool> >& frames){};
    virtual void patchRadius(unsigned& radius){}
};


class AigerInitTraceAdaptor : public TraceAdaptor
{
    struct FlopInit {
        lbool   val;  // Initialized to 0, 1, or x.
        InputId x_id; // Input-number in case of x.
    };

    vec<FlopInit> flop_init;

    void patch(vec<vec<lbool> >& frames)
    {
        vec<lbool>  new_zero;
        vec<lbool>& prv_zero = frames[0];

        for (int i = 0; i < flop_init.size(); i++)
            if (flop_init[i].val == l_Undef){
                assert(flop_init[i].x_id != UINT32_MAX);
                assert(flop_init[i].x_id < (uint32_t)prv_zero.size());
                new_zero.push(prv_zero[flop_init[i].x_id]);
            }else
                new_zero.push(flop_init[i].val);
        new_zero.moveTo(prv_zero);
    }


public:
    void flop(InputId fid, lbool val, InputId x_id = UINT32_MAX)
    {
        flop_init.growTo(fid+1);
        flop_init[fid].val  = val;
        flop_init[fid].x_id = x_id;
    }
};


#if 0
// TODO: these classes are sketchy at the moment.

//=================================================================================================
// A simple class to represent a set of circuit traces:

class TraceSet {
public:
    Trace                   newTrace ()         { trace_set.push(); return trace_set.size()-1; }
    vec<vec<lbool> >&       getFrames(Trace tr) { assert(tr < (Trace)trace_set.size()); return trace_set[tr].frames; }
    const vec<vec<lbool> >& getFrames(Trace tr) const { assert(tr < (Trace)trace_set.size()); return trace_set[tr].frames; }
    uint32_t&               getLoop  (Trace tr) { assert(tr < (Trace)trace_set.size()); return trace_set[tr].loop; }
    void                    clear    ()         { trace_set.clear(); }

    enum { loop_none = UINT32_MAX };

private:
    struct TraceData {
        vec<vec<lbool> > frames;
        uint32_t         loop;
        TraceData() : loop(loop_none){}
    };
    vec<TraceData> trace_set;
};

//=================================================================================================
// A class to represent a set of properties and their verification statuses:

class PropertySet {
public:
    Property   newProperty      (Sig s, PropType t)    { props.push(PropData(s,t)); return props.size()-1; }
    void       setPropTrue      (Property p)           { assert(p < (Property)props.size()); props[p].stat = pstat_True; }
    void       setPropFalsified (Property p, Trace cex){ assert(p < (Property)props.size()); props[p].stat = pstat_Falsifiable; props[p].cex = cex; }
    Sig        propSig          (Property p) const     { assert(p < (Property)props.size()); return props[p].sig; }
    PropType   propType         (Property p) const     { assert(p < (Property)props.size()); return props[p].type; }
    PropStatus propStatus       (Property p) const     { assert(p < (Property)props.size()); return props[p].stat; }
    Trace      propCex          (Property p) const     { assert(p < (Property)props.size()); return props[p].cex; }
    void       clear            ()                     { props.clear(); }

private:
    struct PropData {
        Sig        sig;
        PropType   type;
        PropStatus stat;
        Trace      cex;
        PropData(Sig s, PropType t) : sig(s), type(t), stat(pstat_Unknown), cex(trace_Undef){}
    };
    vec<PropData> props;
};
#endif

//=================================================================================================
// A class for representing a sequential circuit together with properties and their current
// verification status. Additionally, extra references to inputs are kept to allow extraction of
// traces (counter-examples). All major transformations and proof-engines should exist as a method
// of this class.

class TipCirc : public SeqCirc {
public:
    TipCirc() : tradaptor(NULL), resultFile(NULL), verbosity(0){}
    ~TipCirc(){ delete tradaptor; if (resultFile) fclose(resultFile);}

    //---------------------------------------------------------------------------------------------
    // Top-level user API:

    typedef enum { bmc_Basic = 0, bmc_Simp = 1, bmc_Simp2 = 2 } BmcVersion;

    void readAiger         (const char* file);
    void writeAiger        (const char* file) const;
    void writeResultsAiger (FILE* out) const;
    void printResults      () const;
    void openResultFile    (const char* file);
    void writeResultSafe   (SafeProp p);
    void writeResultLive   (LiveProp p);

    void bmc               (uint32_t begin_cycle, uint32_t stop_cycle, BmcVersion bver = bmc_Basic);
    void sce               (bool use_minimize_alg = true, bool only_coi = false);
    void trip              (RipBmcMode bmc_mode = ripbmc_None);
    void selSafe           (SafeProp p);
    void selLive           (LiveProp p);

    void stats             ();

    //---------------------------------------------------------------------------------------------
    // Debug:

    void printSig          (Sig x) const;
    void printCirc         () const;
    void printTrace        (FILE* out, const vec<vec<lbool> >& tr) const;

    //---------------------------------------------------------------------------------------------
    // Intermediate internal API: (still public)

    // Circuit data: (traces, properties, constraints)

    vec<TraceData>    traces;      // Set of traces falsifying some property.
    vec<SafePropData> safe_props;  // Set of safety properties.
    vec<LivePropData> live_props;  // Set of liveness properties.
    Equivs            cnstrs;      // Set of global constraints (expressed as equivalences).
    vec<Sig>          fairs;       // Set of fairness constraints.
    TraceAdaptor*     tradaptor;   // Trace adaptor to compensate trace changing transformations.

    FILE*             resultFile;  // File to write results to, incrementally
    
    // TODO:
    //   - fairness constraints.
    //   - circuit outputs?

    SafeProp newSafeProp     (Sig x);
    LiveProp newLiveProp     (const vec<Sig>& x);
    Trace    newTrace        ();
    void     adaptTrace      (vec<vec<lbool> >& frames);
    void     setRadiusSafe   (SafeProp p, unsigned radius, const char* engine = NULL);
    void     setProvenSafe   (SafeProp p, const char* engine = NULL);
    void     setProvenLive   (LiveProp p, const char* engine = NULL);
    void     setFalsifiedSafe(SafeProp p, Trace, const char* engine = NULL);
    void     setFalsifiedLive(LiveProp p, Trace, const char* engine = NULL);

    void     extractRoots(vec<Sig>& xs);
    void     updateRoots (GMap<Sig>& cmap);

    void     clear       ();
    void     moveTo      (TipCirc& to);

    // Settings:
    int           verbosity;

 private:

    // Internal private helpers:
    
    void printTrace      (FILE* out, Trace t) const;
    void printTraceAiger (FILE* out, Trace tid) const;
};

//=================================================================================================

inline LiveProp TipCirc::newLiveProp (const vec<Sig>& s) {
    live_props.push();
    LivePropData& d = live_props.last();
    s.copyTo(d.sigs);
    d.stat = pstat_Unknown;
    d.cex = trace_Undef;
    return live_props.size()-1;
}

inline SafeProp TipCirc::newSafeProp (Sig x){ safe_props.push(SafePropData(x)); return safe_props.size()-1; }
inline Trace    TipCirc::newTrace    ()     { traces.push(); return traces.size()-1; }
inline void     TipCirc::adaptTrace  (vec<vec<lbool> >& frames){ if (tradaptor != NULL) tradaptor->adapt(frames); }


//=================================================================================================

};

#endif
