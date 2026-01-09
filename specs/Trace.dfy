include "Type.dfy"
include "System.dfy"


/**
 @Module Name : M_Trace
 @Description : Definitions of a transition path of a system, representing of a system run.
 */
module M_Trace {
    import opened M_SpecTypes
    import opened M_System

    type Trace = nat -> SystemState

    ghost predicate ValidTrace(t : Trace)
    {
        && SystemInit(t(0))
        && (forall i : nat :: && ValidSystemState(t(i))
                              && SystemNext(t(i), t(i+1)))
    }

    // A reachable state in HotStuff is either a initial state, 
    // or a state that can be reached through a valid execution path from the initial state.
    ghost predicate Reachable(ss : SystemState)
    {
        || SystemInit(ss)
        || exists run : seq<SystemState> ::
                                            && |run| > 1
                                            && SystemInit(run[0])
                                            && run[|run|-1] == ss
                                            && (forall i | 0 <= i < |run|-1
                                                        :: 
                                                           && ValidSystemState(run[i])
                                                           && SystemNext(run[i], run[i+1]))
        
    }
}