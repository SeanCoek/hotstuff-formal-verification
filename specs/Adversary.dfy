include "Type.dfy"
include "Auxilarily.dfy"


/**
 @Module Name : M_Adversary
 @Description : Definitions of adversary's state, behaviours, and invariants.
 */
module M_Adversary {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    /**
     * Definition of Byzantine nodes. We group all Byzantine nodes as a adversary.
     * @param byz_nodes -> ID of all Byzantine nodes
     * @param msgReceived -> Messages recieved by all Byzantine nodes
     */
    datatype Adversary = Adversary(
        byz_nodes : set<Address>,
        msgReceived : set<Msg>
    )

    /**
     * Initial state of adversary
     */
    predicate AdversaryInit(a : Adversary)
    {
        && a.byz_nodes == M_SpecTypes.Adversary_Nodes
        && a.byz_nodes <= M_SpecTypes.All_Nodes  // byzantine nodes should exists in the set of all nodes.
        && |a.byz_nodes| <= f(|M_SpecTypes.All_Nodes|)    // the counts of byzantine nodes should not exceed 1/3 of all nodes.
        && a.msgReceived == {}
    }

    predicate AdversaryCanCreateMsg(
        msgReceived : set<Msg>,
        byzNodes : set<Address>,
        m : Msg)
    {
        && m.sender in byzNodes
        && MessageQCsHaveVoteEvidence(msgReceived, byzNodes, m)
    }

    /**
     * Definiton of transition state for adversary
     * @param a -> current(or old) state of adversary
     * @param inMsg -> Messages recieved by current adversary
     * @param a' -> next(or new) state of adversary
     * @param outMsg -> Messages sent by current adversary when state transition happens.
     */
    predicate AdversaryNext(
        a : Adversary, 
        inMsg : set<Msg>,
        a' : Adversary, 
        outMsg : set<Msg>
        )
    {
        var msgReceived := a.msgReceived + inMsg;
        && a' == a.(
            msgReceived := msgReceived
        )
        && (forall m | m in outMsg ::
                    || m in msgReceived // relay received messages to other nodes.
                    || AdversaryCanCreateMsg(msgReceived, a.byz_nodes, m)
            )
    }
}
