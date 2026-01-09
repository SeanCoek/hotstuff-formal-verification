include "Type.dfy"
include "Replica.dfy"
include "System.dfy"
include "Lemmas_Replica.dfy"


/**
 @Module Name : M_Lemmas_System
 @Description : Lemmas for system, such as proving state invariants, message relations during system's transitions.
 */
module M_Lemmas_System {
    import opened M_SpecTypes
    import opened M_Replica
    import opened M_System
    import opened M_Lemmas_Replica

    lemma LemmaInitialSystemStateHoldsValidity(ss : SystemState)
    requires SystemInit(ss)
    ensures ValidSystemState(ss)
    {

    }

    lemma LemmaSystemTransitionHoldsValidity(ss : SystemState, ss' : SystemState)
    requires ValidSystemState(ss)
    requires SystemNext(ss, ss')
    ensures ValidSystemState(ss')
    {
        // Prove a valid state after system transition will still be valid
        if ss == ss' {
            assert ValidSystemState(ss');
        }
        else {
            // assert false;
            forall replica, msgReceivedByNodes, msgSentByNodes
                    | && msgReceivedByNodes <= ss.msgSent
                      && SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes)
            ensures ValidSystemState(ss') {
                LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
            }
        }
    }

    lemma LemmaReplicaMsgReceivedMustBeSent(
        ss : SystemState,
        ss' : SystemState
    )
    requires ValidSystemState(ss)
    requires SystemNext(ss, ss')
    ensures forall r | IsHonest(ss', r) :: ss'.nodeStates[r].msgReceived <= ss'.msgSent
    {
        if ss == ss' {

        }
        else {
            // assert false;
            var replica, msgReceivedByNodes, msgSentByNodes
                   :|   && msgReceivedByNodes <= ss.msgSent
                        && SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
            LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, msgReceivedByNodes, msgSentByNodes);
        }
    }

    lemma LemmaInvNodeInSystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures Inv_Node_System(ss')
    {
        var r := ss.nodeStates[replica];
        var r' := ss'.nodeStates[replica];
        if IsHonest(ss, replica)
        {
            LemmaReplicaStableIDInReplicaNext(r, inMsg, r', outMsg);
            // assert r'.id == r.id;
        }
        else
        {
            // Prove AdversaryNext Won't change replica ID
            // assert forall r | IsHonest(ss, r) :: ss.nodeStates[r].id == ss'.nodeStates[r].id;
            // assert forall r | r in ss.adversary.byz_nodes
            //                 ::
            //                   && ss'.nodeStates[r].id == ss.nodeStates[r].id;
        }
    }

    lemma LemmaHonestReplicaIsValidInSystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures forall r | IsHonest(ss', r) :: ValidReplicaState(ss'.nodeStates[r])
    {
        if IsHonest(ss, replica) {
            LemmaReplicaNextIsValid(ss.nodeStates[replica],
                                    inMsg,
                                    ss'.nodeStates[replica],
                                    outMsg);
        }
    }

    lemma LemmaHonestSentMsgCapturedBySystemInSystemNextByOneReplica(
            ss : SystemState, 
            ss' : SystemState, 
            replica : Address,
            inMsg : set<Msg>,
            outMsg : set<Msg>,
            m : Msg)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    requires m in outMsg && IsHonest(ss', replica)
    // ensures forall m | m in outMsg && IsHonest(ss', m.sender) :: m in ss'.nodeStates[m.sender].msgSent
    ensures m.sender == replica
    // ensures m in ss'.nodeStates[m.sender].msgSent
    {
        var r := ss.nodeStates[replica];
        var r' := ss'.nodeStates[replica];
        LemmaSystemNextByOneReplicaIsValid(ss, ss', replica, inMsg, outMsg);
        // assert ValidSystemState(ss');
        assert r'.id == replica;
        LemmaMsgSentBySameReplicaInReplicaNext(r, inMsg, r', outMsg);
        assert r'.id == m.sender;
    }

    lemma LemmaHonestReplicaMsgReceivedIsSubsetOfSystemMsgSentInSystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures forall r | IsHonest(ss', r) :: ss'.nodeStates[r].msgReceived <= ss'.msgSent
    {
        if IsHonest(ss, replica) {
            var rState := ss.nodeStates[replica];
            var rState' := ss'.nodeStates[replica];
            LemmaMsgRelationInReplicaNext(rState, inMsg, rState', outMsg);
        }
    }

    lemma LemmaReplicaMsgSentIsSubsetOfSystemMsgSentInSystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures forall r | r in ss'.nodeStates.Keys :: ss'.nodeStates[r].msgSent <= ss'.msgSent
    {
        if IsHonest(ss, replica) {
            var rState := ss.nodeStates[replica];
            var rState' := ss'.nodeStates[replica];
            LemmaMsgRelationInReplicaNext(rState, inMsg, rState', outMsg);
            assert rState'.msgSent <= ss'.msgSent;
        }
        else {
            forall r_byz | r_byz in ss.adversary.byz_nodes
            ensures ss'.nodeStates[r_byz].msgSent <= ss'.msgSent {
                var byzState := ss.nodeStates[r_byz];
                var byzState' := ss'.nodeStates[r_byz];
                // assert forall r | r in ss.nodeStates.Keys :: ss.nodeStates[r].msgSent <= ss.msgSent by {
                //     assert ValidSystemState(ss);
                // }
                assert byzState'.msgSent <= ss'.msgSent;
            }
        }
    }

    lemma LemmaSystemNextByOneReplicaIsValid(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures ValidSystemState(ss')
    {
        LemmaInvNodeInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
        LemmaReplicaMsgSentIsSubsetOfSystemMsgSentInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
        LemmaHonestReplicaIsValidInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
        LemmaHonestReplicaMsgReceivedIsSubsetOfSystemMsgSentInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
    }
}