include "../specs/Type.dfy"
include "../specs/Replica.dfy"
include "../specs/System.dfy"
include "Lemmas_Replica.dfy"


/**
 @Module Name : M_Lemmas_System
 @Description : Lemmas for system, such as proving state invariants, message relations during system's transitions.
 */
module M_Lemmas_System {
    import opened M_SpecTypes
    import opened M_Replica
    import opened M_System
    import opened M_Adversary
    import opened M_AuxilarilyFunc
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
    ensures m.sender == replica
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

    lemma LemmaAdversaryMsgReceivedIsSubsetOfSystemMsgSentInSystemNextByOneReplica(
        ss : SystemState,
        ss' : SystemState,
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures ss'.adversary.msgReceived <= ss'.msgSent
    {
    }

    lemma {:isolate_assertions} LemmaHonestSenderOriginInSystemNextByOneReplica(
        ss : SystemState,
        ss' : SystemState,
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures Inv_HonestSenderOrigin(ss')
    {
        forall m |
            && m in ss'.msgSent
            && IsHonest(ss', m.sender)
        ensures m in ss'.nodeStates[m.sender].msgSent
        {
            if m in ss.msgSent {
                assert IsHonest(ss, m.sender);
                assert m in ss.nodeStates[m.sender].msgSent;
                if IsHonest(ss, replica) && m.sender == replica {
                    LemmaMsgRelationInReplicaNext(
                        ss.nodeStates[replica],
                        inMsg,
                        ss'.nodeStates[replica],
                        outMsg);
                }
            } else {
                assert m in outMsg;
                if IsHonest(ss, replica) {
                    assert ss.nodeStates[replica].id == replica;
                    LemmaReplicaStableIDInReplicaNext(
                        ss.nodeStates[replica],
                        inMsg,
                        ss'.nodeStates[replica],
                        outMsg);
                    assert ss'.nodeStates[replica].id == replica;
                    LemmaMsgSentBySameReplicaInReplicaNext(
                        ss.nodeStates[replica],
                        inMsg,
                        ss'.nodeStates[replica],
                        outMsg);
                    LemmaMsgRelationInReplicaNext(
                        ss.nodeStates[replica],
                        inMsg,
                        ss'.nodeStates[replica],
                        outMsg);
                    assert m.sender == replica;
                } else {
                    var adversaryReceived := ss.adversary.msgReceived + inMsg;
                    assert adversaryReceived <= ss.msgSent;
                    assert m !in adversaryReceived;
                    assert AdversaryCanCreateMsg(
                        adversaryReceived,
                        ss.adversary.byz_nodes,
                        m);
                    assert m.sender in ss'.adversary.byz_nodes;
                    assert false;
                }
            }
        }
    }

    lemma LemmaQCSignatureEvidenceInSystemNextByOneReplica(
        ss : SystemState,
        ss' : SystemState,
        replica : Address,
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    requires inMsg <= ss.msgSent
    requires SystemNextByOneReplica(ss, ss', replica, inMsg, outMsg)
    ensures Inv_QCSignatureEvidence(ss')
    {
        assert ss.msgSent <= ss'.msgSent;
        forall m | m in ss'.msgSent
            ensures MessageQCsHaveVoteEvidence(
                ss'.msgSent,
                ss'.adversary.byz_nodes,
                m)
        {
            if m in ss.msgSent {
                assert MessageQCsHaveVoteEvidence(
                    ss.msgSent,
                    ss.adversary.byz_nodes,
                    m);
                LemmaMessageQCEvidenceMonotonic(
                    ss.msgSent,
                    ss'.msgSent,
                    ss.adversary.byz_nodes,
                    m);
            } else {
                assert m in outMsg;
                if IsHonest(ss, replica) {
                    assert ss.nodeStates[replica].msgReceived + inMsg <= ss.msgSent;
                    assert forall received |
                        received in ss.nodeStates[replica].msgReceived + inMsg
                        :: MessageQCsHaveVoteEvidence(
                            ss.msgSent,
                            ss.adversary.byz_nodes,
                            received);
                    LemmaReplicaNextOutputQCsHaveVoteEvidence(
                        ss.nodeStates[replica],
                        inMsg,
                        ss'.nodeStates[replica],
                        outMsg,
                        ss.msgSent,
                        ss.adversary.byz_nodes);
                    LemmaMessageQCEvidenceMonotonic(
                        ss.msgSent,
                        ss'.msgSent,
                        ss.adversary.byz_nodes,
                        m);
                } else {
                    var adversaryReceived := ss.adversary.msgReceived + inMsg;
                    assert adversaryReceived <= ss.msgSent;
                    if m in adversaryReceived {
                        assert m in ss.msgSent;
                        assert false;
                    } else {
                        assert AdversaryCanCreateMsg(
                            adversaryReceived,
                            ss.adversary.byz_nodes,
                            m);
                        LemmaMessageQCEvidenceMonotonic(
                            adversaryReceived,
                            ss'.msgSent,
                            ss.adversary.byz_nodes,
                            m);
                    }
                }
            }
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
        LemmaAdversaryMsgReceivedIsSubsetOfSystemMsgSentInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
        LemmaHonestSenderOriginInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
        LemmaQCSignatureEvidenceInSystemNextByOneReplica(ss, ss', replica, inMsg, outMsg);
    }
}
