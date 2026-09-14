include "../specs/Type.dfy"
include "../specs/System.dfy"
include "../specs/Trace.dfy"
include "../specs/Invariants.dfy"
include "../specs/Replica.dfy"
include "../specs/Auxilarily.dfy"
include "../specs/Adversary.dfy"
include "Axioms.dfy"
include "Lemmas_System.dfy"
include "Lemmas.dfy"
include "../common/sets.dfy"

/**
 * Constructive non-vacuity witnesses for the HotStuff transition system.
 *
 * LemmaReachableProperPrepareVote is parametric in the configured node set and
 * assumes only that the view-1 leader is honest.  It is the regression witness
 * for proposalVoteFilter and exercises the real safeNode guard.
 *
 * LemmaReachableSingleNodeHonestDecision is a bounded successful-execution
 * witness.  In the one-node configuration (whose quorum is one), it constructs
 * every proposal, vote, QC, and SystemNext step through DECIDE, then proves that
 * the honest replica's blockchain extends Genesis.  This is an existence and
 * non-vacuity result, not a fairness or liveness theorem.
 */
module M_Reachability_Witness {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_Replica
    import opened M_Adversary
    import opened M_System
    import opened M_Trace
    import opened M_Axiom
    import opened M_Lemma
    import opened M_Lemmas_System
    import opened M_Set

    lemma LemmaInitialMessagesCardinality(senders : set<Address>)
    requires senders <= All_Nodes
    ensures |getMultiInitialMsg(senders)| == |senders|
    decreases |senders|
    {
        if senders != {} {
            var sender :| sender in senders;
            var remaining := senders - {sender};
            LemmaInitialMessagesCardinality(remaining);
            assert getMultiInitialMsg(senders)
                == getMultiInitialMsg(remaining) + {getInitialMsg(sender)} by {
                forall m
                    ensures m in getMultiInitialMsg(senders)
                        <==> m in getMultiInitialMsg(remaining) + {getInitialMsg(sender)}
                {
                    if m in getMultiInitialMsg(senders) {
                        var source :| && source in senders
                                      && m == getInitialMsg(source);
                        if source != sender {
                            assert source in remaining;
                        }
                    }
                    if m in getMultiInitialMsg(remaining) {
                        var source :| && source in remaining
                                      && m == getInitialMsg(source);
                        assert source in senders;
                    }
                }
            }
            assert getInitialMsg(sender) !in getMultiInitialMsg(remaining) by {
                if getInitialMsg(sender) in getMultiInitialMsg(remaining) {
                    var source :| && source in remaining
                                  && getInitialMsg(sender) == getInitialMsg(source);
                    assert sender == source;
                    assert false;
                }
            }
            SetExtension(getInitialMsg(sender), getMultiInitialMsg(remaining));
        }
    }

    lemma LemmaInitialMessagesMatchNewView(senders : set<Address>)
    requires senders <= All_Nodes
    ensures getMatchMsg(getMultiInitialMsg(senders), MT_NewView, 0)
        == getMultiInitialMsg(senders)
    {
        forall m
            ensures m in getMatchMsg(getMultiInitialMsg(senders), MT_NewView, 0)
                <==> m in getMultiInitialMsg(senders)
        {
            if m in getMultiInitialMsg(senders) {
                var source :| && source in senders
                              && m == getInitialMsg(source);
                assert ValidNewView(m);
            }
        }
    }

    function InitialReplicaState(id : Address) : ReplicaState
    requires id in All_Nodes
    {
        ReplicaState(
            id,
            [Genesis_Block],
            1,
            getInitialQC(MT_Prepare),
            getInitialQC(MT_PreCommit),
            {},
            {getInitialMsg(id)})
    }

    function InitialNodeStates() : map<Address, ReplicaState>
    {
        map id | id in All_Nodes :: id := InitialReplicaState(id)
    }

    function InitialSystemState() : SystemState
    {
        SystemState(
            InitialNodeStates(),
            Adversary(Adversary_Nodes, {}),
            getMultiInitialMsg(All_Nodes))
    }

    lemma LemmaConstructedInitialStateIsInitial()
    ensures SystemInit(InitialSystemState())
    {
        Axiom_Common_Constraints();
        Axiom_Byz_Constraints();
    }

    lemma LemmaReachableAfterStep(ss : SystemState, ss' : SystemState)
    requires Reachable(ss)
    requires ValidSystemState(ss)
    requires SystemNext(ss, ss')
    ensures Reachable(ss')
    {
        LemmaReachableStateIsValid(ss);
        if SystemInit(ss) {
            var extendedRun := [ss, ss'];
            assert forall i | 0 <= i < |extendedRun|-1 ::
                && ValidSystemState(extendedRun[i])
                && SystemNext(extendedRun[i], extendedRun[i+1]);
            assert exists run : seq<SystemState> ::
                && |run| > 1
                && SystemInit(run[0])
                && run[|run|-1] == ss'
                && (forall i | 0 <= i < |run|-1 ::
                    && ValidSystemState(run[i])
                    && SystemNext(run[i], run[i+1]));
        } else {
            var run : seq<SystemState> :|
                && |run| > 1
                && SystemInit(run[0])
                && run[|run|-1] == ss
                && (forall i | 0 <= i < |run|-1 ::
                    && ValidSystemState(run[i])
                    && SystemNext(run[i], run[i+1]));
            var extendedRun := run + [ss'];
            forall i | 0 <= i < |extendedRun|-1
                ensures
                    && ValidSystemState(extendedRun[i])
                    && SystemNext(extendedRun[i], extendedRun[i+1])
            {
                if i < |run|-1 {
                } else {
                    assert i == |run|-1;
                    assert extendedRun[i] == ss;
                    assert extendedRun[i+1] == ss';
                }
            }
            assert exists nextRun : seq<SystemState> ::
                && |nextRun| > 1
                && SystemInit(nextRun[0])
                && nextRun[|nextRun|-1] == ss'
                && (forall i | 0 <= i < |nextRun|-1 ::
                    && ValidSystemState(nextRun[i])
                    && SystemNext(nextRun[i], nextRun[i+1]));
        }
    }

    lemma LemmaSingleSubStepIsReplicaNext(
        r : ReplicaState,
        inMsg : set<Msg>,
        received : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires received == r.(msgReceived := r.msgReceived + inMsg)
    requires ValidReplicaState(received)
    requires ReplicaNextSubStep(received, r', outMsg)
    ensures ReplicaNext(r, inMsg, r', outMsg)
    {
        var localRun := [received, r'];
        var localOutputs := [outMsg];
        assert setUnionOnSeq(localOutputs) == outMsg;
    }

    lemma LemmaReachableHonestSingleSubStep(
        ss : SystemState,
        ss' : SystemState,
        replica : Address,
        inMsg : set<Msg>,
        received : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires Reachable(ss)
    requires ValidSystemState(ss)
    requires IsHonest(ss, replica)
    requires inMsg <= ss.msgSent
    requires received == ss.nodeStates[replica].(
        msgReceived := ss.nodeStates[replica].msgReceived + inMsg)
    requires ValidReplicaState(received)
    requires ReplicaNextSubStep(received, r', outMsg)
    requires ss' == SystemState(
        ss.nodeStates[replica := r'],
        ss.adversary,
        ss.msgSent + outMsg)
    ensures Reachable(ss')
    ensures ValidSystemState(ss')
    {
        LemmaSingleSubStepIsReplicaNext(
            ss.nodeStates[replica], inMsg, received, r', outMsg);
        assert SystemNextByOneReplica(
            ss, ss', replica, inMsg, outMsg);
        assert SystemNext(ss, ss');
        LemmaReachableAfterStep(ss, ss');
        LemmaSystemTransitionHoldsValidity(ss, ss');
    }

    lemma LemmaMoreReceivedMessagesPreserveReplicaValidity(
        r : ReplicaState,
        messages : set<Msg>)
    requires ValidReplicaState(r)
    ensures ValidReplicaState(r.(
        msgReceived := r.msgReceived + messages))
    {
    }

    lemma LemmaSplitSingletonMessage(m : Msg)
    ensures splitMsgByBlocks({m}) == {{m}}
    {
        reveal splitMsgByBlocks();
        assert messagesForBlock({m}, m.block) == {m};
    }

    lemma LemmaMaxSingletonSet<T>(items : set<T>)
    ensures getMaxLengthSet({items}) == items
    {
    }

    lemma LemmaFilterKeepsSingletonVote(vote : Msg)
    requires ValidVoteMsg(vote)
    ensures filterDoubleVote({vote}) == {vote}
    {
        reveal filterDoubleVote();
        assert !hasDoubleVote({vote}, vote);
    }

    function SingleVoteQC(vote : Msg) : Cert
    {
        Cert(
            vote.mType,
            vote.viewNum,
            vote.block,
            {vote.partialSig})
    }

    lemma LemmaSingleVoteFormsValidQC(vote : Msg)
    requires ValidVoteMsg(vote)
    requires All_Nodes == {vote.sender}
    ensures ValidQC(SingleVoteQC(vote))
    {
        assert quorum(|All_Nodes|) == 1;
    }

    lemma {:isolate_assertions} LemmaWitnessDecideMessageIsOnlyCommitQC()
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures getMatchQC(
        WitnessStateAfterDecideMessage().msgReceived
            + {WitnessDecideMessage()},
        MT_Decide,
        MT_Commit,
        1) == {WitnessCommitQC()}
    {
        LemmaSingleVoteFormsValidQC(WitnessCommitVote());
        assert ValidDecideMsg(WitnessDecideMessage());
        forall qc
            ensures qc in getMatchQC(
                WitnessStateAfterDecideMessage().msgReceived
                    + {WitnessDecideMessage()},
                MT_Decide,
                MT_Commit,
                1) <==> qc == WitnessCommitQC()
        {
        }
    }

    lemma {:isolate_assertions} LemmaWitnessUponDecideUpdatesBlockchain()
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    requires ValidReplicaState(
        WitnessStateAfterDecideMessage().(
            msgReceived := WitnessStateAfterDecideMessage().msgReceived
                + {WitnessDecideMessage()}))
    ensures UponDecide(
        WitnessStateAfterDecideMessage().(
            msgReceived := WitnessStateAfterDecideMessage().msgReceived
                + {WitnessDecideMessage()}),
        WitnessStateAfterHonestDecision(),
        {WitnessDecideMessage()})
    {
        var received := WitnessStateAfterDecideMessage().(
            msgReceived := WitnessStateAfterDecideMessage().msgReceived
                + {WitnessDecideMessage()});
        var commitVote := WitnessCommitVote();
        LemmaSingleVoteFormsValidQC(commitVote);
        LemmaWitnessDecideMessageIsOnlyCommitQC();
        assert getMatchQC(
            received.msgReceived,
            MT_Decide,
            MT_Commit,
            1) == {WitnessCommitQC()};
        assert getMatchVoteMsg(
            received.msgReceived,
            MT_Commit,
            1) == {commitVote};
        LemmaSplitSingletonMessage(commitVote);
        LemmaMaxSingletonSet({commitVote});
        assert splitMsgByBlocks({commitVote}) == {{commitVote}};
        assert getMaxLengthSet(splitMsgByBlocks({commitVote}))
            == {commitVote};
        assert ExtractSignatrues({commitVote}) == {commitVote.partialSig};
        assert getAncestors(WitnessCommitQC().block)
            == [Genesis_Block, WitnessProposal().block];
        assert received.bc == [Genesis_Block];
        assert received.bc < getAncestors(WitnessCommitQC().block);
        assert received.bc
            + getAncestors(WitnessCommitQC().block)[|received.bc|..]
            == getAncestors(WitnessCommitQC().block);
        assert received.id == leader(1);
        assert received.viewNum == 1;
        assert WitnessCommitQC() == Cert(
            MT_Commit,
            commitVote.viewNum,
            commitVote.block,
            ExtractSignatrues({commitVote}));
        assert WitnessDecideMessage() == Msg(
            received.id,
            MT_Decide,
            received.viewNum,
            EmptyBlock,
            WitnessCommitQC(),
            SigNone,
            CertNone);
        assert WitnessStateAfterHonestDecision() == received.(
            bc := getAncestors(WitnessCommitQC().block),
            msgSent := received.msgSent + {WitnessDecideMessage()});
        Axiom_Common_Constraints();
        assert UponDecide(
            received,
            WitnessStateAfterHonestDecision(),
            {WitnessDecideMessage()});
    }

    function WitnessProposal() : Msg
    {
        Msg(
            leader(1),
            MT_Prepare,
            1,
            getNewBlock(Genesis_Block, 1),
            getInitialQC(MT_Prepare),
            SigNone,
            CertNone)
    }

    function WitnessPrepareVote() : Msg
    {
        buildVoteMsg(
            leader(1),
            MT_Prepare,
            WitnessProposal().block,
            CertNone,
            1,
            getInitialQC(MT_PreCommit),
            leader(1))
    }

    function WitnessPrepareQC() : Cert
    {
        SingleVoteQC(WitnessPrepareVote())
    }

    function WitnessPreCommitRequest() : Msg
    {
        Msg(
            leader(1),
            MT_PreCommit,
            1,
            EmptyBlock,
            WitnessPrepareQC(),
            SigNone,
            CertNone)
    }

    function WitnessPreCommitVote() : Msg
    {
        buildVoteMsg(
            leader(1),
            MT_PreCommit,
            WitnessProposal().block,
            CertNone,
            1,
            CertNone,
            leader(1))
    }

    function WitnessPreCommitQC() : Cert
    {
        SingleVoteQC(WitnessPreCommitVote())
    }

    function WitnessCommitRequest() : Msg
    {
        Msg(
            leader(1),
            MT_Commit,
            1,
            EmptyBlock,
            WitnessPreCommitQC(),
            SigNone,
            CertNone)
    }

    function WitnessCommitVote() : Msg
    {
        buildVoteMsg(
            leader(1),
            MT_Commit,
            WitnessProposal().block,
            CertNone,
            1,
            CertNone,
            leader(1))
    }

    function WitnessCommitQC() : Cert
    {
        SingleVoteQC(WitnessCommitVote())
    }

    function WitnessDecideMessage() : Msg
    {
        Msg(
            leader(1),
            MT_Decide,
            1,
            EmptyBlock,
            WitnessCommitQC(),
            SigNone,
            CertNone)
    }

    function WitnessStateAfterPrepareVote() : ReplicaState
    {
        InitialReplicaState(leader(1)).(
            msgReceived := getMultiInitialMsg(All_Nodes) + {WitnessProposal()},
            msgSent := {
                getInitialMsg(leader(1)),
                WitnessProposal(),
                WitnessPrepareVote()})
    }

    function WitnessStateAfterPreCommitRequest() : ReplicaState
    {
        WitnessStateAfterPrepareVote().(
            msgReceived := WitnessStateAfterPrepareVote().msgReceived
                + {WitnessPrepareVote()},
            msgSent := WitnessStateAfterPrepareVote().msgSent
                + {WitnessPreCommitRequest()})
    }

    function WitnessStateAfterPreCommitVote() : ReplicaState
    {
        WitnessStateAfterPreCommitRequest().(
            prepareQC := WitnessPrepareQC(),
            msgReceived := WitnessStateAfterPreCommitRequest().msgReceived
                + {WitnessPreCommitRequest()},
            msgSent := WitnessStateAfterPreCommitRequest().msgSent
                + {WitnessPreCommitVote(), WitnessPreCommitRequest()})
    }

    function WitnessStateAfterCommitRequest() : ReplicaState
    {
        WitnessStateAfterPreCommitVote().(
            msgReceived := WitnessStateAfterPreCommitVote().msgReceived
                + {WitnessPreCommitVote()},
            msgSent := WitnessStateAfterPreCommitVote().msgSent
                + {WitnessCommitRequest()})
    }

    function WitnessStateAfterCommitVote() : ReplicaState
    {
        WitnessStateAfterCommitRequest().(
            lockedQC := WitnessPreCommitQC(),
            msgReceived := WitnessStateAfterCommitRequest().msgReceived
                + {WitnessCommitRequest()},
            msgSent := WitnessStateAfterCommitRequest().msgSent
                + {WitnessCommitVote(), WitnessCommitRequest()})
    }

    function WitnessStateAfterDecideMessage() : ReplicaState
    {
        WitnessStateAfterCommitVote().(
            msgReceived := WitnessStateAfterCommitVote().msgReceived
                + {WitnessCommitVote()},
            msgSent := WitnessStateAfterCommitVote().msgSent
                + {WitnessDecideMessage()})
    }

    function WitnessStateAfterHonestDecision() : ReplicaState
    {
        WitnessStateAfterDecideMessage().(
            bc := getAncestors(WitnessCommitQC().block),
            msgReceived := WitnessStateAfterDecideMessage().msgReceived
                + {WitnessDecideMessage()},
            msgSent := WitnessStateAfterDecideMessage().msgSent
                + {WitnessDecideMessage()})
    }

    function WitnessMessagesAfterPrepareVote() : set<Msg>
    {
        getMultiInitialMsg(All_Nodes)
            + {WitnessProposal(), WitnessPrepareVote()}
    }

    function WitnessMessagesAfterPreCommitRequest() : set<Msg>
    {
        WitnessMessagesAfterPrepareVote() + {WitnessPreCommitRequest()}
    }

    function WitnessMessagesAfterPreCommitVote() : set<Msg>
    {
        WitnessMessagesAfterPreCommitRequest() + {WitnessPreCommitVote()}
    }

    function WitnessMessagesAfterCommitRequest() : set<Msg>
    {
        WitnessMessagesAfterPreCommitVote() + {WitnessCommitRequest()}
    }

    function WitnessMessagesAfterCommitVote() : set<Msg>
    {
        WitnessMessagesAfterCommitRequest() + {WitnessCommitVote()}
    }

    function WitnessMessagesAfterDecideMessage() : set<Msg>
    {
        WitnessMessagesAfterCommitVote() + {WitnessDecideMessage()}
    }

    ghost predicate WitnessStage(
        ss : SystemState,
        localState : ReplicaState,
        sentMessages : set<Msg>)
    {
        && Reachable(ss)
        && ValidSystemState(ss)
        && IsHonest(ss, leader(1))
        && ss.nodeStates[leader(1)] == localState
        && ss.msgSent == sentMessages
    }

    ghost predicate HasProperPrepareVote(ss : SystemState)
    {
        exists replica, vote ::
            && IsHonest(ss, replica)
            && vote in ss.nodeStates[replica].msgSent
            && ValidPrepareVote(vote)
            && vote.block.Block?
            && vote.viewNum == 1
    }

    ghost predicate HasDecideMessage(ss : SystemState)
    {
        exists decide ::
            && decide in ss.msgSent
            && ValidDecideMsg(decide)
    }

    ghost predicate HasHonestDecision(ss : SystemState)
    {
        exists replica, decide ::
            && IsHonest(ss, replica)
            && decide in ss.nodeStates[replica].msgReceived
            && ValidDecideMsg(decide)
            && decide.justify.block in ss.nodeStates[replica].bc
            && |ss.nodeStates[replica].bc| > 1
    }

    ghost predicate ProperPrepareWitnessState(
        ss : SystemState,
        proposal : Msg,
        vote : Msg)
    {
        var leaderId := leader(1);
        var expectedProposal := Msg(
            leaderId,
            MT_Prepare,
            1,
            getNewBlock(Genesis_Block, 1),
            getInitialQC(MT_Prepare),
            SigNone,
            CertNone);
        var expectedVote := buildVoteMsg(
            leaderId,
            MT_Prepare,
            expectedProposal.block,
            CertNone,
            1,
            getInitialQC(MT_PreCommit),
            leaderId);
        var leaderState := InitialReplicaState(leaderId).(
            msgReceived := getMultiInitialMsg(All_Nodes) + {expectedProposal},
            msgSent := {getInitialMsg(leaderId), expectedProposal, expectedVote});
        && proposal == expectedProposal
        && vote == expectedVote
        && ss.nodeStates.Keys == All_Nodes
        && ss.nodeStates[leaderId] == leaderState
        && ss.adversary == Adversary(Adversary_Nodes, {})
        && ss.msgSent
            == getMultiInitialMsg(All_Nodes) + {expectedProposal, expectedVote}
    }

    lemma {:isolate_assertions} LemmaConstructReachableProperPrepareVote()
        returns (ss2 : SystemState, proposal : Msg, vote : Msg)
    requires leader(1) in Honest_Nodes
    ensures Reachable(ss2)
    ensures HasProperPrepareVote(ss2)
    ensures ProperPrepareWitnessState(ss2, proposal, vote)
    ensures WitnessStage(
        ss2,
        WitnessStateAfterPrepareVote(),
        WitnessMessagesAfterPrepareVote())
    {
        Axiom_Byz_Constraints();
        var ss0 := InitialSystemState();
        LemmaConstructedInitialStateIsInitial();
        LemmaInitialSystemStateHoldsValidity(ss0);
        assert Reachable(ss0);

        var leaderId := leader(1);
        assert leaderId in All_Nodes;
        assert leaderId !in Adversary_Nodes by {
            if leaderId in Adversary_Nodes {
                assert leaderId in Adversary_Nodes * Honest_Nodes;
                assert false;
            }
        }
        assert IsHonest(ss0, leaderId);
        var r0 := ss0.nodeStates[leaderId];
        assert r0 == InitialReplicaState(leaderId);

        LemmaInitialMessagesCardinality(All_Nodes);
        LemmaInitialMessagesMatchNewView(All_Nodes);
        var received1 := r0.(msgReceived := r0.msgReceived + ss0.msgSent);
        assert received1.msgReceived == getMultiInitialMsg(All_Nodes);
        assert ValidReplicaState(received1);
        var newViews := getMatchMsg(received1.msgReceived, MT_NewView, 0);
        assert newViews == getMultiInitialMsg(All_Nodes);
        assert |newViews| == |All_Nodes|;
        assert |newViews| >= quorum(|All_Nodes|);
        assert forall m | m in newViews ::
            && ValidQC(m.justify)
            && m.justify == getInitialQC(MT_Prepare);
        var highQC := getHighQC(newViews);
        assert highQC == getInitialQC(MT_Prepare) by {
            var m :| && m in newViews
                      && ValidQC(m.justify)
                      && m.justify == highQC;
        }
        var proposalBlock := getNewBlock(highQC.block, 1);
        proposal := Msg(
            leaderId,
            MT_Prepare,
            1,
            proposalBlock,
            highQC,
            SigNone,
            CertNone);
        assert ValidProposal(proposal);
        Lemma_DirectChildExtendsParent(proposalBlock, highQC.block);

        assert getMatchProposalMsg(received1.msgReceived, 1) == {};
        assert !isVotedInView(received1.msgSent, MT_Prepare, 1);
        var proposalOut := {proposal};
        var r1 := received1.(msgSent := received1.msgSent + proposalOut);
        assert UponPrepare(received1, r1, proposalOut);
        LemmaSingleSubStepIsReplicaNext(
            r0, ss0.msgSent, received1, r1, proposalOut);
        var ss1 := SystemState(
            ss0.nodeStates[leaderId := r1],
            ss0.adversary,
            ss0.msgSent + proposalOut);
        assert SystemNextByOneReplica(
            ss0,
            ss1,
            leaderId,
            ss0.msgSent,
            proposalOut);
        assert SystemNext(ss0, ss1);
        LemmaReachableAfterStep(ss0, ss1);
        LemmaSystemTransitionHoldsValidity(ss0, ss1);

        var received2 := r1.(msgReceived := r1.msgReceived + {proposal});
        assert ValidReplicaState(received2);
        assert getMatchProposalMsg(received2.msgReceived, 1) == {proposal};
        assert !isVotedInView(received2.msgSent, MT_Prepare, 1);
        assert received2.lockedQC == getInitialQC(MT_PreCommit);
        assert highQC.block == received2.lockedQC.block;
        assert extension(proposal.block, received2.lockedQC.block);
        assert safeNode(proposal.block, proposal.justify, received2.lockedQC);
        vote := buildVoteMsg(
            leaderId,
            MT_Prepare,
            proposal.block,
            CertNone,
            1,
            received2.lockedQC,
            leaderId);
        assert voteForProposal(proposal, received2.lockedQC, leaderId) == vote;
        assert getVotesForSafeProposals(
            getMatchProposalMsg(received2.msgReceived, 1),
            received2.lockedQC,
            leaderId) == {vote};
        assert proposalVoteFilter({vote}) == {vote};
        assert onlyOneVote({vote}) == {vote};
        assert getVotesIfUnVoted({vote}, false) == {vote};
        assert getMatchMsg(received2.msgReceived, MT_NewView, 0) == newViews;
        var voteOut := {vote, proposal};
        var r2 := received2.(msgSent := received2.msgSent + voteOut);
        assert UponPrepare(received2, r2, voteOut);
        LemmaSingleSubStepIsReplicaNext(
            r1, {proposal}, received2, r2, voteOut);
        ss2 := SystemState(
            ss1.nodeStates[leaderId := r2],
            ss1.adversary,
            ss1.msgSent + voteOut);
        assert SystemNextByOneReplica(
            ss1,
            ss2,
            leaderId,
            {proposal},
            voteOut);
        assert SystemNext(ss1, ss2);
        LemmaReachableAfterStep(ss1, ss2);

        assert ValidPrepareVote(vote);
        assert vote in ss2.nodeStates[leaderId].msgSent;
        assert HasProperPrepareVote(ss2);
        assert ProperPrepareWitnessState(ss2, proposal, vote);
        LemmaSystemTransitionHoldsValidity(ss1, ss2);
        assert WitnessStage(
            ss2,
            WitnessStateAfterPrepareVote(),
            WitnessMessagesAfterPrepareVote());
    }

    lemma LemmaReachableProperPrepareVote()
    requires leader(1) in Honest_Nodes
    ensures exists ss ::
        && Reachable(ss)
        && HasProperPrepareVote(ss)
    {
        var ss, proposal, vote := LemmaConstructReachableProperPrepareVote();
    }

    lemma {:isolate_assertions} LemmaReachablePreCommitRequest()
        returns (ss3 : SystemState)
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures WitnessStage(
        ss3,
        WitnessStateAfterPreCommitRequest(),
        WitnessMessagesAfterPreCommitRequest())
    {
        var leaderId := leader(1);
        var ss2, proposal, prepareVote :=
            LemmaConstructReachableProperPrepareVote();
        assert WitnessStage(
            ss2,
            WitnessStateAfterPrepareVote(),
            WitnessMessagesAfterPrepareVote());
        assert prepareVote == WitnessPrepareVote();
        var r2 := ss2.nodeStates[leaderId];
        assert r2 == WitnessStateAfterPrepareVote();

        var prepareQC := WitnessPrepareQC();
        LemmaSingleVoteFormsValidQC(prepareVote);
        var preCommitRequest := WitnessPreCommitRequest();
        assert ValidPrecommitRequest(preCommitRequest);
        var received3 := r2.(
            msgReceived := r2.msgReceived + {prepareVote});
        LemmaMoreReceivedMessagesPreserveReplicaValidity(
            r2, {prepareVote});
        assert ValidReplicaState(received3);
        assert getMatchQC(
            received3.msgReceived,
            MT_PreCommit,
            MT_Prepare,
            1) == {};
        assert getMatchVoteMsg(
            received3.msgReceived,
            MT_Prepare,
            1) == {prepareVote};
        LemmaSplitSingletonMessage(prepareVote);
        LemmaMaxSingletonSet({prepareVote});
        LemmaFilterKeepsSingletonVote(prepareVote);
        assert ExtractSignatrues({prepareVote}) == {prepareVote.partialSig};
        assert !isVotedInView(received3.msgSent, MT_PreCommit, 1);
        var outMsg := {preCommitRequest};
        var r3 := received3.(msgSent := received3.msgSent + outMsg);
        assert UponPreCommit(received3, r3, outMsg);
        ss3 := SystemState(
            ss2.nodeStates[leaderId := r3],
            ss2.adversary,
            ss2.msgSent + outMsg);
        LemmaReachableHonestSingleSubStep(
            ss2, ss3, leaderId, {prepareVote}, received3, r3, outMsg);
        assert r3 == WitnessStateAfterPreCommitRequest();
        assert ss3.msgSent == WitnessMessagesAfterPreCommitRequest();
        assert WitnessStage(
            ss3,
            WitnessStateAfterPreCommitRequest(),
            WitnessMessagesAfterPreCommitRequest());
    }

    lemma {:isolate_assertions} LemmaReachablePreCommitVote()
        returns (ss4 : SystemState)
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures WitnessStage(
        ss4,
        WitnessStateAfterPreCommitVote(),
        WitnessMessagesAfterPreCommitVote())
    {
        var leaderId := leader(1);
        var ss3 := LemmaReachablePreCommitRequest();
        assert WitnessStage(
            ss3,
            WitnessStateAfterPreCommitRequest(),
            WitnessMessagesAfterPreCommitRequest());
        var r3 := ss3.nodeStates[leaderId];
        assert r3 == WitnessStateAfterPreCommitRequest();

        var prepareVote := WitnessPrepareVote();
        var prepareQC := WitnessPrepareQC();
        var preCommitRequest := WitnessPreCommitRequest();
        var preCommitVote := WitnessPreCommitVote();
        LemmaSingleVoteFormsValidQC(prepareVote);
        assert ValidPrecommitRequest(preCommitRequest);
        assert ValidPrecommitVote(preCommitVote);
        var received4 := r3.(
            msgReceived := r3.msgReceived + {preCommitRequest});
        LemmaMoreReceivedMessagesPreserveReplicaValidity(
            r3, {preCommitRequest});
        assert ValidReplicaState(received4);
        assert getMatchQC(
            received4.msgReceived,
            MT_PreCommit,
            MT_Prepare,
            1) == {prepareQC};
        assert getMatchVoteMsg(
            received4.msgReceived,
            MT_Prepare,
            1) == {prepareVote};
        LemmaSplitSingletonMessage(prepareVote);
        LemmaMaxSingletonSet({prepareVote});
        LemmaFilterKeepsSingletonVote(prepareVote);
        assert ExtractSignatrues({prepareVote}) == {prepareVote.partialSig};
        assert !isVotedInView(received4.msgSent, MT_PreCommit, 1);
        var outMsg := {preCommitVote, preCommitRequest};
        var r4 := received4.(
            prepareQC := prepareQC,
            msgSent := received4.msgSent + outMsg);
        assert UponPreCommit(received4, r4, outMsg);
        ss4 := SystemState(
            ss3.nodeStates[leaderId := r4],
            ss3.adversary,
            ss3.msgSent + outMsg);
        LemmaReachableHonestSingleSubStep(
            ss3,
            ss4,
            leaderId,
            {preCommitRequest},
            received4,
            r4,
            outMsg);
        assert r4 == WitnessStateAfterPreCommitVote();
        assert ss4.msgSent == WitnessMessagesAfterPreCommitVote();
        assert WitnessStage(
            ss4,
            WitnessStateAfterPreCommitVote(),
            WitnessMessagesAfterPreCommitVote());
    }

    lemma {:isolate_assertions} LemmaReachableCommitRequest()
        returns (ss5 : SystemState)
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures WitnessStage(
        ss5,
        WitnessStateAfterCommitRequest(),
        WitnessMessagesAfterCommitRequest())
    {
        var leaderId := leader(1);
        var ss4 := LemmaReachablePreCommitVote();
        assert WitnessStage(
            ss4,
            WitnessStateAfterPreCommitVote(),
            WitnessMessagesAfterPreCommitVote());
        var r4 := ss4.nodeStates[leaderId];
        assert r4 == WitnessStateAfterPreCommitVote();

        var preCommitVote := WitnessPreCommitVote();
        var preCommitQC := WitnessPreCommitQC();
        var commitRequest := WitnessCommitRequest();
        LemmaSingleVoteFormsValidQC(preCommitVote);
        assert ValidCommitRequest(commitRequest);
        var received5 := r4.(
            msgReceived := r4.msgReceived + {preCommitVote});
        LemmaMoreReceivedMessagesPreserveReplicaValidity(
            r4, {preCommitVote});
        assert ValidReplicaState(received5);
        assert getMatchQC(
            received5.msgReceived,
            MT_Commit,
            MT_PreCommit,
            1) == {};
        assert getMatchVoteMsg(
            received5.msgReceived,
            MT_PreCommit,
            1) == {preCommitVote};
        LemmaSplitSingletonMessage(preCommitVote);
        LemmaMaxSingletonSet({preCommitVote});
        assert ExtractSignatrues({preCommitVote})
            == {preCommitVote.partialSig};
        assert !isVotedInView(received5.msgSent, MT_Commit, 1);
        var outMsg := {commitRequest};
        var r5 := received5.(msgSent := received5.msgSent + outMsg);
        assert UponCommit(received5, r5, outMsg);
        ss5 := SystemState(
            ss4.nodeStates[leaderId := r5],
            ss4.adversary,
            ss4.msgSent + outMsg);
        LemmaReachableHonestSingleSubStep(
            ss4, ss5, leaderId, {preCommitVote}, received5, r5, outMsg);
        assert r5 == WitnessStateAfterCommitRequest();
        assert ss5.msgSent == WitnessMessagesAfterCommitRequest();
        assert WitnessStage(
            ss5,
            WitnessStateAfterCommitRequest(),
            WitnessMessagesAfterCommitRequest());
    }

    lemma {:isolate_assertions} LemmaReachableCommitVote()
        returns (ss6 : SystemState)
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures WitnessStage(
        ss6,
        WitnessStateAfterCommitVote(),
        WitnessMessagesAfterCommitVote())
    {
        var leaderId := leader(1);
        var ss5 := LemmaReachableCommitRequest();
        assert WitnessStage(
            ss5,
            WitnessStateAfterCommitRequest(),
            WitnessMessagesAfterCommitRequest());
        var r5 := ss5.nodeStates[leaderId];
        assert r5 == WitnessStateAfterCommitRequest();

        var preCommitVote := WitnessPreCommitVote();
        var preCommitQC := WitnessPreCommitQC();
        var commitRequest := WitnessCommitRequest();
        var commitVote := WitnessCommitVote();
        LemmaSingleVoteFormsValidQC(preCommitVote);
        assert ValidCommitRequest(commitRequest);
        assert ValidCommitVote(commitVote);
        var received6 := r5.(
            msgReceived := r5.msgReceived + {commitRequest});
        LemmaMoreReceivedMessagesPreserveReplicaValidity(
            r5, {commitRequest});
        assert ValidReplicaState(received6);
        assert getMatchQC(
            received6.msgReceived,
            MT_Commit,
            MT_PreCommit,
            1) == {preCommitQC};
        assert getMatchVoteMsg(
            received6.msgReceived,
            MT_PreCommit,
            1) == {preCommitVote};
        LemmaSplitSingletonMessage(preCommitVote);
        LemmaMaxSingletonSet({preCommitVote});
        assert ExtractSignatrues({preCommitVote})
            == {preCommitVote.partialSig};
        assert !isVotedInView(received6.msgSent, MT_Commit, 1);
        var outMsg := {commitVote, commitRequest};
        var r6 := received6.(
            lockedQC := preCommitQC,
            msgSent := received6.msgSent + outMsg);
        assert UponCommit(received6, r6, outMsg);
        ss6 := SystemState(
            ss5.nodeStates[leaderId := r6],
            ss5.adversary,
            ss5.msgSent + outMsg);
        LemmaReachableHonestSingleSubStep(
            ss5, ss6, leaderId, {commitRequest}, received6, r6, outMsg);
        assert r6 == WitnessStateAfterCommitVote();
        assert ss6.msgSent == WitnessMessagesAfterCommitVote();
        assert WitnessStage(
            ss6,
            WitnessStateAfterCommitVote(),
            WitnessMessagesAfterCommitVote());
    }

    lemma {:isolate_assertions} LemmaReachableDecideMessageState()
        returns (ss7 : SystemState)
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures WitnessStage(
        ss7,
        WitnessStateAfterDecideMessage(),
        WitnessMessagesAfterDecideMessage())
    {
        var leaderId := leader(1);
        var ss6 := LemmaReachableCommitVote();
        assert WitnessStage(
            ss6,
            WitnessStateAfterCommitVote(),
            WitnessMessagesAfterCommitVote());
        var r6 := ss6.nodeStates[leaderId];
        assert r6 == WitnessStateAfterCommitVote();

        var commitVote := WitnessCommitVote();
        var commitQC := WitnessCommitQC();
        var decide := WitnessDecideMessage();
        LemmaSingleVoteFormsValidQC(commitVote);
        assert ValidDecideMsg(decide);
        var received7 := r6.(
            msgReceived := r6.msgReceived + {commitVote});
        LemmaMoreReceivedMessagesPreserveReplicaValidity(
            r6, {commitVote});
        assert ValidReplicaState(received7);
        assert getMatchQC(
            received7.msgReceived,
            MT_Decide,
            MT_Commit,
            1) == {};
        assert getMatchVoteMsg(
            received7.msgReceived,
            MT_Commit,
            1) == {commitVote};
        LemmaSplitSingletonMessage(commitVote);
        LemmaMaxSingletonSet({commitVote});
        assert ExtractSignatrues({commitVote}) == {commitVote.partialSig};
        var outMsg := {decide};
        var r7 := received7.(msgSent := received7.msgSent + outMsg);
        assert UponDecide(received7, r7, outMsg);
        ss7 := SystemState(
            ss6.nodeStates[leaderId := r7],
            ss6.adversary,
            ss6.msgSent + outMsg);
        LemmaReachableHonestSingleSubStep(
            ss6, ss7, leaderId, {commitVote}, received7, r7, outMsg);
        assert r7 == WitnessStateAfterDecideMessage();
        assert ss7.msgSent == WitnessMessagesAfterDecideMessage();
        assert WitnessStage(
            ss7,
            WitnessStateAfterDecideMessage(),
            WitnessMessagesAfterDecideMessage());
    }

    lemma LemmaReachableSingleNodeDecideMessage()
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures exists ss ::
        && Reachable(ss)
        && HasDecideMessage(ss)
    {
        var ss := LemmaReachableDecideMessageState();
        assert WitnessStage(
            ss,
            WitnessStateAfterDecideMessage(),
            WitnessMessagesAfterDecideMessage());
        assert WitnessDecideMessage() in ss.msgSent;
        assert ValidDecideMsg(WitnessDecideMessage());
        assert HasDecideMessage(ss);
    }

    lemma {:isolate_assertions} LemmaReachableHonestDecisionState()
        returns (ss8 : SystemState)
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures WitnessStage(
        ss8,
        WitnessStateAfterHonestDecision(),
        WitnessMessagesAfterDecideMessage())
    ensures HasHonestDecision(ss8)
    {
        var leaderId := leader(1);
        var ss7 := LemmaReachableDecideMessageState();
        assert WitnessStage(
            ss7,
            WitnessStateAfterDecideMessage(),
            WitnessMessagesAfterDecideMessage());
        var r7 := ss7.nodeStates[leaderId];
        assert r7 == WitnessStateAfterDecideMessage();

        var commitVote := WitnessCommitVote();
        var commitQC := WitnessCommitQC();
        var decide := WitnessDecideMessage();
        LemmaSingleVoteFormsValidQC(commitVote);
        assert ValidDecideMsg(decide);
        var received8 := r7.(
            msgReceived := r7.msgReceived + {decide});
        LemmaMoreReceivedMessagesPreserveReplicaValidity(r7, {decide});
        assert ValidReplicaState(received8);
        LemmaWitnessDecideMessageIsOnlyCommitQC();
        assert getMatchQC(
            received8.msgReceived,
            MT_Decide,
            MT_Commit,
            1) == {commitQC};
        assert getMatchVoteMsg(
            received8.msgReceived,
            MT_Commit,
            1) == {commitVote};
        LemmaSplitSingletonMessage(commitVote);
        LemmaMaxSingletonSet({commitVote});
        assert ExtractSignatrues({commitVote}) == {commitVote.partialSig};
        var ancestors := getAncestors(commitQC.block);
        assert commitQC.block == WitnessProposal().block;
        assert ancestors == [Genesis_Block, WitnessProposal().block];
        assert received8.bc == [Genesis_Block];
        assert received8.bc < ancestors;
        var outMsg := {decide};
        var r8 := received8.(
            bc := ancestors,
            msgSent := received8.msgSent + outMsg);
        LemmaWitnessUponDecideUpdatesBlockchain();
        assert UponDecide(received8, r8, outMsg);
        ss8 := SystemState(
            ss7.nodeStates[leaderId := r8],
            ss7.adversary,
            ss7.msgSent + outMsg);
        LemmaReachableHonestSingleSubStep(
            ss7, ss8, leaderId, {decide}, received8, r8, outMsg);
        assert r8 == WitnessStateAfterHonestDecision();
        assert ss8.msgSent == WitnessMessagesAfterDecideMessage();
        assert WitnessStage(
            ss8,
            WitnessStateAfterHonestDecision(),
            WitnessMessagesAfterDecideMessage());
        assert decide in ss8.nodeStates[leaderId].msgReceived;
        assert decide.justify.block in ss8.nodeStates[leaderId].bc;
        assert |ss8.nodeStates[leaderId].bc| > 1;
        assert HasHonestDecision(ss8);
    }

    lemma LemmaReachableSingleNodeHonestDecision()
    requires leader(1) in Honest_Nodes
    requires All_Nodes == {leader(1)}
    ensures exists ss ::
        && Reachable(ss)
        && HasHonestDecision(ss)
    {
        var ss := LemmaReachableHonestDecisionState();
    }
}
