include "../specs/Replica.dfy"
include "../specs/Type.dfy"
include "../specs/Auxilarily.dfy"
include "Axioms.dfy"
include "../common/proofs.dfy"


/**
 @Module Name : M_Lemmas_Replica
 @Description : Lemmas for replica, such as proving state invariants, message relations during replica's transitions.
 */
module M_Lemmas_Replica {

    import opened M_Replica
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_ProofTactic
    import opened M_Set

    ghost predicate ValidReplicaNextSubSeq(s : seq<ReplicaState>, o : seq<set<Msg>>)
    {
        && |s| >= 2
        && |o| == |s| - 1
        && (forall i | 0 <= i < |s| - 1 ::
            && ValidReplicaState(s[i])
            && ReplicaNextSubStep(s[i], s[i+1], o[i])
        )
    }

    lemma LemmaReplicaMsgReceiveStableInNextSubSeq(s : seq<ReplicaState>, o : seq<set<Msg>>)
    requires ValidReplicaNextSubSeq(s, o)
    ensures forall i, j | && 0 <= i < |s|
                          && 0 <= j < |s|
                        ::
                          && s[i].msgReceived == s[j].msgReceived
    {
        var msgRecSeq := mapSeq(s, getMsgReceiveReplica);
        forall i, j | && 0 <= i < |s|
                      && 0 <= j < |s|
        ensures s[i].msgReceived == s[j].msgReceived {
            forall i | 0 <= i < |s|-1 
            ensures msgRecSeq[i] == msgRecSeq[i+1] {
                LemmaMsgRecRelationInReplicaNextSub(s[i], s[i+1], o[i]);
            }
            LemmaSetEqualityTransitiveInSeq(msgRecSeq);
        }
    }

    lemma LemmaReplicaStableIDInReplicaNextSub(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>
    )
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures r.id == r'.id
    {
    }

    lemma LemmaMsgRecRelationInReplicaNextSub(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures r'.msgReceived == r.msgReceived
    {

    }

    lemma LemmaMsgSentRelationInReplicaNextSub(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures r'.msgSent == r.msgSent + outMsg
    {
    }

    lemma LemmaInitReplicaIsValid(r : ReplicaState)
    requires ReplicaInit(r, r.id)
    ensures ValidReplicaState(r)
    {
        // assert r.commitQC.CertNone?;
        // assert r.prepareQC.CertNone?;
        assert r.bc == [M_SpecTypes.Genesis_Block];
        // assert r.msgSent == {};
    }

    lemma LemmaReplicaNextIsValid(r : ReplicaState, inMsg : set<Msg>, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNext(r, inMsg, r', outMsg)
    ensures ValidReplicaState(r')
    {
        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );
        var s : seq<ReplicaState>, o : seq<set<Msg>> :|
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o);
        assert ValidReplicaState(r') by {
            assert ValidReplicaState(s[|s|-2]);
            assert ReplicaNextSubStep(s[|s|-2], s[|s|-1], o[|s|-2]);
            LemmaReplicaNextSubIsValid(s[|s|-2], s[|s|-1], o[|s|-2]);
        }
    }

    lemma LemmaReplicaNextSubIsValid(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        
        if exists outMsg :: ReplicaNextSubStep(r, r', outMsg)
        {
            var outMsg :| ReplicaNextSubStep(r, r', outMsg);
            if UponPrepare(r, r', outMsg)
            {
                LemmaValidationHoldsInPreparePhase(r, r', outMsg);
            }
            else if UponPreCommit(r, r', outMsg)
            {
                LemmaValidationHoldsInPreCommitPhase(r, r', outMsg);
            }
            else if UponCommit(r, r', outMsg)
            {
                LemmaValidationHoldsInCommitPhase(r, r', outMsg);
            }
            else if UponDecide(r, r', outMsg)
            {
                LemmaValidationHoldsInDecidePhase(r, r', outMsg);
            }
            else
            {
                LemmaValidationHoldsInNewViewPhase(r, r', outMsg);
                // UponTimeOut are proved automatically by Dafny
            }
        }
    }

    lemma LemmaReplicaSendMsgWithOwnIDInReplicaNextSub(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>
    )
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures forall m | m in outMsg :: m.sender == r'.id
    {
    }


    lemma LemmaReplicaStableIDInSeqOfReplicaNextSub(
    s : seq<ReplicaState>,
    o : seq<set<Msg>>
    )
    requires |s| >= 2 && |o| == |s|-1
    requires forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
    ensures forall i, j | && 0 <= i < |s|
                          && 0 <= j < |s|
                        :: s[i].id == s[j].id
    {
        forall i, j | && 0 <= i < |s|
                      && 0 <= j < |s|
        ensures s[i].id == s[j].id {
            var idSeq := mapSeq(s, getReplicaID);
            forall i | 0 <= i < |s|-1 
            ensures idSeq[i] == idSeq[i+1] {
                LemmaReplicaStableIDInReplicaNextSub(s[i], s[i+1], o[i]);
            }
            LemmaEqualityTransitiveInSeq(idSeq);
        }
    }

    lemma LemmaMsgSentBySameReplicaInReplicaNext(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNext(r, inMsg, r', outMsg)
    ensures forall m | m in outMsg :: m.sender == r'.id
    {

        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );
        var s : seq<ReplicaState>, o : seq<set<Msg>> :|
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o);

        forall i, j | 0 <= i < |s| && 0 <= j < |s|
        ensures s[i].id == s[j].id
        {
            LemmaReplicaStableIDInSeqOfReplicaNextSub(s, o);
        }

        forall i | 0 <= i < |s| - 1
        ensures forall m | m in o[i] :: m.sender == r'.id
        {
            LemmaReplicaSendMsgWithOwnIDInReplicaNextSub(s[i], s[i+1], o[i]);
        }

    }

    lemma LemmaMsgRelationInReplicaNext(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNext(r, inMsg, r', outMsg)
    ensures r'.msgReceived == r.msgReceived + inMsg
    ensures r'.msgSent == r.msgSent + outMsg
    {
        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );
        var s : seq<ReplicaState>, o : seq<set<Msg>> :|
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o);

        var msgRecSeq := mapSeq(s, getMsgReceiveReplica);
        var msgSentSeq := mapSeq(s, getMsgSentReplica);
        assert s[|s|-1].msgReceived == s[0].msgReceived by {
            forall i | 0 <= i < |s|-1 
            ensures msgRecSeq[i] == msgRecSeq[i+1] {
                LemmaMsgRecRelationInReplicaNextSub(s[i], s[i+1], o[i]);
            }
            LemmaSetEqualityTransitiveInSeq(msgRecSeq);
        }

        assert s[|s|-1].msgSent == s[0].msgSent + outMsg by {
            forall i | 0 < i < |s|
            ensures msgSentSeq[i] == msgSentSeq[i-1] + o[i-1] {
                LemmaMsgSentRelationInReplicaNextSub(s[i-1], s[i], o[i-1]);
            }
            LemmaSeqCumulative(msgSentSeq, o);
        }

    }

    lemma LemmaReplicaNextSubStepHoldsMsgSubsetRelation(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures r.msgReceived <= r'.msgReceived
    ensures r'.msgReceived - r.msgReceived <= outMsg
    ensures r'.msgSent == r.msgSent + outMsg
    {}

    lemma LemmaValidationHoldForReplicaTransition(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires (|| UponNextView(r, r', outMsg)
              || UponTimeOut(r, r', outMsg)
              || UponPrepare(r, r', outMsg)
              || UponPreCommit(r, r', outMsg)
              || UponCommit(r, r', outMsg)
              || UponDecide(r, r', outMsg)
              ) 
    ensures ValidReplicaState(r')
    {
        LemmaReplicaNextSubIsValid(r, r', outMsg);
    }

    lemma LemmaAtMostOneValidVoteAfterAddingNonVote(
        votes : set<Msg>,
        nonVote : Msg)
    requires |votes| == 0 || |votes| == 1
    requires !ValidVoteMsg(nonVote)
    ensures forall m1, m2 |
                && m1 in votes + {nonVote}
                && m2 in votes + {nonVote}
                && ValidVoteMsg(m1)
                && ValidVoteMsg(m2)
            :: m1 == m2
    {
        LemmaSetAtMostOneElementHasUniqueElements(votes);
        forall m1, m2 |
            && m1 in votes + {nonVote}
            && m2 in votes + {nonVote}
            && ValidVoteMsg(m1)
            && ValidVoteMsg(m2)
        ensures m1 == m2
        {
            assert m1 != nonVote;
            assert m2 != nonVote;
            assert m1 in votes;
            assert m2 in votes;
        }
    }

    lemma LemmaPrepareOutputVoteShape(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures forall m | m in outMsg && ValidVoteMsg(m) ::
                && ValidPrepareVote(m)
                && m.viewNum == r.viewNum
    {
    }

    lemma LemmaPrepareOutputContainsAtMostOneVote(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures forall m1, m2 |
                && m1 in outMsg
                && m2 in outMsg
                && ValidVoteMsg(m1)
                && ValidVoteMsg(m2)
            :: m1 == m2
    {
        var isVoted := isVotedInView(r.msgSent, MT_Prepare, r.viewNum);
        var matchProposals := getMatchProposalMsg(r.msgReceived, r.viewNum);
        var candidateVotes := getVotesForSafeProposals(matchProposals, r.lockedQC, r.id);
        var validVotes := proposalVoteFilter(candidateVotes);
        var oneVote := onlyOneVote(validVotes);
        var finalVotes := getVotesIfUnVoted(oneVote, isVoted);

        LemmaSubsetCardinality(finalVotes, oneVote);
        assert |finalVotes| == 0 || |finalVotes| == 1;
        LemmaSetAtMostOneElementHasUniqueElements(finalVotes);

        if leader(r.viewNum) == r.id {
            var matchMsgs := getMatchMsg(r.msgReceived, MT_NewView, r.viewNum-1);
            if |matchMsgs| >= quorum(|M_SpecTypes.All_Nodes|) {
                var highQC := getHighQC(matchMsgs);
                var proposal := getNewBlock(highQC.block);
                var proposeMsg := Msg(r.id, MT_Prepare, r.viewNum, proposal, highQC, SigNone, CertNone);
                assert !ValidVoteMsg(proposeMsg);
                LemmaAtMostOneValidVoteAfterAddingNonVote(finalVotes, proposeMsg);
            }
        }
    }

    lemma LemmaPrepareOutputContainsNoVoteAfterVoting(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    requires isVotedInView(r.msgSent, MT_Prepare, r.viewNum)
    ensures forall m | m in outMsg :: !ValidVoteMsg(m)
    {
    }

    lemma LemmaPrepareOutputPreservesVoteUniqueness(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures forall m1, m2 |
                && m1 in r'.msgSent
                && m2 in r'.msgSent
                && ValidVoteMsg(m1)
                && ValidVoteMsg(m2)
                && m1.viewNum == m2.viewNum
                && m1.mType == m2.mType
            :: m1 == m2
    {
        LemmaPrepareOutputVoteShape(r, r', outMsg);
        LemmaPrepareOutputContainsAtMostOneVote(r, r', outMsg);
        if isVotedInView(r.msgSent, MT_Prepare, r.viewNum) {
            LemmaPrepareOutputContainsNoVoteAfterVoting(r, r', outMsg);
        }
    }

    lemma LemmaPrepareOutputHasProposalProvenance(
        r : ReplicaState,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures forall m | m in r'.msgSent && ValidPrepareVote(m) ::
                exists proposal | proposal in r'.msgReceived ::
                    && ValidProposal(proposal)
                    && corrVoteMsgAndToVotedMsg(m, proposal)
                    && ValidQC(m.lockedQC)
                    && safeNode(m.block, proposal.justify, m.lockedQC)
    {
    }

    lemma LemmaValidationHoldsInPreparePhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        LemmaPrepareOutputPreservesVoteUniqueness(r, r', outMsg);
        LemmaPrepareOutputHasProposalProvenance(r, r', outMsg);
        assert Inv_Votes(r');
    }

    lemma LemmaVarStableInPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPreCommit(r, r', outMsg)
    ensures r'.viewNum == r.viewNum
    ensures r'.lockedQC == r.lockedQC
    ensures r'.bc == r.bc
    ensures r'.id == r.id
    ensures r'.msgReceived == r.msgReceived
    {

    }

    lemma LemmaVarStableInCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponCommit(r, r', outMsg)
    ensures r'.viewNum == r.viewNum
    ensures r'.prepareQC == r.prepareQC
    ensures r'.bc == r.bc
    ensures r'.id == r.id
    ensures r'.msgReceived == r.msgReceived
    {
        assert r'.viewNum == r.viewNum;
        assert r'.prepareQC == r.prepareQC;
        assert r'.bc == r.bc;
        assert r'.id == r.id;
        assert r'.msgReceived == r.msgReceived;
    }

    lemma LemmaVarStableInDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponDecide(r, r', outMsg)
    ensures r'.viewNum == r.viewNum
    ensures r'.prepareQC == r.prepareQC
    ensures r'.lockedQC == r.lockedQC
    ensures r'.id == r.id
    ensures r'.msgReceived == r.msgReceived
    {}

    lemma LemmaOnlySendDecideRequestMsgInDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponDecide(r, r', outMsg)
    ensures outMsg != {} ==> forall m | m in outMsg :: ValidDecideMsg(m)
    {}


    lemma LemmaValidationHoldsInPreCommitPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPreCommit(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        NoOuterClient();
    }

    lemma LemmaValidationHoldsInCommitPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponCommit(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        NoOuterClient();
    }

    lemma LemmaValidationHoldsInDecidePhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponDecide(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        var leader := leader(r.viewNum);
        LemmaVarStableInDecide(r, r', outMsg);
        assert r'.viewNum > 0;
        assert ValidQC(r'.prepareQC);
        assert ValidQC(r'.lockedQC);
        assert r'.viewNum >= r'.prepareQC.viewNum;
        assert r'.viewNum >= r'.lockedQC.viewNum;
        assert && |r'.bc| > 0
               && r'.bc[0] == M_SpecTypes.Genesis_Block;
        
        assert (r'.prepareQC.Cert? ==>
                                    && ValidQC(r'.prepareQC)
                                    && r'.prepareQC.cType == MT_Prepare
                                    && (
                                        || (exists m | m in r'.msgReceived
                                                    ::
                                                      && m.justify == r'.prepareQC
                                                      && ValidPrecommitRequest(m)
                                            )
                                        || isInitialQC(r'.prepareQC)
                                    )
                );
        assert (r'.lockedQC.Cert? ==>
                                    && ValidQC(r'.lockedQC)
                                    && r'.lockedQC.cType == MT_PreCommit
                                    && (
                                        || (exists m | m in r'.msgReceived
                                                    ::
                                                      && m.justify == r'.lockedQC
                                                      && ValidCommitRequest(m)
                                            )
                                        || isInitialQC(r'.lockedQC)
                                    )
                );
        

        assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
                || (exists m | && m in r'.msgReceived
                               && ValidDecideMsg(m)
                            ::
                               r'.bc <= getAncestors(m.justify.block)
                )
         ) by {
            if leader != r.id {
                var matchMsgs := getMatchMsg(r.msgReceived, MT_Commit, r.viewNum);
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet := getMaxLengthSet(splitSets);

                var matchQCs := getMatchQC(r.msgReceived, MT_Decide, MT_Commit, r.viewNum);
                assert r.msgReceived <= r'.msgReceived;
                if |matchQCs| > 0 {
                    // assert |matchQCs| == 1;
                    var m_qc :| m_qc in matchQCs;
                    var match_msg :| && match_msg in r.msgReceived
                                     && match_msg.justify == m_qc;
                    var ancestors := getAncestors(m_qc.block);
                    assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
                            || (exists m | && m in r'.msgReceived
                                           && ValidDecideMsg(m)
                                        ::
                                           r'.bc <= getAncestors(m.justify.block)
                                )
                            );
                } else {
                    assert r' == r;
                }
            } else {

            }
        }
        
        assert |r'.bc| > 0;
        assert r'.bc[0] == M_SpecTypes.Genesis_Block;
        assert r'.msgSent == r.msgSent + outMsg;
        LemmaOnlySendDecideRequestMsgInDecide(r, r', outMsg);
        assert (forall m | m in r'.msgSent
                        ::
                           !(ValidDecideMsg(m))
                           ==>
                           m in r.msgSent);
    }


    lemma LemmaValidationHoldsInNewViewPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponNextView(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        NoOuterClient();
        assert && (forall m | m in r'.msgSent :: ValidMsg(m));
    }

    lemma LemmaReplicaVoteCommitOnlyWhenReceiveValidPrecommitQC(r : ReplicaState,
                                                                r' : ReplicaState,
                                                                outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures forall m |  && m in outMsg 
                        && ValidCommitVote(m)
                    :: 
                        && UponCommit(r, r', outMsg)
                        && (exists m2 | m2 in r'.msgReceived
                                     :: 
                                        && ValidQC(m2.justify)
                                        && m2.justify.cType.MT_PreCommit?
                                        && m2.justify.block == m.partialSig.block
                                        && m2.justify.viewNum == m.partialSig.viewNum)
    {

    }

    lemma LemmaReplicaStableIDInReplicaNext(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires ReplicaNext(r, inMsg, r', outMsg)
    ensures r.id == r'.id
    {
        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );
        var s : seq<ReplicaState>, o : seq<set<Msg>> :|
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o);

        forall i, j | 0 <= i < |s| && 0 <= j < |s|
        ensures s[i].id == s[j].id
        {
            LemmaReplicaStableIDInSeqOfReplicaNextSub(s, o);
        }
    }

    lemma LemmaPrepareVoteOnlyExistInPreparePhase(
    r : ReplicaState,
    inMsg : set<Msg>,
    r' : ReplicaState,
    outMsg : set<Msg>
    )
    requires ValidReplicaState(r)
    requires ReplicaNextSubStep(r, r', outMsg)
    ensures forall m | && m in outMsg 
                    ::
                       && m.partialSig.Signature?
                       && m.mType == MT_Prepare
                       ==>
                       UponPrepare(r, r', outMsg)
    {

    }
}
