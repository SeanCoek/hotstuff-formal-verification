include "Replica.dfy"
include "Type.dfy"
include "Auxilarily.dfy"
include "Axioms.dfy"
include "common/proofs.dfy"


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

    ghost predicate ValidReplicaNextSubSeq(s : seq<ReplicaState>, o : seq<set<Msg>>)
    {
        && |s| > 2
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
                && |s| > 2
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
                && |s| > 2
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
                && |s| > 2
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


    lemma LemmaValidationHoldsInPreparePhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPrepare(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
    }

    lemma LemmaVarStableInPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPreCommit(r, r', outMsg)
    ensures r'.viewNum == r.viewNum
    ensures r'.commitQC == r.commitQC
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


    lemma LemmaValidationHoldsInPreCommitPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponPreCommit(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        NoOuterClient();
        // var leader := leader(r.viewNum);
        // assert r'.viewNum > 0;
        // assert r'.prepareQC.Cert? ==>
        //                         && ValidQC(r'.prepareQC)
        //                         && r'.prepareQC.cType == MT_Prepare
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.prepareQC;
        // assert (r'.prepareQC.Cert? ==>
        //                         && ValidQC(r'.prepareQC)
        //                         && r'.prepareQC.cType == MT_Prepare
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.prepareQC
        //     ) by {
        //         if leader == r.id {
        //             if r'.prepareQC.Cert? {
        //                 assert ValidQC(r'.prepareQC);
        //                 // assert r'.prepareQC.cType == MT_Prepare;
        //                 // assert r'.msgReceived == r.msgReceived;
        //             }
        //         }
        //         else {
        //             if r'.prepareQC.Cert? {
        //                 assert ValidQC(r'.prepareQC);
        //             }
        //         }
        // }
        
        // assert (r'.commitQC.Cert? ==>
        //                         && ValidQC(r'.commitQC)
        //                         && r'.commitQC.cType == MT_PreCommit
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.commitQC
        //     );

        // assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
        //         || (exists m | && m in r'.msgReceived
        //                     && m.justify.Cert?
        //                     && m.justify.cType.MT_Commit?
        //                     && ValidQC(m.justify)
        //                     ::
        //                     r'.bc <= getAncestors(m.justify.block)
        //         )
        //  );

        // assert |r.bc| > 0;
        // assert r.bc[0] == M_SpecTypes.Genesis_Block;

        // assert forall m | m in r'.msgSent :: ValidMsg(m) by {
        //     NoOuterClient();
        // }
    }

    lemma LemmaValidationHoldsInCommitPhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponCommit(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        NoOuterClient();
        // var leader := leader(r.viewNum);
        // assert r'.viewNum > 0;
        // assert r'.prepareQC.Cert? ==>
        //                         && ValidQC(r'.prepareQC)
        //                         && r'.prepareQC.cType == MT_Prepare
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.prepareQC;
        // assert (r'.prepareQC.Cert? ==>
        //                         && ValidQC(r'.prepareQC)
        //                         && r'.prepareQC.cType == MT_Prepare
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.prepareQC
        //     ) by {
        //         if leader == r.id {
        //             if r'.prepareQC.Cert? {
        //                 assert ValidQC(r'.prepareQC);
        //                 // assert r'.prepareQC.cType == MT_Prepare;
        //                 // assert r'.msgReceived == r.msgReceived;
        //             }
        //         }
        //         else {
        //             if r'.prepareQC.Cert? {
        //                 assert ValidQC(r'.prepareQC);
        //             }
        //         }
        // }
        
        // assert (r'.commitQC.Cert? ==>
        //                         && ValidQC(r'.commitQC)
        //                         && r'.commitQC.cType == MT_PreCommit
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.commitQC
        //     );

        // assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
        //         || (exists m | && m in r'.msgReceived
        //                     && m.justify.Cert?
        //                     && m.justify.cType.MT_Commit?
        //                     && ValidQC(m.justify)
        //                     ::
        //                     r'.bc <= getAncestors(m.justify.block)
        //         )
        //  );

        // assert |r.bc| > 0;
        // assert r.bc[0] == M_SpecTypes.Genesis_Block;
        // assert forall m | m in r'.msgSent :: ValidMsg(m) by {
        //     NoOuterClient();
        // }
    }

    lemma LemmaValidationHoldsInDecidePhase(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    requires UponDecide(r, r', outMsg)
    ensures ValidReplicaState(r')
    {
        var leader := leader(r.viewNum);
        assert r'.viewNum > 0;
        // assert Inv_Blockchain_Inner_Consistency(r'.bc);
        assert && |r'.bc| > 0
               && r'.bc[0] == M_SpecTypes.Genesis_Block;
        
        // assert r'.prepareQC.Cert? ==>
        //                         && ValidQC(r'.prepareQC)
        //                         && r'.prepareQC.cType == MT_Prepare
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.prepareQC;
        // assert (r'.prepareQC.Cert? ==>
        //                         && ValidQC(r'.prepareQC)
        //                         && r'.prepareQC.cType == MT_Prepare
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.prepareQC
            // ) by {
            //     if leader == r.id {
            //         if r'.prepareQC.Cert? {
            //             assert ValidQC(r'.prepareQC);
            //             // assert r'.prepareQC.cType == MT_Prepare;
            //             // assert r'.msgReceived == r.msgReceived;
            //         }
            //     }
            //     else {
            //         if r'.prepareQC.Cert? {
            //             assert ValidQC(r'.prepareQC);
            //         }
            //     }
        // }
        
        // assert (r'.commitQC.Cert? ==>
        //                         && ValidQC(r'.commitQC)
        //                         && r'.commitQC.cType == MT_PreCommit
        //                         && exists m | m in r'.msgReceived
        //                                     ::
        //                                     && m.justify == r'.commitQC
        //     );

        assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
                || (exists m | && m in r'.msgReceived
                            // && m.mType.MT_Decide?
                            && m.justify.Cert?
                            && m.justify.cType.MT_Commit?
                            && ValidQC(m.justify)
                            // && m.justify.block.Block?
                            ::
                            r'.bc <= getAncestors(m.justify.block)
                )
         ) by {
            if leader != r.id {
                var matchMsgs := getMatchMsg(r.msgReceived, MT_Commit, r.viewNum);
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet := getMaxLengthSet(splitSets);

                var matchQCs := getMatchQC(r.msgReceived, MT_Decide, MT_Commit, r.viewNum);
                // assert |matchQCs| <= 1;
                assert r.msgReceived <= r'.msgReceived;
                if |matchQCs| > 0 {
                    // assert |matchQCs| == 1;
                    var m_qc :| m_qc in matchQCs;
                    var match_msg :| && match_msg in r.msgReceived
                                     && match_msg.justify == m_qc;
                    // assert matchQCs <= r'.msgReceived;
                    var ancestors := getAncestors(m_qc.block);
                    // if |ancestors| <= |r.bc| {
                    //     assert r' == r;
                    // }
                    assert (|| r'.bc == [M_SpecTypes.Genesis_Block]
                            || (exists m | && m in r'.msgReceived
                                        // && m.mType.MT_Decide?
                                        && m.justify.Cert?
                                        && m.justify.cType.MT_Commit?
                                        && ValidQC(m.justify)
                                        // && m.justify.block.Block?
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
                && |s| > 2
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