include "../specs/Type.dfy"
include "../specs/Auxilarily.dfy"
include "../specs/System.dfy"
include "../specs/Trace.dfy"
include "../specs/Replica.dfy"
include "Axioms.dfy"
include "../common/sets.dfy"
include "Lemmas_Replica.dfy"
include "Lemmas_System.dfy"


/**
 @Module Name : M_Lemmas
 @Description : Lemmas for proving properties of reachable system states, such as proving a valid QC is formed only if sufficient votes exist.
 */
module M_Lemma {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_System
    import opened M_Trace
    import opened M_Replica
    import opened M_Axiom
    import opened M_Set
    import opened M_Lemmas_Replica
    import opened M_Lemmas_System

    lemma LemmaExtensionTransitive(child : Block, middle : Block, parent : Block)
    requires child.Block? && middle.Block? && parent.Block?
    requires extension(child, middle)
    requires extension(middle, parent)
    ensures extension(child, parent)
    {
    }

    predicate BadPrepareHolder(ss : SystemState, commitQC : Cert, m : Msg)
    requires ValidQC(commitQC)
    {
        && m in ss.msgSent
        && ValidQC(m.justify)
        && m.justify.cType.MT_Prepare?
        && commitQC.viewNum <= m.justify.viewNum
        && !extension(m.justify.block, commitQC.block)
    }

    predicate QCHeldInSystem(ss : SystemState, qc : Cert)
    {
        exists holder | holder in ss.msgSent ::
            holder.justify == qc
    }

    /* If an honest replica send out a vote message,
       then this message should be found in its output buffer (msgSent).
       The reason we can conclude this is that we assume signatures cannot
       be forged by byzantine nodes.
       */
    lemma LemmaExistVoteMsgForSignature(
        ss : SystemState,
        holder : Msg,
        qc : Cert,
        sig : Signature)
    requires Reachable(ss)
    requires ValidQC(qc)
    requires !TrustedInitialQC(qc)
    requires holder in ss.msgSent
    requires QCOccursInMessage(holder, qc)
    requires sig in qc.signatures
    requires IsHonest(ss, sig.signer)
    ensures exists vote | vote in ss.nodeStates[sig.signer].msgSent ::
        && ValidVoteMsg(vote)
        && vote.partialSig == sig
        && corrVoteMsg(sig, vote)
    {
        LemmaReachableStateIsValid(ss);
        assert MessageQCsHaveVoteEvidence(
            ss.msgSent,
            ss.adversary.byz_nodes,
            holder);
        assert CertificateHasVoteEvidence(
            ss.msgSent,
            ss.adversary.byz_nodes,
            qc);
        assert sig.signer !in ss.adversary.byz_nodes;
        assert SignatureHasVoteEvidence(ss.msgSent, sig);
        var vote :| && vote in ss.msgSent
                    && ValidVoteMsg(vote)
                    && vote.partialSig == sig;
        assert vote.sender == sig.signer;
        assert IsHonest(ss, vote.sender);
        assert vote in ss.nodeStates[vote.sender].msgSent;
    }

    lemma LemmaHeldCommitQCViewPositive(
        ss : SystemState,
        holder : Msg,
        qc : Cert)
    requires Reachable(ss)
    requires holder in ss.msgSent
    requires holder.justify == qc
    requires ValidQC(qc) && qc.cType.MT_Commit?
    ensures qc.viewNum > 0
    {
        assert !TrustedInitialQC(qc);
        LemmaExistHonestSignerInValidQC(ss, qc);
        var sig :| && sig in qc.signatures
                    && IsHonest(ss, sig.signer);
        LemmaExistVoteMsgForSignature(ss, holder, qc, sig);
        var vote :| && vote in ss.nodeStates[sig.signer].msgSent
                    && ValidVoteMsg(vote)
                    && vote.partialSig == sig
                    && corrVoteMsg(sig, vote);
        LemmaReachableStateIsValid(ss);
        assert ValidReplicaState(ss.nodeStates[sig.signer]);
        assert vote.viewNum > 0;
        assert vote.viewNum == qc.viewNum;
    }
    
    lemma LemmaHonestNodeOnlyVoteOnceInOneView(
                                                ss : SystemState,
                                                r : Address
                                                )
    requires Reachable(ss)
    requires IsHonest(ss, r)
    ensures forall v1, v2 | && v1 in ss.nodeStates[r].msgSent
                            && v2 in ss.nodeStates[r].msgSent
                            && ValidVoteMsg(v1)
                            && ValidVoteMsg(v2)
                          ::
                            && v1.mType == v2.mType
                            && v1.viewNum == v2.viewNum
                            ==>
                            v1 == v2
    {
        LemmaReachableStateIsValid(ss);
    }

    lemma LemmaExistVoteMsgIfCertificateFormed(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && !TrustedInitialQC(m.justify)
                          ::
                             && (forall s : Signature | && s in m.justify.signatures
                                                        && s.Signature?
                                                        && IsHonest(ss, s.signer)
                                                     ::
                                                        && (exists m1 : Msg | && m1 in ss.msgSent
                                                                          ::
                                                                             corrVoteMsg(s, m1)
                                                            )
                                )
    {
        forall m | && m in ss.msgSent
                   && ValidQC(m.justify)
                   && !TrustedInitialQC(m.justify)
        ensures (forall s : Signature | && s in m.justify.signatures
                                        && s.Signature?
                                        && IsHonest(ss, s.signer)
                                     ::
                                        && (exists m1 : Msg | && m1 in ss.msgSent
                                                            ::
                                                              corrVoteMsg(s, m1)
                                            )
                                ) 
        {
            forall s : Signature | && s in m.justify.signatures
                                   && s.Signature?
                                   && IsHonest(ss, s.signer)
            ensures (exists m1 : Msg | && m1 in ss.msgSent
                                    ::
                                      corrVoteMsg(s, m1)
                    )
            {
                LemmaReachableStateIsValid(ss);
                LemmaExistVoteMsgForSignature(ss, m, m.justify, s);
            }
        }
    }


    lemma LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss : SystemState)
    requires Reachable(ss)
    ensures forall r, msgs | && IsHonest(ss, r)
                             && msgs == ss.nodeStates[r].msgReceived
                          ::
                             && msgs <= ss.msgSent
    {
        LemmaReachableStateIsValid(ss);
    }


    lemma LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_PreCommit
                             && !TrustedInitialQC(m.justify)
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                 && ValidQC(m2.justify)
                                                 && m2.justify.cType == MT_Prepare
                                                 && correspondingQC(m.justify, m2.justify)
                            )
    {
        forall m : Msg | && m in ss.msgSent
                                && ValidQC(m.justify)
                                && m.justify.cType == MT_PreCommit
                                && !TrustedInitialQC(m.justify)
        ensures (exists m2 : Msg :: && m2 in ss.msgSent
                                    && ValidQC(m2.justify)
                                    && m2.justify.cType == MT_Prepare
                                    && correspondingQC(m.justify, m2.justify)
                            )
        {
            var sgns := m.justify.signatures;
            var signers := set sig | sig in sgns :: sig.signer;
            LemmaExistHonestSignerInValidQC(ss, m.justify);
            LemmaReachableStateIsValid(ss);
            var sign_honest :| && sign_honest in sgns
                              && IsHonest(ss, sign_honest.signer);
            LemmaExistVoteMsgForSignature(ss, m, m.justify, sign_honest);
            var corrVote :| && corrVote in ss.nodeStates[sign_honest.signer].msgSent
                            && ValidVoteMsg(corrVote)
                            && corrVoteMsg(sign_honest, corrVote);
            assert ValidPrecommitVote(corrVote);
            HonestReplicaVotePrecommitOnlyWhenItReceivePrepareQC(ss, sign_honest.signer);
        }
    }

    lemma LemmaExistValidPrecommitQCForEveryValidCommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                    && ValidQC(m2.justify)
                                                    && m2.justify.cType == MT_PreCommit
                                                    && correspondingQC(m.justify, m2.justify)
                            )
    {
        forall m : Msg | && m in ss.msgSent
                                && ValidQC(m.justify)
                                && m.justify.cType == MT_Commit
        ensures (exists m2 : Msg :: && m2 in ss.msgSent
                                    && ValidQC(m2.justify)
                                    && m2.justify.cType == MT_PreCommit
                                    && correspondingQC(m.justify, m2.justify)
                            )
        {
            var sgns := m.justify.signatures;
            var signers := set sig | sig in sgns :: sig.signer;
            LemmaExistHonestSignerInValidQC(ss, m.justify);
            LemmaReachableStateIsValid(ss);
            var sign_honest :| && sign_honest in sgns
                              && IsHonest(ss, sign_honest.signer);
            LemmaExistVoteMsgForSignature(ss, m, m.justify, sign_honest);
            var corrVote :| && corrVote in ss.nodeStates[sign_honest.signer].msgSent
                            && ValidVoteMsg(corrVote)
                            && corrVoteMsg(sign_honest, corrVote);
            assert ValidCommitVote(corrVote);
            HonestReplicaVoteCommitOnlyWhenItReceivePrecommitQC(ss, sign_honest.signer);
        }
    }


    lemma LemmaExistValidPrepareQCForEveryValidCommitQC(ss : SystemState)
    requires Reachable(ss)
    ensures forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
                          ::
                             && (exists m2 : Msg :: && m2 in ss.msgSent
                                                    && ValidQC(m2.justify)
                                                    && m2.justify.cType == MT_Prepare
                                                    && correspondingQC(m.justify, m2.justify))
    {
        LemmaExistValidPrecommitQCForEveryValidCommitQC(ss);
        LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss);
        forall m : Msg | && m in ss.msgSent
                             && ValidQC(m.justify)
                             && m.justify.cType == MT_Commit
        ensures exists m2 : Msg :: && m2 in ss.msgSent
                                  && ValidQC(m2.justify)
                                  && m2.justify.cType == MT_Prepare
                                  && correspondingQC(m.justify, m2.justify)
        {
            LemmaHeldCommitQCViewPositive(ss, m, m.justify);
            var precommitHolder :| && precommitHolder in ss.msgSent
                                   && ValidQC(precommitHolder.justify)
                                   && precommitHolder.justify.cType == MT_PreCommit
                                   && correspondingQC(m.justify, precommitHolder.justify);
            assert precommitHolder.justify.viewNum > 0;
            assert !TrustedInitialQC(precommitHolder.justify);
        }
    }


    /**
        Every Prepare QC at or after a Commit QC extends the committed block.
        The strict-view case is proved by choosing the earliest conflicting
        Prepare QC and unfolding the two branches of safeNode.
     */
    lemma {:isolate_assertions} LemmaPrepareQCAfterCommitExtends(
        ss : SystemState,
        qc_commit : Cert,
        qc_prepare : Cert)
    requires Reachable(ss)
    requires ValidQC(qc_commit) && qc_commit.cType.MT_Commit?
    requires ValidQC(qc_prepare) && qc_prepare.cType.MT_Prepare?
    requires QCHeldInSystem(ss, qc_commit)
    requires QCHeldInSystem(ss, qc_prepare)
    requires qc_prepare.viewNum >= qc_commit.viewNum
    ensures extension(qc_prepare.block, qc_commit.block)
    {
        LemmaReachableStateIsValid(ss);
        var commitHolder :| && commitHolder in ss.msgSent
                            && commitHolder.justify == qc_commit;
        var prepareHolder :| && prepareHolder in ss.msgSent
                             && prepareHolder.justify == qc_prepare;
        LemmaHeldCommitQCViewPositive(ss, commitHolder, qc_commit);
        LemmaExistValidPrepareQCForEveryValidCommitQC(ss);

        if qc_prepare.viewNum == qc_commit.viewNum {
            var commitPrepareHolder :| && commitPrepareHolder in ss.msgSent
                                       && ValidQC(commitPrepareHolder.justify)
                                       && commitPrepareHolder.justify.cType.MT_Prepare?
                                       && correspondingQC(qc_commit, commitPrepareHolder.justify);
            LemmaSameValidQCInSameView(
                ss,
                prepareHolder,
                commitPrepareHolder,
                qc_prepare,
                commitPrepareHolder.justify);
            assert commitPrepareHolder.justify.block == qc_commit.block;
            assert qc_prepare.block == commitPrepareHolder.justify.block;
        } else if !extension(qc_prepare.block, qc_commit.block) {
            var badMessages := set m | m in ss.msgSent
                                         && BadPrepareHolder(ss, qc_commit, m) :: m;
            assert prepareHolder in badMessages;
            assert badMessages != {};
            assert forall m | m in badMessages :: m.justify.Cert?;
            var firstBad := argminView(badMessages);
            var badQC := firstBad.justify;
            assert BadPrepareHolder(ss, qc_commit, firstBad);
            assert ValidQC(badQC) && badQC.cType.MT_Prepare?;
            assert qc_commit.viewNum <= badQC.viewNum;
            assert badQC.viewNum <= qc_prepare.viewNum;

            if badQC.viewNum == qc_commit.viewNum {
                var commitPrepareHolder :| && commitPrepareHolder in ss.msgSent
                                           && ValidQC(commitPrepareHolder.justify)
                                           && commitPrepareHolder.justify.cType.MT_Prepare?
                                           && correspondingQC(qc_commit, commitPrepareHolder.justify);
                assert firstBad.justify == badQC;
                LemmaSameValidQCInSameView(
                    ss,
                    firstBad,
                    commitPrepareHolder,
                    badQC,
                    commitPrepareHolder.justify);
                assert badQC.block == commitPrepareHolder.justify.block;
                assert commitPrepareHolder.justify.block == qc_commit.block;
                assert extension(badQC.block, qc_commit.block);
                assert false;
            } else {
                LemmaExistSameHonestNodeInTwoValidQC(ss, qc_commit, badQC);
                var commonReplica :| && IsHonest(ss, commonReplica)
                                      && commonReplica in getMajoritySignerInValidQC(qc_commit)
                                      && commonReplica in getMajoritySignerInValidQC(badQC);
                var rState := ss.nodeStates[commonReplica];
                assert ValidReplicaState(rState);

                LemmaExistSignIfSignerInQCSigners(qc_commit);
                LemmaExistSignIfSignerInQCSigners(badQC);
                var commitSig :| && commitSig in qc_commit.signatures
                                  && commitSig.signer == commonReplica;
                var prepareSig :| && prepareSig in badQC.signatures
                                   && prepareSig.signer == commonReplica;
                assert !TrustedInitialQC(qc_commit);
                assert !TrustedInitialQC(badQC);
                LemmaExistVoteMsgForSignature(
                    ss, commitHolder, qc_commit, commitSig);
                LemmaExistVoteMsgForSignature(
                    ss, firstBad, badQC, prepareSig);
                var commitVote :| && commitVote in rState.msgSent
                                   && ValidVoteMsg(commitVote)
                                   && corrVoteMsg(commitSig, commitVote);
                var prepareVote :| && prepareVote in rState.msgSent
                                    && ValidVoteMsg(prepareVote)
                                    && corrVoteMsg(prepareSig, prepareVote);

                assert ValidCommitVote(commitVote);
                assert ValidPrepareVote(prepareVote);
                assert commitVote.viewNum == qc_commit.viewNum;
                assert commitVote.block == qc_commit.block;
                assert prepareVote.viewNum == badQC.viewNum;
                assert prepareVote.block == badQC.block;
                assert commitVote.viewNum < prepareVote.viewNum;
                assert PrepareVoteEvidence(rState, prepareVote);
                assert commitVote.viewNum <= prepareVote.lockedQC.viewNum;
                assert prepareVote.lockedQC.viewNum < prepareVote.viewNum;

                var proposal :| && proposal in rState.msgReceived
                                && ValidProposal(proposal)
                                && corrVoteMsgAndToVotedMsg(prepareVote, proposal)
                                && extension(proposal.block, proposal.justify.block)
                                && safeNode(prepareVote.block, proposal.justify, prepareVote.lockedQC);
                assert proposal.block == prepareVote.block;
                assert proposal.viewNum == prepareVote.viewNum;
                assert proposal in ss.msgSent;

                assert commitVote.viewNum > 0;
                assert prepareVote.lockedQC.viewNum > 0;
                assert !TrustedInitialQC(prepareVote.lockedQC);
                assert LockedQCEvidence(rState.msgReceived, prepareVote.lockedQC);
                var lockHolder :| && lockHolder in rState.msgReceived
                                  && ValidCommitRequest(lockHolder)
                                  && lockHolder.justify == prepareVote.lockedQC;
                assert lockHolder in ss.msgSent;
                LemmaExistValidPrepareQCForEveryValidPrecommitQC(ss);
                var lockPrepareHolder :| && lockPrepareHolder in ss.msgSent
                                         && ValidQC(lockPrepareHolder.justify)
                                         && lockPrepareHolder.justify.cType.MT_Prepare?
                                         && correspondingQC(prepareVote.lockedQC, lockPrepareHolder.justify);
                var lockPrepareQC := lockPrepareHolder.justify;
                assert qc_commit.viewNum <= lockPrepareQC.viewNum;
                assert lockPrepareQC.viewNum < badQC.viewNum;
                assert extension(lockPrepareQC.block, qc_commit.block) by {
                    if !extension(lockPrepareQC.block, qc_commit.block) {
                        assert BadPrepareHolder(ss, qc_commit, lockPrepareHolder);
                        assert lockPrepareHolder in badMessages;
                        assert firstBad.justify.viewNum <= lockPrepareHolder.justify.viewNum;
                        assert false;
                    }
                }

                if extension(prepareVote.block, prepareVote.lockedQC.block) {
                    assert lockPrepareQC.block == prepareVote.lockedQC.block;
                    LemmaExtensionTransitive(prepareVote.block, lockPrepareQC.block, qc_commit.block);
                    assert extension(badQC.block, qc_commit.block);
                    assert false;
                } else {
                    assert proposal.justify.viewNum > prepareVote.lockedQC.viewNum;
                    assert qc_commit.viewNum <= proposal.justify.viewNum;
                    assert proposal.justify.viewNum < badQC.viewNum;
                    assert extension(proposal.justify.block, qc_commit.block) by {
                        if !extension(proposal.justify.block, qc_commit.block) {
                            assert BadPrepareHolder(ss, qc_commit, proposal);
                            assert proposal in badMessages;
                            assert firstBad.justify.viewNum <= proposal.justify.viewNum;
                            assert false;
                        }
                    }
                    LemmaExtensionTransitive(proposal.block, proposal.justify.block, qc_commit.block);
                    assert extension(badQC.block, qc_commit.block);
                    assert false;
                }
            }
        }
    }

    lemma LemmaHonestNodeWontVoteConflictInPrepare(
        ss : SystemState,
        r : Address,
        qc1_commit : Cert,
        qc2_prepare : Cert)
    requires Reachable(ss)
    requires IsHonest(ss, r)
    requires ValidQC(qc1_commit) && qc1_commit.cType.MT_Commit?
    requires ValidQC(qc2_prepare) && qc2_prepare.cType.MT_Prepare?
    requires QCHeldInSystem(ss, qc1_commit)
    requires QCHeldInSystem(ss, qc2_prepare)
    requires predNodeInTwoQC(qc1_commit, qc2_prepare, r)
    requires qc2_prepare.viewNum >= qc1_commit.viewNum
    ensures extension(qc2_prepare.block, qc1_commit.block)
    {
        LemmaPrepareQCAfterCommitExtends(ss, qc1_commit, qc2_prepare);
    }

    lemma LemmaExistSignIfSignerInQCSigners(qc : Cert)
    requires ValidQC(qc)
    ensures forall r | r in getMajoritySignerInValidQC(qc)
                    ::
                      exists sig :: && sig in qc.signatures
                                    && sig.signer == r
    {

    }

    lemma LemmaReachableStateIsValid(ss : SystemState)
    requires Reachable(ss)
    ensures ValidSystemState(ss)
    {
        if !SystemInit(ss) {
            var run : seq<SystemState> :|
                                            && |run| > 1
                                            && SystemInit(run[0])
                                            && run[|run|-1] == ss
                                            && (forall i | 0 <= i < |run|-1
                                                        :: 
                                                           && ValidSystemState(run[i])
                                                           && SystemNext(run[i], run[i+1]));
            forall i | 0 < i <= |run|-1
            ensures ValidSystemState(run[i]) {
                LemmaSystemTransitionHoldsValidity(run[i-1], run[i]);
            }
        } else {

        }
    }


    lemma HonestReplicaVoteCommitOnlyWhenItReceivePrecommitQC(ss : SystemState, r : Address)
    requires Reachable(ss)
    requires IsHonest(ss, r)
    ensures forall m | && m in ss.nodeStates[r].msgSent
                       && ValidCommitVote(m)
                    :: 
                       exists m2 | m2 in ss.nodeStates[r].msgReceived
                                ::
                                   && ValidCommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2)
    {
        LemmaReachableStateIsValid(ss);
    }

    lemma HonestReplicaVotePrecommitOnlyWhenItReceivePrepareQC(ss : SystemState, r : Address)
    requires Reachable(ss)
    requires IsHonest(ss, r)
    ensures forall m | && m in ss.nodeStates[r].msgSent
                       && ValidPrecommitVote(m)
                    :: 
                       exists m2 | m2 in ss.nodeStates[r].msgReceived
                                ::
                                   && ValidPrecommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2)
    {
        LemmaReachableStateIsValid(ss);
    }

    lemma LemmaCommitQCVoteOnlyExistCorrespondingPrecommitQC(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>
    )
    requires ValidReplicaState(r)
    requires ReplicaNext(r, inMsg, r', outMsg)
    ensures forall m | && m in outMsg
                       && ValidCommitVote(m)
                    :: 
                       exists m2 | m2 in r'.msgReceived
                                :: 
                                   && ValidQC(m2.justify)
                                   && m2.justify.cType.MT_PreCommit?
                                   && m2.justify.block == m.partialSig.block
                                   && m2.justify.viewNum == m.partialSig.viewNum
    {
        forall m | && m in outMsg
                   && ValidCommitVote(m)
        ensures exists m2 | m2 in r'.msgReceived
                         :: 
                            && ValidQC(m2.justify)
                            && m2.justify.cType.MT_PreCommit?
                            && m2.justify.block == m.partialSig.block
                            && m2.justify.viewNum == m.partialSig.viewNum
        {
            var replicaWithNewMsgReceived := r.(
                msgReceived := r.msgReceived + inMsg
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
            assert exists i | 0 <= i < |o| :: m in o[i] by {
                LemmaElementInSetUnionOnSeqMustExistInOneOfTheSets(m, o);
            }
            var i :| 0 <= i < |o| && m in o[i];
            assert  && UponCommit(s[i], s[i+1], o[i])
                    && (exists m3 | m3 in r'.msgReceived
                                :: 
                                && ValidQC(m3.justify)
                                && m3.justify.cType.MT_PreCommit?
                                && m3.justify.block == m.partialSig.block
                                && m3.justify.viewNum == m.partialSig.viewNum) by {
                assert ValidReplicaState(s[i]);
                assert ReplicaNextSubStep(s[i], s[i+1], o[i]);
                LemmaReplicaVoteCommitOnlyWhenReceiveValidPrecommitQC(s[i], s[i+1], o[i]);
                assert r'.msgReceived == s[i+1].msgReceived by {
                    assert r' == s[|s|-1];
                    LemmaReplicaMsgReceiveStableInNextSubSeq(s, o);
                }
            }
            
        }
    }

    lemma LemmaExistHonestSignerInValidQC(ss : SystemState, qc : Cert)
    requires Reachable(ss)
    requires ValidQC(qc)
    ensures exists sig | sig in qc.signatures
                       ::
                         IsHonest(ss, sig.signer)
    {
        var sgns := qc.signatures;
        assert |sgns| >= quorum(|M_SpecTypes.All_Nodes|);
        var signers := set sig | sig in sgns :: sig.signer;
        NumVoters(sgns);
        assert |signers| >= quorum(|M_SpecTypes.All_Nodes|);
        Axiom_Common_Constraints();
        Axiom_Byz_Constraints();
        LemmaHonestInQuorum(M_SpecTypes.All_Nodes,
                            M_SpecTypes.Adversary_Nodes,
                            signers);
        var honest :| && honest in signers
                      && honest in M_SpecTypes.Honest_Nodes;
        assert All_Nodes == Honest_Nodes + Adversary_Nodes;
        assert Honest_Nodes * Adversary_Nodes == {};
        LemmaAdditiveOnSeparateSet(All_Nodes, Adversary_Nodes, Honest_Nodes);
        assert Honest_Nodes == All_Nodes - Adversary_Nodes;
        LemmaReachableStateIsValid(ss);
        assert IsHonest(ss, honest);
    }

    lemma LemmaExistSameHonestNodeInTwoValidQC(
        ss : SystemState,
        qc1 : Cert,
        qc2 : Cert
    )
    requires Reachable(ss)
    requires ValidQC(qc1) && ValidQC(qc2)
    ensures var signers1 := getMajoritySignerInValidQC(qc1);
            var signers2 := getMajoritySignerInValidQC(qc2);
            exists r | IsHonest(ss, r)
                    ::
                       && r in signers1
                       && r in signers2
    {
        var signers1 := getMajoritySignerInValidQC(qc1);
        var signers2 := getMajoritySignerInValidQC(qc2);
        LemmaReachableStateIsValid(ss);
        LemmaTwoQuorumIntersection(All_Nodes, Adversary_Nodes, signers1, signers2);
    }

    lemma LemmaSameValidQCInSameView(
        ss : SystemState,
        holder1 : Msg,
        holder2 : Msg,
        cert1 : Cert,
        cert2 : Cert)
    requires Reachable(ss)
    requires holder1 in ss.msgSent && QCOccursInMessage(holder1, cert1)
    requires holder2 in ss.msgSent && QCOccursInMessage(holder2, cert2)
    requires ValidQC(cert1) && ValidQC(cert2)
    requires !TrustedInitialQC(cert1) && !TrustedInitialQC(cert2)
    requires cert1.cType == cert2.cType
    requires cert1.viewNum == cert2.viewNum
    ensures cert1.block == cert2.block
    {
        LemmaReachableStateIsValid(ss);
        LemmaExistSameHonestNodeInTwoValidQC(ss, cert1, cert2);
        var signers1 := getMajoritySignerInValidQC(cert1);
        var signers2 := getMajoritySignerInValidQC(cert2);
        var replica :| IsHonest(ss, replica) && replica in signers1 * signers2;
        var rState := ss.nodeStates[replica];

        LemmaExistSignIfSignerInQCSigners(cert1);
        LemmaExistSignIfSignerInQCSigners(cert2);
        var sign1 :| && sign1 in cert1.signatures
                     && sign1.signer == replica;
        var sign2 :| && sign2 in cert2.signatures
                     && sign2.signer == replica;
        LemmaExistVoteMsgForSignature(ss, holder1, cert1, sign1);
        LemmaExistVoteMsgForSignature(ss, holder2, cert2, sign2);
        var v1 :| && v1 in rState.msgSent
                  && ValidVoteMsg(v1)
                  && v1.partialSig == sign1
                  && corrVoteMsg(sign1, v1);
        var v2 :| && v2 in rState.msgSent
                  && ValidVoteMsg(v2)
                  && v2.partialSig == sign2
                  && corrVoteMsg(sign2, v2);

        LemmaHonestNodeOnlyVoteOnceInOneView(ss, replica);
        assert v1.block == v2.block;
    }

}
