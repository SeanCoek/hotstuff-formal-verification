include "../specs/Type.dfy"
include "../common/sets.dfy"

module M_AuxilarilyFunc {
    import opened M_SpecTypes
    import opened M_Set
    import opened Std.Collections.Seq
    import opened Std.Collections.Set

    function orderMsg(m : Msg) : nat

    lemma{:axiom} LemmaOrderMsg()
    ensures forall m, m' :: m != m' ==> orderMsg(m) != orderMsg(m')

    function digestBlock(block : Block) : Hash

    lemma{:axiom} LemmaHash()
    ensures forall b, b' :: digestBlock(b) == digestBlock(b') <==> b == b'

    /**
     * @returns Set union of a sequence of sets
     */
    function setUnionOnSeq<T>(sets : seq<set<T>>) : (r : set<T>)
    ensures |sets| > 0 ==> r == sets[0] + setUnionOnSeq(sets[1..])
    ensures |sets| > 0 ==> (forall i | 0 <= i < |sets| :: sets[i] <= r)
    ensures |sets| > 0 ==> (forall x | x in r :: (
                                                    exists i | 0 <= i < |sets|
                                                            ::
                                                               x in sets[i]
                                                )
                            )
    {
        if sets == [] then
            {}
        else
            sets[0] + setUnionOnSeq(sets[1..])
    }

    lemma LemmaSetUnionOnSeqAdditive<T> (u : set<T>, s : seq<set<T>>, a : set<T>)
    requires u == setUnionOnSeq(s)
    ensures a + u == setUnionOnSeq([a] + s)
    {
    }

    lemma LemmaElementInSetUnionOnSeqMustExistInOneOfTheSets<T>(e : T, sets : seq<set<T>>)
    requires e in setUnionOnSeq(sets)
    ensures exists i | 0 <= i < |sets|:: e in sets[i]
    {

    }

    /**
    * @returns The maximum number of Byzantine validators allowed in a network
    *          of `setSize` validators
    */
    function f(setSize:nat) : nat
    {
        if setSize == 0 then
            0
        else
            (setSize - 1) / 3
    }

    function{:axiom} getInitialQC(cType : MsgType) : (r : Cert)
    ensures ValidQC(r)
    ensures r.cType == cType && r.viewNum == 0 && r.block == Genesis_Block

    predicate isInitialQC(qc : Cert)
    {
        && ValidQC(qc)
        && qc.block == Genesis_Block
        && qc.viewNum == 0
    }

    predicate TrustedInitialQC(qc : Cert)
    {
        || qc == getInitialQC(MT_Prepare)
        || qc == getInitialQC(MT_PreCommit)
    }

    predicate SignatureHasVoteEvidence(msgs : set<Msg>, sig : Signature)
    {
        exists vote | vote in msgs ::
            && ValidVoteMsg(vote)
            && vote.partialSig == sig
    }

    predicate CertificateHasVoteEvidence(
        msgs : set<Msg>,
        byzNodes : set<Address>,
        qc : Cert)
    {
        || TrustedInitialQC(qc)
        || (
            && ValidQC(qc)
            && (forall sig | sig in qc.signatures ::
                || sig.signer in byzNodes
                || SignatureHasVoteEvidence(msgs, sig))
        )
    }

    predicate QCOccursInMessage(m : Msg, qc : Cert)
    {
        || m.justify == qc
        || m.lockedQC == qc
    }

    predicate MessageQCsHaveVoteEvidence(
        msgs : set<Msg>,
        byzNodes : set<Address>,
        m : Msg)
    {
        && (ValidQC(m.justify) ==>
            CertificateHasVoteEvidence(msgs, byzNodes, m.justify))
        && (ValidQC(m.lockedQC) ==>
            CertificateHasVoteEvidence(msgs, byzNodes, m.lockedQC))
    }

    lemma LemmaSignatureEvidenceMonotonic(
        msgs : set<Msg>,
        msgs' : set<Msg>,
        sig : Signature)
    requires msgs <= msgs'
    requires SignatureHasVoteEvidence(msgs, sig)
    ensures SignatureHasVoteEvidence(msgs', sig)
    {
    }

    lemma LemmaCertificateEvidenceMonotonic(
        msgs : set<Msg>,
        msgs' : set<Msg>,
        byzNodes : set<Address>,
        qc : Cert)
    requires msgs <= msgs'
    requires CertificateHasVoteEvidence(msgs, byzNodes, qc)
    ensures CertificateHasVoteEvidence(msgs', byzNodes, qc)
    {
        if !TrustedInitialQC(qc) {
            forall sig | sig in qc.signatures
                ensures sig.signer in byzNodes || SignatureHasVoteEvidence(msgs', sig)
            {
                if sig.signer !in byzNodes {
                    LemmaSignatureEvidenceMonotonic(msgs, msgs', sig);
                }
            }
        }
    }


    lemma LemmaMessageQCEvidenceMonotonic(
        msgs : set<Msg>,
        msgs' : set<Msg>,
        byzNodes : set<Address>,
        m : Msg)
    requires msgs <= msgs'
    requires MessageQCsHaveVoteEvidence(msgs, byzNodes, m)
    ensures MessageQCsHaveVoteEvidence(msgs', byzNodes, m)
    {
        if ValidQC(m.justify) {
            LemmaCertificateEvidenceMonotonic(msgs, msgs', byzNodes, m.justify);
        }
        if ValidQC(m.lockedQC) {
            LemmaCertificateEvidenceMonotonic(msgs, msgs', byzNodes, m.lockedQC);
        }
    }

    function getInitialMsg(sender : Address) : (m : Msg)
    requires sender in All_Nodes
    ensures ValidNewView(m)
    {
        Msg(sender, MT_NewView, 0, EmptyBlock, getInitialQC(MT_Prepare), SigNone, CertNone)
    }

    function getMultiInitialMsg(senders : set<Address>) : (r : set<Msg>)
    requires forall r | r in senders :: r in All_Nodes
    {
        set r | r in senders :: getInitialMsg(r)
    }

    /**
    * @returns The minimum size that any two subsets of validators for a
    *          network with `setSize` validators must have to guarantee that
    *          their intersection includes at least one honest validator under
    *          the assumption that no more than `f(setSeize)` validators are
    *          Byzantine.
    */
    function quorum(setSize : nat) : (r: nat)
    ensures r <= setSize
    {
        // 2*(setSize - 1) / 3 + 1
        // 2 * f(setSize) + 1
        // if setSize <= 3
        // then 
        //     setSize - f(setSize) + 1
        // else
        //     2 * f(setSize) + 1
        if setSize == 0 then 0 else setSize - f(setSize)
    }  

    lemma LemmaTwoQuorumIntersection(
                                    allNodes : set<Address>,
                                    byzNodes : set<Address>,
                                    q1 : set<Address>,
                                    q2 : set<Address>)
    requires |allNodes| > 0
    requires q1 <= allNodes && |q1| >= quorum(|allNodes|)
    requires q2 <= allNodes && |q2| >= quorum(|allNodes|)
    requires |byzNodes| <= f(|allNodes|)
    ensures var honest := allNodes - byzNodes; q1 * q2 * honest != {}
    {
        var honest := allNodes - byzNodes;
        // prove q1*q2*honest != {}
        calc {
            |q1 * q2 * honest|;
            ==
            |(q1*q2) * honest|;
            ==
            |q1*q2| + |honest| - |(q1*q2) + honest|;
            >=
            |q1*q2| + |allNodes| - |byzNodes| - |(q1*q2) + honest|;
            >= calc {
                |q1 * q2|;
                ==
                |q1| + |q2| - |q1+q2|;
                >= calc {
                    |q1+q2|;
                    <= { LemmaSubsetCardinality(q1+q2, allNodes); }
                    |allNodes|;
                    }
                |q1| + |q2| - |allNodes|;
                }
            |q1| + |q2| - |byzNodes| - |(q1*q2) + honest|;
            >= {LemmaSubsetCardinality((q1*q2)+honest, allNodes);}
            |q1| + |q2| - |byzNodes| - |allNodes|;
            >=
            2 * quorum(|allNodes|) - |byzNodes| - |allNodes|;
            >=
            2 * quorum(|allNodes|) - f(|allNodes|) - |allNodes|;
            >=
            1;

            // 2 * (2*f + 1) - f - n
            // 2 * (2 * (n-1)/3 + 1) - (n-1)/3 - n

        }
    }

    lemma LemmaHonestInQuorum<T> (allNodes: set<T>, byzNodes: set<T>, q1: set<T>)
    requires allNodes != {}
    requires q1 <= allNodes
    requires |q1| >= quorum(|allNodes|)
    requires |byzNodes| <= f(|allNodes|)
    ensures var honest := allNodes - byzNodes; q1 * honest != {}
    {
        var honest := allNodes - byzNodes;

        calc {
            |q1 * honest|;
            ==
            |q1| + |honest| - |q1 + honest|;
            >=
            |q1| + |allNodes| - |byzNodes| - |q1 + honest|;
            >= { LemmaSubsetCardinality(q1+honest, allNodes); }
            |q1| - |byzNodes|;
            >=
            quorum(|allNodes|) - f(|allNodes|);
            >= 
            1;
        }
    }

    /* Mapping each round to a delegated leader */
    function{:axiom} leader(round : nat) : (l : Address)
    ensures l in M_SpecTypes.All_Nodes

    /* 
    Referring to ``MATCHINGMSG(m, t, v)'' in Algorithm 1 of HotStuff-2018
    The returning messsage should satisfy ``(m.type = t) && (m.viewNum = v)''
    However, the above constrains seem not sufficient enough.
    For example, a byzantine node might send multiple message with same type and view number,
    but carring different block, quorum certificate, etc.
    Therefore, we should strengthen this function by adding constrains.
    */
    function{:axiom} getMatchMsg(msgs : set<Msg>, msgType : MsgType, view : nat) : (r : set<Msg>)
    ensures forall m | m in r :: ValidMsg(m) && m.mType == msgType && m.viewNum == view
    ensures forall m | m in msgs :: ValidMsg(m) && m.mType == msgType && m.viewNum == view ==> m in r
    ensures forall m | m in r
                    :: 
                       exists m2 | m2 in msgs
                                :: 
                                   m == m2

    function getMatchVoteMsg(msgs : set<Msg>, t : MsgType, view : nat) : (r : set<Msg>)
    ensures (forall m | m in r 
                    :: && m in msgs
                       && m.mType == t
                       && m.viewNum == view
                       && (
                        || ValidPrepareVote(m)
                        || ValidPrecommitVote(m)
                        || ValidCommitVote(m)
                       )
            )
    ensures (forall m | m in msgs
                    :: 
                        (&& m.mType == t
                        && m.viewNum == view
                        && (
                            || ValidPrepareVote(m)
                            || ValidPrecommitVote(m)
                            || ValidCommitVote(m)
                        )
                    
                    ==> m in r)
            )
    {
        set m | && m in msgs
                && m.mType == t
                && m.viewNum == view
                && (
                    || ValidPrepareVote(m)
                    || ValidPrecommitVote(m)
                    || ValidCommitVote(m)
                )
    }

    function getMatchProposalMsg(msgs : set<Msg>, view : nat) : (r : set<Msg>)
    ensures forall m | m in r :: (
                                  && m in msgs 
                                  && ValidProposal(m)
                                  && m.viewNum == view
                                )
    ensures forall m | m in msgs :: (
                                     && ValidProposal(m)
                                     && m.viewNum == view
                                    )
                                    ==>
                                    m in r
    {
        set m | && m in msgs
                && ValidProposal(m)
                && m.viewNum == view
    }


    function ExtractSignatrues(msgs : set<Msg>) : (r : set<Signature>)
    requires forall m | m in msgs :: ValidVoteMsg(m)
    requires forall m1, m2 | m1 in msgs && m2 in msgs
                          :: 
                            m1 != m2
                            ==>
                            corrVotesFromDiffSigner(m1, m2)
                            
    ensures |r| == |msgs|
    ensures forall s | s in r :: exists m | m in msgs :: m.partialSig == s
    {
        NumSignatures(msgs);
        set m | m in msgs
             ::
                m.partialSig
    }

    lemma NumSignatures(msgs : set<Msg>)
    requires forall m | m in msgs :: ValidVoteMsg(m)
    requires forall m1, m2 | m1 in msgs && m2 in msgs
                          :: 
                              ( m1 != m2
                                ==>
                                corrVotesFromDiffSigner(m1, m2)
                              ) 
    ensures |msgs| == |set sig | sig in msgs :: sig.partialSig|
    {
        if |msgs| == 0 {}
        else {
            var m :| m in msgs;
            var msgs' := msgs - {m};
            NumSignatures(msgs');
            SetExtension(m.partialSig, set sig | sig in msgs' :: sig.partialSig);
            assert |(set sig | sig in msgs' :: sig.partialSig) + {m.partialSig}| == |set sig | sig in msgs' :: sig.partialSig| + 1;
            assert (set sig | sig in msgs :: sig.partialSig) == (set sig | sig in msgs' :: sig.partialSig) + {m.partialSig};
            assert |set sig | sig in msgs :: sig.partialSig| == |set sig | sig in msgs' :: sig.partialSig| + 1;
        }
    }


    ghost function getMatchQC(msgs : set<Msg>, mType : MsgType, cType : MsgType, view : nat) : (r : set<Cert>)
    ensures forall c | c in r :: ValidQC(c) && c.cType == cType && c.viewNum == view
    ensures forall c | c in r :: exists m | m in msgs && ValidMsg(m) && m.mType == mType :: m.justify == c
    ensures forall m | m in msgs && ValidMsg(m) :: (
                                                    && m.mType == mType
                                                    && ValidQC(m.justify)
                                                    && m.justify.cType == cType
                                                    && m.justify.viewNum == view
                                                    ==>
                                                    m.justify in r
    )
    {
        set m | && m in msgs
                && ValidMsg(m)
                && m.mType == mType
                && ValidQC(m.justify)
                && m.justify.cType == cType
                && m.justify.viewNum == view
              ::
                m.justify
    }


    function{:axiom} getHighQC(msgs : set<Msg>) : (r : Cert)
    requires msgs != {}
    requires forall m | m in msgs :: ValidQC(m.justify)
    ensures ValidQC(r)
    ensures forall m | m in msgs :: ValidQC(m.justify) ==> r.viewNum >= m.justify.viewNum
    ensures exists m | m in msgs :: ValidQC(m.justify) && m.justify == r

    function{:axiom} getNewBlock(parent : Block) : (r : Block)
    ensures r.Block?
    ensures r.parent == parent
    ensures r.parent != r

    function{:axiom} getAncestors(b : Block) : (r : seq<Block>)
    ensures |r| > 0 && r[|r|-1] == b
    ensures forall i | 0 <= i < |r| :: r[i].Block?
    ensures forall i, j | 0 <= i < j < |r| :: r[i] != r[j]  // None duplication
    ensures forall i | 0 <= i < |r|-1 :: r[i] == r[i+1].parent

    predicate extension(child : Block, parent : Block)
    requires child.Block?
    {
        getAncestors(parent) <= getAncestors(child)
    }

    lemma Lemma_AncestorOfParentIsPrefixOfAncestorOfChild(child : Block, parent : Block)
    requires child.Block? && parent.Block?
    requires extension(child, parent)
    ensures Seq.IsPrefix(getAncestors(parent), getAncestors(child))
    {
        // var acstr_p, acstr_c := getAncestors(parent), getAncestors(child);
        // assert parent in acstr_c;
        // assert parent == acstr_p[|acstr_p|-1];
        // assert acstr_p <= acstr_c by {
        //     if |acstr_c| == 2 {
        //         assert acstr_c == [parent, child] by {
        //             assert |acstr_c| == 2;
        //             assert parent in acstr_c;
        //             assert child == acstr_c[|acstr_c|-1];
        //             assert forall i, j | 0 <= i < j < |acstr_c| :: acstr_c[i] != acstr_c[j];
        //         }
        //     }
        // }
    }

    predicate safeNode(block : Block, qc : Cert, lockedQC : Cert)
    requires block.Block? && lockedQC.Cert? && qc.Cert?
    {
        || extension(block, lockedQC.block)
        || qc.viewNum > lockedQC.viewNum
    }

    function Multicast(m : Msg, recipients : set<Address>) : set<MsgWithRecipient>
    {
        set r | r in recipients :: MsgWithRecipient(m, r)
    }

    predicate NoConflict(b1 : Block, b2 : Block)
    requires b1.Block? && b2.Block?
    {
        || b1 == b2
        || extension(b1, b2)
        || extension(b2, b1)
    }

    /**
     * A valid Quorum Certificate should hold the following constraints
     * Refer to the function "tverify(<qc.type, qc.view, qc.node>, qc.sig)" described in the paper
     * It is supposed to be a threshold decryption
     */
    predicate ValidQC(qc : Cert)
    {
        && qc.Cert?
        && qc.block.Block?
        // All votes should be voting for same thing
        && (forall s |  && s in qc.signatures
                    ::  
                        && s.Signature?
                        && s.mType == qc.cType
                        && s.viewNum == qc.viewNum
                        && s.block == qc.block
                        && s.signer in All_Nodes
            )
        // For any two votes, if there are not the same vote,
        // then there are coming from different signers
        && (forall s1, s2 | && s1 in qc.signatures 
                            && s2 in qc.signatures
                         :: 
                            && s1 != s2 ==> s1.signer != s2.signer
                         )
        && |qc.signatures| >= quorum(|All_Nodes|)
    }

    function getVotesInValidQC(qc : Cert) : (votes: set<Signature>)
    requires ValidQC(qc)
    ensures |votes| >= quorum(|All_Nodes|)
    {
        qc.signatures
    }

    lemma SetExtension<T>(x: T, s: set<T>)
    requires x !in s
    ensures |s+{x}| == |s| + 1
    {}

    lemma NumVoters(signatures: set<Signature>)
    requires forall s :: s in signatures ==> s.Signature?
    requires forall s1, s2 | s1 in signatures && s2 in signatures :: s1 != s2 ==> s1.signer != s2.signer
    ensures |signatures| == |set sig | sig in signatures :: sig.signer|
    decreases |signatures|
    {
        if |signatures| == 0 {}
        else {
            var s :| s in signatures;
            var signatures' := signatures - {s};
            NumVoters(signatures');
            SetExtension(s.signer, set sig | sig in signatures' :: sig.signer);
            assert |(set sig | sig in signatures' :: sig.signer) + {s.signer}| == |set sig | sig in signatures' :: sig.signer| + 1;
            assert (set sig | sig in signatures :: sig.signer) == (set sig | sig in signatures' :: sig.signer) + {s.signer};
            assert |set sig | sig in signatures :: sig.signer| == |set sig | sig in signatures' :: sig.signer| + 1;
        }
    }

    function getMajoritySignerInValidQC(qc : Cert) : (ret : set<Address>)
    requires ValidQC(qc)
    ensures forall s | s in qc.signatures :: s.signer in All_Nodes
    ensures |ret| >= quorum(|All_Nodes|)
    {
        var votes := getVotesInValidQC(qc);
        NumVoters(votes);
        set vote | vote in votes
                    :: vote.signer
    }

    function{:axiom} splitMsgByBlocks(msgs : set<Msg>) : (r : set<set<Msg>>)
    ensures |msgs| > 0 ==> |r| > 0
    ensures forall mset | mset in r :: mset <= msgs
    ensures forall mset1, mset2 | mset1 in r && mset2 in r :: (mset1 != mset2) ==> |mset1 * mset2| == 0
    ensures (forall mset | mset in r :: (forall m1, m2 | m1 in mset && m2 in mset :: m1.block == m2.block))


    function{:axiom} getMaxLengthSet<T>(sets : set<set<T>>) : (r : set<T>)
    ensures r in sets
    ensures forall s | s in sets :: |r| >= |s|


    function{:axiom} argmin<T>(s: set<T>, f: T -> int) : (ret : T)
    requires s != {}
    ensures forall x :: x in s ==> f(ret) <= f(x)
    ensures ret in s

    function{:axiom} argminView(s: set<Msg>) : (ret : Msg)
    requires s != {}
    requires forall x | x in s :: x.justify.Cert?
    ensures ret in s
    ensures forall x :: x in s ==> ret.justify.viewNum <= x.justify.viewNum

    function{:axiom} argmax<T>(s: set<T>, f: T -> int) : (ret : T)
    requires s != {}
    ensures forall x :: x in s ==> f(ret) >= f(x)
    ensures ret in s

    predicate msgWithValidQC(m : Msg, cType : MsgType)
    {
        && ValidQC(m.justify)
        && m.justify.cType == cType
    }

    /**
     * >>>>>>>>>>>>>>>>>>>>>>>>>>>> Validation of message <<<<<<<<<<<<<<<<<<<<<<<<<
     * > Here we define predicates to determine correct message in different kind.
     * > There are 8 different kinds of valid messages : 
     * > 1. NewView
     * > 2. Prepare Request (Proposal)
     * > 3. Prepare Vote
     * > 4. Precommit Request
     * > 5. Precommit Vote
     * > 6. Commit Request
     * > 7. Commit Vote
     * > 8. Decide Message
     */

    predicate ValidNewView(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_NewView?
        && ValidQC(m.justify)
        && m.justify.cType.MT_Prepare?
        && m.viewNum >= m.justify.viewNum
        && m.partialSig.SigNone?
        && m.block.EmptyBlock?
    }

    predicate ValidProposal(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_Prepare?
        && m.partialSig.SigNone?
        && ValidQC(m.justify)
        && m.justify.cType.MT_Prepare?
        && m.viewNum > m.justify.viewNum
        && m.block.Block?
        && m.block.parent == m.justify.block
    }

    predicate ValidPrepareVote(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_Prepare?
        && m.justify.CertNone?
        && m.block.Block?
        && m.partialSig.Signature?
        && m.partialSig.mType == m.mType
        && m.partialSig.block == m.block
        && m.partialSig.viewNum == m.viewNum
        && m.partialSig.signer in All_Nodes
        && m.sender == m.partialSig.signer
        && m.lockedQC.Cert?
    }

    predicate ValidPrecommitRequest(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_PreCommit?
        && m.partialSig.SigNone?
        && ValidQC(m.justify)
        && m.justify.cType.MT_Prepare?
        && m.justify.viewNum == m.viewNum
        && m.block.EmptyBlock?
    }

    predicate ValidPrecommitVote(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_PreCommit?
        && m.justify.CertNone?
        && m.block.Block?
        && m.partialSig.Signature?
        && m.partialSig.mType == m.mType
        && m.partialSig.block == m.block
        && m.partialSig.viewNum == m.viewNum
        && m.partialSig.signer in All_Nodes
        && m.sender == m.partialSig.signer
        && m.lockedQC.CertNone?
    }

    predicate ValidCommitRequest(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_Commit?
        && m.partialSig.SigNone?
        && ValidQC(m.justify)
        && m.justify.cType.MT_PreCommit?
        && m.justify.viewNum == m.viewNum
        && m.block.EmptyBlock?
    }

    predicate ValidCommitVote(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_Commit?
        && m.justify.CertNone?
        && m.block.Block?
        && m.partialSig.Signature?
        && m.partialSig.mType == m.mType
        && m.partialSig.block == m.block
        && m.partialSig.viewNum == m.viewNum
        && m.partialSig.signer in All_Nodes
        && m.sender == m.partialSig.signer
        && m.lockedQC.CertNone?
    }

    predicate ValidDecideMsg(m : Msg)
    {
        && m.sender in All_Nodes
        && m.mType.MT_Decide?
        && m.partialSig.SigNone?
        && ValidQC(m.justify)
        && m.justify.cType.MT_Commit?
        && m.justify.viewNum == m.viewNum
        && m.block.EmptyBlock?
    }

    predicate ValidMsg(m : Msg)
    {
        || ValidNewView(m)
        || ValidProposal(m)
        || ValidPrepareVote(m)
        || ValidPrecommitRequest(m)
        || ValidPrecommitVote(m)
        || ValidCommitRequest(m)
        || ValidCommitVote(m)
        || ValidDecideMsg(m)
    }

    predicate ValidVoteMsg(m : Msg)
    {
        || ValidPrepareVote(m)
        || ValidPrecommitVote(m)
        || ValidCommitVote(m)
    }

    predicate ValidMsg_old(m : Msg)
    {
        || (
            && m.mType.MT_NewView?
            && ( 
                || (
                    && ValidQC(m.justify)
                    && m.justify.cType.MT_Prepare?
                )
                || m.justify.CertNone?
            )
            && m.partialSig.SigNone?
            && m.block.EmptyBlock?
        )
        || (
            && m.mType.MT_Prepare?
            && (
                ||
                // Proposal From Leader
                (   && m.partialSig.SigNone?
                    && ValidQC(m.justify)
                    && m.justify.cType.MT_Prepare?
                    && m.block.Block?
                    && m.block.parent == m.justify.block
                    )
                // Prepare Vote
                || 
                (   && m.justify.CertNone?
                    && m.partialSig.Signature?
                    && m.partialSig.mType == m.mType
                    && m.partialSig.block == m.block
                    && m.partialSig.viewNum == m.viewNum
                    && m.partialSig.signer in All_Nodes
                    )
            )
        )
        || (
            && m.mType.MT_PreCommit?
            && (
                ||
                (   && m.partialSig.SigNone?
                    && ValidQC(m.justify)
                    && m.justify.cType.MT_Prepare?
                    && m.justify.viewNum == m.viewNum
                    && m.block.EmptyBlock?
                    )
                // PreCommit Vote  
                || 
                (   && m.justify.CertNone?
                    && m.partialSig.Signature?
                    && m.partialSig.mType == m.mType
                    && m.partialSig.block == m.block
                    && m.partialSig.viewNum == m.viewNum
                    && m.partialSig.signer in All_Nodes
                )
            )
        )
        || (
            && m.mType.MT_Commit?
            && (
                ||
                (   && m.partialSig.SigNone?
                    && ValidQC(m.justify)
                    && m.justify.cType.MT_PreCommit?
                    && m.justify.viewNum == m.viewNum
                    && m.block.EmptyBlock?
                    )
                // Commit Vote  
                || 
                (   && m.justify.CertNone?
                    && m.partialSig.Signature?
                    && m.partialSig.mType == m.mType
                    && m.partialSig.block == m.block
                    && m.partialSig.viewNum == m.viewNum
                    && m.partialSig.signer in All_Nodes
                )
            )
        )
        || (
            && m.mType.MT_Decide?
            && m.partialSig.SigNone?
            && ValidQC(m.justify)
            && m.justify.cType.MT_Commit?
            && m.justify.viewNum == m.viewNum
            && m.block.EmptyBlock?
        )
    }
    /** <<<<<<<<<<<<<<<<<<<<<<<<< End of validation of message >>>>>>>>>>>>>>>>>>>>>
    */

    predicate correspondingQC(qc : Cert, qc' : Cert)
    requires ValidQC(qc) && ValidQC(qc')
    {
        && qc.block == qc'.block
        && qc.viewNum == qc'.viewNum
    }

    predicate corrVoteMsg(sig : Signature, vote : Msg)
    requires sig.Signature?
    {
        && sig.mType == vote.mType
        && sig.viewNum == vote.viewNum
        && sig.block == vote.block
    }

    predicate corrVoteMsgAndToVotedMsg(vote : Msg, toVote : Msg)
    requires ValidVoteMsg(vote) && ValidMsg(toVote)
    requires ValidQC(toVote.justify)
    {
        || ( // Prepare Vote
            && ValidPrepareVote(vote)
            && ValidProposal(toVote)
            && vote.partialSig.block == toVote.block
            && vote.partialSig.viewNum == toVote.viewNum
        )
        || ( // Precommit Vote
            && ValidPrecommitVote(vote)
            && ValidPrecommitRequest(toVote)
            && vote.partialSig.block == toVote.justify.block
            && vote.partialSig.viewNum == toVote.justify.viewNum
        )
        || ( // Commit Vote
            && ValidCommitVote(vote)
            && ValidCommitRequest(toVote)
            && vote.partialSig.block == toVote.justify.block
            && vote.partialSig.viewNum == toVote.justify.viewNum
        )
    }

    predicate corrVotesFromDiffSigner(v1 : Msg, v2 : Msg)
    requires ValidVoteMsg(v1) && ValidVoteMsg(v2)
    {
        && v1.partialSig.mType == v2.partialSig.mType
        && v1.partialSig.block == v2.partialSig.block
        && v1.partialSig.viewNum == v2.partialSig.viewNum
        && v1.partialSig.signer != v2.partialSig.signer
    }

    function mapSeq<A, B>(s : seq<A>, f: A->B) : (r : seq<B>)
    ensures |r| == |s|
    ensures forall i | 0 <= i < |s| :: r[i] == f(s[i])
    {
        if |s| == 0
        then []
        else [f(s[0])] + mapSeq(s[1..], f)
    }

    function buildMsg(sender : Address, mType : MsgType, node : Block, qc : Cert, viewNum : nat, lockedQC : Cert) : (m : Msg)
    {
        Msg(sender, mType, viewNum, node, qc, SigNone, lockedQC)
    }

    function buildVoteMsg(sender : Address, mType : MsgType, node : Block, qc : Cert, viewNum : nat, lockedQC : Cert, signer : Address) : (m : Msg)
    {
        Msg(sender, mType, viewNum, node, qc,
            Signature(signer, mType, viewNum, node), lockedQC)
    }

    function getVotesForSafeProposals(proposals : set<Msg>, lockedQC : Cert, id : Address) : (votes : set<Msg>)
    requires forall p | p in proposals :: ValidProposal(p)
    requires ValidQC(lockedQC) || lockedQC.CertNone?
    ensures forall vote | vote in votes ::
                exists proposal | proposal in proposals ::
                    vote == voteForProposal(proposal, lockedQC, id)
    {
        set vote | vote in proposals
                :: voteForProposal(vote, lockedQC, id)
    }

    function voteForProposal(proposal : Msg, lockedQC : Cert, id : Address) : (vote : Msg)
    requires ValidProposal(proposal)
    requires ValidQC(lockedQC) || lockedQC.CertNone?
    ensures vote.block.Block? ==>
                && vote == buildVoteMsg(id, MT_Prepare, proposal.block, CertNone, proposal.viewNum, lockedQC, id)
                && vote.lockedQC == lockedQC
                && lockedQC.Cert?
                && vote.block == proposal.block
                && vote.viewNum == proposal.viewNum
                && extension(proposal.block, proposal.justify.block)
                && safeNode(proposal.block, proposal.justify, lockedQC)
    {
        if 
            && extension(proposal.block, proposal.justify.block) 
            && lockedQC.Cert?
            && safeNode(proposal.block, proposal.justify, lockedQC)
        then 
            buildVoteMsg(id, MT_Prepare, proposal.block, CertNone, proposal.viewNum, lockedQC, id)
        else 
            buildVoteMsg(id, MT_Prepare, EmptyBlock, CertNone, proposal.viewNum, lockedQC, id)
    }

    function proposalVoteFilter(votes : set<Msg>) : (r : set<Msg>)
    requires forall v | v in votes :: v.partialSig.Signature?
    ensures forall v | v in r :: ValidMsg(v)
    ensures r <= votes
    {
        set v | && v in votes
                && ValidMsg(v)
                && !v.block.EmptyBlock?
                && !v.partialSig.block.EmptyBlock?
                :: v
    }

    predicate isVotedInView(msgSent : set<Msg>, vType : MsgType, view : nat)
    {
        exists v | && v in msgSent
                ::
                   && ValidVoteMsg(v)
                   && v.mType == vType
                   && v.viewNum == view
    }

    function getVotesIfUnVoted(votes : set<Msg>, voted : bool) : (r : set<Msg>)
    ensures r <= votes
    ensures voted ==> r == {}
    ensures !voted ==> r == votes
    {
        var empty := {};
        if voted
        then
            empty
        else
            votes
    }

    function onlyOneVote(votes : set<Msg>) : (r : set<Msg>)
    requires forall v | v in votes :: ValidVoteMsg(v)
    ensures forall v | v in r :: v in votes
    ensures |r| == 1 || |r| == 0
    ensures r == votes || r == {}
    {
        var empty := {};
        if |votes| != 1
        then
            empty
        else
            votes
    }

    predicate predHonestNodeInTwoQC(honest : set<Address>, qc1 : Cert, qc2 : Cert, r : Address)
    requires ValidQC(qc1) && ValidQC(qc2)
    {
        var signers1 := getMajoritySignerInValidQC(qc1);
        var signers2 := getMajoritySignerInValidQC(qc2);
        r in signers1 * signers2 * honest
    }

    predicate predNodeInTwoQC(qc1 : Cert, qc2 : Cert, r : Address)
    requires ValidQC(qc1) && ValidQC(qc2)
    {
        var signers1 := getMajoritySignerInValidQC(qc1);
        var signers2 := getMajoritySignerInValidQC(qc2);
        r in signers1 * signers2
    }

    predicate predHasDoneVoteInView(msgSent : set<Msg>, vType : MsgType, view : nat)
    {
        var existsVotes := set v | && v in msgSent
                                   && ValidVoteMsg(v)
                                   && v.mType == vType
                                   && v.viewNum == view;
        existsVotes != {}
    }

    function getSameSignersInTwoQC(qc1 : Cert, qc2 : Cert) : (r : set<Address>)
    requires ValidQC(qc1) && ValidQC(qc2)
    {
        var signers1 := getMajoritySignerInValidQC(qc1);
        var signers2 := getMajoritySignerInValidQC(qc2);
        signers1 * signers2
    }

    lemma LemmaGetSameSignersInTwoQCIsInBothQC(qc1 : Cert, qc2 : Cert, r : Address, signers1 : set<Address>, signers2 : set<Address>)
    requires ValidQC(qc1) && ValidQC(qc2)
    requires r in getSameSignersInTwoQC(qc1, qc2)
    requires signers1 == getMajoritySignerInValidQC(qc1)
    requires signers2 == getMajoritySignerInValidQC(qc2)
    ensures r in signers1 * signers2
    {

    }


    function{:axiom} filterDoubleVote(msgs : set<Msg>) : (r : set<Msg>)
    requires forall m | m in msgs :: ValidVoteMsg(m)
    requires forall m1, m2 | && m1 in msgs 
                             && m2 in msgs
                          ::
                             && m1.mType == m2.mType
                             && m1.viewNum == m2.viewNum
                             && m1.block == m2.block
    ensures forall m | m in r :: m in msgs
    ensures forall m1, m2 | && m1 in msgs 
                            && m2 in msgs
                            && m1 != m2
                            && ValidVoteMsg(m1)
                            && ValidVoteMsg(m2)
                         ::
                            m1.partialSig.signer == m2.partialSig.signer
                            ==>
                            && m1 !in r
                            && m2 !in r

}
