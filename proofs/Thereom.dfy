include "../specs/Type.dfy"
include "../specs/System.dfy"
include "../specs/Trace.dfy"
include "../specs/Invariants.dfy"
include "../specs/Replica.dfy"
include "../specs/Auxilarily.dfy"
include "Lemmas.dfy"
include "../common/sets.dfy"


/**
 @Module Name : M_Thereom
 @Description : Lemmas for proving properties of reachable system states, such as proving a valid QC is formed only if sufficient votes exist.
 */
module M_Thereom {
    import opened M_SpecTypes
    import opened M_System
    import opened M_Trace
    import opened M_Invariants
    import opened M_Replica
    import opened M_AuxilarilyFunc
    import opened M_Lemma
    import opened M_Set

    predicate consistentBlockchains(bc1 : Blockchain, bc2 : Blockchain)
    {
        || bc1 <= bc2
        || bc2 <= bc1
    }

    ghost predicate consistency(t : Trace)
    {
        forall i, r1, r2 |
                    && IsHonest(t(i), r1)
                    && IsHonest(t(i), r2)
                :: consistentBlockchains(t(i).nodeStates[r1].bc, t(i).nodeStates[r2].bc)
    }

    /**
     * In every reachable system state, 
     * local blockchains in honest replicas should be consistent.
     * 
    */
    lemma LemmaReachableSystemStateIsConsistent(ss : SystemState)
    requires Reachable(ss)
    ensures forall r1, r2 | 
                            && IsHonest(ss, r1)
                            && IsHonest(ss, r2)
                         :: 
                            consistentBlockchains(ss.nodeStates[r1].bc, ss.nodeStates[r2].bc)
    {
        forall r1, r2 | 
                        && IsHonest(ss, r1)
                        && IsHonest(ss, r2)
        ensures consistentBlockchains(ss.nodeStates[r1].bc, ss.nodeStates[r2].bc)
        {
            var s1, s2 := ss.nodeStates[r1], ss.nodeStates[r2];
            // Here we should prove: s1.bc <= s2.bc || s2.bc <= s1.bc
            LemmaReachableStateIsValid(ss);
            assert ValidReplicaState(s1) && ValidReplicaState(s2);
            if s1.bc != [M_SpecTypes.Genesis_Block] && s2.bc != [M_SpecTypes.Genesis_Block] {
                // local blockchain in s1 and s2 are neither the initial blockchain (i.e. blockchain of one block `Genesis_Block`)
                // which means s1 and s2 must have received a message with a commit QC and update their local blockchain accordingly.
                assert exists m1 | && m1 in s1.msgReceived
                                    && m1.justify.Cert?
                                    && m1.justify.cType == MT_Commit
                                    && ValidQC(m1.justify)
                                    && m1.justify.block.Block?
                                ::
                                    s1.bc <= getAncestors(m1.justify.block);
                var m1 :| && m1 in s1.msgReceived
                                    && m1.justify.Cert?
                                    && m1.justify.cType == MT_Commit
                                    && ValidQC(m1.justify)
                                    && m1.justify.block.Block?
                                    && s1.bc <= getAncestors(m1.justify.block);

                assert exists m2 | && m2 in s2.msgReceived
                                   && m2.justify.Cert?
                                   && m2.justify.cType.MT_Commit?
                                   && ValidQC(m2.justify)
                                   && m2.justify.block.Block?
                                ::
                                   s2.bc <= getAncestors(m2.justify.block);
                var m2 :| && m2 in s2.msgReceived
                                   && m2.justify.Cert?
                                   && m2.justify.cType.MT_Commit?
                                   && ValidQC(m2.justify)
                                   && m2.justify.block.Block?
                                   && s2.bc <= getAncestors(m2.justify.block);
                // all messages received must be sent by nodes, which is captured by `msgSent` in system state
                assert m1 in ss.msgSent by {
                    assert s1.msgReceived <= ss.msgSent by {
                        LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);
                    }
                }
                assert m2 in ss.msgSent by {
                    assert s2.msgReceived <= ss.msgSent by {
                        LemmaMsgReceivedByReplicaIsSubsetOfAllMsgSentBySystem(ss);
                    }
                }

                // Quorum Certificate is formed in a chain manner,
                // more visually, QC(prepare) -> QC(precommit) -> QC(commit)
                // Hence, we have a corresponding prepare QC for every commit QC.
                assert exists m1_p : Msg :: && m1_p in ss.msgSent
                                            && ValidQC(m1_p.justify)
                                            && m1_p.justify.cType == MT_Prepare
                                            && m1_p.justify.block == m1.justify.block
                                            && m1_p.justify.viewNum == m1.justify.viewNum by {
                    LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                }

                assert exists m2_p : Msg :: && m2_p in ss.msgSent
                                            && ValidQC(m2_p.justify)
                                            && m2_p.justify.cType == MT_Prepare
                                            && m2_p.justify.block == m2.justify.block
                                            && m2_p.justify.viewNum == m2.justify.viewNum by {
                    LemmaExistValidPrepareQCForEveryValidCommitQC(ss);
                }

                var m1_p :| && m1_p in ss.msgSent
                                            && ValidQC(m1_p.justify)
                                            && m1_p.justify.cType == MT_Prepare
                                            && m1_p.justify.block == m1.justify.block
                                            && m1_p.justify.viewNum == m1.justify.viewNum;
                var m2_p :| && m2_p in ss.msgSent
                                            && ValidQC(m2_p.justify)
                                            && m2_p.justify.cType == MT_Prepare
                                            && m2_p.justify.block == m2.justify.block
                                            && m2_p.justify.viewNum == m2.justify.viewNum;


                if m1_p.justify.viewNum <= m2_p.justify.viewNum {
                    assert extension(m2_p.justify.block, m1_p.justify.block) by {
                        // Quorum properties, there is at least one honest node exists in both two quorums.
                        LemmaExistSameHonestNodeInTwoValidQC(ss, m1.justify, m2_p.justify);
                        var r :| && r in getSameSignersInTwoQC(m2_p.justify, m1.justify)
                                 && IsHonest(ss, r);
                        // Replica `r` will not send a prepare vote for a block conflicting a commit QC `m1.justify` if it has voted this QC before.
                        LemmaHonestNodeWontVoteConflictInPrepare(ss, r, m1.justify, m2_p.justify);
                        assert extension(m2_p.justify.block, m1.justify.block);
                    }
                } else {
                    // this case is when m2_p.justify.viewNum < m1_p.justify.viewNum
                    assert extension(m1_p.justify.block, m2_p.justify.block) by {
                        LemmaExistSameHonestNodeInTwoValidQC(ss, m2.justify, m1_p.justify);
                        var r :| && r in getSameSignersInTwoQC(m1_p.justify, m2.justify)
                                 && IsHonest(ss, r);
                        LemmaHonestNodeWontVoteConflictInPrepare(ss, r, m2.justify, m1_p.justify);
                        assert extension(m1_p.justify.block, m2.justify.block);
                    }
                }

                assert || extension(m1.justify.block, m2.justify.block) // ancestors of m2.justify.block is prefix of ancestors of m1.justify.block
                       || extension(m2.justify.block, m1.justify.block);
                
                var m1_acstr, m2_acstr := getAncestors(m1.justify.block), getAncestors(m2.justify.block); 

                assert s2.bc <= m2_acstr;
                assert s1.bc <= m1_acstr;
                assert m1_acstr <= m2_acstr|| m2_acstr <= m1_acstr; // by the definition of function `extension`
                assert s1.bc <= s2.bc || s2.bc <= s1.bc;
                // Q.E.D.
            }
            else {  // s1.bc == [M_SpecTypes.Genesis_Block] || s2.bc == [M_SpecTypes.Genesis_Block]
                // OBSERVE 
                // by the invariant that an honest replica always holds a local blockchain starting with Genesis_Block
                // Q.E.D.
            }
            // Q.E.D.
        }
    }
}