include "Type.dfy"
include "Auxilarily.dfy"
include "../proofs/Axioms.dfy"
include "../common/proofs.dfy"
include "Invariants.dfy"

/**
 @Module Name : M_Replica
 @Description : Definitions of replica's state, behaviours, and invariants 
 */
module M_Replica {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_ProofTactic
    import opened M_Invariants

    /**
     *  Bookeeping variables for a replica
     *  id : identifier
     *  bc : local blockchain
     *  viewNum : view number
     *  prepareQC : Quorum Certificate for prepare message
     *  lockedQC : Qurum Certificate for pre-commit message
     *  msgReceived : all the messages recieved by replica
     *  msgSent : all the messages sent by replica
     */
    datatype ReplicaState = ReplicaState(
        id : Address,
        bc : Blockchain,
        viewNum : nat,
        prepareQC : Cert,
        lockedQC : Cert,
        msgReceived : set<Msg>,
        msgSent : set<Msg>
    )

    /**
     *  Replica state initialization
     *  This predicate defines what a initialize state of replica should satisfy.
     *  At the initial stage of HotStuff, an unique address (id) will be assigned to each replica
     *  and all the replica will start at view 1.
     *
     *  We assume at view 0, 
     *  all replica hold a local blockchain with a predifined block `Genesis_Block`, 
     *  which requires they keep prepare and precommit Quorum Certificate(QC) for the same block.
     *  To enter view 1, they will send a New View message `getInitalMsg(id)`.
     *  
     */
    ghost predicate ReplicaInit(r : ReplicaState, id : Address)
    {
        NoOuterClient();    // ensures param `id` is in the set of all nodes
        && r.id == id
        && r.bc == [M_SpecTypes.Genesis_Block]
        && r.viewNum == 1
        && r.prepareQC == getInitialQC(MT_Prepare)
        && r.lockedQC == getInitialQC(MT_PreCommit)
        && r.msgReceived == {}
        && r.msgSent == {getInitialMsg(id)}
    }

    /**
     * Consider this as a big step of state transition.
     * A current state (@param:r) receives many messages (@param:inMsg), 
     * and then transfer to another state (@param:r') by many single actions defined in @Func:ReplicaNextSubStep,
     * sending out messages (@param:outMsg) during making those transitions.
     */
    ghost predicate ReplicaNext(
        r : ReplicaState,
        inMsg : set<Msg>,
        r' : ReplicaState,
        outMsg : set<Msg>
        )
    requires ValidReplicaState(r)
    {
        var allMsgReceived := r.msgReceived + inMsg;
        var replicaWithNewMsgReceived := r.(
            msgReceived := allMsgReceived
        );
        exists s : seq<ReplicaState>, o : seq<set<Msg>> ::
                && |s| >= 2
                && |o| == |s| - 1
                && s[0] == replicaWithNewMsgReceived
                && s[|s|-1] == r'
                && (forall i | 0 <= i < |s| - 1 ::
                    && ValidReplicaState(s[i])
                    && ReplicaNextSubStep(s[i], s[i+1], o[i])
                )
                && outMsg == setUnionOnSeq(o)

    }

    /**
     *  All different state transitions.
     *  Current state (@param:r) could transfer to the next state (@param:r'),
     *  together with sending out messages (@param:outMsg)
     */
    ghost predicate ReplicaNextSubStep(
        r : ReplicaState, 
        r' : ReplicaState, 
        outMsg : set<Msg>
        )
    requires ValidReplicaState(r)
    {
        || UponNextView(r, r', outMsg)
        || UponPrepare(r, r', outMsg)
        || UponPreCommit(r, r', outMsg)
        || UponCommit(r, r', outMsg)
        || UponDecide(r, r', outMsg)
        || UponTimeOut(r, r', outMsg)
    }


    // Refactor for outMsg (28/11/2025)
    predicate UponPrepare(r : ReplicaState, r' : ReplicaState, outMsg: set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        var isVoted := isVotedInView(r.msgSent, MT_Prepare, r.viewNum);
        if leader == r.id // Leader
        then
            var matchProposals := getMatchProposalMsg(r.msgReceived, r.viewNum);
            var votes := if r.lockedQC.viewNum < r.viewNum
                         then getVotesForSafeProposals(matchProposals, r.lockedQC, r.id)
                         else {};
            var filteredVotes := proposalVoteFilter(votes);
            var filteredVotes := onlyOneVote(filteredVotes);
            var filteredVotes := getVotesIfUnVoted(filteredVotes, isVoted);
            var matchMsgs := getMatchMsg(r.msgReceived, MT_NewView, r.viewNum-1);
            // if |matchMsgs| > 0
            if |matchMsgs| >= quorum(|M_SpecTypes.All_Nodes|)
            then
                var highQC := getHighQC(matchMsgs);
                var proposal := getNewBlock(highQC.block);
                var proposeMsg := Msg(r.id, MT_Prepare, r.viewNum, proposal, highQC, SigNone, CertNone);
                && outMsg == filteredVotes + {proposeMsg}
                && r' == r.(msgSent := r.msgSent + filteredVotes + {proposeMsg})
            else
                && outMsg == filteredVotes
                && r' == r.(msgSent := r.msgSent + filteredVotes)
        else
            var matchProposals := getMatchProposalMsg(r.msgReceived, r.viewNum);
            var votes := if r.lockedQC.viewNum < r.viewNum
                         then getVotesForSafeProposals(matchProposals, r.lockedQC, r.id)
                         else {};
            var filteredVotes := proposalVoteFilter(votes);
            var filteredVotes := onlyOneVote(filteredVotes);
            var filteredVotes := getVotesIfUnVoted(filteredVotes, isVoted);
            && outMsg == filteredVotes
            && r' == r.(msgSent := r.msgSent + outMsg)
    }

    ghost predicate UponPreCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        assert r.prepareQC.Cert? ==> ValidQC(r.prepareQC);
        var isVoted := isVotedInView(r.msgSent, MT_PreCommit, r.viewNum);
        if leader == r.id // Leader
        then
            // Leader doing leader and replica's work
            var matchQCs := getMatchQC(r.msgReceived, MT_PreCommit, MT_Prepare, r.viewNum);
            // if |matchQCs| > 0 
            if |matchQCs| == 1 
            then 
                var m_qc :| m_qc in matchQCs;
                var votes := {buildVoteMsg(r.id, MT_PreCommit, m_qc.block, CertNone, r.viewNum, CertNone, r.id)};
                var votes := getVotesIfUnVoted(votes, isVoted);
                var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_Prepare, r.viewNum);

                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet := getMaxLengthSet(splitSets);
                var filtedMaxSet := filterDoubleVote(maxSet);

                if |filtedMaxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in filtedMaxSet;
                    var sgns := ExtractSignatrues(filtedMaxSet);
                    var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                    var precommitMsg := Msg(r.id, MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone, CertNone);
                    && outMsg == votes + {precommitMsg}
                    && r' == r.(prepareQC := m_qc,
                                msgSent := r.msgSent + votes + {precommitMsg})
                else
                    && outMsg == votes
                    && r' == r.(prepareQC := m_qc,
                                msgSent := r.msgSent + votes)
            else    // Only doing leader's work
                var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_Prepare, r.viewNum);
                var splitSets := splitMsgByBlocks(matchMsgs);
                var maxSet := getMaxLengthSet(splitSets);
                var filtedMaxSet := filterDoubleVote(maxSet);

                if |filtedMaxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    var m :| m in filtedMaxSet;
                    var sgns := ExtractSignatrues(filtedMaxSet);
                    var prepareQC := Cert(MT_Prepare, m.viewNum, m.block, sgns);
                    var precommitMsg := Msg(r.id, MT_PreCommit, r.viewNum, EmptyBlock, prepareQC, SigNone, CertNone);

                    && outMsg == {precommitMsg}
                    && r' == r.(msgSent := r.msgSent + {precommitMsg})
                else
                    && r' == r
                    && outMsg == {}
        else    // Only doing replica's work
            var matchQCs := getMatchQC(r.msgReceived, MT_PreCommit, MT_Prepare, r.viewNum);
            // if |matchQCs| > 0 
            if |matchQCs| == 1 
            then 
                var m_qc :| m_qc in matchQCs;
                assert exists m | m in r.msgReceived
                                ::
                                  && ValidMsg(m)
                                  && m.justify == m_qc;
                                
                var votes := {buildVoteMsg(r.id, MT_PreCommit, m_qc.block, CertNone, r.viewNum, CertNone, r.id)};
                NoOuterClient();
                var votes := getVotesIfUnVoted(votes, isVoted);

                && outMsg == votes
                && r' == r.(prepareQC := m_qc,
                            msgSent := r.msgSent + votes)
                && ValidQC(r'.prepareQC)
            else 
                && outMsg == {}
                && r' == r
            
    }

    ghost predicate UponCommit(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        var isVoted := isVotedInView(r.msgSent, MT_Commit, r.viewNum);
        var matchQCs := getMatchQC(r.msgReceived, MT_Commit, MT_PreCommit, r.viewNum);
        if leader == r.id // Leader
        then
            // Leader doing leader and replica's work
            var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_PreCommit, r.viewNum);
            var splitSets := splitMsgByBlocks(matchMsgs);
            var maxSet := getMaxLengthSet(splitSets);
            // if |matchQCs| > 0 
            if |matchQCs| == 1
            then 
                var m_qc :| m_qc in matchQCs;
                var votes := {buildVoteMsg(r.id, MT_Commit, m_qc.block, CertNone, r.viewNum, CertNone, r.id)};
                var votes := getVotesIfUnVoted(votes, isVoted);
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var precommitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                    var commitMsg := Msg(r.id, MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone, CertNone);

                    && outMsg == votes + {commitMsg}
                    && r' == r.(lockedQC := m_qc,
                                msgSent := r.msgSent + votes + {commitMsg})
                else
                    && outMsg == votes
                    && r' == r.(lockedQC := m_qc,
                                msgSent := r.msgSent + votes)
            else    // Only doing leader's work
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|) && |maxSet| > 0
                then
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var precommitQC := Cert(MT_PreCommit, m.viewNum, m.block, sgns);
                    var commitMsg := Msg(r.id, MT_Commit, r.viewNum, EmptyBlock, precommitQC, SigNone, CertNone);
                    && outMsg == {commitMsg}
                    && r' == r.(msgSent := r.msgSent + {commitMsg})
                else
                    && r' == r
                    && outMsg == {}
        else    // Only doing replica's work
            // if |matchQCs| > 0 
            if |matchQCs| == 1
            then 
                var m_qc :| m_qc in matchQCs;
                var votes := {buildVoteMsg(r.id, MT_Commit, m_qc.block, CertNone, r.viewNum, CertNone, r.id)};
                var votes := getVotesIfUnVoted(votes, isVoted);
                && outMsg == votes
                && r' == r.(lockedQC := m_qc,
                            msgSent := r.msgSent + votes)
            else 
                && outMsg == {}
                && r' == r
    }

    ghost predicate UponDecide(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var leader := leader(r.viewNum);
        var matchMsgs := getMatchVoteMsg(r.msgReceived, MT_Commit, r.viewNum);
        var splitSets := splitMsgByBlocks(matchMsgs);
        var maxSet := getMaxLengthSet(splitSets);

        var matchQCs := getMatchQC(r.msgReceived, MT_Decide, MT_Commit, r.viewNum);

        if leader == r.id
        then
            if |matchQCs| > 0
            then
                var m_qc :| m_qc in matchQCs;
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var commitQC := Cert(MT_Commit, m.viewNum, m.block, sgns);
                    var decideMsg := Msg(r.id, MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone, CertNone);

                    && outMsg == {decideMsg}
                    && r' == r.(msgSent := r.msgSent + {decideMsg})
                    && var ancestors := getAncestors(m_qc.block);
                    && (
                        || (
                            && r.bc < ancestors
                            && r' == r.(bc := r.bc + ancestors[|r.bc|..])
                            )
                        || (
                            && r' == r
                            )
                    )
                else
                    && var ancestors := getAncestors(m_qc.block);
                    && (
                        || (
                            && r.bc < ancestors
                            && r' == r.(bc := r.bc + ancestors[|r.bc|..])
                            )
                        || (
                            && r' == r
                            )
                    )
                    && outMsg == {}
            else    // |matchQCs| <= 0
                if |maxSet| >= quorum(|M_SpecTypes.All_Nodes|)
                then
                    Axiom_Common_Constraints();
                    var m :| m in maxSet;
                    var sgns := ExtractSignatrues(maxSet);
                    var commitQC := Cert(MT_Commit, m.viewNum, m.block, sgns);
                    var decideMsg := Msg(r.id, MT_Decide, r.viewNum, EmptyBlock, commitQC, SigNone, CertNone);
                    && r' == r.(msgSent := r.msgSent + {decideMsg})
                    && outMsg == {decideMsg}
                else
                    && r' == r
                    && outMsg == {}
        else    // Not a leader
            if |matchQCs| > 0
            then
                var m_qc :| m_qc in matchQCs;
                var ancestors := getAncestors(m_qc.block);
                && (
                    || (
                        && r.bc < ancestors
                        && r' == r.(bc := r.bc + ancestors[|r.bc|..])
                        )
                    || (
                        && r' == r
                        )
                )
                && outMsg == {}
            else
                && r' == r
                && outMsg == {}
    }

    predicate UponTimeOut(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        UponNextView(r, r', outMsg)
    }

    predicate UponNextView(r : ReplicaState, r' : ReplicaState, outMsg : set<Msg>)
    requires ValidReplicaState(r)
    {
        var newViewMsg := Msg(r.id, MT_NewView, r.viewNum, EmptyBlock, r.prepareQC, SigNone, CertNone);
        assert r.viewNum >= r.prepareQC.viewNum;
        && r' == r.(viewNum := r.viewNum + 1,
                    msgSent := r.msgSent + {newViewMsg})
        && outMsg == {newViewMsg}
        
    } 


    /**
     * Invariants that a replica should hold at every state if it act honestly and correctly. 
     */
    ghost predicate ValidReplicaState(r : ReplicaState)
    {
        && r.viewNum > 0
        && Inv_PrepareQC(r)
        && Inv_LockedQC(r)
        && Inv_LocalBC(r)
        && Inv_ValidationOnMsgSent(r)
        && Inv_Votes(r)
        && Inv_LockHistory(r)
    }

    predicate Inv_PrepareQC(r : ReplicaState)
    // If a replica accepted a Prepare certificate,
    // then it must received a PreCommit Message from the leader before, together with a valid Prepare certificate,
    // or the prepare certificate is the initial certificate set up at the begining stage of the system
    {
        && ValidQC(r.prepareQC)
        && r.viewNum >= r.prepareQC.viewNum
        &&(r.prepareQC.Cert? ==>
                                && ValidQC(r.prepareQC)
                                && r.prepareQC.cType == MT_Prepare
                                && ( || (exists m | m in r.msgReceived
                                            ::
                                            && m.justify == r.prepareQC
                                            && ValidPrecommitRequest(m)
                                        )
                                     || isInitialQC(r.prepareQC)
                                )
            )
    }

    predicate Inv_LockedQC(r : ReplicaState)
    // Similar to invPrepareQC()
    {  
        && ValidQC(r.lockedQC)
        && r.viewNum >= r.lockedQC.viewNum
        && (r.lockedQC.Cert? ==>
                                && ValidQC(r.lockedQC)
                                && r.lockedQC.cType == MT_PreCommit
                                && (|| (exists m | m in r.msgReceived
                                            ::
                                            && m.justify == r.lockedQC
                                            && ValidCommitRequest(m))
                                    || isInitialQC(r.lockedQC)
                                )
        )
    }

    predicate LockedQCEvidence(msgReceived : set<Msg>, qc : Cert)
    {
        || isInitialQC(qc)
        || (exists m | m in msgReceived ::
                && ValidCommitRequest(m)
                && m.justify == qc)
    }

    predicate PrepareVoteEvidence(r : ReplicaState, vote : Msg)
    requires ValidPrepareVote(vote)
    {
        && ValidQC(vote.lockedQC)
        && vote.lockedQC.cType.MT_PreCommit?
        && vote.lockedQC.viewNum < vote.viewNum
        && LockedQCEvidence(r.msgReceived, vote.lockedQC)
        && (exists proposal | proposal in r.msgReceived ::
                && ValidProposal(proposal)
                && corrVoteMsgAndToVotedMsg(vote, proposal)
                && extension(proposal.block, proposal.justify.block)
                && safeNode(vote.block, proposal.justify, vote.lockedQC))
    }

    predicate Inv_LocalBC(r : ReplicaState)
    // Invariants of local blockchain
    // If a replica received a Decide Message with a valid certificate,
    // then it should always update its local blockchain accordingly.
    {
        && (|| r.bc == [M_SpecTypes.Genesis_Block]
            || (exists m | && m in r.msgReceived
                           && ValidDecideMsg(m)
                        ::
                           r.bc <= getAncestors(m.justify.block)
            )
        )
        && |r.bc| > 0
        && r.bc[0] == M_SpecTypes.Genesis_Block
    }

    predicate Inv_ValidationOnMsgSent(r : ReplicaState)
    {
        && (forall m | m in r.msgSent :: ValidMsg(m))
    }

    predicate Inv_Votes(r : ReplicaState)
    // Invariants about replica's vote
    {
        && (forall m | && m in r.msgSent
                       && ValidPrecommitVote(m)
                    :: 
                       exists m2 | m2 in r.msgReceived
                                ::
                                   && ValidPrecommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2))
        && (forall m | && m in r.msgSent
                       && ValidCommitVote(m)
                    :: 
                       exists m2 | m2 in r.msgReceived
                                ::
                                   && ValidCommitRequest(m2)
                                   && corrVoteMsgAndToVotedMsg(m, m2))
        && (forall m | && m in r.msgSent
                         && ValidPrepareVote(m)
                     :: PrepareVoteEvidence(r, m))
        && (forall m1, m2 | && m1 in r.msgSent
                            && m2 in r.msgSent
                            && ValidVoteMsg(m1)
                            && ValidVoteMsg(m2)
                         ::
                            (&& m1.viewNum == m2.viewNum
                             && m1.mType == m2.mType)
                            ==>
                            m1 == m2)
    }

    predicate Inv_LockHistory(r : ReplicaState)
    {
        && r.lockedQC.Cert?
        && (forall vote |
                && vote in r.msgSent
                && ValidVoteMsg(vote)
            :: vote.viewNum <= r.viewNum)
        && (forall commitVote |
                && commitVote in r.msgSent
                && ValidCommitVote(commitVote)
            :: commitVote.viewNum <= r.lockedQC.viewNum)
        && (forall commitVote, prepareVote |
                && commitVote in r.msgSent
                && ValidCommitVote(commitVote)
                && prepareVote in r.msgSent
                && ValidPrepareVote(prepareVote)
                && commitVote.viewNum < prepareVote.viewNum
            :: commitVote.viewNum <= prepareVote.lockedQC.viewNum)
    }

    function getMsgReceiveReplica(r : ReplicaState) : (m : set<Msg>)
    {
        r.msgReceived
    }

    function getMsgSentReplica(r : ReplicaState) : (m : set<Msg>)
    {
        r.msgSent
    }

    function getReplicaID(r : ReplicaState) : (id : Address)
    { 
        r. id
    }

}
