include "Type.dfy"
include "Adversary.dfy"
include "Replica.dfy"
include "Auxilarily.dfy"
include "Axioms.dfy"
include "Invariants.dfy"


/**
 @Module Name : M_System
 @Description : Definitions of system's state, behaviours, and invariants 
 */
module M_System {

    import opened M_SpecTypes
    import opened M_Replica
    import opened M_Adversary
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_Invariants

    /**
     * Definition of a system state
     * @param nodeStates -> a map storing node states, using node address as key
     * @param adversary -> structure for Byzantine nodes
     * @param msgSent -> all message sent by replicas
     */
    datatype SystemState = SystemState(
        nodeStates : map<Address, ReplicaState>,
        adversary : Adversary,
        msgSent : set<Msg>
    )

    /**
     * Replicas not in adversary are considered as an honest node
     * return `true` if and only if replica exists in the set of all nodes and not in the set of Byzantine nodes.
     */
    predicate IsHonest(ss : SystemState, r : Address)
    {
        r in ss.nodeStates.Keys - ss.adversary.byz_nodes
    }

    predicate Inv_Node_System(ss : SystemState)
    {
        && Inv_Node_Constraint()
        && Inv_ID_Consistent(ss)
        && ss.nodeStates.Keys == M_SpecTypes.All_Nodes
        && ss.adversary.byz_nodes == M_SpecTypes.Adversary_Nodes
    }

    predicate Inv_ID_Consistent(ss : SystemState)
    {
        forall r | r in ss.nodeStates.Keys :: ss.nodeStates[r].id == r
    }

    /**
     * Invariants that a system should hold at every reachable state in HotStuff. 
     */
    ghost predicate ValidSystemState(ss : SystemState)
    {
        NoOuterClient();
        && Inv_Node_System(ss)
        && (forall replica | replica in ss.nodeStates.Keys :: ss.nodeStates[replica].msgSent <= ss.msgSent)
        && (forall replica | IsHonest(ss, replica) :: ValidReplicaState(ss.nodeStates[replica]))
        && (forall replica | IsHonest(ss, replica) :: ss.nodeStates[replica].msgReceived <= ss.msgSent)
    }

    /**
     * Definitions of the initial state of a system
     */
    ghost predicate SystemInit(ss : SystemState)
    {
        && Inv_Node_System(ss)
        && ss.msgSent == getMultiInitialMsg(ss.nodeStates.Keys) // Each replica will send an initial message (defined in `Replica_Init`)
        && ss.nodeStates.Keys == M_SpecTypes.All_Nodes
        && (forall r | r in ss.nodeStates :: ReplicaInit(ss.nodeStates[r], r))
        && AdversaryInit(ss.adversary)
    }


    /**
     * Definiton of system state transition triggered by a particular node
     * @param ss -> current system state
     * @param ss' -> next system state
     * @param replica -> address of the node causing this state transition
     * @param inMsg -> messages recieved by this node
     * @param outMsg -> messages sent when state transition happens
     */
    ghost predicate SystemNextByOneReplica(
        ss : SystemState, 
        ss' : SystemState, 
        replica : Address, 
        inMsg : set<Msg>,
        outMsg : set<Msg>)
    requires ValidSystemState(ss)
    {
        && replica in ss.nodeStates.Keys
        // fixed set of replica
        && ss.nodeStates.Keys == ss'.nodeStates.Keys
        // separate different actions by replica's honesty
        && (
            if IsHonest(ss, replica) then
                // update the state for honest replica
                && ss'.nodeStates == ss.nodeStates[replica := ss'.nodeStates[replica]]
                && ss'.adversary == ss.adversary
                && ReplicaNext(ss.nodeStates[replica], inMsg, ss'.nodeStates[replica], outMsg)
            else
                // udpate states for adversary nodes
                && AdversaryNext(ss.adversary, inMsg, ss'.adversary, outMsg)
                && (forall r | r in ss.adversary.byz_nodes
                            :: 
                                var rState := ss.nodeStates[r];
                                var rState' := ss'.nodeStates[r];
                                rState' == rState.(msgReceived := rState.msgReceived + inMsg,
                                                   msgSent := rState.msgSent + outMsg)
                )
                && (forall r | IsHonest(ss, r)
                            :: ss'.nodeStates[r] == ss.nodeStates[r])
        )
        && ss.adversary.byz_nodes == ss'.adversary.byz_nodes
        && ss'.msgSent == ss.msgSent + outMsg
    }

    /**
     * Definitions of state transitions of a system
     * @param ss -> current system state
     * @param ss' -> next system state
     */
    ghost predicate SystemNext(ss : SystemState, ss' : SystemState)
    requires ValidSystemState(ss)
    {
        // System state stalls
        || ss == ss'
        // replica received messages and transmit to another state, which changes system state.
        || (exists replica, msgReceivedByNodes, msgSentByNodes
                   | msgReceivedByNodes <= ss.msgSent
                  :: SystemNextByOneReplica(ss, ss', replica, msgReceivedByNodes, msgSentByNodes))
    }
}