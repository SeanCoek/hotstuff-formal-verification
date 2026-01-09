
/**
 @Module Name : M_SpecTypes
 @Description : Type system for HotStuff
 */
module M_SpecTypes {

  type {:extern "Address"} Address(==,!new)
  type {:extern "Hash"} Hash(==,!new)


  datatype Block = Block(parent : Block) | EmptyBlock

  type Blockchain = seq<Block>


  datatype Cert = Cert(
                    cType : MsgType,
                    viewNum : nat,
                    block : Block,
                    signatures : set<Signature>
                  ) | CertNone

  datatype Signature = Signature(
                         signer : Address,
                         mType : MsgType,
                         viewNum : nat,
                         block : Block
                       ) | SigNone

  datatype MsgType = MT_NewView | MT_Prepare | MT_PreCommit | MT_Commit | MT_Decide



  datatype Msg = Msg(
    sender : Address,
    mType : MsgType,
    viewNum : nat,
    block : Block,
    justify : Cert,
    partialSig : Signature,
    lockedQC : Cert
  )

  datatype MsgWithRecipient = MsgWithRecipient(
    msg : Msg,
    recipient : Address
  )

  const Honest_Nodes : set<Address>

  const Adversary_Nodes : set<Address>

  const All_Nodes : set<Address> := Honest_Nodes + Adversary_Nodes

  const Genesis_Block : Block

  datatype Configuration = Configuration(
    honestNodes : set<Address>,
    adversaryNodes : set<Address>,
    nodes : set<Address> := honestNodes + adversaryNodes,   // all the nodes, containing byzantine nodes
    genesisBlock : Block
  )
}