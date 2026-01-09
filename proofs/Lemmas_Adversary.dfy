include "../specs/Replica.dfy"
include "../specs/Adversary.dfy"
include "../specs/System.dfy"
include "../specs/Type.dfy"
include "../specs/Auxilarily.dfy"
include "Axioms.dfy"
include "../common/proofs.dfy"

module M_Lemmas_Adversary {

    import opened M_Replica
    import opened M_Adversary
    import opened M_System
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc
    import opened M_Axiom
    import opened M_ProofTactic
}