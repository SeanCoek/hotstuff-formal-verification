include "Type.dfy"
include "Auxilarily.dfy"

module M_Axiom {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    lemma{:axiom} Axiom_Common_Constraints()
    ensures All_Nodes != {}

    lemma{:axiom} Axiom_Byz_Constraints()
    ensures |Adversary_Nodes| <= f(|All_Nodes|)
    ensures Adversary_Nodes * Honest_Nodes == {}

    lemma{:axiom} NoOuterClient()
    ensures forall id : Address :: id in All_Nodes

}