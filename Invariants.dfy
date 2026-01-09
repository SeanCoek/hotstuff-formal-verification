include "Type.dfy"
include "Auxilarily.dfy"


module M_Invariants {
    import opened M_SpecTypes
    import opened M_AuxilarilyFunc

    predicate Inv_Node_Constraint()
    {   
        && |M_SpecTypes.All_Nodes| > 0
        && |Adversary_Nodes| <= f(|All_Nodes|)
        && M_SpecTypes.Honest_Nodes * M_SpecTypes.Adversary_Nodes == {}
    }

}