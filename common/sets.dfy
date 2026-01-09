

module M_Set {

    import opened Std.Collections.Set

    lemma LemmaProperSubsetCardinality<T>(x: set<T>, y:set<T>)
    requires x < y
    ensures |x| < |y|
    {
        // if (x != {}) {
        //     var e :| e in x;
        //     LemmaProperSubsetCardinality(x-{e}, y-{e});
        // }
        Set.LemmaSubsetSize(x, y);
    }

    lemma LemmaSubsetCardinality<T> (x: set<T>, y:set<T>)
    ensures x < y ==> |x| < |y| // Strangely Dafny can't prove this. HAVE TO prove it by our own
    ensures x <= y ==> |x| <= |y| 
    {
        // if (x < y) {
        //     LemmaProperSubsetCardinality(x, y);
        // }
        // if (x == y) {
        //     // OBSERVE
        // }
        Set.LemmaSubsetSize(x, y);
    }

    lemma LemmaAdditiveOnSeparateSet<T> (s: set<T>, x: set<T>, y: set<T>)
    requires x * y == {}
    requires s == x + y
    ensures s - x == y
    {
        if (x != {} && y != {})
        {
            forall e | e in s - x
            ensures e in y {

            }
            assert |s-x| == |y|;
            // LemmaSetEquivlent(s-x, y);
            Set.LemmaSubsetEquality(s-x, y);
            assert s - x == y;
        }
        else
        {
            //OBSERVE
        }
    }

    lemma LemmaSetEquivlent<T> (x: set<T>, y: set<T>)
    requires forall e | e in x :: e in y
    requires |x| == |y|
    ensures x == y
    {
        // if (x == {})
        // {
        //     //OBSERVE
        // }
        // else {
        //     var e :| e in x;
        //     LemmaSetEquivlent(x-{e}, y-{e});
        // }
        Set.LemmaSubsetEquality(x, y);
    }

    lemma LemmaSubsetTransitive<T> (x : set<T>, y : set<T>, z : set<T>)
    requires x <= y && y <= z
    ensures x <= z
    {}

    lemma LemmaSetEqualityTransitive<T> (x : set<T>, y : set<T>, z : set<T>)
    requires x == y && y == z
    ensures x == z
    {}


    lemma LemmaTest<T> (x: set<T>, y: set<T>)
    requires x < y
    ensures |x| < |y|
    {
        Set.LemmaSubsetSize(x, y);
    }

    ghost predicate isTotoalOrder<T(!new)> (R : (T, T) -> bool)
    {
        && (forall x :: R(x, x))
        && (forall x, y :: R(x, y) && R(y, x) ==> x == y)
        && (forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z))
        && (forall x, y :: R(x, y) || R(y, x))
    }

    // function setToSeq<T(!new)> (s : set<T>, R : (T, T) -> bool) : (r : seq<T>)
    // requires isTotoalOrder(R)
    // ensures forall i | 0 <= i < |r| :: r[i] in s
    // ensures forall e | e in s :: e in r
    // {
    //     if s == {} then []
    //     else

    // }

    lemma setEqualityTest<T>(s1 : set<T>, s2 : set<T>, p : T -> bool)
    requires s1 == s2
    ensures (forall e | e in s1 
                    :: p(e))
            ==>
            (forall e | e in s2
                    :: p(e))
    {}

}