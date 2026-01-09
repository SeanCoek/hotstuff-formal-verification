// include "sets.dfy"
include "../Auxilarily.dfy"
module M_ProofTactic
{
    import opened M_Set
    import opened M_AuxilarilyFunc

    lemma LemmaSubsetTransitiveInSeq<T> (s : seq<set<T>>)
    requires |s| > 0
    requires forall i | 0 <= i < |s|-1 :: s[i] <= s[i+1]
    ensures forall i | 0 <= i <= |s|-1 :: s[0] <= s[i]
    {
        forall i | 0 <= i <= |s|-1
        ensures s[0] <= s[i] {
            if i == 0 {

            }
            else
            {
                LemmaSubsetTransitiveInSeq(s[1..]);
            }
        }
    }

    lemma LemmaSetEqualityTransitiveInSeq<T> (s : seq<set<T>>)
    requires |s| > 0
    requires forall i | 0 <= i < |s|-1 :: s[i] == s[i+1]
    ensures forall i | 0 <= i <= |s|-1 :: s[0] == s[i]
    ensures forall i, j | && 0 <= i <= |s|-1
                          && 0 <= j <= |s|-1
                        ::
                          s[i] == s[j]
    {
        forall i | 0 <= i <= |s|-1
        ensures s[0] == s[i] {
            if |s| == 1 {
            }
            else
            {
                LemmaSetEqualityTransitiveInSeq(s[1..]);
            }
        }
    }

    lemma LemmaSeqCumulative<T> (a : seq<set<T>>, b : seq<set<T>>)
    requires |b| > 0
    requires |a| == |b| + 1
    requires forall i | 0 < i < |a| :: a[i] == a[i-1] + b[i-1]
    ensures a[|a|-1] == a[0] + setUnionOnSeq(b)
    {
        if |b| == 1
        {
        }
        else 
        {
            LemmaSeqCumulative(a[1..], b[1..]);
        }
    }

    predicate prepareImp1<T> (outMsg : set<T>)
    {
        forall vote | vote in outMsg ::
                                && outMsg == {vote}
    }

    predicate prepareImp2<T> (outMsg : set<T>)
    {
        var votes := outMsg;
        outMsg == votes
    }

    lemma LemmaRefactorTest<T> (outMsg : set<T>)
    requires prepareImp1(outMsg)
    ensures prepareImp2(outMsg)
    {
        // assert |outMsg| <= 1;
    }

    lemma LemmaEqualityTransitiveInSeq<T> (s : seq<T>)
    requires |s| > 0
    requires forall i | 0 <= i < |s|-1 :: s[i] == s[i+1]
    ensures forall i | 0 <= i <= |s|-1 :: s[0] == s[i]
    ensures forall i, j | && 0 <= i <= |s|-1
                          && 0 <= j <= |s|-1
                        ::
                          s[i] == s[j]
    {
        forall i | 0 <= i <= |s|-1
        ensures s[0] == s[i] {
            if |s| == 1 {
            }
            else
            {
                LemmaEqualityTransitiveInSeq(s[1..]);
            }
        }
    }

}