

module M_Seq {
    import opened Std.Collections.Seq

    lemma Lemma_PrefixOfTwoPrefixSeqAlsoPrefix<T>(pre1 : seq<T>,
                                            pre2 : seq<T>,
                                            seq1 : seq<T>,
                                            seq2 : seq<T>)
    requires pre1 <= seq1
    requires pre2 <= seq2
    requires seq1 <= seq2 || seq2 <= seq1
    ensures pre1 <= pre2 || pre2 <= pre1
    {
    }
}