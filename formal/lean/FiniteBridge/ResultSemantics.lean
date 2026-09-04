namespace FiniteBridge

inductive SearchResult (Witness : Type)
  | found (witness : Witness)
  | provedEmpty
  | unknown
  deriving Repr

theorem found_ne_provedEmpty
    {Witness : Type} {witness : Witness} :
    SearchResult.found witness ≠ SearchResult.provedEmpty := by
  intro h
  cases h

theorem provedEmpty_has_no_witness
    {Witness : Type} :
    ¬ ∃ w, SearchResult.found w = (SearchResult.provedEmpty : SearchResult Witness) := by
  intro h
  rcases h with ⟨w, hw⟩
  exact found_ne_provedEmpty hw

end FiniteBridge
