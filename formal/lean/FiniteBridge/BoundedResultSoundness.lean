import FiniteBridge.ResultSemantics

namespace FiniteBridge

/-- A found search result carries a concrete witness. -/
theorem found_result_exists_witness
    {Witness : Type} {witness : Witness} :
    ∃ w, SearchResult.found witness = (SearchResult.found w : SearchResult Witness) := by
  exact ⟨witness, rfl⟩

/-- `provedEmpty` is disjoint from every witness-bearing result. -/
theorem provedEmpty_result_has_no_witness
    {Witness : Type} :
    ¬ ∃ w, SearchResult.found w = (SearchResult.provedEmpty : SearchResult Witness) := by
  exact provedEmpty_has_no_witness

end FiniteBridge
