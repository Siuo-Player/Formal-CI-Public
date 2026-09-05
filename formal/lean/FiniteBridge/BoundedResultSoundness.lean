import FiniteBridge.ResultSemantics

namespace FiniteBridge

theorem found_result_exists_witness
    {Witness : Type} {witness : Witness} :
    ∃ w, SearchResult.found witness = (SearchResult.found w : SearchResult Witness) := by
  exact ⟨witness, rfl⟩

theorem provedEmpty_result_has_no_witness
    {Witness : Type} :
    ¬ ∃ w, SearchResult.found w = (SearchResult.provedEmpty : SearchResult Witness) := by
  exact provedEmpty_has_no_witness

end FiniteBridge
