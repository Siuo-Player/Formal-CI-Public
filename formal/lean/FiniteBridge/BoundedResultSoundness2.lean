import FiniteBridge.ResultSemantics

namespace FiniteBridge

theorem found_result_exists_witness_2
    {Witness : Type} {witness : Witness} :
    ∃ w, SearchResult.found witness = (SearchResult.found w : SearchResult Witness) := by
  exact ⟨witness, rfl⟩

end FiniteBridge
