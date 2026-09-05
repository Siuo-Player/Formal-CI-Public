import FiniteBridge.ResultSemantics
namespace FiniteBridge
example {Witness : Type} {witness : Witness} : ∃ w, SearchResult.found witness = (SearchResult.found w : SearchResult Witness) := by exact ⟨witness, rfl⟩
end FiniteBridge
