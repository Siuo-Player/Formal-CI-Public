import FiniteBridge.ResultSemantics

namespace FiniteBridge

/-- A boundary covers every witness satisfying the validity predicate. -/
def CoversAll {Witness : Type} (boundary valid : Witness → Prop) : Prop :=
  ∀ w, valid w → boundary w

/-- No valid witness occurs inside the searched boundary. -/
def BoundaryEmpty {Witness : Type} (boundary valid : Witness → Prop) : Prop :=
  ¬ ∃ w, boundary w ∧ valid w

/-- Exhaustion of a complete boundary turns an empty search into global emptiness. -/
theorem complete_boundary_no_witness
    {Witness : Type} {boundary valid : Witness → Prop}
    (hcover : CoversAll boundary valid)
    (hempty : BoundaryEmpty boundary valid) :
    ¬ ∃ w, valid w := by
  intro hvalid
  rcases hvalid with ⟨w, hw⟩
  exact hempty ⟨w, hcover w hw, hw⟩

/-- A result classified as proved-empty is sound when a complete empty boundary
    has already ruled out every valid witness. -/
def ProvedEmptySound {Witness : Type}
    (valid : Witness → Prop) (result : SearchResult Witness) : Prop :=
  result = SearchResult.provedEmpty → ¬ ∃ w, valid w

/-- Complete coverage plus boundary emptiness makes a proved-empty result sound. -/
theorem provedEmpty_sound_of_complete_boundary
    {Witness : Type} {boundary valid : Witness → Prop}
    (hcover : CoversAll boundary valid)
    (hempty : BoundaryEmpty boundary valid) :
    ProvedEmptySound valid (SearchResult.provedEmpty : SearchResult Witness) := by
  intro _
  exact complete_boundary_no_witness hcover hempty

end FiniteBridge
