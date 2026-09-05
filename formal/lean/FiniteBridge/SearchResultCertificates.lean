import Mathlib
import FiniteBridge.ResultSemantics

namespace FiniteBridge

/-- A search result is sound when every reported witness is valid and a proved-empty
result really means that no valid witness exists. `UNKNOWN` makes no claim. -/
def SearchResultSound {Witness : Type} (valid : Witness → Prop)
    (result : SearchResult Witness) : Prop :=
  match result with
  | SearchResult.found witness => valid witness
  | SearchResult.provedEmpty => ¬ ∃ w, valid w
  | SearchResult.unknown => True

/-- A finite boundary covers the validity predicate when every valid witness occurs in it. -/
def CoversValid {Witness : Type} (valid : Witness → Prop)
    (boundary : Finset Witness) : Prop :=
  ∀ w, valid w → w ∈ boundary

/-- A finite boundary is empty of valid witnesses. -/
def BoundaryHasNoValid {Witness : Type} (valid : Witness → Prop)
    (boundary : Finset Witness) : Prop :=
  ∀ w, w ∈ boundary → ¬ valid w

/-- A found result is sound when its reported witness satisfies the validity predicate. -/
theorem found_searchResultSound
    {Witness : Type} {valid : Witness → Prop} {witness : Witness} :
    valid witness →
      SearchResultSound valid (SearchResult.found witness) := by
  intro hvalid
  exact hvalid

/-- If a finite boundary covers every valid witness and contains no valid witness,
then the corresponding proved-empty claim is sound. -/
theorem provedEmpty_searchResultSound
    {Witness : Type} {valid : Witness → Prop}
    {boundary : Finset Witness}
    (hcover : CoversValid valid boundary)
    (hempty : BoundaryHasNoValid valid boundary) :
    SearchResultSound valid (SearchResult.provedEmpty : SearchResult Witness) := by
  intro hvalid
  rcases hvalid with ⟨w, hw⟩
  exact hempty w (hcover w hw) hw

/-- `UNKNOWN` is always sound because it intentionally asserts no existence or
non-existence claim about valid witnesses. -/
theorem unknown_searchResultSound
    {Witness : Type} {valid : Witness → Prop} :
    SearchResultSound valid (SearchResult.unknown : SearchResult Witness) := by
  trivial

end FiniteBridge
