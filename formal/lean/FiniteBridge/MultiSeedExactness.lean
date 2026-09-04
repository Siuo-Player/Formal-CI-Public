import Mathlib
import FiniteBridge.SemanticExactness

namespace FiniteBridge

def ChainAfterSeeds (Seeds : Set Nat) : Nat → Prop :=
  fun node => ∃ seed, seed ∈ Seeds ∧ seed ≤ node

theorem chain_multiseed_affected_to_semantically_changed
    (Seeds : Set Nat) (node : Nat)
    (h : Affected ChainEdge Seeds node) :
    SemanticallyChanged ChainBefore (ChainAfterSeeds Seeds) node := by
  rcases h with ⟨seed, hseed, hpath⟩
  have hle : seed ≤ node := by
    induction hpath with
    | refl => exact Nat.le_refl seed
    | tail hpath hstep ih =>
        exact Nat.le_trans ih (Nat.le_of_lt hstep)
  exact by
    simp [SemanticallyChanged, StableUnderEdit, ChainBefore, ChainAfterSeeds]
    exact ⟨seed, hseed, hle⟩

theorem chain_multiseed_semantically_changed_to_affected
    (Seeds : Set Nat) (node : Nat)
    (h : SemanticallyChanged ChainBefore (ChainAfterSeeds Seeds) node) :
    Affected ChainEdge Seeds node := by
  have hex : ∃ seed, seed ∈ Seeds ∧ seed ≤ node := by
    simpa [SemanticallyChanged, StableUnderEdit, ChainBefore, ChainAfterSeeds]
      using h
  rcases hex with ⟨seed, hseed, hle⟩
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact affected_of_seed (Seeds := Seeds) (seed := seed) hseed
  · exact ⟨seed, hseed, Relation.ReflTransGen.single hlt⟩

/-- Exactness extends from one seed to arbitrary seed sets for this restricted
chain semantics. The dependency relation remains structural and independent
of the semantic-change predicate. -/
theorem chain_multiseed_affected_iff_semantically_changed
    (Seeds : Set Nat) (node : Nat) :
    Affected ChainEdge Seeds node ↔
      SemanticallyChanged ChainBefore (ChainAfterSeeds Seeds) node := by
  constructor
  · exact chain_multiseed_affected_to_semantically_changed Seeds node
  · exact chain_multiseed_semantically_changed_to_affected Seeds node

example :
    Affected ChainEdge ({2, 4} : Set Nat) 5 := by
  refine ⟨2, ?_, ?_⟩
  · simp
  · exact Relation.ReflTransGen.single (by decide)

example :
    SemanticallyChanged ChainBefore (ChainAfterSeeds ({2, 4} : Set Nat)) 5 := by
  simp [SemanticallyChanged, StableUnderEdit, ChainBefore, ChainAfterSeeds]
  exact ⟨2, by simp, by decide⟩

end FiniteBridge
