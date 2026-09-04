import Mathlib
import FiniteBridge.SemanticExactness

namespace FiniteBridge

/-- Restricted reachability for the strict natural-number chain. -/
def ChainReachable (source target : Nat) : Prop :=
  Relation.ReflTransGen ChainEdge source target

theorem chainReachable_to_le
    (source target : Nat)
    (h : ChainReachable source target) :
    source ≤ target := by
  induction h with
  | refl => exact Nat.le_refl source
  | tail hreach hstep ih =>
      exact Nat.le_trans ih (Nat.le_of_lt hstep)

theorem le_to_chainReachable
    (source target : Nat)
    (h : source ≤ target) :
    ChainReachable source target := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single hlt

/-- The reflexive-transitive closure of the strict chain is exactly `≤`. -/
theorem chainReachable_iff_le
    (source target : Nat) :
    ChainReachable source target ↔ source ≤ target := by
  constructor
  · exact chainReachable_to_le source target
  · exact le_to_chainReachable source target

example : ChainReachable 2 5 := by
  exact le_to_chainReachable 2 5 (by decide)

example : ¬ ChainReachable 5 2 := by
  intro h
  have hle := chainReachable_to_le 5 2 h
  omega

end FiniteBridge
