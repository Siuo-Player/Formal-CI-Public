import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- A one-state witness has zero edges. -/
theorem singleton_witness_has_zero_edges
    {n : Nat} {r : Transition n} {start target : State n}
    (xs : List (State n))
    (hw : BoundedWitness r start target xs)
    (hlen : xs.length = 1) :
    xs.length - 1 = 0 := by
  omega

/-- A bounded witness of singleton length has equal endpoints. -/
theorem singleton_witness_endpoints_equal
    {n : Nat} {r : Transition n} {start target : State n}
    (xs : List (State n))
    (hw : BoundedWitness r start target xs)
    (hlen : xs.length = 1) :
    start = target := by
  rcases hw with ⟨hne, hhead, hlast, _, _, _⟩
  cases xs with
  | nil => simp at hne
  | cons x tail =>
      cases tail with
      | nil =>
          simpa using hhead.symm.trans hlast
      | cons y ys =>
          simp at hlen

end FiniteBridge
