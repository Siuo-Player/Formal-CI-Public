import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Reachability using exactly `fuel` transition steps. -/
inductive ReachWithin {n : Nat} (r : Transition n) (start : State n) :
    Nat → State n → Prop
  | self : ReachWithin r start 0 start
  | step {fuel : Nat} {current target : State n} :
      ReachWithin r start fuel current → r current target →
      ReachWithin r start (fuel + 1) target

namespace ReachWithin

variable {n : Nat} {r : Transition n} {start target current : State n}

/-- Append a second exact-length reach to an existing exact-length reach. -/
theorem trans {fuel₁ fuel₂ : Nat}
    (h₁ : ReachWithin r start fuel₁ current)
    (h₂ : ReachWithin r current fuel₂ target) :
    ReachWithin r start (fuel₁ + fuel₂) target := by
  induction h₂ with
  | self => simpa using h₁
  | @step fuel current target hreach hstep ih =>
      simpa [Nat.add_assoc] using ReachWithin.step ih hstep

/-- Every exact-length reach is ordinary reflexive-transitive reachability. -/
theorem to_reflTransGen :
    ReachWithin r start fuel target → Relation.ReflTransGen r start target := by
  intro h
  induction h with
  | self => exact Relation.ReflTransGen.refl
  | @step fuel current target hreach hstep ih =>
      exact Relation.ReflTransGen.tail ih hstep

end ReachWithin

end FiniteBridge
