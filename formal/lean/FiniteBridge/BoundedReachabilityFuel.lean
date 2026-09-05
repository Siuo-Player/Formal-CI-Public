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
