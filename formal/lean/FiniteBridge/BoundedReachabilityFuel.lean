import Mathlib
import FiniteBridge.Foundations

namespace FiniteBridge

/-- Reachability witnessed using at most `fuel` transition steps.  Extra fuel is
allowed: reflexive reachability remains available at every budget. -/
inductive ReachWithin {n : Nat} (r : Transition n) (start : State n) :
    Nat → State n → Prop
  | self (fuel : Nat) : ReachWithin r start fuel start
  | step {fuel : Nat} {current target : State n} :
      ReachWithin r start fuel current → r current target →
      ReachWithin r start (fuel + 1) target

namespace ReachWithin

variable {n : Nat} {r : Transition n} {start target current : State n}

/-- Increasing the fuel budget preserves bounded reachability. -/
theorem monotone {fuel extra : Nat} :
    ReachWithin r start fuel target →
    ReachWithin r start (fuel + extra) target := by
  intro h
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        monotone (extra := extra) (by simpa [Nat.add_assoc] using h)

/-- Every fuel-bounded reach is ordinary reflexive-transitive reachability. -/
theorem to_reflTransGen :
    ReachWithin r start fuel target → Relation.ReflTransGen r start target := by
  intro h
  induction h with
  | self fuel => exact Relation.ReflTransGen.refl
  | @step fuel current target hreach hstep ih =>
      exact Relation.ReflTransGen.tail ih hstep

end ReachWithin

end FiniteBridge
