import Mathlib
import FiniteBridge.ResultSemantics
import FiniteBridge.BoundedResult
import FiniteBridge.Dependency
import FiniteBridge.DependencyClosure
import FiniteBridge.SemanticDependency
import FiniteBridge.SemanticLocality
import FiniteBridge.SemanticExactness
import FiniteBridge.ChainReachability

namespace FiniteBridge

abbrev State (n : Nat) := Fin n

def Transition (n : Nat) := State n → State n → Prop

def SimplePath {n : Nat} (xs : List (State n)) : Prop := xs.Nodup

theorem simplePath_length_le_state_count
    {n : Nat} {xs : List (State n)}
    (hxs : SimplePath xs) : xs.length ≤ n := by
  simpa [SimplePath] using hxs.length_le_card

theorem simplePath_edge_count_le_state_count_sub_one
    {n : Nat} {xs : List (State n)}
    (hxs : SimplePath xs) (_hnonempty : xs ≠ []) : xs.length - 1 ≤ n - 1 := by
  have h := simplePath_length_le_state_count hxs
  omega

def TransitionValid {n : Nat} (r : Transition n) : List (State n) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => r a b ∧ TransitionValid r (b :: rest)

def BoundedWitness {n : Nat} (r : Transition n) (start target : State n) (xs : List (State n)) : Prop :=
  ∃ hne : xs ≠ [],
    xs.head hne = start ∧
    xs.getLast hne = target ∧
    SimplePath xs ∧
    TransitionValid r xs ∧
    xs.length - 1 ≤ n - 1

theorem boundedWitness_of_simplePath
    {n : Nat} {r : Transition n} {start target : State n}
    {xs : List (State n)}
    (hne : xs ≠ [])
    (hhead : xs.head hne = start)
    (hlast : xs.getLast hne = target)
    (hpath : SimplePath xs)
    (hvalid : TransitionValid r xs) :
    BoundedWitness r start target xs := by
  refine ⟨hne, hhead, hlast, hpath, hvalid, ?_⟩
  exact simplePath_edge_count_le_state_count_sub_one hpath hne

def v01Transition : Transition 4
  | a, b => match a.val, b.val with
    | 0, 1 => True
    | 1, 2 => True
    | 2, 3 => True
    | _, _ => False

example : SimplePath ([0, 1, 2, 3] : List (State 4)) := by
  simp [SimplePath]

example : TransitionValid v01Transition ([0, 1, 2, 3] : List (State 4)) := by
  simp [TransitionValid, v01Transition]

example : ([0, 1, 2, 3] : List (State 4)).length - 1 ≤ 4 - 1 := by
  decide

end FiniteBridge
