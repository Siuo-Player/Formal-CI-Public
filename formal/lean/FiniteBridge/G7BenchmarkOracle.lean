import Mathlib
import FiniteBridge.ConcreteRunnerRefinement
import FiniteBridge.ExecutableTargetSearchResult

namespace FiniteBridge

/-!
G7 benchmark/oracle correspondence for the first machine-readable fixtures.

The oracle below is deliberately a separate bounded path enumerator. It does
not inspect `executableRun` or reuse the frontier implementation. This gives
us an independently structured executable classifier for tiny benchmark
instances before any claim is made about engine correspondence.
-/

def oracleReachable (r : Transition n) [DecidableRel r]
    : Nat → State n → State n → Bool
  | 0, start, target => decide (start = target)
  | fuel + 1, start, target =>
      if start = target then
        true
      else
        decide (∃ mid : State n, r start mid ∧ oracleReachable r fuel mid target = true)

/- The fixture relations are written as decidable propositions rather than
   matching on `Fin.val`, so Lean can synthesize executable decisions. -/
def v01TransitionG7 : Transition 4 :=
  fun a b =>
    (a = 0 ∧ b = 1) ∨
    (a = 1 ∧ b = 2) ∨
    (a = 2 ∧ b = 3)

def e01BaseTransition : Transition 3 :=
  fun a b =>
    (a = 0 ∧ b = 1) ∨
    (a = 1 ∧ b = 2)

def e01AdmissibleTransition : Transition 3 := fun _ _ => False

def d01CorrespondenceTransitionV1 : Transition 4 :=
  fun a b =>
    (a = 0 ∧ b = 1) ∨
    (a = 1 ∧ b = 3) ∨
    (a = 0 ∧ b = 2) ∨
    (a = 2 ∧ b = 3)

def d01CorrespondenceTransitionV2 : Transition 4 :=
  fun a b =>
    (a = 0 ∧ b = 2) ∨
    (a = 2 ∧ b = 3)

def s01ConcreteTransition : Transition 4 :=
  fun a b =>
    (a = 0 ∧ b = 1) ∨
    (a = 2 ∧ b = 3)

instance v01Decidable : DecidableRel v01TransitionG7 := by
  intro a b
  change Decidable ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3))
  infer_instance

instance e01Decidable : DecidableRel e01BaseTransition := by
  intro a b
  change Decidable ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))
  infer_instance

instance e01AdmissibleDecidable : DecidableRel e01AdmissibleTransition := by
  intro a b
  change Decidable False
  exact isFalse id

instance d01v1Decidable : DecidableRel d01CorrespondenceTransitionV1 := by
  intro a b
  change Decidable ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 3) ∨ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 3))
  infer_instance

instance d01v2Decidable : DecidableRel d01CorrespondenceTransitionV2 := by
  intro a b
  change Decidable ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 3))
  infer_instance

instance s01Decidable : DecidableRel s01ConcreteTransition := by
  intro a b
  change Decidable ((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3))
  infer_instance

/-!
Canonical fixture correspondence:

* V01 maps START/FOREST/BRIDGE/TOWER to 0/1/2/3.
* E01 maps START/FOREST/TOWER to 0/1/2. Its admissible relation is empty
  because the only two edges both touch the forbidden FOREST state.
* D01 maps START/NORTH/SOUTH/TOWER to 0/1/2/3. Version 2 removes NORTH and
  therefore retains only START -> SOUTH -> TOWER.
-/

def v01Start : State 4 := 0
def v01Target : State 4 := 3

def e01Start : State 3 := 0
def e01Target : State 3 := 2

def d01Start : State 4 := 0
def d01Target : State 4 := 3

def s01Start : State 4 := 0
def s01Target : State 4 := 3

example : oracleReachable v01TransitionG7 3 v01Start v01Target = true := by
  native_decide

example : oracleReachable e01AdmissibleTransition 3 e01Start e01Target = false := by
  native_decide

example : oracleReachable d01CorrespondenceTransitionV1 2 d01Start d01Target = true := by
  native_decide

example : oracleReachable d01CorrespondenceTransitionV2 2 d01Start d01Target = true := by
  native_decide

example : oracleReachable v01TransitionG7 2 v01Start v01Target = false := by
  native_decide

/-! Search/oracle agreement is checked on the concrete formal fixtures.
The two classifiers are separate computations; the equality below is a fixture
level correspondence statement, not a theorem about arbitrary engines.
-/

instance {α : Type} [DecidableEq α] : DecidableEq (SearchResult α) := by
  intro x y
  cases x with
  | found wx =>
      cases y with
      | found wy =>
          exact if h : wx = wy then isTrue (by cases h; rfl) else isFalse (by intro hxy; cases hxy; exact h rfl)
      | provedEmpty => exact isFalse (by intro hxy; cases hxy)
      | unknown => exact isFalse (by intro hxy; cases hxy)
  | provedEmpty =>
      cases y with
      | found wy => exact isFalse (by intro hxy; cases hxy)
      | provedEmpty => exact isTrue rfl
      | unknown => exact isFalse (by intro hxy; cases hxy)
  | unknown =>
      cases y with
      | found wy => exact isFalse (by intro hxy; cases hxy)
      | provedEmpty => exact isFalse (by intro hxy; cases hxy)
      | unknown => exact isTrue rfl

example :
    SearchState.executableTargetSearchResult
      (r := v01TransitionG7) v01Start v01Target =
      SearchResult.found v01Target := by
  native_decide

example :
    SearchState.executableTargetSearchResult
      (r := e01AdmissibleTransition) e01Start e01Target =
      SearchResult.provedEmpty := by
  native_decide

example :
    SearchState.executableTargetSearchResult
      (r := d01CorrespondenceTransitionV1) d01Start d01Target =
      SearchResult.found d01Target := by
  native_decide

example :
    SearchState.executableTargetSearchResult
      (r := d01CorrespondenceTransitionV2) d01Start d01Target =
      SearchResult.found d01Target := by
  native_decide

/-!
S01 is intentionally not represented as a positive correspondence. Its
abstract path exists while no concrete A-to-D path exists, so an abstraction
result must not be promoted to concrete realizability.
-/

example : oracleReachable s01ConcreteTransition 3 s01Start s01Target = false := by
  native_decide

end FiniteBridge
