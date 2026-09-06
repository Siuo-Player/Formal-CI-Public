import Mathlib
import FiniteBridge.ConcreteRunnerRefinement
import FiniteBridge.ExecutableTargetSearchResult

namespace FiniteBridge

/-! 
G7 benchmark/oracle correspondence for the first machine-readable fixtures.

The oracle below is deliberately a separate bounded path enumerator.  It does
not inspect `executableRun` or reuse the frontier implementation.  This gives
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


def forbiddenTransition (r : Transition n) (forbidden : Finset (State n))
    : Transition n :=
  fun a b => a ∉ forbidden ∧ b ∉ forbidden ∧ r a b

/-- V01: START → FOREST → BRIDGE → TOWER. -/
def v01CorrespondenceTransition : Transition 4 :=
  fun a b =>
    (a.val = 0 ∧ b.val = 1) ∨
    (a.val = 1 ∧ b.val = 2) ∨
    (a.val = 2 ∧ b.val = 3)

/-- E01: START → FOREST → TOWER, with FOREST excluded by admissibility. -/
def e01CorrespondenceTransition : Transition 3 :=
  fun a b =>
    (a.val = 0 ∧ b.val = 1) ∨
    (a.val = 1 ∧ b.val = 2)

/-- D01 v1: two valid branches from START to TOWER. -/
def d01CorrespondenceTransitionV1 : Transition 4 :=
  fun a b =>
    (a.val = 0 ∧ b.val = 1) ∨
    (a.val = 1 ∧ b.val = 3) ∨
    (a.val = 0 ∧ b.val = 2) ∨
    (a.val = 2 ∧ b.val = 3)

/-- D01 v2 removes NORTH (state 1) from admissible transitions. -/
def d01CorrespondenceTransitionV2 : Transition 4 :=
  forbiddenTransition d01CorrespondenceTransitionV1 ({1} : Finset (State 4))

instance e01Decidable : DecidableRel e01CorrespondenceTransition := by
  intro a b
  dsimp [e01CorrespondenceTransition]
  infer_instance

instance d01v1Decidable : DecidableRel d01CorrespondenceTransitionV1 := by
  intro a b
  dsimp [d01CorrespondenceTransitionV1]
  infer_instance

instance d01v2Decidable : DecidableRel d01CorrespondenceTransitionV2 := by
  intro a b
  dsimp [d01CorrespondenceTransitionV2, forbiddenTransition]
  infer_instance

instance v01Decidable : DecidableRel v01CorrespondenceTransition := by
  intro a b
  dsimp [v01CorrespondenceTransition]
  infer_instance

/-!
Canonical fixture correspondence:

* V01 maps START/FOREST/BRIDGE/TOWER to 0/1/2/3.
* E01 maps START/FOREST/TOWER to 0/1/2.
* D01 maps START/NORTH/SOUTH/TOWER to 0/1/2/3.

The forbidden-state condition for E01 is represented by a separate admissible
transition relation; the D01 delta is represented by the same construction
with NORTH forbidden in v2.
-/

def v01Start : State 4 := 0
def v01Target : State 4 := 3

def e01BaseTransition : Transition 3 := e01CorrespondenceTransition

def e01AdmissibleTransition : Transition 3 :=
  forbiddenTransition e01BaseTransition ({1} : Finset (State 3))

def e01Start : State 3 := 0
def e01Target : State 3 := 2

def d01Start : State 4 := 0
def d01Target : State 4 := 3

instance e01AdmissibleDecidable : DecidableRel e01AdmissibleTransition := by
  intro a b
  dsimp [e01AdmissibleTransition, forbiddenTransition]
  infer_instance

example : oracleReachable v01CorrespondenceTransition 3 v01Start v01Target = true := by
  native_decide

example : oracleReachable e01AdmissibleTransition 3 e01Start e01Target = false := by
  native_decide

example : oracleReachable d01CorrespondenceTransitionV1 2 d01Start d01Target = true := by
  native_decide

example : oracleReachable d01CorrespondenceTransitionV2 2 d01Start d01Target = true := by
  native_decide

example : oracleReachable v01CorrespondenceTransition 2 v01Start v01Target = false := by
  native_decide

/-! Search/oracle agreement is checked on the concrete formal fixtures.
The two classifiers are separate computations; the equality below is a fixture
level correspondence statement, not a theorem about arbitrary engines.
-/

example :
    SearchState.executableTargetSearchResult
      (r := v01CorrespondenceTransition) v01Start v01Target =
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
S01 is intentionally not represented as a positive correspondence.  Its
abstract path exists while no concrete A-to-D path exists, so an abstraction
result must not be promoted to concrete realizability.
-/

def s01ConcreteTransition : Transition 4 :=
  fun a b =>
    (a.val = 0 ∧ b.val = 1) ∨
    (a.val = 2 ∧ b.val = 3)

def s01Start : State 4 := 0
def s01Target : State 4 := 3

instance s01Decidable : DecidableRel s01ConcreteTransition := by
  intro a b
  dsimp [s01ConcreteTransition]
  infer_instance

example : oracleReachable s01ConcreteTransition 3 s01Start s01Target = false := by
  native_decide

end FiniteBridge
