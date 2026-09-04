import FiniteBridge.ResultSemantics

namespace FiniteBridge

def boundedResult (completeBoundary : Bool) (foundWitness : Bool) :
    SearchResult Nat :=
  if foundWitness then
    SearchResult.found 0
  else if completeBoundary then
    SearchResult.provedEmpty
  else
    SearchResult.unknown

theorem bounded_failure_below_complete_boundary_is_unknown :
    boundedResult false false = (SearchResult.unknown : SearchResult Nat) := by
  rfl

theorem bounded_failure_at_complete_boundary_is_provedEmpty :
    boundedResult true false = (SearchResult.provedEmpty : SearchResult Nat) := by
  rfl

theorem found_result_has_witness :
    boundedResult false true = (SearchResult.found 0 : SearchResult Nat) := by
  rfl

end FiniteBridge
