import FiniteBridge.ResultSemantics

namespace FiniteBridge

/--
Semantic result of a bounded search.
A concrete candidate yields a witness-bearing result; failure is only
classified as proved empty when the search boundary is complete.
-/
def boundedSearchResult {Witness : Type}
    (completeBoundary : Bool) (candidate : Option Witness) :
    SearchResult Witness :=
  match candidate with
  | some witness => SearchResult.found witness
  | none =>
      if completeBoundary then
        SearchResult.provedEmpty
      else
        SearchResult.unknown

theorem boundedSearchResult_found
    {Witness : Type} {completeBoundary : Bool} {witness : Witness} :
    boundedSearchResult completeBoundary (some witness) =
      SearchResult.found witness := by
  rfl

theorem boundedSearchResult_provedEmpty
    {Witness : Type} :
    boundedSearchResult true (none : Option Witness) =
      (SearchResult.provedEmpty : SearchResult Witness) := by
  rfl

theorem boundedSearchResult_unknown
    {Witness : Type} :
    boundedSearchResult false (none : Option Witness) =
      (SearchResult.unknown : SearchResult Witness) := by
  rfl

end FiniteBridge
