import FiniteBridge.DependencyClosure

namespace FiniteBridge

/-- A node is semantically changed when its validity predicate differs between
before and after states. -/
def SemanticallyChanged
    (Before After : α → Prop) (node : α) : Prop :=
  ¬ StableUnderEdit Before After node

/-- Local change propagation: a changed node is either an edited seed or has a
changed predecessor. This is the exact semantic locality condition required to
connect a dependency graph with validity changes. -/
def LocallyPropagatesChange
    (Edge : α → α → Prop)
    (Before After : α → Prop)
    (Seeds : Set α) : Prop :=
  ∀ {node},
    SemanticallyChanged Before After node →
      node ∈ Seeds ∨
        ∃ pred, Edge pred node ∧ SemanticallyChanged Before After pred

/-- Under a well-founded dependency relation, local change propagation implies
that every semantic validity change lies in the dependency closure of an edited
seed. This is a semantic bridge theorem, rather than a restatement of graph
reachability: the new premise is the local semantic propagation property. -/
theorem semantically_changed_affected_of_wellFounded
    {α : Type}
    {Edge : α → α → Prop}
    (hWF : WellFounded Edge)
    {Before After : α → Prop}
    {Seeds : Set α}
    (hprop : LocallyPropagatesChange Edge Before After Seeds) :
    ∀ {node},
      SemanticallyChanged Before After node → Affected Edge Seeds node := by
  intro node hchanged
  induction node using hWF.induction with
  | h node ih =>
      rcases hprop hchanged with hseed | ⟨pred, hpred, hpred_changed⟩
      · exact affected_of_seed hseed
      · exact affected_of_affected_path
          (ih pred hpred hpred_changed)
          (Relation.ReflTransGen.single hpred)

end FiniteBridge
