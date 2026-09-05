import FiniteBridge.SemanticDependency

namespace FiniteBridge

/-- The dependency relation may conservatively over-approximate semantic
influence. In this example every node is marked as affected, while the
before/after validity predicates are identical everywhere. -/
def OverApproxEdge : Bool → Bool → Prop :=
  fun _ _ => True

def EmptyBefore : Bool → Prop :=
  fun _ => False

def EmptyAfter : Bool → Prop :=
  fun _ => False

def SingleSeed : Set Bool :=
  {true}

theorem false_node_is_affected :
    Affected OverApproxEdge SingleSeed false := by
  refine ⟨true, ?_, ?_⟩
  · simp [SingleSeed]
  · exact Relation.ReflTransGen.single (by trivial)

theorem false_node_is_not_semantically_changed :
    ¬ SemanticallyChanged EmptyBefore EmptyAfter false := by
  intro hchanged
  apply hchanged
  simp [SemanticallyChanged, StableUnderEdit, EmptyBefore, EmptyAfter]

/-- Therefore the unrestricted converse
`Affected Edge Seeds node → SemanticallyChanged Before After node`
is false for arbitrary dependency relations. -/
theorem affected_does_not_imply_semantically_changed :
    ¬ (∀ {α : Type} (Edge : α → α → Prop)
        (Before After : α → Prop) (Seeds : Set α) (node : α),
        Affected Edge Seeds node →
          SemanticallyChanged Before After node) := by
  intro h
  have ha := h OverApproxEdge EmptyBefore EmptyAfter SingleSeed false
    false_node_is_affected
  exact false_node_is_not_semantically_changed ha

end FiniteBridge
