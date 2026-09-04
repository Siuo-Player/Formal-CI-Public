import Mathlib

namespace FiniteBridge

def DependsOn (Edge : α → α → Prop) (seed node : α) : Prop :=
  Relation.ReflTransGen Edge seed node

def Affected (Edge : α → α → Prop) (Seeds : Set α) (node : α) : Prop :=
  ∃ seed, seed ∈ Seeds ∧ DependsOn Edge seed node

theorem affected_of_direct_dependency
    {α : Type} {Edge : α → α → Prop} {Seeds : Set α} {seed node : α}
    (hseed : seed ∈ Seeds) (hedge : Edge seed node) :
    Affected Edge Seeds node := by
  refine ⟨seed, hseed, Relation.ReflTransGen.single hedge⟩

theorem backward_node_affected
    {α : Type} {Edge : α → α → Prop}
    {Seeds : Set α} {seed node : α}
    (hseed : seed ∈ Seeds)
    (hpath : DependsOn Edge seed node) :
    Affected Edge Seeds node :=
  ⟨seed, hseed, hpath⟩

def StableUnderEdit
    (Before After : α → Prop) (node : α) : Prop :=
  Before node ↔ After node

def DependencyComplete
    (Edge : α → α → Prop)
    (Before After : α → Prop) : Prop :=
  ∀ {Seeds node},
    (¬ Affected Edge Seeds node) → StableUnderEdit Before After node

end FiniteBridge
