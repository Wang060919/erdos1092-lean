import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

namespace Erdos1092

open SimpleGraph

/-- Ordinary vertices have a layer and a cyclic coordinate; the right summand is the apex. -/
abbrev Vertex (R t : ℕ) := (Fin R × ZMod t) ⊕ Unit

def cycleAdj {t : ℕ} (a b : ZMod t) : Prop :=
  a ≠ b ∧ (b = a + 1 ∨ a = b + 1)

lemma cycleAdj_symm {t : ℕ} {a b : ZMod t} (h : cycleAdj a b) : cycleAdj b a :=
  ⟨h.1.symm, h.2.symm⟩

def MycAdj (R t : ℕ) : Vertex R t → Vertex R t → Prop
  | Sum.inl (i, a), Sum.inl (j, b) =>
      cycleAdj a b ∧ ((i.val = 0 ∧ j.val = 0) ∨
        j.val = i.val + 1 ∨ i.val = j.val + 1)
  | Sum.inl (i, _), Sum.inr _ => i.val + 1 = R
  | Sum.inr _, Sum.inl (i, _) => i.val + 1 = R
  | Sum.inr _, Sum.inr _ => False

def mycGraph (R t : ℕ) : SimpleGraph (Vertex R t) where
  Adj := MycAdj R t
  symm := by
    constructor
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact ⟨cycleAdj_symm h.1, h.2.elim
          (fun h0 => Or.inl ⟨h0.2, h0.1⟩)
          (fun hs => Or.inr hs.symm)⟩
      | inr b => exact h
    | inr a =>
      cases b with
      | inl b => exact h
      | inr b => exact h
  loopless := by
    constructor
    intro a h
    cases a with
    | inl a => exact h.1.1 rfl
    | inr a => exact h

open scoped Classical in
/-- A budget bound for every missing-edge subgraph whose incident vertices lie in `S`.
This support formulation avoids losing non-induced subgraphs or charging isolated vertices
outside `S`; it will be bridged to the original `Subgraph` formulation. -/
def LocalCutBound {V : Type*} [Fintype V] [DecidableEq V]
    (ε : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ (H : SimpleGraph V), H ≤ G → ∀ S : Finset V,
    (∀ ⦃u v⦄, H.Adj u v → u ∈ S ∧ v ∈ S) →
    ∃ E : Finset (Sym2 V), E ⊆ H.edgeFinset ∧
      (E.card : ℝ) ≤ ε * S.card ∧ (H.deleteEdges E).Colorable 2

end Erdos1092
