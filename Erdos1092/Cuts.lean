import Erdos1092.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

namespace Erdos1092
open SimpleGraph Finset
open scoped BigOperators Classical

/-- The ordinary part of an arbitrary missing-edge subgraph. -/
def ordinaryPart {R t : ℕ} (H : SimpleGraph (Vertex R t)) : SimpleGraph (Vertex R t) where
  Adj u v := H.Adj u v ∧ u.isLeft ∧ v.isLeft
  symm := by constructor; intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by constructor; intro u h; exact H.irrefl h.1

/-- At most two levels can supply an ordinary neighbor. -/
lemma neighborLevel_count {R : ℕ} (i : Fin R) :
    (univ.filter fun j : Fin R =>
      (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1).card ≤ 2 := by
  classical
  let A := univ.filter fun j : Fin R =>
    (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1
  have hinj : Set.InjOn (fun j : Fin R => j.val) A := by
    intro a ha b hb hab
    exact Fin.ext hab
  have hsub : A.image (fun j => j.val) ⊆ {if i.val = 0 then 0 else i.val - 1, i.val + 1} := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    have hh := (mem_filter.mp hj).2
    rcases hh with hh | hh | hh
    · simp [hh.1, hh.2]
    · simp [hh]
    · have hi : i.val ≠ 0 := by omega
      simp [hi, show j.val = i.val - 1 by omega]
  have hc : (A.image (fun j => j.val)).card ≤ 2 :=
    (card_le_card hsub).trans card_le_two
  rwa [card_image_of_injOn hinj] at hc

lemma ordinaryPart_degree_le_four {R t : ℕ} [NeZero t]
    (H : SimpleGraph (Vertex R t)) (hH : H ≤ mycGraph R t) (u : Vertex R t) :
    (ordinaryPart H).degree u ≤ 4 := by
  classical
  cases u with
  | inr z =>
      have hzero : (ordinaryPart H).neighborFinset (Sum.inr z) = ∅ := by
        ext v
        rw [mem_neighborFinset]
        simp [ordinaryPart]
      rw [← card_neighborFinset_eq_degree, hzero]
      simp
  | inl p =>
      rcases p with ⟨i, a⟩
      let L := univ.filter fun j : Fin R =>
        (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1
      let C : Finset (ZMod t) := {a + 1, a - 1}
      have hsub : (ordinaryPart H).neighborFinset (Sum.inl (i,a)) ⊆
          (L ×ˢ C).image Sum.inl := by
        intro v hv
        have hh : H.Adj (Sum.inl (i,a)) v ∧ (Sum.inl (i,a) : Vertex R t).isLeft ∧ v.isLeft :=
          ((mem_neighborFinset _ _ _).mp hv)
        cases v with
        | inr z => simp at hh
        | inl p =>
          rcases p with ⟨j,b⟩
          have hg : cycleAdj a b ∧
              ((i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 ∨ i.val = j.val + 1) := hH hh.1
          apply mem_image.mpr
          refine ⟨(j,b), mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hg.2⟩, ?_⟩,rfl⟩
          rcases hg.1.2 with hb | hb
          · simp [C,hb]
          · have hb' : b = a - 1 := by rw [hb]; abel
            simp [C,hb']
      have hL : L.card ≤ 2 := neighborLevel_count i
      have hC : C.card ≤ 2 := card_le_two
      rw [← card_neighborFinset_eq_degree]
      calc
        _ ≤ ((L ×ˢ C).image Sum.inl).card := card_le_card hsub
        _ ≤ (L ×ˢ C).card := card_image_le
        _ = L.card * C.card := card_product _ _
        _ ≤ 4 := by nlinarith

lemma ordinaryPart_card_edges_le {R t : ℕ} [NeZero t]
    (H : SimpleGraph (Vertex R t)) (hH : H ≤ mycGraph R t)
    (S : Finset (Vertex R t))
    (hS : ∀ ⦃u v⦄, H.Adj u v → u ∈ S ∧ v ∈ S) :
    (ordinaryPart H).edgeFinset.card ≤ 2 * S.card := by
  classical
  have hs : ∑ u, (ordinaryPart H).degree u = ∑ u ∈ S, (ordinaryPart H).degree u := by
    symm
    apply sum_subset (subset_univ S)
    intro u hu hnot
    rw [degree_eq_zero]
    intro v hv
    exact hnot (hS hv.1).1
  have hd : ∑ u ∈ S, (ordinaryPart H).degree u ≤ S.card * 4 := by
    calc
      _ ≤ ∑ _u ∈ S, 4 := sum_le_sum fun u hu => ordinaryPart_degree_le_four H hH u
      _ = S.card * 4 := by simp
  rw [← hs, sum_degrees_eq_twice_card_edges] at hd
  omega

/-- Averaging in its division-free form, usable for an arbitrary finite partition of edges. -/
lemma exists_small_fiber {α β : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    (E : Finset β) (p : α → β → Prop) [∀ a, DecidablePred (p a)]
    (huniq : ∀ e ∈ E, ∀ a b, p a e → p b e → a = b) :
    ∃ a, Fintype.card α * (E.filter (p a)).card ≤ E.card := by
  classical
  have hsum : ∑ a : α, (E.filter (p a)).card ≤ E.card := by
    have heq : ∀ a : α, (E.filter (p a)).card = ∑ e ∈ E, if p a e then 1 else 0 := by
      intro a
      simp only [card_eq_sum_ones, sum_filter]
    simp_rw [heq]
    rw [sum_comm]
    calc
      _ ≤ ∑ _e ∈ E, 1 := by
        apply sum_le_sum
        intro e he
        by_cases hex : ∃ a, p a e
        · obtain ⟨a, ha⟩ := hex
          have hp : ∀ b, p b e ↔ b = a := by
            intro b
            exact ⟨fun hb => huniq e he b a hb ha, fun hb => hb ▸ ha⟩
          simp [hp]
        · simp only [not_exists] at hex
          simp [hex]
      _ = E.card := by simp
  by_contra hnot
  push Not at hnot
  have hgt : E.card * Fintype.card α <
      (∑ a : α, (E.filter (p a)).card) * Fintype.card α := by
    calc
      _ = ∑ _a : α, E.card := by simp [mul_comm]
      _ < ∑ a : α, Fintype.card α * (E.filter (p a)).card :=
        sum_lt_sum_of_nonempty univ_nonempty fun a _ => hnot a
      _ = _ := by rw [← mul_sum, mul_comm]
  have hc : 0 < Fintype.card α := Fintype.card_pos
  nlinarith

/-- Successive positions on a cut-open modular cycle have opposite parity. -/
lemma zmod_parity_next {t : ℕ} [NeZero t] (ht : 3 ≤ t) (a : ZMod t)
    (ha : a + 1 ≠ 0) : a.val % 2 ≠ (a + 1).val % 2 := by
  have hone : (1 : ZMod t).val = 1 := ZMod.val_one'' (by omega)
  have hav := ZMod.val_lt a
  have hlt : a.val + 1 < t := by
    by_contra hn
    have he : a.val + 1 = t := by omega
    have hz : (a + 1).val = 0 := by rw [ZMod.val_add, hone, he]; simp
    exact ha ((ZMod.val_eq_zero _).mp hz)
  rw [ZMod.val_add, hone, Nat.mod_eq_of_lt hlt]
  omega

/-- Cut edges crossing a specified positive height. -/
def heightRel {R t : ℕ} (h : ℕ) : Vertex R t → Vertex R t → Prop
  | Sum.inl (i,_), Sum.inl (j,_) =>
      (i.val < h ∧ h ≤ j.val) ∨ (j.val < h ∧ h ≤ i.val)
  | _, _ => False

lemma heightRel_symm {R t : ℕ} (h : ℕ) (u v : Vertex R t) :
    heightRel h u v ↔ heightRel h v u := by
  cases u <;> cases v <;> simp [heightRel, or_comm]

def heightEdge {R t : ℕ} (h : ℕ) : Sym2 (Vertex R t) → Prop :=
  Sym2.lift ⟨heightRel h, fun u v => propext (heightRel_symm h u v)⟩

lemma heightEdge_unique {R t : ℕ} [NeZero t] (H : SimpleGraph (Vertex R t))
    (hH : H ≤ mycGraph R t) (e : Sym2 (Vertex R t)) (he : e ∈ H.edgeFinset)
    (a b : Fin (R-1)) (ha : heightEdge (a.val+1) e) (hb : heightEdge (b.val+1) e) : a = b := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hh : (mycGraph R t).Adj u v := hH (by simpa only [mem_edgeFinset,mem_edgeSet] using he)
      cases u with
      | inr z => cases v <;> simp [heightEdge,heightRel,Sym2.lift_mk] at ha
      | inl p =>
          cases v with
          | inr z => simp [heightEdge,heightRel,Sym2.lift_mk] at ha
          | inl q =>
              rcases p with ⟨i,x⟩
              rcases q with ⟨j,y⟩
              change cycleAdj x y ∧ ((i.val = 0 ∧ j.val = 0) ∨ j.val = i.val+1 ∨ i.val = j.val+1) at hh
              change (i.val < a.val+1 ∧ a.val+1 ≤ j.val) ∨ (j.val < a.val+1 ∧ a.val+1 ≤ i.val) at ha
              change (i.val < b.val+1 ∧ b.val+1 ≤ j.val) ∨ (j.val < b.val+1 ∧ b.val+1 ≤ i.val) at hb
              apply Fin.ext
              rcases hh.2 with hh | hh | hh <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

/-- Below-height edges at the chosen seam of the index cycle. -/
def seamRel {R t : ℕ} (h : ℕ) (s : ZMod t) : Vertex R t → Vertex R t → Prop
  | Sum.inl (i,a), Sum.inl (j,b) =>
      i.val < h ∧ j.val < h ∧ ((a = s ∧ b = s+1) ∨ (b = s ∧ a = s+1))
  | _, _ => False

lemma seamRel_symm {R t : ℕ} (h : ℕ) (s : ZMod t) (u v : Vertex R t) :
    seamRel h s u v ↔ seamRel h s v u := by
  cases u <;> cases v <;> simp [seamRel, and_left_comm, or_comm]

def seamEdge {R t : ℕ} (h : ℕ) (s : ZMod t) : Sym2 (Vertex R t) → Prop :=
  Sym2.lift ⟨seamRel h s, fun u v => propext (seamRel_symm h s u v)⟩

lemma two_ne_zero {t : ℕ} (ht : 3 ≤ t) : (2 : ZMod t) ≠ 0 := by
  intro hz
  have hd : t ∣ 2 := (ZMod.natCast_eq_zero_iff 2 t).mp hz
  have := Nat.le_of_dvd (by omega : 0 < 2) hd
  omega

lemma seamEdge_unique {R t : ℕ} (ht : 3 ≤ t)
    (e : Sym2 (Vertex R t)) (h : ℕ) (a b : ZMod t)
    (ha : seamEdge h a e) (hb : seamEdge h b e) : a = b := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      cases u with
      | inr z => cases v <;> simp [seamEdge,seamRel,Sym2.lift_mk] at ha
      | inl p =>
          cases v with
          | inr z => simp [seamEdge,seamRel,Sym2.lift_mk] at ha
          | inl q =>
              rcases p with ⟨i,x⟩
              rcases q with ⟨j,y⟩
              change i.val < h ∧ j.val < h ∧ ((x=a ∧ y=a+1) ∨ (y=a ∧ x=a+1)) at ha
              change i.val < h ∧ j.val < h ∧ ((x=b ∧ y=b+1) ∨ (y=b ∧ x=b+1)) at hb
              rcases ha.2.2 with ha | ha <;> rcases hb.2.2 with hb | hb
              · exact ha.1.symm.trans hb.1
              · have hz : (2 : ZMod t) = 0 := by
                  linear_combination ha.1 - ha.2 - hb.2 + hb.1
                exact False.elim (two_ne_zero ht hz)
              · have hz : (2 : ZMod t) = 0 := by
                  linear_combination ha.1 - ha.2 - hb.2 + hb.1
                exact False.elim (two_ne_zero ht hz)
              · exact ha.1.symm.trans hb.1

/-- Two colors, using index parity below the height and layer parity above it. -/
def cutColor {R t : ℕ} [NeZero t] (h : ℕ) (s : ZMod t) : Vertex R t → Fin 2
  | Sum.inl (i,a) => if i.val < h then ⟨(a-(s+1)).val % 2, Nat.mod_lt _ (by omega)⟩
      else ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩
  | Sum.inr _ => ⟨R % 2, Nat.mod_lt _ (by omega)⟩

lemma cycle_parity {t : ℕ} [NeZero t] (ht : 3 ≤ t) (s a b : ZMod t)
    (hab : cycleAdj a b)
    (hseam : ¬ ((a=s ∧ b=s+1) ∨ (b=s ∧ a=s+1))) :
    (a-(s+1)).val % 2 ≠ (b-(s+1)).val % 2 := by
  rcases hab.2 with hb | ha
  · have hne : (a-(s+1))+1 ≠ 0 := by
      intro hz
      have he : a=s := by linear_combination hz
      exact hseam (Or.inl ⟨he, by simpa [he] using hb⟩)
    have hh := zmod_parity_next ht (a-(s+1)) hne
    have he : b-(s+1) = (a-(s+1))+1 := by rw [hb]; abel
    rw [he]
    exact hh
  · have hne : (b-(s+1))+1 ≠ 0 := by
      intro hz
      have he : b=s := by linear_combination hz
      exact hseam (Or.inr ⟨he, by simpa [he] using ha⟩)
    have hh := zmod_parity_next ht (b-(s+1)) hne
    have he : a-(s+1) = (b-(s+1))+1 := by rw [ha]; abel
    rw [he]
    exact hh.symm

lemma cutColor_valid {R t : ℕ} [NeZero t] (ht : 3 ≤ t)
    (h : ℕ) (hpos : 1 ≤ h) (hR : h < R) (s : ZMod t)
    (u v : Vertex R t) (huv : (mycGraph R t).Adj u v)
    (hh : ¬heightRel h u v) (hs : ¬seamRel h s u v) :
    cutColor h s u ≠ cutColor h s v := by
  cases u with
  | inl p =>
      rcases p with ⟨i,a⟩
      cases v with
      | inl q =>
          rcases q with ⟨j,b⟩
          change cycleAdj a b ∧ ((i.val=0 ∧ j.val=0) ∨ j.val=i.val+1 ∨ i.val=j.val+1) at huv
          by_cases hi : i.val < h
          · have hj : j.val < h := by
              by_contra hj
              exact hh (Or.inl ⟨hi, by omega⟩)
            have hp := cycle_parity ht s a b huv.1 (fun hn => hs ⟨hi,hj,hn⟩)
            simpa [cutColor,hi,hj,Fin.ext_iff] using hp
          · have hj : ¬j.val < h := by
              intro hj
              exact hh (Or.inr ⟨hj, by omega⟩)
            have hp : i.val % 2 ≠ j.val % 2 := by
              rcases huv.2 with hb | hb | hb <;> omega
            simpa [cutColor,hi,hj,Fin.ext_iff] using hp
      | inr z =>
          change i.val+1=R at huv
          have hi : ¬i.val < h := by omega
          have hp : i.val % 2 ≠ R % 2 := by omega
          simpa [cutColor,hi,Fin.ext_iff] using hp
  | inr z =>
      cases v with
      | inr w => exact False.elim huv
      | inl p =>
          rcases p with ⟨i,a⟩
          change i.val+1=R at huv
          have hi : ¬i.val < h := by omega
          have hp : R % 2 ≠ i.val % 2 := by omega
          simpa [cutColor,hi,Fin.ext_iff] using hp

lemma mem_ordinary_height {R t : ℕ} [NeZero t] (H : SimpleGraph (Vertex R t))
    (h : ℕ) (u v : Vertex R t) (huv : H.Adj u v) (hh : heightRel h u v) :
    s(u,v) ∈ (ordinaryPart H).edgeFinset := by
  classical
  rw [mem_edgeFinset, mem_edgeSet]
  cases u <;> cases v <;> simp_all [heightRel, ordinaryPart]

lemma mem_ordinary_seam {R t : ℕ} [NeZero t] (H : SimpleGraph (Vertex R t))
    (h : ℕ) (a : ZMod t) (u v : Vertex R t) (huv : H.Adj u v) (hh : seamRel h a u v) :
    s(u,v) ∈ (ordinaryPart H).edgeFinset := by
  classical
  rw [mem_edgeFinset, mem_edgeSet]
  cases u <;> cases v <;> simp_all [seamRel, ordinaryPart]

/-- All non-induced subgraphs admit the two-cut budget, uniformly in their support size. -/
theorem mycGraph_localCutBound (R t : ℕ) [NeZero t] (hR : 2 ≤ R) (ht : 3 ≤ t) :
    LocalCutBound (2/(R-1 : ℝ) + 2/(t : ℝ)) (mycGraph R t) := by
  classical
  intro H hH S hS
  let O := (ordinaryPart H).edgeFinset
  have ho : O.card ≤ 2*S.card := ordinaryPart_card_edges_le H hH S hS
  have hO : ordinaryPart H ≤ mycGraph R t := fun u v huv => hH huv.1
  let : Nonempty (Fin (R-1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a,ha⟩ := exists_small_fiber O
    (fun a : Fin (R-1) => heightEdge (a.val+1))
    (fun e he a b h1 h2 => heightEdge_unique (ordinaryPart H) hO e he a b h1 h2)
  let h := a.val+1
  have hpos : 1 ≤ h := by omega
  have hlt : h < R := by have := a.isLt; omega
  let A := O.filter (heightEdge h)
  have hAc : (R-1)*A.card ≤ 2*S.card := by
    simpa [A,h,Fintype.card_fin] using ha.trans ho
  obtain ⟨b,hb⟩ := exists_small_fiber O (fun b : ZMod t => seamEdge h b)
    (fun e _ a b h1 h2 => seamEdge_unique ht e h a b h1 h2)
  let B := O.filter (seamEdge h b)
  have hBc : t*B.card ≤ 2*S.card := by
    simpa [B,ZMod.card] using hb.trans ho
  have hsubO : O ⊆ H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hh : (ordinaryPart H).Adj u v := by simpa [O,mem_edgeFinset,mem_edgeSet] using he
        simpa [mem_edgeFinset,mem_edgeSet] using hh.1
  refine ⟨A ∪ B, union_subset (Subset.trans (filter_subset _ _) hsubO)
    (Subset.trans (filter_subset _ _) hsubO), ?_, ?_⟩
  · have hr : (0 : ℝ) < (R-1 : ℕ) := by exact_mod_cast (show 0 < R-1 by omega)
    have htr : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hac : (A.card : ℝ) ≤ 2/(R-1 : ℝ)*S.card := by
      have hc : ((R-1 : ℕ) : ℝ)*A.card ≤ 2*S.card := by exact_mod_cast hAc
      have he : ((R-1 : ℕ) : ℝ) = (R-1 : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [he] at hc hr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hr).mpr
      nlinarith
    have hbc : (B.card : ℝ) ≤ 2/(t : ℝ)*S.card := by
      have hc : (t : ℝ)*B.card ≤ 2*S.card := by exact_mod_cast hBc
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ htr).mpr
      nlinarith
    have hcard : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ)+B.card := by exact_mod_cast card_union_le A B
    nlinarith
  · refine ⟨⟨cutColor h b, ?_⟩⟩
    intro u v huv
    have hdel := deleteEdges_adj.mp huv
    apply cutColor_valid ht h hpos hlt b u v (hH hdel.1)
    · intro hh
      apply hdel.2
      apply mem_union_left
      apply mem_filter.mpr
      exact ⟨mem_ordinary_height H h u v hdel.1 hh,hh⟩
    · intro hh
      apply hdel.2
      apply mem_union_right
      apply mem_filter.mpr
      exact ⟨mem_ordinary_seam H h b u v hdel.1 hh,hh⟩

end Erdos1092
