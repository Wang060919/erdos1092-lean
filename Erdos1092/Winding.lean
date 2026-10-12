import Erdos1092.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Int.Parity

namespace Erdos1092

open SimpleGraph
open scoped BigOperators

/- The orientation of a proper edge in a three-color palette. Its value on a
monochromatic pair is unused, but retaining ±1 everywhere simplifies parity. -/
def colorDelta (a b : Fin 3) : ℤ :=
  if b.val = (a.val + 1) % 3 then 1 else -1

lemma colorDelta_reverse {a b : Fin 3} (h : a ≠ b) :
    colorDelta b a = -colorDelta a b := by
  fin_cases a <;> fin_cases b <;> norm_num [colorDelta] at *

lemma colorDelta_mod_two (a b : Fin 3) : colorDelta a b % 2 = 1 := by
  unfold colorDelta
  split <;> norm_num

/-- This concerns closed walks, so no distinctness of opposite vertices is needed. -/
lemma colorDelta_closed_four {a b c d : Fin 3}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    colorDelta a b + colorDelta b c + colorDelta c d + colorDelta d a = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [colorDelta] at *

section Cyclic

variable {t : ℕ} [NeZero t]

lemma cyclic_sum_add_one (f : ZMod t → ℤ) :
    (∑ i, f (i + 1)) = ∑ i, f i := by
  exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod t)) _ f (fun _ => rfl)

lemma cyclic_sum_sub_one (f : ZMod t → ℤ) :
    (∑ i, f (i - 1)) = ∑ i, f i := by
  simpa [sub_eq_add_neg] using
    Fintype.sum_equiv (Equiv.addRight (-1 : ZMod t)) (fun i => f (i + -1)) f (fun _ => rfl)

def forwardDelta (c : ℕ → ZMod t → Fin 3) (j : ℕ) (i : ZMod t) : ℤ :=
  colorDelta (c j i) (c (j + 1) (i + 1))

def backwardDelta (c : ℕ → ZMod t → Fin 3) (j : ℕ) (i : ZMod t) : ℤ :=
  colorDelta (c j i) (c (j + 1) (i - 1))

def layerWinding (c : ℕ → ZMod t → Fin 3) (j : ℕ) : ℤ :=
  ∑ i, (forwardDelta c j i - backwardDelta c j i)

def baseWinding (c : ℕ → ZMod t → Fin 3) : ℤ :=
  ∑ i, colorDelta (c 0 i) (c 0 (i + 1))

lemma baseWinding_odd (c : ℕ → ZMod t → Fin 3) (ht : Odd t) :
    Odd (baseWinding c) := by
  apply Int.odd_iff.mpr
  unfold baseWinding
  rw [Finset.sum_int_mod]
  simp only [colorDelta_mod_two]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rcases ht with ⟨k, hk⟩
  omega

lemma base_layer_winding (c : ℕ → ZMod t → Fin 3)
    (hbase : ∀ i, c 0 i ≠ c 0 (i + 1))
    (hfwd : ∀ i, c 0 i ≠ c 1 (i + 1))
    (hbwd : ∀ i, c 0 i ≠ c 1 (i - 1)) :
    layerWinding c 0 = 2 * baseWinding c := by
  have hpoint (i : ZMod t) :
      colorDelta (c 0 i) (c 0 (i + 1)) +
        colorDelta (c 0 (i - 1)) (c 0 i) +
        backwardDelta c 0 (i + 1) - forwardDelta c 0 (i - 1) = 0 := by
    have h := colorDelta_closed_four (hbase i) (by simpa using hbwd (i + 1))
      (by simpa using (hfwd (i - 1)).symm) (by simpa using hbase (i - 1))
    have hrev : colorDelta (c 1 i) (c 0 (i - 1)) =
        -colorDelta (c 0 (i - 1)) (c 1 i) :=
      colorDelta_reverse (by simpa using hfwd (i - 1))
    rw [hrev] at h
    simpa [forwardDelta, backwardDelta, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hsum := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset (ZMod t))) =>
    hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [cyclic_sum_add_one, cyclic_sum_sub_one] at hsum
  have hshift : (∑ i : ZMod t, colorDelta (c 0 (i - 1)) (c 0 i)) = baseWinding c := by
    simpa [baseWinding] using
      cyclic_sum_sub_one (fun i : ZMod t => colorDelta (c 0 i) (c 0 (i + 1)))
  rw [hshift] at hsum
  unfold baseWinding at hsum
  unfold layerWinding baseWinding
  rw [Finset.sum_sub_distrib]
  linarith

lemma successive_layer_winding (c : ℕ → ZMod t → Fin 3) (j : ℕ)
    (hfwd : ∀ i, c j i ≠ c (j + 1) (i + 1))
    (hbwd : ∀ i, c j i ≠ c (j + 1) (i - 1))
    (hfwd' : ∀ i, c (j + 1) i ≠ c (j + 2) (i + 1))
    (hbwd' : ∀ i, c (j + 1) i ≠ c (j + 2) (i - 1)) :
    layerWinding c j = layerWinding c (j + 1) := by
  have hpoint (i : ZMod t) :
      forwardDelta c j i + backwardDelta c (j + 1) (i + 1) -
        forwardDelta c (j + 1) (i - 1) - backwardDelta c j i = 0 := by
    have h := colorDelta_closed_four (hfwd i) (by simpa using hbwd' (i + 1))
      (by simpa using (hfwd' (i - 1)).symm) (hbwd i).symm
    have hrev : colorDelta (c (j + 2) i) (c (j + 1) (i - 1)) =
        -colorDelta (c (j + 1) (i - 1)) (c (j + 2) i) :=
      colorDelta_reverse (by simpa using hfwd' (i - 1))
    rw [hrev, colorDelta_reverse (hbwd i)] at h
    simpa [forwardDelta, backwardDelta, Nat.add_assoc, sub_eq_add_neg] using h
  have hsum := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset (ZMod t))) =>
    hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [cyclic_sum_add_one, cyclic_sum_sub_one] at hsum
  simp only [layerWinding, Finset.sum_sub_distrib]
  linarith

lemma top_layer_winding (c : ℕ → ZMod t → Fin 3) (j : ℕ) (apex : Fin 3)
    (hfwd : ∀ i, c j i ≠ c (j + 1) (i + 1))
    (hbwd : ∀ i, c j i ≠ c (j + 1) (i - 1))
    (htop : ∀ i, c (j + 1) i ≠ apex) :
    layerWinding c j = 0 := by
  have hpoint (i : ZMod t) :
      forwardDelta c j i + colorDelta (c (j + 1) (i + 1)) apex -
        colorDelta (c (j + 1) (i - 1)) apex - backwardDelta c j i = 0 := by
    have h := colorDelta_closed_four (hfwd i) (htop (i + 1))
      (htop (i - 1)).symm (hbwd i).symm
    rw [colorDelta_reverse (htop (i - 1)), colorDelta_reverse (hbwd i)] at h
    simpa [forwardDelta, backwardDelta, sub_eq_add_neg] using h
  have hsum := Finset.sum_eq_zero (fun i (_ : i ∈ (Finset.univ : Finset (ZMod t))) =>
    hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [cyclic_sum_add_one (fun i => colorDelta (c (j + 1) i) apex),
    cyclic_sum_sub_one (fun i => colorDelta (c (j + 1) i) apex)] at hsum
  simp only [layerWinding, Finset.sum_sub_distrib]
  linarith

lemma winding_contradiction (R : ℕ) (hR : 2 ≤ R) (htOdd : Odd t)
    (c : ℕ → ZMod t → Fin 3) (apex : Fin 3)
    (hbase : ∀ i, c 0 i ≠ c 0 (i + 1))
    (hfwd : ∀ j, j + 1 < R → ∀ i, c j i ≠ c (j + 1) (i + 1))
    (hbwd : ∀ j, j + 1 < R → ∀ i, c j i ≠ c (j + 1) (i - 1))
    (htop : ∀ i, c (R - 1) i ≠ apex) : False := by
  have heq (j : ℕ) (hj : j + 1 < R) : layerWinding c j = layerWinding c 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj' : j + 1 < R := by omega
      exact (successive_layer_winding c j (hfwd j hj') (hbwd j hj')
        (hfwd (j + 1) hj) (hbwd (j + 1) hj)).symm.trans (ih hj')
  have hj : R - 2 + 1 < R := by omega
  have htop' : ∀ i, c (R - 2 + 1) i ≠ apex := by
    simpa only [show R - 2 + 1 = R - 1 by omega] using htop
  have hzero := top_layer_winding c (R - 2) apex (hfwd _ hj) (hbwd _ hj) htop'
  rw [heq _ hj, base_layer_winding c hbase (hfwd 0 (by omega))
    (hbwd 0 (by omega))] at hzero
  have hwzero : baseWinding c = 0 := by omega
  have hodd := baseWinding_odd c htOdd
  rw [hwzero] at hodd
  norm_num at hodd

end Cyclic

lemma cycleAdj_next {t : ℕ} (ht : 3 ≤ t) (i : ZMod t) :
    cycleAdj i (i + 1) := by
  refine ⟨?_, Or.inl rfl⟩
  intro h
  have h' : i + 0 = i + (1 : ZMod t) := by simpa using h
  have hone : (1 : ZMod t) = 0 := (add_left_cancel h').symm
  have := ZMod.one_eq_zero_iff.mp hone
  omega

lemma cycleAdj_prev {t : ℕ} (ht : 3 ≤ t) (i : ZMod t) :
    cycleAdj i (i - 1) := by
  refine ⟨?_, Or.inr (sub_add_cancel i 1).symm⟩
  intro h
  have h' : i + 0 = i + (-1 : ZMod t) := by simpa [sub_eq_add_neg] using h
  have hone : (1 : ZMod t) = 0 := neg_eq_zero.mp (add_left_cancel h').symm
  have := ZMod.one_eq_zero_iff.mp hone
  omega

/-- The actual generalized Mycielski graph of an odd cycle needs four colors.
All hypotheses are the construction's original integer parameter conditions. -/
theorem mycGraph_not_colorable_three (R t : ℕ) [NeZero t]
    (hR : 2 ≤ R) (ht : 3 ≤ t) (htOdd : Odd t) :
    ¬(mycGraph R t).Colorable 3 := by
  rintro ⟨C⟩
  let c (j : ℕ) (i : ZMod t) : Fin 3 :=
    if hj : j < R then C (Sum.inl (⟨j, hj⟩, i)) else 0
  have hbase (i : ZMod t) : c 0 i ≠ c 0 (i + 1) := by
    have h0 : 0 < R := by omega
    dsimp only [c]
    simp only [dif_pos h0]
    apply C.valid
    exact ⟨cycleAdj_next ht i, Or.inl ⟨rfl, rfl⟩⟩
  have hfwd (j : ℕ) (hj : j + 1 < R) (i : ZMod t) :
      c j i ≠ c (j + 1) (i + 1) := by
    have hj0 : j < R := by omega
    dsimp only [c]
    simp only [dif_pos hj0, dif_pos hj]
    apply C.valid
    exact ⟨cycleAdj_next ht i, Or.inr (Or.inl rfl)⟩
  have hbwd (j : ℕ) (hj : j + 1 < R) (i : ZMod t) :
      c j i ≠ c (j + 1) (i - 1) := by
    have hj0 : j < R := by omega
    dsimp only [c]
    simp only [dif_pos hj0, dif_pos hj]
    apply C.valid
    exact ⟨cycleAdj_prev ht i, Or.inr (Or.inl rfl)⟩
  have htop (i : ZMod t) : c (R - 1) i ≠ C (Sum.inr ()) := by
    have hj : R - 1 < R := by omega
    dsimp only [c]
    simp only [dif_pos hj]
    apply C.valid
    show R - 1 + 1 = R
    omega
  exact winding_contradiction R hR htOdd c (C (Sum.inr ())) hbase hfwd hbwd htop

end Erdos1092
