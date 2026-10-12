import Erdos1092.Winding
import Erdos1092.Cuts
import Erdos1092.Outer
import Erdos1092.Transport
import Erdos1092.Parameters

namespace Erdos1092

open SimpleGraph Filter Asymptotics

theorem localCutBound_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ε δ : ℝ} (hεδ : ε ≤ δ)
    (h : LocalCutBound ε G) : LocalCutBound δ G := by
  classical
  intro H hH S hS
  obtain ⟨E, hE, hcard, hcolor⟩ := h H hH S hS
  exact ⟨E, hE, hcard.trans
    (mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg S.card)), hcolor⟩

/-- The actual finite construction supplies every premise of the outer argument. -/
theorem exists_finite_hereditary_counterexample (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ X : SimpleGraph (Fin n),
      ¬X.Colorable 3 ∧ LocalCutBound ε X := by
  classical
  obtain ⟨M, hM, hbound⟩ := exists_cut_parameter ε hε
  have : NeZero (2 * M + 1) := parameter_cycle_ne_zero M
  let V := Vertex (M + 1) (2 * M + 1)
  let G := mycGraph (M + 1) (2 * M + 1)
  have hG : ¬G.Colorable 3 := mycGraph_not_colorable_three
    (M + 1) (2 * M + 1) (parameter_layer_ge_two hM)
    (parameter_cycle_ge_three hM) (parameter_cycle_odd M)
  have hcut : LocalCutBound ε G := by
    apply localCutBound_mono _ (mycGraph_localCutBound
      (M + 1) (2 * M + 1) (parameter_layer_ge_two hM) (parameter_cycle_ge_three hM))
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hbound
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  exact ⟨n, G.comap e, not_colorable_comap_equiv e hG,
    localCutBound_comap_equiv e hcut⟩

/-- Complete resolution at every fixed color parameter: no admissible budget is
eventually at least linear. Admissibility retains all subgraph sizes simultaneously. -/
theorem erdos_1092 (r : ℕ) (hr : 2 ≤ r) :
    ¬∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  no_admissible_bigO exists_finite_hereditary_counterexample hr

theorem erdos_1092_all :
    ∀ r : ℕ, 2 ≤ r → ¬∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  erdos_1092

theorem f_asymptotic_2 :
    ¬∃ g : ℕ → ℕ, IsAdmissible 2 g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  erdos_1092 2 (by decide)

theorem f_asymptotic_general :
    ¬∀ r : ℕ, 2 ≤ r → ∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) := by
  intro h
  exact f_asymptotic_2 (h 2 (by decide))

end Erdos1092
