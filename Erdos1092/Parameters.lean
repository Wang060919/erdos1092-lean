import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Erdos1092

/-- The construction parameters are chosen before any subgraph is given. -/
theorem exists_cut_parameter (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 2 ≤ M ∧
      2 / (M : ℝ) + 2 / ((2 * M + 1 : ℕ) : ℝ) ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (4 / ε) (2 : ℝ))
  have hM2 : (2 : ℝ) < M := (le_max_right _ _).trans_lt hM
  have hMlarge : 4 / ε < (M : ℝ) := (le_max_left _ _).trans_lt hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hMnat : 2 ≤ M := by exact_mod_cast hM2.le
  have hden : (M : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hratio : 2 / ((2 * M + 1 : ℕ) : ℝ) ≤ 2 / (M : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hMpos hden
  have hfour : 4 / (M : ℝ) ≤ ε := by
    apply (div_le_iff₀ hMpos).mpr
    have := (div_lt_iff₀ hε).mp hMlarge
    nlinarith
  refine ⟨M, hMnat, ?_⟩
  calc
    2 / (M : ℝ) + 2 / ((2 * M + 1 : ℕ) : ℝ) ≤
        2 / (M : ℝ) + 2 / (M : ℝ) := by linarith
    _ = 4 / (M : ℝ) := by ring
    _ ≤ ε := hfour

lemma parameter_layer_ge_two {M : ℕ} (hM : 2 ≤ M) : 2 ≤ M + 1 := by omega

lemma parameter_cycle_ge_three {M : ℕ} (hM : 2 ≤ M) : 3 ≤ 2 * M + 1 := by omega

lemma parameter_cycle_odd (M : ℕ) : Odd (2 * M + 1) := by
  exact ⟨M, by omega⟩

lemma parameter_cycle_ne_zero (M : ℕ) : NeZero (2 * M + 1) := by
  exact ⟨by omega⟩

end Erdos1092
