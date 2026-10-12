import Erdos1092

open SimpleGraph Filter Asymptotics

open scoped Classical in
/-- Independent literal transcription of the original all-size budget condition. -/
def OriginalAdmissible (r : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ H : Subgraph G,
      ∃ E : Finset (Sym2 H.verts),
        E ⊆ H.coe.edgeFinset ∧ E.card ≤ g (Fintype.card H.verts) ∧
        chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
    chromaticNumber G ≤ (r + 1 : ℕ∞)

theorem admissible_literal (r : ℕ) (g : ℕ → ℕ) :
    Erdos1092.IsAdmissible r g = OriginalAdmissible r g := rfl

theorem original_fixed_r (r : ℕ) (hr : 2 ≤ r) :
    ¬∃ g : ℕ → ℕ, OriginalAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  Erdos1092.erdos_1092 r hr

theorem original_r_two :
    ¬∃ g : ℕ → ℕ, OriginalAdmissible 2 g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  original_fixed_r 2 (by decide)

theorem original_all_fixed :
    ∀ r : ℕ, 2 ≤ r → ¬∃ g : ℕ → ℕ, OriginalAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) :=
  original_fixed_r

#check Erdos1092.erdos_1092
#check Erdos1092.exists_finite_hereditary_counterexample
#print Erdos1092.IsAdmissible
#print axioms admissible_literal
#print axioms original_fixed_r
#print axioms original_r_two
#print axioms original_all_fixed
