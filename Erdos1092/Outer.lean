import Erdos1092.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic

namespace Erdos1092

open SimpleGraph Filter Asymptotics

open scoped Classical in
/-- The original assertion, including every non-induced subgraph and every vertex count. -/
def IsAdmissible (r : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ H : G.Subgraph,
      ∃ E : Finset (Sym2 H.verts),
        E ⊆ H.coe.edgeFinset ∧ E.card ≤ g (Fintype.card H.verts) ∧
        chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
    chromaticNumber G ≤ (r + 1 : ℕ∞)

/-- Join with a complete graph: all cross edges are present. -/
def cliqueJoin {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (V ⊕ Fin k) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr u, .inr v => u ≠ v
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := by
    constructor
    intro u v h
    cases u <;> cases v <;> first | exact G.symm h | exact h.symm | trivial
  loopless := by
    constructor
    intro u h
    cases u
    · exact G.irrefl h
    · exact h rfl

/-- A clique uses `k` different colors, leaving only three for the original graph. -/
theorem cliqueJoin_not_colorable {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hG : ¬G.Colorable 3) : ¬(cliqueJoin G k).Colorable (3 + k) := by
  classical
  rintro ⟨C⟩
  let used : Finset (Fin (3 + k)) := Finset.univ.image (fun v : Fin k => C (.inr v))
  have hi : Function.Injective (fun v : Fin k => C (.inr v)) := by
    intro u v huv
    by_contra hne
    exact C.valid (show (cliqueJoin G k).Adj (.inr u) (.inr v) from hne) huv
  have hcard : used.card = k := by
    simp [used, Finset.card_image_of_injective _ hi]
  have havail : Fintype.card ↥usedᶜ ≤ 3 := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hcard]
    omega
  let D : G.Coloring ↥usedᶜ := Coloring.mk
    (fun v => ⟨C (.inl v), by
      simp only [Finset.mem_compl, used, Finset.mem_image, Finset.mem_univ, true_and,
        not_exists]
      intro u hu
      exact C.valid (show (cliqueJoin G k).Adj (.inl v) (.inr u) from True.intro) hu.symm⟩)
    (fun {u v} huv h => C.valid (show (cliqueJoin G k).Adj (.inl u) (.inl v) from huv)
      (congrArg Subtype.val h))
  exact hG (D.colorable.mono havail)

open scoped Classical in
/-- A support-sensitive deletion bound, allowing an arbitrary number of remaining colors. -/
def LocalColorCutBound {V : Type*} [Fintype V] [DecidableEq V]
    (ε : ℝ) (q : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ (H : SimpleGraph V), H ≤ G → ∀ S : Finset V,
    (∀ ⦃u v⦄, H.Adj u v → u ∈ S ∧ v ∈ S) →
    ∃ E : Finset (Sym2 V), E ⊆ H.edgeFinset ∧
      (E.card : ℝ) ≤ ε * S.card ∧ (H.deleteEdges E).Colorable q

/-- The join requires only deleting edges in the original graph. -/
theorem cliqueJoin_localCut {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ε : ℝ} (hε : 0 ≤ ε) (hG : LocalCutBound ε G) (k : ℕ) :
    LocalColorCutBound ε (2 + k) (cliqueJoin G k) := by
  classical
  intro H hH S hS
  let J := H.comap (Sum.inl : V → V ⊕ Fin k)
  let T := S.preimage (Sum.inl : V → V ⊕ Fin k) Sum.inl_injective.injOn
  have hJ : J ≤ G := fun u v huv => hH huv
  have hT : ∀ ⦃u v⦄, J.Adj u v → u ∈ T ∧ v ∈ T := by
    intro u v huv
    simpa [T, J] using hS huv
  obtain ⟨E, hE, hcard, ⟨C⟩⟩ := hG J hJ T hT
  let f : V ↪ V ⊕ Fin k := ⟨Sum.inl, Sum.inl_injective⟩
  let F := E.map f.sym2Map
  have hF : F ⊆ H.edgeFinset := by
    have hmap : ∀ a : Sym2 V, a ∈ E → f.sym2Map a ∈ H.edgeFinset := by
      refine Sym2.ind ?_
      intro u v ha
      have huv : J.Adj u v := by simpa using hE ha
      simpa [f, J] using huv
    intro a ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp ha
    exact hba ▸ hmap b hb
  have hsize : T.card ≤ S.card := by
    dsimp [T]
    rw [Finset.card_preimage]
    exact Finset.card_filter_le _ _
  have hbound : (F.card : ℝ) ≤ ε * S.card := by
    calc
      (F.card : ℝ) = E.card := by simp [F]
      _ ≤ ε * T.card := hcard
      _ ≤ ε * S.card := mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) hε
  let D : (H.deleteEdges F).Coloring (Fin 2 ⊕ Fin k) := Coloring.mk
    (Sum.elim (fun v => Sum.inl (C v)) Sum.inr)
    (by
      intro u v huv
      obtain ⟨huv, hnot⟩ := (deleteEdges_adj).mp huv
      cases u with
      | inl u =>
        cases v with
        | inl v =>
          intro heq
          apply C.valid
            (show (J.deleteEdges E).Adj u v from deleteEdges_adj.mpr ⟨huv, by
              intro he
              apply hnot
              exact Finset.mem_map.mpr ⟨s(u,v), he, rfl⟩⟩)
          exact Sum.inl.inj heq
        | inr v => exact Sum.inl_ne_inr
      | inr u =>
        cases v with
        | inl v => exact Sum.inr_ne_inl
        | inr v =>
          intro heq
          exact (hH huv) (Sum.inr.inj heq))
  refine ⟨F, hF, hbound, ?_⟩
  simpa using D.colorable

/-- Relabeling vertices preserves the support-sensitive bound. -/
theorem localColorCut_comap_equiv {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {ε : ℝ} {q : ℕ}
    (hG : LocalColorCutBound ε q G) (e : W ≃ V) :
    LocalColorCutBound ε q (G.comap e) := by
  classical
  intro H hH S hS
  let J := H.comap e.symm
  have hJ : J ≤ G := by
    intro u v huv
    simpa using hH huv
  have hT : ∀ ⦃u v⦄, J.Adj u v → u ∈ S.image e ∧ v ∈ S.image e := by
    intro u v huv
    obtain ⟨hu, hv⟩ := hS huv
    exact ⟨Finset.mem_image.mpr ⟨e.symm u, hu, e.apply_symm_apply u⟩,
      Finset.mem_image.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩⟩
  obtain ⟨E, hE, hcard, ⟨C⟩⟩ := hG J hJ (S.image e) hT
  let F := E.map e.symm.toEmbedding.sym2Map
  have hF : F ⊆ H.edgeFinset := by
    have hmap : ∀ a : Sym2 V, a ∈ E → e.symm.toEmbedding.sym2Map a ∈ H.edgeFinset := by
      refine Sym2.ind ?_
      intro u v ha
      simpa [J] using hE ha
    intro a ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp ha
    exact hba ▸ hmap b hb
  refine ⟨F, hF, ?_, ?_⟩
  · simpa [F, Finset.card_image_of_injective _ e.injective] using hcard
  · refine ⟨Coloring.mk (fun v => C (e v)) ?_⟩
    intro u v huv
    apply C.valid
    obtain ⟨huv, hn⟩ := deleteEdges_adj.mp huv
    apply deleteEdges_adj.mpr
    refine ⟨by simpa [J] using huv, ?_⟩
    intro he
    apply hn
    apply Finset.mem_map.mpr
    refine ⟨s(e u, e v), he, ?_⟩
    simp

open scoped Classical in
/-- Restrict an ambient deletion set to the original subgraph's vertex subtype.
Isolated vertices stay in the vertex count, and edges need not be induced. -/
theorem localColorCut_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ε : ℝ} {q : ℕ} (hG : LocalColorCutBound ε q G)
    (H : G.Subgraph) :
    ∃ E : Finset (Sym2 H.verts), E ⊆ H.coe.edgeFinset ∧
      (E.card : ℝ) ≤ ε * Fintype.card H.verts ∧ (H.coe.deleteEdges E).Colorable q := by
  classical
  have hs : ∀ ⦃u v⦄, H.spanningCoe.Adj u v →
      u ∈ H.verts.toFinset ∧ v ∈ H.verts.toFinset := by
    intro u v huv
    exact ⟨by simpa using H.edge_vert huv, by simpa using H.edge_vert (H.adj_symm huv)⟩
  obtain ⟨E, hE, hcard, ⟨C⟩⟩ := hG H.spanningCoe H.spanningCoe_le H.verts.toFinset hs
  let f : H.verts ↪ V := Function.Embedding.subtype _
  let F := E.preimage f.sym2Map f.sym2Map.injective.injOn
  have hF : F ⊆ H.coe.edgeFinset := by
    intro a ha
    have he : f.sym2Map a ∈ E := Finset.mem_preimage.mp ha
    have he' := hE he
    induction a using Sym2.ind with
    | _ u v => simpa [f] using he'
  have hle : F.card ≤ E.card := by
    simpa [F, Finset.card_preimage] using
      (Finset.card_filter_le E (fun v => v ∈ Set.range f.sym2Map))
  refine ⟨F, hF, ?_, ?_⟩
  · calc
      (F.card : ℝ) ≤ E.card := by exact_mod_cast hle
      _ ≤ ε * Fintype.card H.verts := by simpa using hcard
  · refine ⟨Coloring.mk (fun v => C v) ?_⟩
    intro u v huv
    apply C.valid
    obtain ⟨huv, hn⟩ := deleteEdges_adj.mp huv
    exact deleteEdges_adj.mpr ⟨huv, fun he => hn (Finset.mem_preimage.mpr he)⟩

/-- An eventually linear lower bound also absorbs the cuts at the finitely many small sizes:
their edge counts are integers and the chosen real bound is below one. -/
theorem exists_small_cut_budget {g : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hlinear : ∃ M : ℕ, ∀ m ≥ M, c * m ≤ (g m : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m a : ℕ, (a : ℝ) ≤ ε * m → a ≤ g m := by
  obtain ⟨M, hM⟩ := hlinear
  let ε : ℝ := min c (1 / ((M : ℝ) + 1))
  have hden : 0 < (M : ℝ) + 1 := by positivity
  have hε : 0 < ε := lt_min hc (one_div_pos.mpr hden)
  have hεc : ε ≤ c := min_le_left _ _
  have hεM : ε * ((M : ℝ) + 1) ≤ 1 := by
    calc
      ε * ((M : ℝ) + 1) ≤ (1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hden.le
      _ = 1 := by field_simp
  refine ⟨ε, hε, ?_⟩
  intro m a ha
  by_cases hm : M ≤ m
  · have := ha.trans ((mul_le_mul_of_nonneg_right hεc (Nat.cast_nonneg m)).trans (hM m hm))
    exact_mod_cast this
  · have hm' : (m : ℝ) < (M : ℝ) + 1 := by exact_mod_cast (show m < M + 1 by omega)
    have ha1 : (a : ℝ) < 1 := lt_of_le_of_lt ha
      ((mul_lt_mul_of_pos_left hm' hε).trans_le hεM)
    have : a < 1 := by exact_mod_cast ha1
    have : a = 0 := by omega
    simp [this]

/-- The outer argument uses the actual finite core only through this interface.
The final theorem supplies this interface from the explicit graph construction. -/
theorem no_admissible_eventual_linear
    (coreExists : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ X : SimpleGraph (Fin n),
      ¬X.Colorable 3 ∧ LocalCutBound ε X)
    {r : ℕ} (hr : 2 ≤ r) {g : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hlinear : ∃ M : ℕ, ∀ m ≥ M, c * m ≤ (g m : ℝ)) : ¬IsAdmissible r g := by
  classical
  obtain ⟨ε, hε, hbudget⟩ := exists_small_cut_budget hc hlinear
  obtain ⟨n, X, hX, hcut⟩ := coreExists ε hε
  let k := r - 2
  have hrk : 2 + k = r := by dsimp [k]; omega
  let Y := cliqueJoin X k
  let N := Fintype.card (Fin n ⊕ Fin k)
  let e : Fin N ≃ (Fin n ⊕ Fin k) := (Fintype.equivFin _).symm
  let G := Y.comap e
  have hlocal : LocalColorCutBound ε r G := by
    rw [← hrk]
    exact localColorCut_comap_equiv (cliqueJoin_localCut hε.le hcut k) e
  intro hadm
  have hchrom := hadm N G (by
    intro H
    obtain ⟨E, hE, hb, hcolor⟩ := localColorCut_subgraph hlocal H
    exact ⟨E, hE, hbudget _ _ hb, hcolor.chromaticNumber_le⟩)
  obtain ⟨C⟩ := chromaticNumber_le_iff_colorable.mp hchrom
  have hY : Y.Colorable (r + 1) := by
    refine ⟨Coloring.mk (fun v => C (e.symm v)) ?_⟩
    intro u v huv
    apply C.valid
    simpa [G] using huv
  have hnum : r + 1 = 3 + k := by omega
  exact cliqueJoin_not_colorable X k hX (hnum ▸ hY)

/-- The analytic notation in the canonical problem yields the exact eventual lower bound. -/
theorem no_admissible_bigO
    (coreExists : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ X : SimpleGraph (Fin n),
      ¬X.Colorable 3 ∧ LocalCutBound ε X)
    {r : ℕ} (hr : 2 ≤ r) :
    ¬∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ)) := by
  rintro ⟨g, hadm, hbig⟩
  obtain ⟨C, hC, hbound⟩ := hbig.exists_pos
  have hevent : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ C * (g n : ℝ) := by
    filter_upwards [hbound.bound] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n),
      abs_of_nonneg (show (0 : ℝ) ≤ g n from Nat.cast_nonneg (g n))] using hn
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  apply no_admissible_eventual_linear coreExists hr (one_div_pos.mpr hC) _ hadm
  refine ⟨M, fun m hm => ?_⟩
  have := hM m hm
  change (1 / C) * (m : ℝ) ≤ (g m : ℝ)
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hC).mpr
  simpa [mul_comm] using this

end Erdos1092
