import Erdos1092.Basic

namespace Erdos1092

open SimpleGraph

theorem localCutBound_comap_equiv {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {ε : ℝ} {G : SimpleGraph V} (e : W ≃ V)
    (h : LocalCutBound ε G) : LocalCutBound ε (G.comap e) := by
  classical
  intro H hH S hS
  let H' := H.comap e.symm
  let S' := S.map e.toEmbedding
  have hH' : H' ≤ G := by
    intro u v huv
    have hh := hH huv
    simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hh
  have hS' : ∀ ⦃u v⦄, H'.Adj u v → u ∈ S' ∧ v ∈ S' := by
    intro u v huv
    obtain ⟨hu, hv⟩ := hS huv
    constructor
    · exact Finset.mem_map.mpr ⟨e.symm u, hu, e.apply_symm_apply u⟩
    · exact Finset.mem_map.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩
  obtain ⟨E, hE, hcard, ⟨c⟩⟩ := h H' hH' S' hS'
  let E' := E.map e.symm.toEmbedding.sym2Map
  refine ⟨E', ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ E.map e.symm.toEmbedding.sym2Map at hq
    obtain ⟨q0, hq0, heq⟩ := Finset.mem_map.mp hq
    rw [← heq]
    have he := hE hq0
    revert he
    refine Sym2.inductionOn q0 (fun u v he => ?_)
    simpa only [Function.Embedding.sym2Map_apply, Sym2.map_mk,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      H', SimpleGraph.comap_adj, Equiv.toEmbedding_apply] using he
  · simpa only [E', S', Finset.card_map] using hcard
  · refine ⟨Coloring.mk (fun w => c (e w)) ?_⟩
    intro u v huv
    apply c.valid
    rw [SimpleGraph.deleteEdges_adj] at huv ⊢
    refine ⟨?_, ?_⟩
    · simpa only [H', SimpleGraph.comap_adj, Equiv.symm_apply_apply] using huv.1
    · intro hmem
      apply huv.2
      apply Finset.mem_map.mpr
      refine ⟨s(e u, e v), hmem, ?_⟩
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk,
        Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

theorem not_colorable_comap_equiv {V W : Type*}
    {G : SimpleGraph V} {n : ℕ} (e : W ≃ V)
    (h : ¬ G.Colorable n) : ¬ (G.comap e).Colorable n := by
  rintro ⟨c⟩
  apply h
  refine ⟨Coloring.mk (fun v => c (e.symm v)) ?_⟩
  intro u v huv
  apply c.valid
  simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply] using huv

end Erdos1092
