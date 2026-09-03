import Submission.SmallGraphEncoding
import Submission.NoTwoCyclesTransport

/-! Padding a finite graph with isolated vertices before binary encoding. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.PaddedGraphEncoding
open SmallGraphEncoding
variable {V W : Type*} [Fintype V] [Fintype W]
set_option maxHeartbeats 1000000

lemma degree_map (G : SimpleGraph V) (f : V ↪ W) (v : V) :
    (G.map f).degree (f v) = G.degree v := by
  have hN : (G.map f).neighborSet (f v) = f '' G.neighborSet v := by
    ext w
    constructor
    · rintro ⟨x,y,hxy,hx,hy⟩
      have hxv := f.injective hx
      subst x
      exact ⟨y,hxy,hy⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨v,y,hy,rfl,rfl⟩
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq,hN,Set.ncard_image_of_injective _ f.injective]

lemma degree_map_outside (G : SimpleGraph V) (f : V ↪ W) (v : W)
    (hv : v ∉ Set.range f) : (G.map f).degree v = 0 := by
  apply ((G.map f).degree_eq_zero_iff_notMem_support v).mpr
  rintro ⟨w,x,y,hxy,hx,hy⟩
  exact hv ⟨x,hx⟩

lemma sum_degreeCode (N d code : ℕ) :
    ((List.range N).map (degreeCode N d code)).sum =
      2 * (graph N d code).edgeSet.ncard := by
  have hh := (graph N d code).sum_degrees_eq_twice_card_edges
  simp_rw [graph_degree] at hh
  rw [Fin.sum_univ_eq_sum_range (degreeCode N d code) N] at hh
  rw [← List.toFinset_range,List.sum_toFinset _ List.nodup_range] at hh
  simpa only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh

lemma exists_padded_encoding {n N M d : ℕ} (table : EdgeTable N M)
    (G : SimpleGraph V) (v : V) (hn : Fintype.card V = n)
    (hpad : n ≤ N) (hd : G.degree v = d) :
    ∃ (e : Fin n ≃ V) (code : ℕ), code < 2^M ∧
      graph N d code = G.map (e.symm.toEmbedding.trans (Fin.castLEEmb hpad)) := by
  obtain ⟨e,he0,heN⟩ := FiniteNeighborLabels.exists_labeling G v n d hn hd
  let f : V ↪ Fin N := e.symm.toEmbedding.trans (Fin.castLEEmb hpad)
  have hnpos : 0 < n := by have := G.degree_lt_card_verts v; omega
  have hdn : d < n := by have := G.degree_lt_card_verts v; omega
  have hfv : (f v).val = 0 := by
    have hh : e.symm v = ⟨0,hnpos⟩ := by rw [← he0,e.symm_apply_apply]
    change (e.symm v).val = 0
    rw [hh]
  have hfval (x : V) : (f x).val = (e.symm x).val := rfl
  have hfN (x : V) : G.Adj v x ↔ 0 < (f x).val ∧ (f x).val ≤ d := by
    simpa only [e.apply_symm_apply,hfval] using heN (e.symm x)
  have hroot : ∀ i j : Fin N, i.val = 0 →
      ((G.map f).Adj i j ↔ 0 < j.val ∧ j.val ≤ d) := by
    intro i j hi
    have hiv : i = f v := Fin.ext (hi.trans hfv.symm)
    rw [hiv]
    constructor
    · rintro ⟨x,y,hxy,hx,hy⟩
      have hxv := f.injective hx
      subst x
      simpa only [hy] using (hfN y).mp hxy
    · rintro ⟨hjpos,hjd⟩
      let j' : Fin n := ⟨j.val,by omega⟩
      have hfj : f (e j') = j := by
        apply Fin.ext
        change (e.symm (e j')).val = j.val
        rw [e.symm_apply_apply]
      refine ⟨v,e j',?_,rfl,hfj⟩
      apply (heN j').mpr
      exact ⟨hjpos,hjd⟩
  obtain ⟨code,hcode,hG⟩ := encode_graph table (G.map f) d hroot
  exact ⟨e,code,hcode,hG⟩

lemma padded_degree {n N : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V)
    (hpad : n ≤ N) (i : Fin n) :
    (G.map (e.symm.toEmbedding.trans (Fin.castLEEmb hpad))).degree
      (Fin.castLE hpad i) = G.degree (e i) := by
  have hh := degree_map G (e.symm.toEmbedding.trans (Fin.castLEEmb hpad)) (e i)
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  simpa only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,
    Fin.castLEEmb_apply,Equiv.symm_apply_apply] using hh

lemma padded_degree_outside {n N : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V)
    (hpad : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    (G.map (e.symm.toEmbedding.trans (Fin.castLEEmb hpad))).degree i = 0 := by
  have hz : i ∉ Set.range (e.symm.toEmbedding.trans (Fin.castLEEmb hpad)) := by
    rintro ⟨x,hx⟩
    have hh := congrArg Fin.val hx
    change (e.symm x).val = i.val at hh
    have := (e.symm x).isLt
    omega
  have hh := degree_map_outside G (e.symm.toEmbedding.trans (Fin.castLEEmb hpad)) i hz
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh

end Erdos184.PaddedGraphEncoding
