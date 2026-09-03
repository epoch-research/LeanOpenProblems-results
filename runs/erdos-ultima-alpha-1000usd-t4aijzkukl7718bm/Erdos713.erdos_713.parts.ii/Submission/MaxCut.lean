import FormalConjecturesUtil

/-! A bipartite subgraph retaining at least half of all edges. -/

open SimpleGraph Finset

namespace Erdos713Cut

variable {V : Type*}

def cut (G : SimpleGraph V) (χ : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ χ u ≠ χ v
  symm := fun u v h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun v h => h.1.ne rfl

theorem cut_le (G : SimpleGraph V) (χ : V → Bool) : cut G χ ≤ G := fun _ _ h => h.1

theorem cut_bipartite (G : SimpleGraph V) (χ : V → Bool) : (cut G χ).IsBipartite := by
  let C : (cut G χ).Coloring Bool := ⟨χ, fun h => h.2⟩
  simpa using C.colorable

open scoped Classical in
theorem twice_card_colorings [Fintype V] {u v : V} (huv : u ≠ v) :
    2 * (univ.filter (fun χ : V → Bool => χ u ≠ χ v)).card = Fintype.card (V → Bool) := by
  classical
  let p : (V → Bool) → Prop := fun χ => χ u ≠ χ v
  let flip : (V → Bool) → (V → Bool) := fun χ => Function.update χ u (!(χ u))
  have hinv : Function.Involutive flip := by
    intro χ
    funext w
    by_cases hw : w = u
    · subst w
      simp [flip]
    · simp [flip, hw]
  have hcard : (univ.filter p).card = (univ.filter (fun χ => ¬p χ)).card := by
    apply card_bijective flip hinv.bijective
    intro χ
    cases h₁ : χ u <;> cases h₂ : χ v <;>
      simp [p, flip, huv, huv.symm, h₁, h₂]
  have hh := card_filter_add_card_filter_not (s := (univ : Finset (V → Bool))) p
  rw [← hcard] at hh
  simpa only [card_univ, two_mul] using hh

open scoped Classical in
theorem exists_bipartite_half [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ K : SimpleGraph V, K ≤ G ∧ K.IsBipartite ∧ G.edgeFinset.card ≤ 2 * K.edgeFinset.card := by
  classical
  let r : (V → Bool) → G.Dart → Prop := fun χ d => χ d.fst ≠ χ d.snd
  have hAbove (χ : V → Bool) :
      ((univ : Finset G.Dart).bipartiteAbove r χ).card = 2 * (cut G χ).edgeFinset.card := by
    let e : ↥((univ : Finset G.Dart).bipartiteAbove r χ) ≃ (cut G χ).Dart :=
      { toFun := fun d => ⟨d.val.toProd, ⟨d.val.adj, ((mem_bipartiteAbove r).mp d.prop).2⟩⟩
        invFun := fun d => ⟨⟨d.toProd, d.adj.1⟩,
          (mem_bipartiteAbove r).mpr ⟨mem_univ _, d.adj.2⟩⟩
        left_inv := by intro d; rfl
        right_inv := by intro d; rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, dart_card_eq_twice_card_edges]
  have hBelow (d : G.Dart) :
      2 * ((univ : Finset (V → Bool)).bipartiteBelow r d).card = Fintype.card (V → Bool) :=
    twice_card_colorings d.adj.ne
  obtain ⟨χ₀, _, hmax⟩ := exists_max_image (univ : Finset (V → Bool))
    (fun χ => (cut G χ).edgeFinset.card) ⟨fun _ => false, mem_univ _⟩
  refine ⟨cut G χ₀, cut_le G χ₀, cut_bipartite G χ₀, ?_⟩
  let N := Fintype.card (V → Bool)
  let M := (cut G χ₀).edgeFinset.card
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := r)
    (s := (univ : Finset (V → Bool))) (t := (univ : Finset G.Dart))
  simp_rw [hAbove] at hsum
  have hDouble : 4 * (∑ χ : V → Bool, (cut G χ).edgeFinset.card) =
      (2 * G.edgeFinset.card) * N := by
    calc
      4 * (∑ χ : V → Bool, (cut G χ).edgeFinset.card) =
          2 * (∑ χ : V → Bool, 2 * (cut G χ).edgeFinset.card) := by
        rw [← mul_sum]
        ring
      _ = 2 * (∑ d : G.Dart, ((univ : Finset (V → Bool)).bipartiteBelow r d).card) :=
        congrArg (2 * ·) hsum
      _ = ∑ d : G.Dart, 2 * ((univ : Finset (V → Bool)).bipartiteBelow r d).card := by rw [mul_sum]
      _ = ∑ _ : G.Dart, N := sum_congr rfl fun d _ => hBelow d
      _ = (2 * G.edgeFinset.card) * N := by
        simp only [sum_const, card_univ, Nat.nsmul_eq_mul, dart_card_eq_twice_card_edges]
  have hSumle : (∑ χ : V → Bool, (cut G χ).edgeFinset.card) ≤ N * M := by
    calc
      (∑ χ : V → Bool, (cut G χ).edgeFinset.card) ≤ ∑ _ : V → Bool, M :=
        sum_le_sum fun χ hχ => hmax χ hχ
      _ = N * M := by simp only [sum_const, card_univ, Nat.nsmul_eq_mul, N]
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have hMul : N * G.edgeFinset.card ≤ N * (2 * M) := by
    nlinarith only [hDouble, hSumle]
  exact (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_comm] using hMul)

end Erdos713Cut

#print axioms Erdos713Cut.exists_bipartite_half
