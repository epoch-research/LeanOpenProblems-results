import FormalConjecturesUtil

/-! Restricted characteristic-two polarity graphs.  These are actual regular
C4-free graphs, but are not asserted to be extremal graphs. -/
open SimpleGraph
namespace Erdos713RestrictedPolarity
variable {K : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 1000000

/-- A nonzero set of first coordinates removes all loops from the polarity
relation in characteristic two. -/
def graph (A : Finset K) (hA : (0 : K) ∉ A) : SimpleGraph (A × K) where
  Adj u v := u.2 + v.2 = (u.1 : K) * (v.1 : K)
  symm u v h := by simpa only [add_comm, mul_comm] using h
  loopless u h := by
    have hz : (u.1 : K) * (u.1 : K) = 0 :=
      h.symm.trans (CharTwo.add_self_eq_zero _)
    have hu : (u.1 : K) = 0 := (mul_self_eq_zero.mp hz)
    exact hA (hu ▸ u.1.property)

lemma common_neighbor_unique (A : Finset K) (hA : (0 : K) ∉ A)
    {u v x y : A × K} (huv : u ≠ v)
    (hux : (graph A hA).Adj u x) (hvx : (graph A hA).Adj v x)
    (huy : (graph A hA).Adj u y) (hvy : (graph A hA).Adj v y) : x = y := by
  change u.2 + x.2 = (u.1 : K) * (x.1 : K) at hux
  change v.2 + x.2 = (v.1 : K) * (x.1 : K) at hvx
  change u.2 + y.2 = (u.1 : K) * (y.1 : K) at huy
  change v.2 + y.2 = (v.1 : K) * (y.1 : K) at hvy
  have hfst : (u.1 : K) ≠ (v.1 : K) := by
    intro he
    apply huv
    refine Prod.ext (Subtype.ext he) ?_
    linear_combination hux - hvx + ((x.1 : K) * he)
  have hz : ((u.1 : K) - (v.1 : K)) * ((x.1 : K) - (y.1 : K)) = 0 := by
    linear_combination -hux + hvx + huy - hvy
  have hxy : (x.1 : K) = (y.1 : K) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hfst))
  refine Prod.ext (Subtype.ext hxy) ?_
  linear_combination hux - huy + ((u.1 : K) * hxy)

lemma c4_free (A : Finset K) (hA : (0 : K) ∉ A) :
    (cycleGraph 4).Free (graph A hA) := by
  rintro ⟨f⟩
  have h02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (f.injective h)
  have he : f 1 = f 3 := common_neighbor_unique A hA h02
    (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 1))
    (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 2 1))
    (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 3))
    (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 2 3))
  exact (by decide : (1 : Fin 4) ≠ 3) (f.injective he)

/-- The first coordinate parametrizes every neighbourhood exactly. -/
noncomputable def neighborEquiv (A : Finset K) (hA : (0 : K) ∉ A) (v : A × K) :
    (graph A hA).neighborSet v ≃ A where
  toFun w := w.1.1
  invFun a := ⟨(a, (v.1 : K) * (a : K) - v.2), by change v.2 + _ = _; ring⟩
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    have hw := w.2
    change v.2 + w.1.2 = (v.1 : K) * (w.1.1 : K) at hw
    dsimp
    linear_combination -hw
  right_inv a := rfl

open scoped Classical in
lemma degree_eq [Fintype K] (A : Finset K) (hA : (0 : K) ∉ A) (v : A × K) :
    (graph A hA).degree v = A.card := by
  rw [← card_neighborSet_eq_degree]
  simpa using Fintype.card_congr (neighborEquiv A hA v)

open scoped Classical in
lemma edge_count [Fintype K] (A : Finset K) (hA : (0 : K) ∉ A) :
    2 * (graph A hA).edgeFinset.card = A.card ^ 2 * Fintype.card K := by
  rw [← sum_degrees_eq_twice_card_edges]
  simp only [degree_eq, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_coe, nsmul_eq_mul, Nat.cast_id]
  ring

open scoped Classical in
lemma exists_regular_c4_free [Fintype K] (d : ℕ) (hd : d < Fintype.card K) :
    ∃ G : SimpleGraph (Fin (d * Fintype.card K)),
      (cycleGraph 4).Free G ∧ (∀ v, G.degree v = d) ∧
      2 * G.edgeFinset.card = d ^ 2 * Fintype.card K := by
  have hcard : d ≤ ((Finset.univ : Finset K).erase 0).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨A, hsub, hAcard⟩ := Finset.exists_subset_card_eq hcard
  have hA : (0 : K) ∉ A := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
  have hc : Fintype.card (A × K) = d * Fintype.card K := by
    simp only [Fintype.card_prod, Fintype.card_coe, hAcard]
  let e : (A × K) ≃ Fin (d * Fintype.card K) :=
    Fintype.equivFinOfCardEq hc
  let G := (graph A hA).map e.toEmbedding
  let iso : graph A hA ≃g G := Iso.map e (graph A hA)
  refine ⟨G, ?_, ?_, ?_⟩
  · intro hf
    exact c4_free A hA (hf.trans ⟨iso.symm.toCopy⟩)
  · intro v
    have hv := iso.symm.degree_eq v
    have hdv := (degree_eq A hA (iso.symm v)).trans hAcard
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hdv ⊢
    exact hv.symm.trans hdv
  · have he := iso.card_edgeFinset_eq
    have hec := edge_count A hA
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at he hec ⊢
    rw [← he]
    simpa only [hAcard] using hec

#print axioms c4_free
#print axioms degree_eq
#print axioms edge_count
#print axioms exists_regular_c4_free
end Erdos713RestrictedPolarity
