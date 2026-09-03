import FormalConjecturesUtil

/-! Trimming high-degree vertices from the supports of a finite hypergraph.
Vertices are not deleted: edges meeting two or more hubs are counted separately. -/
namespace Erdos1206.HypergraphHubTrimming
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V]

noncomputable def degree (E : Finset (Finset V)) (v : V) : ℕ :=
  (E.filter (fun e => v∈e)).card

noncomputable def vertices (E : Finset (Finset V)) : Finset V := E.biUnion id

noncomputable def hubs (E : Finset (Finset V)) (D : ℕ) : Finset V :=
  (vertices E).filter (fun v => D < degree E v)

noncomputable def bad (E : Finset (Finset V)) (H : Finset V) : Finset (Finset V) :=
  E.filter (fun e => 2 ≤ (e∩H).card)

noncomputable def good (E : Finset (Finset V)) (H : Finset V) : Finset (Finset V) :=
  E.filter (fun e => (e∩H).card ≤ 1)

lemma degree_eq_zero_of_not_vertex {E : Finset (Finset V)} {v : V}
    (hv : v∉vertices E) : degree E v=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hve⟩ := mem_filter.mp he
  exact hv (mem_biUnion.mpr ⟨e,he,hve⟩)

lemma not_hub_degree_le {E : Finset (Finset V)} {D : ℕ} {v : V}
    (hv : v∉hubs E D) : degree E v ≤ D := by
  by_cases hver : v∈vertices E
  · have hn : ¬D < degree E v := fun hh => hv (mem_filter.mpr ⟨hver,hh⟩)
    omega
  · rw [degree_eq_zero_of_not_vertex hver]
    exact Nat.zero_le _

lemma sum_degrees (E : Finset (Finset V)) :
    (∑ v∈vertices E, degree E v)=∑ e∈E, e.card := by
  have hdeg (v : V) : degree E v=∑ e∈E, if v∈e then (1:ℕ) else 0 := by
    simp [degree]
  simp_rw [hdeg]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hs : (vertices E).filter (fun v => v∈e)=e := by
    ext v
    simp only [mem_filter]
    exact ⟨And.right,fun hv => ⟨mem_biUnion.mpr ⟨e,he,hv⟩,hv⟩⟩
  simp only [sum_boole,hs,Nat.cast_id]

/-- The hub threshold times the number of hubs is at most the total incidence count. -/
theorem hubs_card_mul_le (E : Finset (Finset V)) (D r : ℕ)
    (hr : ∀ e∈E, e.card ≤ r) : (hubs E D).card*D ≤ r*E.card := by
  calc
    _ = ∑ _v∈hubs E D, D := by simp
    _ ≤ ∑ v∈hubs E D, degree E v := by
      apply sum_le_sum
      intro v hv
      exact (mem_filter.mp hv).2.le
    _ ≤ ∑ v∈vertices E, degree E v := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) (by intros; exact Nat.zero_le _)
    _ = ∑ e∈E, e.card := sum_degrees E
    _ ≤ ∑ _e∈E, r := sum_le_sum hr
    _ = _ := by simp [Nat.mul_comm]

/-- Pair-codegrees bound the number of edges meeting at least two hubs. -/
theorem bad_card_le (E : Finset (Finset V)) (H : Finset V) (L : ℕ)
    (hL : ∀ x y : V, x≠y → (E.filter (fun e => x∈e ∧ y∈e)).card ≤ L) :
    (bad E H).card ≤ H.card^2*L := by
  let T : V×V → Finset (Finset V) := fun p =>
    if p.1=p.2 then ∅ else E.filter (fun e => p.1∈e ∧ p.2∈e)
  have hs : bad E H ⊆ (H ×ˢ H).biUnion T := by
    intro e he
    obtain ⟨he,hcard⟩ := mem_filter.mp he
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < (e∩H).card by omega)
    refine mem_biUnion.mpr ⟨(x,y),mem_product.mpr ⟨(mem_inter.mp hx).2,(mem_inter.mp hy).2⟩,?_⟩
    dsimp only [T]
    rw [if_neg hxy]
    exact mem_filter.mpr ⟨he,(mem_inter.mp hx).1,(mem_inter.mp hy).1⟩
  have hT (p : V×V) : (T p).card ≤ L := by
    dsimp only [T]
    split_ifs with h
    · simp
    · exact hL _ _ h
  calc
    _ ≤ ((H ×ˢ H).biUnion T).card := card_le_card hs
    _ ≤ ∑ p∈H ×ˢ H, (T p).card := card_biUnion_le
    _ ≤ ∑ _p∈H ×ˢ H, L := sum_le_sum (fun p _ => hT p)
    _ = H.card^2*L := by simp [pow_two]

lemma good_support_size {E : Finset (Finset V)} {H e : Finset V}
    (he : e∈good E H) (hcard : e.card=4) :
    3 ≤ (e\H).card ∧ (e\H).card ≤ 4 := by
  have hh := (mem_filter.mp he).2
  have hc := card_sdiff_add_card_inter e H
  omega

/-- After ignoring the hub coordinates, every remaining coordinate has degree
at most the threshold. This statement does not condition on hub labels. -/
lemma good_degree_le (E : Finset (Finset V)) (D : ℕ) (v : V) :
    ((good E (hubs E D)).filter (fun e => v∈e\hubs E D)).card ≤ D := by
  by_cases hv : v∈hubs E D
  · have he : (good E (hubs E D)).filter (fun e => v∈e\hubs E D)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      exact (mem_sdiff.mp (mem_filter.mp he).2).2 hv
    rw [he,card_empty]
    exact Nat.zero_le _
  · calc
      _ ≤ degree E v := card_le_card (by
        intro e he
        obtain ⟨he,hv'⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_sdiff.mp hv').1⟩)
      _ ≤ D := not_hub_degree_le hv

#print axioms hubs_card_mul_le
#print axioms bad_card_le
#print axioms good_degree_le
end Erdos1206.HypergraphHubTrimming
