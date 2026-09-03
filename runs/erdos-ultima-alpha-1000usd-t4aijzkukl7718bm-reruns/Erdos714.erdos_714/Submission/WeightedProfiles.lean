import Submission.TensorObstruction

/-! A counting obstruction for complete weighted point relations. This does not
settle the balanced Zarankiewicz conjecture. -/
noncomputable section
open Classical Finset SimpleGraph
namespace Erdos714WeightedProfiles
variable {X Y W : Type*} [CommGroup W]

def graph (h : X → Y → W) (valid : X → Y → Prop) :
    SimpleGraph ((X × W) ⊕ (Y × W)) :=
  Erdos714Tensor.incidence fun p q => valid p.1 q.1 ∧ h p.1 q.1 = p.2*q.2

/-- Four fixed point rows have only three independent multiplicative profiles. -/
theorem not_free_of_profiles [Fintype W] (h : X → Y → W)
    (valid : X → Y → Prop) (x : Fin 4 ↪ X) (S : Finset Y)
    (hS : ∀ y ∈ S, ∀ i, valid (x i) y)
    (hcard : 3 * Fintype.card W^3 < S.card) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph h valid) := by
  let profile (y : Y) : Fin 3 → W := fun i => h (x i.succ) y / h (x 0) y
  obtain ⟨v, _, hv⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := (univ : Finset (Fin 3 → W))) (f := profile)
    (fun _ _ => mem_univ _) (n := 3) (by simpa [Nat.mul_comm] using hcard)
  obtain ⟨y, hy⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := S.filter (profile · = v)) (by simpa using hv)
  have hyS (j : Fin 4) : y j ∈ S := (mem_filter.mp (hy ⟨j,rfl⟩)).1
  have hyP (j : Fin 4) : profile (y j) = v := (mem_filter.mp (hy ⟨j,rfl⟩)).2
  let a : Fin 4 → W := Fin.cases 1 v
  let L : Fin 4 → X × W := fun i => (x i,a i)
  let R : Fin 4 → Y × W := fun j => (y j,h (x 0) (y j))
  have hL : Function.Injective L := by
    intro i j hij
    exact x.injective (congrArg Prod.fst hij)
  have hR : Function.Injective R := by
    intro i j hij
    exact y.injective (congrArg Prod.fst hij)
  have edge (i j : Fin 4) : valid (L i).1 (R j).1 ∧
      h (L i).1 (R j).1 = (L i).2*(R j).2 := by
    refine ⟨hS _ (hyS j) i, ?_⟩
    induction i using Fin.cases with
    | zero => simp [L,R,a]
    | succ i =>
      have hp : h (x i.succ) (y j) / h (x 0) (y j) = v i :=
        congrFun (hyP j) i
      simpa [L,R,a] using (div_eq_iff_eq_mul.mp hp)
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim (fun i => Sum.inl (L i)) (fun j => Sum.inr (R j)), ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => simp at huv
      | inr j => exact edge i j
    | inr j =>
      cases v with
      | inl i => exact edge i j
      | inr k => simp at huv
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (hL (Sum.inl.inj huv))
      | inr j => cases huv
    | inr i =>
      cases v with
      | inl j => cases huv
      | inr j => exact congrArg Sum.inr (hR (Sum.inr.inj huv))

/-- Bounded point-dependent deletions do not evade the profile obstruction. -/
theorem not_free_of_bounded_deletions [Fintype W] [Fintype Y]
    (h : X → Y → W) (valid : X → Y → Prop) (x : Fin 4 ↪ X) (b : ℕ)
    (hbad : ∀ i, (univ.filter (fun y => ¬ valid (x i) y)).card ≤ b)
    (hcard : 3 * Fintype.card W^3 + 4*b < Fintype.card Y) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph h valid) := by
  let bad (i : Fin 4) : Finset Y := univ.filter (fun y => ¬ valid (x i) y)
  let B := univ.biUnion bad
  have hB : B.card ≤ 4*b := by
    calc
      B.card ≤ ∑ i : Fin 4, (bad i).card := card_biUnion_le
      _ ≤ ∑ _i : Fin 4, b := sum_le_sum (fun i _ => hbad i)
      _ = 4*b := by simp
  apply not_free_of_profiles h valid x (univ \ B)
  · intro y hy i
    have hyB : y ∉ B := (mem_sdiff.mp hy).2
    simpa [B,bad] using fun hb : ¬ valid (x i) y =>
      hyB (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hb⟩⟩)
  · have hsplit := card_sdiff_add_card_inter (univ : Finset Y) B
    simp only [univ_inter, card_univ] at hsplit
    omega

end Erdos714WeightedProfiles
#print axioms Erdos714WeightedProfiles.not_free_of_profiles
#print axioms Erdos714WeightedProfiles.not_free_of_bounded_deletions
