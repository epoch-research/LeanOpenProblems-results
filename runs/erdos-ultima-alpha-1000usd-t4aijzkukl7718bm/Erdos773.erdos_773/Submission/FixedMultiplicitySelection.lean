import Submission.Hypergraph
import Submission.FractionalSquareSidon
import Submission.APFreeExtraction

/-!
Fixed positive square-difference multiplicity: for each g >= 1, subsets of
roots of size N^(2g/(2g+1)-epsilon) exist eventually. This uses progression-free
extraction to make equal-difference pairs disjoint. At g = 1 this only gives
the already established Sidon exponent 2/3, not the exponent in Erdos 773.
-/
namespace Erdos773.FixedMultiplicitySelection
open Finset Filter
set_option maxHeartbeats 1000000

private def reps (A : Finset ℕ) (D : ℕ) : Finset (A × A) :=
  univ.filter (fun ab => ab.1.val < ab.2.val ∧ ab.2.val ^ 2 = ab.1.val ^ 2 + D)

private def support {A : Finset ℕ} (E : Finset (A × A)) : Finset A :=
  E.image Prod.fst ∪ E.image Prod.snd

private lemma mem_reps {A : Finset ℕ} {D : ℕ} {ab : A × A} :
    ab ∈ reps A D ↔ ab.1.val < ab.2.val ∧ ab.2.val ^ 2 = ab.1.val ^ 2 + D := by
  simp [reps]

private lemma fst_injective {A : Finset ℕ} {D : ℕ} :
    Set.InjOn Prod.fst (reps A D : Set (A × A)) := by
  intro ab hab cd hcd he
  have hab := (mem_reps.mp hab).2
  have hcd := (mem_reps.mp hcd).2
  apply Prod.ext he
  apply Subtype.ext
  have hh : ab.2.val ^ 2 = cd.2.val ^ 2 := by rw [he] at hab; omega
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh

private lemma snd_injective {A : Finset ℕ} {D : ℕ} :
    Set.InjOn Prod.snd (reps A D : Set (A × A)) := by
  intro ab hab cd hcd he
  have hab := (mem_reps.mp hab).2
  have hcd := (mem_reps.mp hcd).2
  apply Prod.ext _ he
  apply Subtype.ext
  have hh : ab.1.val ^ 2 = cd.1.val ^ 2 := by rw [he] at hab; omega
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh

private lemma support_card {A : Finset ℕ} {D : ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n ^ 2)) : Set ℕ))
    {E : Finset (A × A)} (hE : E ⊆ reps A D) :
    (support E).card = 2 * E.card := by
  have hdis : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨ab, hab, hea⟩ := mem_image.mp ha
    obtain ⟨cd, hcd, heb⟩ := mem_image.mp hb
    have hp := mem_reps.mp (hE hab)
    have hq := mem_reps.mp (hE hcd)
    have hm (x : A) : x.val ^ 2 ∈ A.image (fun n : ℕ => n ^ 2) :=
      mem_image.mpr ⟨x.val, x.property, rfl⟩
    have he : cd.1.val ^ 2 + ab.2.val ^ 2 = a.val ^ 2 + a.val ^ 2 := by
      rw [hea] at hp
      rw [heb] at hq
      omega
    have hh := hAP (hm cd.1) (hm a) (hm ab.2) he
    have hv : cd.1.val = a.val := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh
    rw [heb] at hq
    omega
  unfold support
  rw [card_union_of_disjoint hdis,
    card_image_of_injOn (fun p hp q hq he => fst_injective (hE hp) (hE hq) he),
    card_image_of_injOn (fun p hp q hq he => snd_injective (hE hp) (hE hq) he)]
  omega

private def badSupports (A : Finset ℕ) (N g : ℕ) : Finset (Finset A) :=
  (Icc 1 (N ^ 2)).biUnion (fun D => ((reps A D).powersetCard (g + 1)).image support)

private lemma badSupports_size {A : Finset ℕ} {N g : ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n ^ 2)) : Set ℕ))
    {e : Finset A} (he : e ∈ badSupports A N g) : e.card = 2 * g + 2 := by
  obtain ⟨D, hD, he⟩ := mem_biUnion.mp he
  obtain ⟨E, hE, rfl⟩ := mem_image.mp he
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hE
  rw [support_card hAP hsub, hcard]
  omega

private lemma reps_card_le {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N) (D : ℕ) :
    (reps A D).card ≤ (squareDifferenceReps N D).card := by
  apply card_le_card_of_injOn (fun ab => (ab.1.val, ab.2.val))
  · intro ab hab
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hA ab.1.property, hA ab.2.property⟩,
      mem_reps.mp hab⟩
  · intro ab hab cd hcd he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Subtype.ext (congrArg Prod.snd he))

private lemma badSupports_count (A : Finset ℕ) (N g : ℕ) :
    (badSupports A N g).card ≤ ∑ D ∈ Icc 1 (N ^ 2), (reps A D).card ^ (g + 1) := by
  calc
    _ ≤ ∑ D ∈ Icc 1 (N ^ 2), (((reps A D).powersetCard (g + 1)).image support).card :=
      card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum
      intro D hD
      exact card_image_le.trans (by rw [card_powersetCard]; exact Nat.choose_le_pow _ _)

private lemma avoids_bounded {A : Finset ℕ} {N g : ℕ} (hA : A ⊆ Icc 1 N)
    {B : Finset A} (hB : ∀ e ∈ badSupports A N g, ¬e ⊆ B) :
    ∀ D : ℕ, 0 < D → ((reps A D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g := by
  intro D hD
  by_cases hDN : D ≤ N ^ 2
  · by_contra! hlarge
    obtain ⟨E, hE, hcard⟩ := exists_subset_card_eq (show g + 1 ≤
      ((reps A D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card by omega)
    have hsub : E ⊆ reps A D := hE.trans (filter_subset _ _)
    apply hB (support E)
    · exact mem_biUnion.mpr ⟨D, mem_Icc.mpr ⟨hD, hDN⟩,
        mem_image.mpr ⟨E, mem_powersetCard.mpr ⟨hsub, hcard⟩, rfl⟩⟩
    · intro a ha
      rcases mem_union.mp ha with ha | ha
      · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ha
        exact (mem_filter.mp (hE hab)).2.1
      · obtain ⟨ab, hab, rfl⟩ := mem_image.mp ha
        exact (mem_filter.mp (hE hab)).2.2
  · have he : reps A D = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ab hab
      have hh := (mem_reps.mp hab).2
      have hb := (mem_Icc.mp (hA ab.2.property)).2
      have hb2 := Nat.pow_le_pow_left hb 2
      omega
    simp [he]

private lemma image_selection {A : Finset ℕ} {N g : ℕ} (hA : A ⊆ Icc 1 N)
    {B : Finset A} (hB : ∀ D : ℕ, 0 < D →
      ((reps A D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g) :
    ∃ C ⊆ A, C.card = B.card ∧
      ∀ D : ℕ, 0 < D →
        ((squareDifferenceReps N D).filter (fun ab => ab.1 ∈ C ∧ ab.2 ∈ C)).card ≤ g := by
  let C := B.image Subtype.val
  have hC : C ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact b.property
  refine ⟨C, hC, card_image_of_injective B Subtype.val_injective, ?_⟩
  intro D hD
  have he : (squareDifferenceReps N D).filter (fun ab => ab.1 ∈ C ∧ ab.2 ∈ C) =
      ((reps A D).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).image
        (fun ab => (ab.1.val, ab.2.val)) := by
    ext ab
    constructor
    · intro hab
      obtain ⟨hab, ha, hb⟩ := mem_filter.mp hab
      obtain ⟨a, ha, hea⟩ := mem_image.mp ha
      obtain ⟨b, hb, heb⟩ := mem_image.mp hb
      refine mem_image.mpr ⟨(a, b), ?_, Prod.ext hea heb⟩
      apply mem_filter.mpr
      refine ⟨mem_reps.mpr ?_, ha, hb⟩
      simpa only [hea, heb] using (mem_filter.mp hab).2
    · intro hab
      obtain ⟨cd, hcd, rfl⟩ := mem_image.mp hab
      obtain ⟨hcd, hc, hd⟩ := mem_filter.mp hcd
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_product.mpr ⟨hA cd.1.property, hA cd.2.property⟩, mem_reps.mp hcd⟩,
        mem_image.mpr ⟨cd.1, hc, rfl⟩, mem_image.mpr ⟨cd.2, hd, rfl⟩⟩
  rw [he]
  exact card_image_le.trans (hB D hD)

/-- The finite selection bound on an AP-free set of square values. -/
theorem finite_selection {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n ^ 2)) : Set ℕ))
    (g : ℕ) (p K : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hrep : ∀ D ∈ Icc 1 (N ^ 2), ((squareDifferenceReps N D).card : ℝ) ≤ K) :
    ∃ C ⊆ A,
      p * A.card - (N : ℝ) ^ 2 * K ^ (g + 1) * p ^ (2 * g + 2) ≤ C.card ∧
      ∀ D : ℕ, 0 < D →
        ((squareDifferenceReps N D).filter (fun ab => ab.1 ∈ C ∧ ab.2 ∈ C)).card ≤ g := by
  have hnonempty : ∀ e ∈ badSupports A N g, e.Nonempty := by
    intro e he
    have hh := badSupports_size hAP he
    exact card_pos.mp (by omega)
  obtain ⟨B, hB, hcard⟩ := alteration_bound (badSupports A N g) hnonempty p hp hp1
  have hcount : ((badSupports A N g).card : ℝ) ≤ (N : ℝ) ^ 2 * K ^ (g + 1) := by
    calc
      _ ≤ ∑ D ∈ Icc 1 (N ^ 2), ((reps A D).card : ℝ) ^ (g + 1) := by
        exact_mod_cast badSupports_count A N g
      _ ≤ ∑ D ∈ Icc 1 (N ^ 2), K ^ (g + 1) := by
        apply sum_le_sum
        intro D hD
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        have hh : ((reps A D).card : ℝ) ≤ (squareDifferenceReps N D).card := by
          exact_mod_cast reps_card_le hA D
        exact hh.trans (hrep D hD)
      _ = _ := by simp
  have hcost : (∑ e ∈ badSupports A N g, p ^ e.card) ≤
      (N : ℝ) ^ 2 * K ^ (g + 1) * p ^ (2 * g + 2) := by
    calc
      _ = ∑ e ∈ badSupports A N g, p ^ (2 * g + 2) := by
        apply sum_congr rfl
        intro e he
        rw [badSupports_size hAP he]
      _ = ((badSupports A N g).card : ℝ) * p ^ (2 * g + 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg hp _)
  obtain ⟨C, hC, hc, hdiff⟩ := image_selection hA (avoids_bounded hA hB)
  refine ⟨C, hC, ?_, hdiff⟩
  rw [hc]
  simp only [Fintype.card_coe] at hcard
  linarith

private lemma ap_free_roots (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Icc 1 N,
      ThreeAPFree ((A.image (fun n : ℕ => n ^ 2)) : Set ℕ) ∧
      (N : ℝ) ^ (1 - ε) ≤ A.card := by
  filter_upwards [APFreeExtraction.square_ap_free_near_linear ε hε] with N hN
  obtain ⟨B, hB, hAP, hc⟩ := hN
  let A := (Icc 1 N).filter (fun n => n ^ 2 ∈ B)
  have he : A.image (fun n : ℕ => n ^ 2) = B := by
    ext b
    constructor
    · intro hb
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
      exact (mem_filter.mp hn).2
    · intro hb
      obtain ⟨n, hn, rfl⟩ := mem_image.mp (hB hb)
      exact mem_image.mpr ⟨n, mem_filter.mpr ⟨hn, hb⟩, rfl⟩
  have hcard : B.card = A.card := by
    rw [← he]
    exact card_image_of_injective _ (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0))
  refine ⟨A, filter_subset _ _, ?_, ?_⟩
  · rwa [he]
  · rwa [hcard] at hc

/-- Quantitative fixed-capacity selection. For g = 1 the exponent is 2/3,
so this theorem does not prove the near-linear Sidon conjecture. -/
theorem fixed_multiplicity (g : ℕ) (hg : 1 ≤ g) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Icc 1 N,
      (N : ℝ) ^ (1 - 1 / (2 * (g : ℝ) + 1) - ε) ≤ A.card ∧
      ∀ D : ℕ, 0 < D →
        ((squareDifferenceReps N D).filter (fun ab => ab.1 ∈ A ∧ ab.2 ∈ A)).card ≤ g := by
  let q : ℝ := 1 / (2 * g + 1)
  let ρ : ℝ := 3 * g * ε / 4
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hqmul : q * (2 * g + 1) = 1 := by dsimp [q]; field_simp
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) (ht ρ hρ)
  have hslack := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
    (ht (ε / 4) (by positivity))
  filter_upwards [ap_free_roots (ε / 4) (by positivity),
    Fractional.eventually_representation_bound (ε / 8) (by positivity),
    hsmall, hslack, eventually_ge_atTop 1] with N hAP hrep hsmall hslack hN
  obtain ⟨A, hA, hAP, hAc⟩ := hAP
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  let p : ℝ := (N : ℝ) ^ (-q - ε / 2)
  let K : ℝ := (N : ℝ) ^ (ε / 4)
  let S : ℝ := (N : ℝ) ^ (1 - q - 3 * ε / 4)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  have hK (D : ℕ) (hD : D ∈ Icc 1 (N ^ 2)) :
      ((squareDifferenceReps N D).card : ℝ) ≤ K := by
    simpa only [K, show 2 * (ε / 8) = ε / 4 by ring] using hrep D (mem_Icc.mp hD).1
  obtain ⟨C, hC, hcard, hdiff⟩ := finite_selection hA hAP g p K hp hp1 hK
  have hleading : S ≤ p * A.card := by
    calc
      _ = p * (N : ℝ) ^ (1 - ε / 4) := by
        dsimp [p, S]
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAc hp
  have hcost : (N : ℝ) ^ 2 * K ^ (g + 1) * p ^ (2 * g + 2) =
      S * (N : ℝ) ^ (-ρ) := by
    dsimp [K, p, S, ρ]
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
      ← Real.rpow_natCast (N : ℝ) 2]
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    nlinarith only [hqmul]
  have htarget : (N : ℝ) ^ (1 - 1 / (2 * (g : ℝ) + 1) - ε) =
      S * (N : ℝ) ^ (-(ε / 4)) := by
    dsimp [S, q]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have herror := mul_le_mul_of_nonneg_left hsmall hS
  have htargetle := mul_le_mul_of_nonneg_left hslack hS
  rw [hcost] at hcard
  refine ⟨C, hC.trans hA, ?_, hdiff⟩
  rw [htarget]
  nlinarith only [hcard, hleading, herror, htargetle]

#print axioms fixed_multiplicity
#print axioms finite_selection
end Erdos773.FixedMultiplicitySelection
