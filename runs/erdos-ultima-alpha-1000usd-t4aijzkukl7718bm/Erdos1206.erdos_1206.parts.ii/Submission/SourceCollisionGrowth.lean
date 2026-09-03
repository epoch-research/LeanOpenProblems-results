import Submission.LargePrimeSource
import Submission.Compactness

/-!
Conditional full-prefix collision growth on robust multiplicative sources.
This is an obstruction to a counting approach, not a settlement of the conjecture.
-/

namespace Erdos1206
open Filter Finset
open scoped Classical
open CubeCollisionGrowth PrimitiveCollisionMass

lemma largePrimeSource_mul_eventually {k : ℕ} (hk : 0 < k) (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, n ∈ largePrimeSource (2*k) → m*n ∈ largePrimeSource k := by
  filter_upwards [eventually_gt_atTop (m^(2*(k-1)))] with n hn hsrc
  obtain ⟨hn0,p,hp,hpn,hpow⟩ := hsrc
  refine ⟨Nat.mul_pos hm hn0,p,hp,dvd_mul_of_dvd_right hpn m,?_⟩
  have he : 2*k-1 = 2*(k-1)+1 := by omega
  have hlarge : (m*n)^(2*(k-1)) < n^(2*k-1) := by
    rw [he,pow_succ,mul_pow]
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hn (pow_pos hn0 (2*(k-1)))
  have hsq : ((m*n)^(k-1))^2 < (p^k)^2 := by
    simpa only [← pow_mul, Nat.mul_comm] using hlarge.trans hpow
  exact (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp hsq

noncomputable def sourceCollisionsUpTo (D : Set ℕ) (N : ℕ) : Finset Quad := by
  classical
  exact (collisionsUpTo N).filter (fun x =>
    x.1 ∈ D ∧ x.2.1 ∈ D ∧ x.2.2.1 ∈ D ∧ x.2.2.2 ∈ D)



/-- Each fixed positive multiplier eventually sends the source `B` into `D`. -/
def EventuallyDilatesInto (B D : Set ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ᶠ q : ℕ in atTop, q ∈ B → m*q ∈ D

private lemma source_finite_count {B D : Set ℕ}
    (hBD : EventuallyDilatesInto B D) (F : Finset Collision) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℕ,
      ∑ e ∈ F, (((range (N / e.val.2.2.2)).filter
        (fun q => q ∈ B ∧ L ≤ q)).card) ≤ (sourceCollisionsUpTo D N).card := by
  classical
  have hev (e : Collision) : ∀ᶠ q : ℕ in atTop, q ∈ B →
      e.val.1*q ∈ D ∧ e.val.2.1*q ∈ D ∧
      e.val.2.2.1*q ∈ D ∧ e.val.2.2.2*q ∈ D := by
    have he := e.property
    filter_upwards [hBD _ he.1, hBD _ (he.1.trans he.2.1),
      hBD _ (he.1.trans (he.2.1.trans he.2.2.1)),
      hBD _ (primitive_height_pos e)] with q h₁ h₂ h₃ h₄ hq
    exact ⟨h₁ hq,h₂ hq,h₃ hq,h₄ hq⟩
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((Finset.eventually_all F).mpr (fun e _ => hev e))
  refine ⟨L+1,by omega,fun N => ?_⟩
  let S := F.sigma (fun e => (range (N / e.val.2.2.2)).filter
    (fun q => q ∈ B ∧ L+1 ≤ q))
  let f : ((e : Collision) × ℕ) → Quad := fun z => dilate z.2 z.1.val
  have hf : Set.InjOn f (S : Set ((e : Collision) × ℕ)) := by
    intro x hx y hy hxy
    have hqx : 0 < x.2 := by
      have := (mem_filter.mp (mem_sigma.mp hx).2).2.2
      omega
    obtain ⟨he,hq⟩ := primitive_dilate_injective hqx hxy
    cases x with
    | mk e q =>
      cases y with
      | mk e' q' =>
        dsimp only at he hq
        subst e' q'
        rfl
  have hsub : S.image f ⊆ sourceCollisionsUpTo D N := by
    intro x hx
    obtain ⟨⟨e,q⟩,hz,rfl⟩ := mem_image.mp hx
    have hz' := mem_sigma.mp hz
    have hq := mem_filter.mp hz'.2
    dsimp only at hq
    have hq0 : 0 < q := by omega
    have hroot := hL q (by omega) e hz'.1 hq.2.1
    apply mem_filter.mpr
    constructor
    · apply dilate_mem_collisionsUpTo e hq0
      exact (Nat.mul_le_mul_right _ (mem_range.mp hq.1).le).trans
        (Nat.div_mul_le_self N _)
    · simpa only [f,dilate,Nat.mul_comm] using hroot
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa only [S,card_sigma] using hh

private lemma filtered_prefix_card_le (B : Set ℕ) (L M : ℕ) :
    (B ∩ Set.Iio M).ncard ≤
      ((range M).filter (fun q => q ∈ B ∧ L ≤ q)).card + L := by
  classical
  let T := (range M).filter (fun q => q ∈ B)
  have he : B ∩ Set.Iio M = (T : Set ℕ) := by
    ext q
    simp [T,and_comm]
  rw [he,Set.ncard_coe_finset]
  have hsub : T ⊆ ((range M).filter (fun q => q ∈ B ∧ L ≤ q)) ∪ range L := by
    intro q hq
    have h := mem_filter.mp hq
    by_cases hL : L ≤ q
    · exact mem_union_left _ (mem_filter.mpr ⟨h.1,h.2,hL⟩)
    · exact mem_union_right _ (mem_range.mpr (by omega))
  exact (card_le_card hsub).trans (by simpa using (card_union_le
    ((range M).filter (fun q => q ∈ B ∧ L ≤ q)) (range L)))

/-- The multiplier source has positive lower density, with a uniform density
constant independent of the finite family of primitive collisions. -/
theorem source_collision_count_superlinear {B D : Set ℕ}
    (hB : 0 < B.lowerDensity) (hBD : EventuallyDilatesInto B D) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C*N < ((sourceCollisionsUpTo D N).card : ℝ) := by
  classical
  obtain ⟨δ,hδ,K,hK⟩ := prefix_bound_of_positive_lowerDensity hB
  obtain ⟨F,hF⟩ := exists_large_primitive_reciprocal_sum ((C+1)/δ)
  have hF' : C+1 < δ*(∑ e ∈ F, (1 : ℝ)/e.val.2.2.2) := by
    have := (div_lt_iff₀ hδ).mp hF
    linarith
  obtain ⟨L,hL,hcount⟩ := source_finite_count hBD F
  have hbound (N : ℕ) :
      δ*(N : ℝ)*(∑ e ∈ F, (1 : ℝ)/e.val.2.2.2) ≤
        ((sourceCollisionsUpTo D N).card : ℝ) + F.card*(K+L+δ) := by
    have hterm (e : Collision) : δ*(N : ℝ)/e.val.2.2.2 ≤
        (((range (N/e.val.2.2.2)).filter (fun q => q ∈ B ∧ L ≤ q)).card : ℝ)
          + (K+L+δ) := by
      have hpre := hK (N/e.val.2.2.2)
      have hcut : ((B ∩ Set.Iio (N/e.val.2.2.2)).ncard : ℝ) ≤
          (((range (N/e.val.2.2.2)).filter (fun q => q ∈ B ∧ L ≤ q)).card : ℝ) + L :=
        by exact_mod_cast filtered_prefix_card_le B L (N/e.val.2.2.2)
      have hepos : (0 : ℝ) < e.val.2.2.2 := by exact_mod_cast primitive_height_pos e
      have hfloor : (N : ℝ)/e.val.2.2.2 ≤ ((N/e.val.2.2.2 : ℕ) : ℝ)+1 := by
        apply (div_le_iff₀ hepos).mpr
        have h := Nat.lt_mul_div_succ N (primitive_height_pos e)
        have hr : (N : ℝ) < e.val.2.2.2 * (((N/e.val.2.2.2 : ℕ) : ℝ)+1) := by
          exact_mod_cast h
        nlinarith
      have hh := mul_le_mul_of_nonneg_left hfloor hδ.le
      rw [← mul_div_assoc] at hh
      nlinarith
    have hsum := sum_le_sum (fun e (_ : e ∈ F) => hterm e)
    have hc : (∑ e ∈ F, (((range (N/e.val.2.2.2)).filter
        (fun q => q ∈ B ∧ L ≤ q)).card : ℝ)) ≤
        ((sourceCollisionsUpTo D N).card : ℝ) := by exact_mod_cast hcount N
    calc
      _ = ∑ e ∈ F, δ*(N : ℝ)/e.val.2.2.2 := by simp [mul_sum,div_eq_mul_inv]
      _ ≤ _ := hsum
      _ = (∑ e ∈ F, (((range (N/e.val.2.2.2)).filter
          (fun q => q ∈ B ∧ L ≤ q)).card : ℝ)) + F.card*(K+L+δ) := by
        simp [sum_add_distrib,mul_add]
      _ ≤ _ := by linarith [hc]
  obtain ⟨M,hM⟩ := exists_nat_gt ((F.card : ℝ)*(K+L+δ))
  refine ⟨M+1,fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast (show M ≤ N by omega)
  have hh := mul_lt_mul_of_pos_right hF' hNpos
  have hb := hbound N
  nlinarith

/-- Conditional on positive density of the stronger large-prime source, the
original source has superlinear collision growth in its full natural prefixes. -/
theorem largePrimeSource_prefix_superlinear {k : ℕ} (hk : 0 < k)
    (hB : 0 < (largePrimeSource (2*k)).lowerDensity) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M,
      C*N < ((sourceCollisionsUpTo (largePrimeSource k) N).card : ℝ) :=
  source_collision_count_superlinear hB (largePrimeSource_mul_eventually hk) C

#print axioms source_collision_count_superlinear
#print axioms largePrimeSource_prefix_superlinear
end Erdos1206
