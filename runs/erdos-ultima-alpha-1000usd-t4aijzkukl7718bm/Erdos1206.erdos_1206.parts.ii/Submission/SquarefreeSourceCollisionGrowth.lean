import Submission.SourceCollisionGrowth
import Submission.SquarefreeWeightedMass

/-! Full-prefix superlinear collision counts on squarefree roots coprime to 6.
This counts collisions in one source; it gives no upper bound on the size of
its cube-Sidon subsets and does not settle Erdős 1206. -/

namespace Erdos1206.SquarefreeSourceCollisionGrowth
open Finset Filter SquarefreeConicFamily SquarefreeWeightedMass CubeCollisionGrowth
open SquarefreeCoprimeDensity
open scoped Classical Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

abbrev Index := SquarefreeConicFamily.Index

def source : Set ℕ := {n | Squarefree n ∧ Nat.Coprime n 6}

noncomputable def base (x : Index) : PrimitiveCollisionMass.Collision := by
  let o := ordered (M*x.val.1) (M*x.val.2+1) (by omega)
  exact ⟨(roots 0 x.val,roots 1 x.val,roots 2 x.val,roots 3 x.val),
    o.1,o.2.1,o.2.2.1,o.2.2.2,identity _ _,primitive x.property⟩

lemma base_injective : Function.Injective base := by
  intro x y he
  apply Subtype.ext
  exact roots_injective (congrArg Subtype.val he)

lemma root_dvd_modulus (i : Fin 4) (x : ℕ × ℕ) : roots i x ∣ multiplierModulus x := by
  fin_cases i
  · refine ⟨6*roots 1 x*roots 2 x*roots 3 x,?_⟩
    dsimp [multiplierModulus]
    ring
  · refine ⟨6*roots 0 x*roots 2 x*roots 3 x,?_⟩
    dsimp [multiplierModulus]
    ring
  · refine ⟨6*roots 0 x*roots 1 x*roots 3 x,?_⟩
    dsimp [multiplierModulus]
    ring
  · refine ⟨6*roots 0 x*roots 1 x*roots 2 x,?_⟩
    dsimp [multiplierModulus]
    ring

lemma six_dvd_modulus (x : ℕ × ℕ) : 6 ∣ multiplierModulus x := by
  refine ⟨roots 0 x*roots 1 x*roots 2 x*roots 3 x,?_⟩
  dsimp [multiplierModulus]
  ring

lemma multiplier_preserves (x : Index) {q : ℕ}
    (hq : Squarefree q) (hcop : (multiplierModulus x.val).Coprime q) (i : Fin 4) :
    q*roots i x.val ∈ source := by
  have hqr := (hcop.of_dvd_left (root_dvd_modulus i x.val)).symm
  have hq6 := (hcop.of_dvd_left (six_dvd_modulus x.val)).symm
  exact ⟨(Nat.squarefree_mul hqr).mpr ⟨hq,x.property i⟩,
    hq6.mul_left (root_coprime_six i x.val)⟩

noncomputable def rate (x : Index) : ℝ := 1/(32*(1+Real.log (multiplierModulus x.val)))
lemma rate_pos (x : Index) : 0<rate x := by
  dsimp [rate]
  exact one_div_pos.mpr (mul_pos (by norm_num) (logFactor_pos x.val))

lemma multiplier_prefix_bound (x : Index) :
    ∃ K : ℝ, ∀ N : ℕ, rate x*N ≤ (sfCount (multiplierModulus x.val) N : ℝ)+K := by
  let A : Set ℕ := {n | Squarefree n ∧ (multiplierModulus x.val).Coprime n}
  have hr := rate_pos x
  have hden := lowerDensity_log_bound (multiplierModulus x.val) (multiplierModulus_pos x.val)
  have hstrict : rate x < A.lowerDensity := by
    have he : (1:ℝ)/(16*(1+Real.log (multiplierModulus x.val)))=2*rate x := by
      dsimp [rate]
      have hp := (logFactor_pos x.val).ne'
      field_simp
      ring
    rw [he] at hden
    change 2*rate x ≤ A.lowerDensity at hden
    linarith
  have hev : ∀ᶠ N : ℕ in atTop, rate x < A.partialDensity Set.univ N :=
    eventually_lt_of_lt_liminf hstrict (isBoundedUnder_of ⟨0,fun _ => by positivity⟩)
  obtain ⟨L,hL⟩ := eventually_atTop.mp hev
  refine ⟨rate x*L,fun N => ?_⟩
  by_cases hn : N<L
  · have hNr : (N:ℝ) ≤ L := by exact_mod_cast hn.le
    have hh := mul_le_mul_of_nonneg_left hNr hr.le
    have hc : (0:ℝ)≤sfCount (multiplierModulus x.val) N := by positivity
    linarith
  · by_cases hN0 : N=0
    · subst N
      simpa using (show (0:ℝ) ≤ (sfCount (multiplierModulus x.val) 0 : ℝ)+rate x*L by positivity)
    have hp := hL N (by omega)
    have heq : A ∩ Set.Iio N = ((range N).filter (fun n => Squarefree n ∧ (multiplierModulus x.val).Coprime n) : Finset ℕ) := by
      ext n
      simp [A,and_comm]
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio,heq,Set.ncard_coe_finset] at hp
    change rate x < (sfCount (multiplierModulus x.val) N : ℝ)/N at hp
    have hm := (lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN0 : (0:ℝ)<N)).mp hp
    have hz : (0:ℝ) ≤ rate x*L := mul_nonneg hr.le (Nat.cast_nonneg L)
    linarith

lemma finite_dilate_count (E : Finset Index) (N : ℕ) :
    ∑ x ∈ E, sfCount (multiplierModulus x.val) (N/roots 3 x.val) ≤
      (sourceCollisionsUpTo source N).card := by
  let S := E.sigma (fun x => (range (N/roots 3 x.val)).filter
    (fun q => Squarefree q ∧ (multiplierModulus x.val).Coprime q))
  let f : ((x : Index) × ℕ) → Quad := fun z => dilate z.2 (base z.1).val
  have hinj : Set.InjOn f (S : Set ((x : Index) × ℕ)) := by
    intro x hx y hy he
    have hq : 0<x.2 := Nat.pos_of_ne_zero (mem_filter.mp (mem_sigma.mp hx).2).2.1.ne_zero
    obtain ⟨hbase,hqr⟩ := primitive_dilate_injective hq he
    have heq := base_injective hbase
    cases x with
    | mk x q =>
      cases y with
      | mk y r =>
        dsimp only at heq hqr
        subst y r
        rfl
  have hsub : S.image f ⊆ sourceCollisionsUpTo source N := by
    intro z hz
    obtain ⟨⟨x,q⟩,hx,rfl⟩ := mem_image.mp hz
    have hq := mem_filter.mp (mem_sigma.mp hx).2
    have hq0 : 0<q := Nat.pos_of_ne_zero hq.2.1.ne_zero
    apply mem_filter.mpr
    constructor
    · apply dilate_mem_collisionsUpTo (base x) hq0
      change q*roots 3 x.val ≤ N
      exact (Nat.mul_le_mul_right _ (mem_range.mp hq.1).le).trans (Nat.div_mul_le_self N _)
    · exact ⟨multiplier_preserves x hq.2.1 hq.2.2 0,
        multiplier_preserves x hq.2.1 hq.2.2 1,
        multiplier_preserves x hq.2.1 hq.2.2 2,
        multiplier_preserves x hq.2.1 hq.2.2 3⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj] at hc
  simpa only [S,card_sigma,sfCount] using hc

/-- Full-prefix collision counts on the squarefree, coprime-to-six source
exceed every constant multiple of the root cutoff. This is not an independence
bound and is not a negation of the conjecture. -/
theorem collision_count_superlinear (C : ℝ) :
    ∃ L : ℕ, ∀ N ≥ L,
      C*N < ((sourceCollisionsUpTo source N).card : ℝ) := by
  obtain ⟨E,hE⟩ := exists_large_log_weight (32*(C+1))
  have hmass : C+1 < ∑x∈E, rate x/(roots 3 x.val) := by
    have he : (∑x∈E,(1:ℝ)/((roots 3 x.val:ℝ)*(1+Real.log (multiplierModulus x.val)))) =
        32*(∑x∈E,rate x/(roots 3 x.val)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      dsimp [rate]
      have hp := (logFactor_pos x.val).ne'
      have hd : (roots 3 x.val : ℝ) ≠ 0 := by exact_mod_cast (roots_pos 3 x.val).ne'
      field_simp
    rw [he] at hE
    linarith
  choose K hK using multiplier_prefix_bound
  have hbound (N : ℕ) :
      (N:ℝ)*(∑x∈E,rate x/(roots 3 x.val)) ≤
        (sourceCollisionsUpTo source N).card+∑x∈E,(K x+rate x) := by
    have hterm (x : Index) :
        (N:ℝ)*(rate x/(roots 3 x.val)) ≤
          sfCount (multiplierModulus x.val) (N/roots 3 x.val)+K x+rate x := by
      have hd := hK x (N/roots 3 x.val)
      have hpos : (0:ℝ)<roots 3 x.val := by exact_mod_cast roots_pos 3 x.val
      have hfloor : (N:ℝ)/(roots 3 x.val) ≤ ((N/roots 3 x.val : ℕ):ℝ)+1 := by
        apply (div_le_iff₀ hpos).mpr
        exact_mod_cast (by simpa only [mul_comm] using (Nat.lt_mul_div_succ N (roots_pos 3 x.val)).le : N ≤ (N/roots 3 x.val+1)*roots 3 x.val)
      have hm := mul_le_mul_of_nonneg_left hfloor (rate_pos x).le
      nlinarith only [hd,hm,show rate x*((N:ℝ)/(roots 3 x.val))=(N:ℝ)*(rate x/(roots 3 x.val)) by ring]
    have hs := sum_le_sum (fun x (_ : x∈E) => hterm x)
    have hc : (∑x∈E,(sfCount (multiplierModulus x.val) (N/roots 3 x.val):ℝ)) ≤
        (sourceCollisionsUpTo source N).card := by exact_mod_cast finite_dilate_count E N
    rw [← mul_sum] at hs
    simp only [sum_add_distrib] at hs ⊢
    linarith
  obtain ⟨L,hL⟩ := exists_nat_gt (∑x∈E,(K x+rate x))
  refine ⟨L+1,fun N hN => ?_⟩
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hLN : (L:ℝ)<N := by exact_mod_cast (show L<N by omega)
  have hm := mul_lt_mul_of_pos_left hmass hN0
  have hb := hbound N
  nlinarith only [hm,hb,hL,hLN]

#print axioms collision_count_superlinear
end Erdos1206.SquarefreeSourceCollisionGrowth
