import Submission.TripleIntersectionMeanExplore
import Submission.FiniteRepBernoulliExplore

/-! The harmonic-profile mass of pairs with a small summand is uniformly
small compared with log n when the relative cutoff is sufficiently small. -/
namespace Erdos66BoundaryPairMean
open Erdos66Fractional Erdos66FractionalFourthPower Erdos66Generating
  Erdos66Rounding Erdos66CumulativeRoundingError Erdos66TripleIntersectionMean
  Erdos66FiniteRepBernoulli Erdos66FiniteBernoulli
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def boundaryMean (d n : ℕ) : ℝ :=
  ∑ a∈Finset.range (n/d^2), profile a*profile (n-a)

lemma quotient_half (d n : ℕ) (hd : 2 ≤ d) : 2*(n/d^2) ≤ n := by
  have hd2 : 2 ≤ d^2 := by nlinarith
  exact (Nat.mul_le_mul_right (n/d^2) hd2).trans (Nat.mul_div_le n (d^2))

lemma boundaryMean_nonneg (d n : ℕ) : 0 ≤ boundaryMean d n :=
  Finset.sum_nonneg (fun a ha ↦ mul_nonneg (profile_nonneg _) (profile_nonneg _))

lemma boundaryMean_le_product (d n : ℕ) :
    boundaryMean d n ≤ profile (n-n/d^2)*prefixSum profile (n/d^2) := by
  calc
    _ ≤ ∑ a∈Finset.range (n/d^2), profile a*profile (n-n/d^2) := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' := Finset.mem_range.mp ha
      exact mul_le_mul_of_nonneg_left (profile_antitone (by omega)) (profile_nonneg a)
    _ ≤ ∑ a∈Finset.range (n/d^2+1), profile a*profile (n-n/d^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun a _ _ ↦ mul_nonneg (profile_nonneg _) (profile_nonneg _))
    _ = _ := by rw [←Finset.sum_mul,mul_comm]; rfl

lemma boundaryMean_bound (d n : ℕ) (hd : 2 ≤ d) (hn : d^2 ≤ n) :
    boundaryMean d n ≤ 4/(d:ℝ)*ell n := by
  let M := n/d^2
  let K := n-M
  have hhalf : 2*M ≤ n := quotient_half d n hd
  have hKn : K ≤ n := Nat.sub_le _ _
  have hMK : M+K=n := Nat.add_sub_of_le (by omega)
  have hdpos : (0:ℝ) < d := by exact_mod_cast (by omega : 0<d)
  have hnx : (0:ℝ) < (n:ℝ)+1 := by positivity
  have he := ell_one_le n
  have he0 : 0 ≤ ell n := by linarith
  have hHK : (harmonic (K+1):ℝ) ≤ ell n := by
    have hh := harmonic_le_one_add_log (K+1)
    have hl := Real.log_le_log (by positivity : (0:ℝ) < ((K+1:ℕ):ℝ))
      (show ((K+1:ℕ):ℝ) ≤ (n:ℝ)+1 by exact_mod_cast Nat.add_le_add_right hKn 1)
    dsimp only [ell]
    linarith
  have hp : ((n:ℝ)+1)*(profile K)^2 ≤ 2*ell n := by
    have hsq := (profile_square_bound K).trans hHK
    have hNK : (n:ℝ)+1 ≤ 2*((K:ℝ)+1) := by
      have hhalf' : 2*(M:ℝ) ≤ n := by exact_mod_cast hhalf
      have hMK' : (M:ℝ)+K=n := by exact_mod_cast hMK
      linarith
    have hm := mul_le_mul_of_nonneg_right hNK (sq_nonneg (profile K))
    push_cast at hsq
    nlinarith only [hsq,hm]
  have hHM : (harmonic (2*M+1):ℝ) ≤ ell n := by
    have hh := harmonic_le_one_add_log (2*M+1)
    have hl := Real.log_le_log (by positivity : (0:ℝ) < ((2*M+1:ℕ):ℝ))
      (show ((2*M+1:ℕ):ℝ) ≤ (n:ℝ)+1 by exact_mod_cast Nat.add_le_add_right hhalf 1)
    dsimp only [ell]
    linarith
  have hprefix : (prefixSum profile M)^2 ≤ 2*((M:ℝ)+1)*ell n := by
    have hh := (profile_prefix_square_bound M).trans
      (mul_le_mul_of_nonneg_left hHM (by positivity : (0:ℝ) ≤ ((2*M+1:ℕ):ℝ)))
    push_cast at hh
    have heM := mul_le_mul_of_nonneg_right
      (show 2*(M:ℝ)+1 ≤ 2*((M:ℝ)+1) by linarith) he0
    exact hh.trans heM
  have hMd : (d:ℝ)^2*((M:ℝ)+1) ≤ 2*((n:ℝ)+1) := by
    have hdiv : (d:ℝ)^2*(M:ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n (d^2)
    have hn' : (d:ℝ)^2 ≤ n := by exact_mod_cast hn
    nlinarith only [hdiv,hn']
  have hs : (d:ℝ)^2*(prefixSum profile M)^2 ≤ 4*((n:ℝ)+1)*ell n := by
    have h1 := mul_le_mul_of_nonneg_left hprefix (sq_nonneg (d:ℝ))
    have h2 := mul_le_mul_of_nonneg_right hMd (show 0 ≤ 2*ell n by positivity)
    nlinarith only [h1,h2]
  have hm := mul_le_mul hp hs (by positivity : (0:ℝ) ≤ (d:ℝ)^2*(prefixSum profile M)^2)
    (show 0 ≤ 2*ell n by positivity)
  have hsq : ((n:ℝ)+1)*((d:ℝ)*profile K*prefixSum profile M)^2 ≤
      ((n:ℝ)+1)*(8*(ell n)^2) := by convert hm using 1 <;> ring
  have hsq' := le_of_mul_le_mul_left hsq hnx
  have hprod : (d:ℝ)*profile K*prefixSum profile M ≤ 4*ell n := by
    exact le_of_sq_le_sq (hsq'.trans (by nlinarith only [sq_nonneg (ell n)])) (by positivity)
  apply (boundaryMean_le_product d n).trans
  change profile K*prefixSum profile M ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdpos).mpr
  nlinarith only [hprod]

noncomputable def boundaryPairs (L d n : ℕ) : Finset (Fin (L+1) × Fin (L+1)) :=
  (halfPairs L n).filter (fun a ↦ a.1.val<n/d^2 ∧ a.1<a.2)

lemma mem_boundaryPairs {L d n : ℕ} {a : Fin (L+1) × Fin (L+1)} : a∈boundaryPairs L d n ↔
    a.1.val+a.2.val=n ∧ a.1.val<n/d^2 ∧ a.1<a.2 := by
  simp only [boundaryPairs,Finset.mem_filter,mem_halfPairs]
  constructor
  · rintro ⟨⟨hn,h⟩,hd,hlt⟩; exact ⟨hn,hd,hlt⟩
  · rintro ⟨hn,hd,hlt⟩; exact ⟨⟨hn,hlt.le⟩,hd,hlt⟩

lemma boundaryPairs_disjoint (L d n : ℕ) :
    (boundaryPairs L d n : Set (Fin (L+1) × Fin (L+1))).Pairwise
      (fun a b ↦ Disjoint (pairCoords a) (pairCoords b)) :=
  (pairCoords_disjoint L n).mono (Finset.filter_subset _ _)

lemma boundary_pair_mean (L d n : ℕ) :
    (∑ a∈boundaryPairs L d n, ∏ i∈pairCoords a, profile i.val) ≤ boundaryMean d n := by
  have hinj : Set.InjOn (fun a : Fin (L+1) × Fin (L+1) ↦ a.1.val)
      (boundaryPairs L d n : Set (Fin (L+1) × Fin (L+1))) := by
    intro a ha b hb he
    change a.1.val=b.1.val at he
    have ha' := (mem_boundaryPairs.mp ha).1
    have hb' := (mem_boundaryPairs.mp hb).1
    exact Prod.ext (Fin.ext he) (Fin.ext (by omega))
  have hsub : (boundaryPairs L d n).image (fun a ↦ a.1.val) ⊆ Finset.range (n/d^2) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (mem_boundaryPairs.mp hb).2.1
  calc
    _ = ∑ a∈boundaryPairs L d n, profile a.1.val*profile (n-a.1.val) := by
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨hn,_,hlt⟩ := mem_boundaryPairs.mp ha
      simp only [pairCoords,Finset.prod_pair hlt.ne]
      rw [show n-a.1.val=a.2.val by omega]
    _ = ∑ i∈(boundaryPairs L d n).image (fun a ↦ a.1.val), profile i*profile (n-i) :=
      (Finset.sum_image (f := fun i : ℕ ↦ profile i*profile (n-i)) hinj).symm
    _ ≤ boundaryMean d n := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ ↦ mul_nonneg (profile_nonneg _) (profile_nonneg _))

end Erdos66BoundaryPairMean
