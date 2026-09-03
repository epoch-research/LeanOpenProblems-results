import Submission.RefreshVarianceExplore

/-! Finite partial refresh around the exact harmonic fractional profile.
The tail budget is kept explicit; no infinite repair iteration is asserted. -/
namespace Erdos66HarmonicRefresh
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66RefreshAlgebra
  Erdos66RepVariance Erdos66RefreshVariance Erdos66Rounding Erdos66Fractional
  Erdos66Generating AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1800000

lemma bit_decide_indicator (A : Set ℕ) (i : ℕ) : bit (decide (i∈A))=indicator A i := by
  simp only [bit,decide_eq_true_eq,indicator]

lemma selected_prefix_count (L n : ℕ) (A : Set ℕ) (hn : n ≤ L) :
    sumRep (selected L (fun i ↦ decide (i.val∈A))) n=sumRep A n := by
  have he := pairConv_bits L n (fun i ↦ decide (i.val∈A))
  simp_rw [bit_decide_indicator] at he
  rw [pairConv_restriction L n (indicator A) (indicator A) hn] at he
  have hi : sumConv (indicator A) (indicator A) n=(sumRep A n:ℝ) :=
    sum_indicator_antidiagonal A n
  rw [hi] at he
  exact_mod_cast he.symm

lemma mixed_profile (L n : ℕ) (A : Set ℕ) (hn : n ≤ L) :
    pairConv L n (fun i ↦ bit (decide (i.val∈A))) (fun i ↦ profile i.val)=
      (harmonic (n+1):ℝ)+sumConv (roundingError A) profile n := by
  simp_rw [bit_decide_indicator]
  rw [pairConv_restriction L n (indicator A) profile hn]
  have he : sumConv (indicator A) profile n=
      sumConv profile profile n+sumConv (roundingError A) profile n := by
    unfold sumConv
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [roundingError]
    ring
  rw [he,profile_convolution]

lemma harmonic_refresh_variance (L n : ℕ) (θ D : ℝ) (A : Set ℕ) (hn : n ≤ L)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hD : 0 ≤ D)
    (hprefix : ∀ k, |prefixSum (roundingError A) k| ≤ D) :
    repVarianceProxy L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val)) ≤
      θ*((2-θ)*((sumRep A n:ℝ)+(harmonic (n+1):ℝ))+4*(1-θ)*D+1) := by
  have hh := refresh_variance_bound L n θ (fun i ↦ decide (i.val∈A))
    (fun i ↦ profile i.val) hθ (fun i ↦ ⟨profile_nonneg _,profile_le_one _⟩)
  rw [selected_prefix_count L n A hn,mixed_profile L n A hn,
    pairConv_restriction L n profile profile hn,profile_convolution] at hh
  have hm := (abs_le.mp (mixed_convolution_bound (roundingError A) D hD hprefix n)).2
  have hh' := mul_le_mul_of_nonneg_left hm
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hθ.1) (sub_nonneg.mpr hθ.2))
  nlinarith only [hh,hh']

/-- A genuine finite existence theorem, but with the variance upper bound and
summed-tail budget as hypotheses. The output need not preserve prefix discrepancy. -/
theorem exists_harmonic_refresh (L : ℕ) (θ D : ℝ) (A : Set ℕ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hD : 0 ≤ D)
    (hprefix : ∀ k, |prefixSum (roundingError A) k| ≤ D)
    (S : Finset ℕ) (hS : ∀ n∈S, n ≤ L) (V : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1)
    (hV : ∀ n∈S, θ*((2-θ)*((sumRep A n:ℝ)+(harmonic (n+1):ℝ))+4*(1-θ)*D+1) ≤ V n)
    (hsmall : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ B : Set ℕ, B.Finite ∧ (∀ n∈B, n ≤ L) ∧ ∀ n∈S,
      |(sumRep B n:ℝ)-(harmonic (n+1):ℝ)|<
        (1-θ)^2*|(sumRep A n:ℝ)-(harmonic (n+1):ℝ)|+4*θ*(1-θ)*D+θ+ε*V n := by
  let p : Fin (L+1) → ℝ := blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val)
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 :=
    blend_bounds θ _ _ hθ (fun i ↦ ⟨profile_nonneg _,profile_le_one _⟩)
  obtain ⟨ω,hw,hω⟩ := exists_rep_variance_bound L p hp S V ε hε hε1
    (fun n hn ↦ (harmonic_refresh_variance L n θ D A (hS n hn) hθ hD hprefix).trans (hV n hn)) hsmall
  refine ⟨selected L ω,selected_finite L ω,?_,?_⟩
  · rintro n ⟨i,rfl,hi⟩
    exact Nat.le_of_lt_succ i.isLt
  · intro n hn
    have hb := refresh_mean_contraction L n θ D A (hS n hn) hθ hD hprefix
    have he : (sumRep (selected L ω) n:ℝ)-(harmonic (n+1):ℝ)=
        ((sumRep (selected L ω) n:ℝ)-repMean L n p)+
        (repMean L n p-((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ)))+
        (1-θ)^2*((sumRep A n:ℝ)-(harmonic (n+1):ℝ)) := by ring
    rw [he]
    have h₁ := abs_add_le ((sumRep (selected L ω) n:ℝ)-repMean L n p)
      (repMean L n p-((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ)))
    have h₂ := abs_add_le
      (((sumRep (selected L ω) n:ℝ)-repMean L n p)+
        (repMean L n p-((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ))))
      ((1-θ)^2*((sumRep A n:ℝ)-(harmonic (n+1):ℝ)))
    rw [abs_mul,abs_of_nonneg (sq_nonneg (1-θ))] at h₂
    change |repMean L n p-_| ≤ _ at hb
    linarith [hω n hn]

end Erdos66HarmonicRefresh
