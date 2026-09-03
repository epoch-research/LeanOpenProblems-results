import Submission.FiniteRepBernoulliExplore
import Submission.RoundingExplore

/-! Exact means under independent partial refresh of a fixed Boolean set. -/
namespace Erdos66RefreshAlgebra
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66BernoulliConcentration
  Erdos66Rounding Erdos66Fractional Erdos66Generating AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1400000

noncomputable def blend {ι : Type*} (θ : ℝ) (a : ι → Bool) (p : ι → ℝ) (i : ι) : ℝ :=
  (1-θ)*bit (a i)+θ*p i

lemma blend_bounds {ι : Type*} (θ : ℝ) (a : ι → Bool) (p : ι → ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : ι) :
    0 ≤ blend θ a p i ∧ blend θ a p i ≤ 1 := by
  have h₀ := mul_nonneg hθ.1 (hp i).1
  have h₁ := mul_le_mul_of_nonneg_left (hp i).2 hθ.1
  cases ha : a i <;> simp only [blend,ha,bit,Bool.false_eq_true,if_false,if_true,
    mul_zero,mul_one,zero_add] <;> constructor <;> nlinarith [hθ.1,hθ.2]

noncomputable def pairConv (L n : ℕ) (f g : Fin (L+1) → ℝ) : ℝ :=
  ∑ a∈pairs L n, f a.1*g a.2

lemma pairConv_comm (L n : ℕ) (f g : Fin (L+1) → ℝ) :
    pairConv L n f g=pairConv L n g f := by
  unfold pairConv
  apply Finset.sum_equiv (Equiv.prodComm _ _)
  · intro a
    simp only [mem_pairs,Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap]
    omega
  · intro a ha
    exact mul_comm _ _

lemma pairConv_add_scaled_self (L n : ℕ) (f g : Fin (L+1) → ℝ) (s t : ℝ) :
    pairConv L n (fun i ↦ s*f i+t*g i) (fun i ↦ s*f i+t*g i)=
      s^2*pairConv L n f f+2*s*t*pairConv L n f g+t^2*pairConv L n g g := by
  have he : pairConv L n (fun i ↦ s*f i+t*g i) (fun i ↦ s*f i+t*g i)=
      s^2*pairConv L n f f+s*t*pairConv L n f g+
        s*t*pairConv L n g f+t^2*pairConv L n g g := by
    unfold pairConv
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he,pairConv_comm L n g f]
  ring

lemma pairConv_bits (L n : ℕ) (a : Fin (L+1) → Bool) :
    pairConv L n (fun i ↦ bit (a i)) (fun i ↦ bit (a i))=
      (sumRep (selected L a) n:ℝ) := by
  rw [selected_rep]
  unfold pairConv
  rw [symmetric_sum L n _ (fun _ ↦ mul_comm _ _)]
  simp_rw [pair_monomial]

lemma refresh_mean (L n : ℕ) (θ : ℝ) (a : Fin (L+1) → Bool) (p : Fin (L+1) → ℝ) :
    repMean L n (blend θ a p)=
      (1-θ)^2*(sumRep (selected L a) n:ℝ)+
      2*(1-θ)*θ*pairConv L n (fun i ↦ bit (a i)) p+
      θ^2*pairConv L n p p+diagCorrection L n (blend θ a p) := by
  rw [mean_decomposition]
  change pairConv L n (fun i ↦ (1-θ)*bit (a i)+θ*p i)
    (fun i ↦ (1-θ)*bit (a i)+θ*p i)+_= _
  rw [pairConv_add_scaled_self,pairConv_bits]

lemma pairConv_restriction (L n : ℕ) (f g : ℕ → ℝ) (hn : n ≤ L) :
    pairConv L n (fun i ↦ f i.val) (fun i ↦ g i.val)=sumConv f g n := by
  unfold pairConv
  rw [pairs_sum_range L n (fun i j ↦ f i*g j),sumConv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  rw [if_pos (by omega)]

lemma expect_rep (L n : ℕ) (p : Fin (L+1) → ℝ) :
    expect p (fun ω ↦ (sumRep (selected L ω) n:ℝ))=repMean L n p := by
  simp_rw [selected_rep]
  rw [expect_sum]
  simp_rw [expect_const_mul,expect_monomial]
  rfl

/-- The mean's quadratic defect is multiplied by (1-theta)^2, not eliminated
by an arbitrarily small refresh. The diagonal correction remains explicit. -/
lemma refresh_quadratic_mean (L n : ℕ) (θ : ℝ) (A : Set ℕ) (hn : n ≤ L) :
    repMean L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val))=
      (harmonic (n+1):ℝ)+2*(1-θ)*sumConv (roundingError A) profile n+
      (1-θ)^2*sumConv (roundingError A) (roundingError A) n+
      diagCorrection L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val)) := by
  have hb (i : Fin (L+1)) :
      blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val) i=
        profile i.val+(1-θ)*roundingError A i.val := by
    simp only [blend,bit,decide_eq_true_eq,roundingError,indicator]
    ring
  rw [mean_decomposition]
  simp_rw [hb]
  change pairConv L n (fun i ↦ profile i.val+(1-θ)*roundingError A i.val)
    (fun i ↦ profile i.val+(1-θ)*roundingError A i.val)+_=_
  have he := pairConv_add_scaled_self L n (fun i ↦ profile i.val)
    (fun i ↦ roundingError A i.val) 1 (1-θ)
  simp only [one_mul,one_pow] at he
  rw [he,pairConv_restriction L n profile profile hn,
    pairConv_restriction L n profile (roundingError A) hn,
    pairConv_restriction L n (roundingError A) (roundingError A) hn,
    profile_convolution,sumConv_comm_real profile (roundingError A)]
  ring


lemma scalar_blend_variance {ι : Type*} (θ : ℝ) (a : ι → Bool) (p : ι → ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : ι) :
    blend θ a p i-(blend θ a p i)^2 ≤ θ := by
  have hq := blend_bounds θ a p hθ hp i
  have h₀ := mul_nonneg hθ.1 (hp i).1
  have h₁ := mul_le_mul_of_nonneg_left (hp i).2 hθ.1
  have hsq := sq_nonneg (1-blend θ a p i)
  cases ha : a i <;> simp only [blend,ha,bit,Bool.false_eq_true,if_false,if_true,
    mul_zero,mul_one,zero_add] at hq hsq ⊢ <;> nlinarith [sq_nonneg (θ*p i)]

lemma refresh_diag_bounds (L n : ℕ) (θ : ℝ) (a : Fin (L+1) → Bool) (p : Fin (L+1) → ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ diagCorrection L n (blend θ a p) ∧ diagCorrection L n (blend θ a p) ≤ θ := by
  refine ⟨(diagCorrection_bounds L n _ (blend_bounds θ a p hθ hp)).1,?_⟩
  have hc : ((halfPairs L n).filter (fun a ↦ a.1=a.2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,hae⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hbe⟩ := Finset.mem_filter.mp hb
    have ha := (mem_halfPairs.mp ha).1
    have hb := (mem_halfPairs.mp hb).1
    have ha' := congrArg Fin.val hae
    have hb' := congrArg Fin.val hbe
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hh := Finset.sum_le_sum (s := (halfPairs L n).filter (fun a ↦ a.1=a.2))
    (fun b hb ↦ scalar_blend_variance θ a p hθ hp b.1)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have hc' : (((halfPairs L n).filter (fun a ↦ a.1=a.2)).card:ℝ) ≤ 1 := by exact_mod_cast hc
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hc' hθ.1])

/-- With a bounded-discrepancy base, the mean is close to the advertised
convex combination of the OLD counts and harmonic target. -/
lemma refresh_mean_contraction (L n : ℕ) (θ D : ℝ) (A : Set ℕ) (hn : n ≤ L)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hD : 0 ≤ D)
    (hprefix : ∀ k, |prefixSum (roundingError A) k| ≤ D) :
    |repMean L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val))-
      ((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ))| ≤
      4*θ*(1-θ)*D+θ := by
  have hdiag := refresh_diag_bounds L n θ (fun i ↦ decide (i.val∈A))
    (fun i ↦ profile i.val) hθ (fun i ↦ ⟨profile_nonneg _,profile_le_one _⟩)
  have he : repMean L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val))-
      ((1-θ)^2*(sumRep A n:ℝ)+θ*(2-θ)*(harmonic (n+1):ℝ))=
        2*θ*(1-θ)*sumConv (roundingError A) profile n+
        diagCorrection L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val)) := by
    rw [refresh_quadratic_mean L n θ A hn,rounding_decomposition A n]
    ring
  rw [he]
  have hnon : 0 ≤ 2*θ*(1-θ) := mul_nonneg (mul_nonneg (by norm_num) hθ.1) (sub_nonneg.mpr hθ.2)
  have hm := mul_le_mul_of_nonneg_left (mixed_convolution_bound (roundingError A) D hD hprefix n) hnon
  have hh := abs_add_le (2*θ*(1-θ)*sumConv (roundingError A) profile n)
    (diagCorrection L n (blend θ (fun i ↦ decide (i.val∈A)) (fun i ↦ profile i.val)))
  rw [abs_mul,abs_of_nonneg hnon,abs_of_nonneg hdiag.1] at hh
  nlinarith only [hh,hm,hdiag.2]

end Erdos66RefreshAlgebra
