import Submission.MovingPrimeBlockVariance

/-!
The moving prime-block center changes by a bounded amount between integers
in a fixed multiplicative range. No assertion about Sidon sets is made.
-/
namespace Erdos1206.PrimeBlockMeanOscillation
open Finset PrimeBlockVariance MovingPrimeBlockVariance
open scoped Classical

def cutoff (n : ℕ) : ℕ := 2^(Nat.log 4 n+1)

lemma cutoff_pos (n : ℕ) : 0 < cutoff n := by dsimp [cutoff]; positivity

lemma cutoff_sq (n : ℕ) : (cutoff n)^2=4^(Nat.log 4 n+1) := by
  dsimp [cutoff]
  rw [←pow_mul,mul_comm (Nat.log 4 n+1) 2,pow_mul]
  norm_num

lemma cutoff_lower (n : ℕ) : n < (cutoff n)^2 := by
  rw [cutoff_sq]
  exact Nat.lt_pow_succ_log_self (by decide : 1 < (4:ℕ)) n

lemma cutoff_upper {n : ℕ} (hn : 0 < n) : (cutoff n)^2 ≤ 4*n := by
  rw [cutoff_sq,pow_succ]
  have hh := Nat.pow_log_le_self 4 hn.ne'
  omega

lemma cutoff_mono {n m : ℕ} (h : n ≤ m) : cutoff n ≤ cutoff m := by
  apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
  have := Nat.log_mono_right h (b := 4)
  omega

lemma cutoff_ratio {n m R : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hm : m ≤ R*n) (_hR : 1 ≤ R) : cutoff m ≤ 2*R*cutoff n := by
  have hm0 : 0 < m := hn.trans_le hnm
  have hupper := cutoff_upper hm0
  have hlower := cutoff_lower n
  have hpowpos := cutoff_pos n
  have hmul := Nat.mul_le_mul_left (4*R) hlower.le
  have hR2 : 4*R ≤ 4*R^2 := by nlinarith
  have hmul2 := Nat.mul_le_mul_right ((cutoff n)^2) hR2
  have hs : (cutoff m)^2 ≤ (2*R*cutoff n)^2 := by
    calc
      _ ≤ 4*m := hupper
      _ ≤ 4*R*n := by nlinarith only [hm]
      _ ≤ 4*R*(cutoff n)^2 := hmul
      _ ≤ 4*R^2*(cutoff n)^2 := hmul2
      _ = _ := by ring
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp hs

/-- A bound using only bounded weights and the sizes of the cutoffs. -/
lemma mean_cutoff_difference (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, 0 < p) (hw : ∀ p ∈ P, |w p| ≤ 1)
    {U V : ℕ} (hUV : U ≤ V) :
    |mean (P.filter (fun p => p ≤ V)) w-mean (P.filter (fun p => p ≤ U)) w| ≤
      (V:ℝ)/(U+1) := by
  let S := P.filter (fun p => p ≤ U)
  let T := P.filter (fun p => p ≤ V)
  have hST : S ⊆ T := by
    intro p hp
    obtain ⟨hp,hpU⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp,hpU.trans hUV⟩
  have hD (p : ℕ) (hp : p ∈ T \ S) : p ∈ P ∧ U < p ∧ p ≤ V := by
    obtain ⟨hpT,hpS⟩ := mem_sdiff.mp hp
    obtain ⟨hpP,hpV⟩ := mem_filter.mp hpT
    have hpU : ¬ p ≤ U := by intro hh; exact hpS (mem_filter.mpr ⟨hpP,hh⟩)
    exact ⟨hpP,Nat.lt_of_not_ge hpU,hpV⟩
  have hcard : (T \ S).card ≤ V := by
    have hsub : T \ S ⊆ Icc 1 V := fun p hp =>
      mem_Icc.mpr ⟨hP p (hD p hp).1,(hD p hp).2.2⟩
    simpa using card_le_card hsub
  change |(∑ p ∈ T, w p/p)-(∑ p ∈ S, w p/p)| ≤ _
  rw [←sum_sdiff hST,add_sub_cancel_right]
  calc
    _ ≤ ∑ p ∈ T \ S, |w p/(p:ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ T \ S, (1:ℝ)/(U+1) := by
      apply sum_le_sum
      intro p hp
      have hpR : (0:ℝ) < p := by exact_mod_cast hP p (hD p hp).1
      have hpU : (U:ℝ)+1 ≤ p := by exact_mod_cast (hD p hp).2.1
      rw [abs_div,abs_of_pos hpR]
      calc
        _ ≤ (1:ℝ)/p := div_le_div_of_nonneg_right (hw p (hD p hp).1) hpR.le
        _ ≤ _ := one_div_le_one_div_of_le (by positivity) hpU
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      have hcR : ((T \ S).card:ℝ) ≤ V := by exact_mod_cast hcard
      calc
        _ ≤ (V:ℝ)*(1/(U+1)) := mul_le_mul_of_nonneg_right hcR (by positivity)
        _ = (V:ℝ)/(U+1) := by ring

/-- The bound is independent of the prime block and the common scale. -/
theorem movingMean_oscillation (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, |w p| ≤ 1)
    {n m R : ℕ} (hn : 0 < n) (hnm : n ≤ m) (hm : m ≤ R*n) (hR : 1 ≤ R) :
    |movingMean P w m-movingMean P w n| ≤ 2*(R:ℝ) := by
  have hh := mean_cutoff_difference P w (fun p hp => (hP p hp).pos) hw (cutoff_mono hnm)
  change |movingMean P w m-movingMean P w n| ≤ (cutoff m:ℝ)/(cutoff n+1) at hh
  apply hh.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (cutoff n:ℝ)+1)).mpr
  have hratio : (cutoff m:ℝ) ≤ 2*(R:ℝ)*cutoff n := by
    exact_mod_cast cutoff_ratio hn hnm hm hR
  nlinarith [show (0:ℝ) ≤ R from Nat.cast_nonneg R]

#print axioms mean_cutoff_difference
#print axioms movingMean_oscillation
end Erdos1206.PrimeBlockMeanOscillation
