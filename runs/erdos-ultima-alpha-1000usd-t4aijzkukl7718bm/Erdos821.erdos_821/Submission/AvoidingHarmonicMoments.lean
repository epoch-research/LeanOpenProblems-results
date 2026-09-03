import Submission.PrimeSupportHarmonic

/-!
# Uniform harmonic divisor moments after finite prime exclusion

The exclusion cost is the exact finite Euler factor, uniformly in the
cutoff and in the excluded prime set.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def avoidingHarmonicMoment (k z : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 z).filter (fun n => ∀ p ∈ P, ¬p ∣ n), (tau k n : ℝ)/(n : ℝ)

lemma avoidingHarmonicMoment_nonneg (k z : ℕ) (P : Finset ℕ) :
    0 ≤ avoidingHarmonicMoment k z P := by
  apply sum_nonneg
  intro n hn
  positivity

lemma avoidingHarmonicMoment_strip (k z p : ℕ) (hp : p.Prime) (P : Finset ℕ) :
    avoidingHarmonicMoment (k+1) z P ≤
      (1/(1-(p : ℝ)⁻¹)^(k+1))*avoidingHarmonicMoment (k+1) z (insert p P) := by
  let A := (Icc 1 z).filter (fun n => ∀ q ∈ P, ¬q ∣ n)
  let B := (Icc 1 z).filter (fun n => ∀ q ∈ insert p P, ¬q ∣ n)
  let F : ℕ → ℕ × ℕ := fun n => (n.factorization p, n/p^(n.factorization p))
  let w : ℕ × ℕ → ℝ := fun ab =>
    ((tau (k+1) (p^ab.1) : ℝ)/(p : ℝ)^ab.1) *
      ((tau (k+1) ab.2 : ℝ)/(ab.2 : ℝ))
  have reconstruct (n : ℕ) : p^(F n).1*(F n).2 = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hi : Function.Injective F := by
    intro n m h
    calc
      n = p^(F n).1*(F n).2 := (reconstruct n).symm
      _ = p^(F m).1*(F m).2 := by rw [h]
      _ = m := reconstruct m
  have hmap : A.image F ⊆ range (z+1) ×ˢ B := by
    intro ab hab
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hab
    obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnz⟩ := mem_Icc.mp hnI
    have hn0 : n ≠ 0 := by omega
    have ha : n.factorization p ≤ z := Nat.factorization_le_of_le_pow
      (hnz.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le z)))
    have hb : 0 < n/p^(n.factorization p) := Nat.ordCompl_pos p hn0
    refine mem_product.mpr ⟨mem_range.mpr (by dsimp [F]; omega), ?_⟩
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hb, (Nat.div_le_self n _).trans hnz⟩, ?_⟩
    intro q hq hqd
    rcases mem_insert.mp hq with hqp | hqP
    · subst q
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (Nat.coprime_ordCompl hp hn0)
        (dvd_refl p) hqd)
    · exact hnP q hqP (hqd.trans (Nat.ordCompl_dvd n p))
  have he : avoidingHarmonicMoment (k+1) z P = ∑ ab ∈ A.image F, w ab := by
    rw [sum_image hi.injOn]
    unfold avoidingHarmonicMoment
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (mem_Icc.mp (mem_filter.mp hn).1).1
      omega
    have hc := (Nat.coprime_ordCompl hp hn0).pow_left (n.factorization p)
    have ht := tau_mul_coprime (k+1) hc
    have hr := reconstruct n
    change tau (k+1) (p^(F n).1*(F n).2) =
      tau (k+1) (p^(F n).1)*tau (k+1) (F n).2 at ht
    change _ = ((tau (k+1) (p^(F n).1) : ℝ)/(p : ℝ)^(F n).1) *
      ((tau (k+1) (F n).2 : ℝ)/((F n).2 : ℝ))
    conv_lhs => rw [← hr, ht, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
    ring
  rw [he]
  calc
    _ ≤ ∑ ab ∈ range (z+1) ×ˢ B, w ab :=
      sum_le_sum_of_subset_of_nonneg hmap (fun ab _ _ => by dsimp [w]; positivity)
    _ = (∑ a ∈ range (z+1), (tau (k+1) (p^a) : ℝ)/(p : ℝ)^a) *
        avoidingHarmonicMoment (k+1) z (insert p P) := by
      simp only [w, Finset.sum_product, avoidingHarmonicMoment, B, Finset.sum_mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((hasSum_prime_power_tau k p hp).tsum_eq ▸
        (hasSum_prime_power_tau k p hp).summable.sum_le_tsum _ (fun a _ => by positivity))
      (avoidingHarmonicMoment_nonneg _ _ _)

lemma avoidingHarmonicMoment_euler_lower (k z : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1-(p : ℝ)⁻¹)^(k+1))*harmonicMoment (k+1) z ≤
      avoidingHarmonicMoment (k+1) z P := by
  induction P using Finset.induction_on with
  | empty => simp [avoidingHarmonicMoment, harmonicMoment]
  | @insert p P hpP ih =>
    have hp := hP p (mem_insert_self _ _)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hf : 0 < (1-(p : ℝ)⁻¹)^(k+1) :=
      pow_pos (sub_pos.mpr ((inv_lt_one₀ hp0).mpr hp1)) _
    have hstrip := avoidingHarmonicMoment_strip k z p hp P
    have hh : (1-(p : ℝ)⁻¹)^(k+1)*avoidingHarmonicMoment (k+1) z P ≤
        avoidingHarmonicMoment (k+1) z (insert p P) := by
      have hb := mul_le_mul_of_nonneg_left hstrip hf.le
      simpa only [mul_assoc, ← div_eq_mul_inv, one_div, mul_inv_cancel_left₀ hf.ne'] using hb
    rw [prod_insert hpP, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih (fun q hq => hP q (mem_insert_of_mem hq))) hf.le).trans hh

lemma avoidingHarmonicMoment_totient_lower (k z M : ℕ) (hM : 0 < M) :
    ((M.totient : ℝ)/(M : ℝ))^(k+1)*harmonicMoment (k+1) z ≤
      avoidingHarmonicMoment (k+1) z M.primeFactors := by
  have hphi : (M.totient : ℝ)/(M : ℝ) = ∏ p ∈ M.primeFactors, (1-(p : ℝ)⁻¹) := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    push_cast at hh
    rw [hh]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hM.ne')
  rw [hphi, ← Finset.prod_pow]
  exact avoidingHarmonicMoment_euler_lower k z M.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)

end Erdos821.HigherDivisors
