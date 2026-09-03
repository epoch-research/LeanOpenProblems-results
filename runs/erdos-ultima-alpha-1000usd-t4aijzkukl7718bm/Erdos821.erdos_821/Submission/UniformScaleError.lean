import Submission.UniformRoughHalfError
import Submission.FamilyBlockSieve
import Submission.ParametricWidePools

/-!
# Uniform rough-pool errors on fixed multiples of a geometric scale

A fixed multiplicative enlargement of the cutoff is absorbed by a fixed
shift of the scale variable. All errors remain power-saving.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma progressionScaleN_mul_add (t m s : ℕ) :
    progressionScaleN (t*(m+s)) = progressionScaleN (t*m)*progressionScaleN (t*s) := by
  simp only [progressionScaleN,Nat.mul_add,pow_add]

lemma fixed_multiple_le_shifted_scale (t K m : ℕ) (ht : 1 ≤ t) :
    K*progressionScaleN (t*m) ≤ progressionScaleN (t*(m+(K+1))) := by
  have hK : K ≤ progressionScaleN (t*(K+1)) := by
    apply (Nat.lt_two_pow_self (n := K)).le.trans
    unfold progressionScaleN
    apply Nat.pow_le_pow_right (by decide)
    have h := Nat.le_mul_of_pos_left (K+1) ht
    omega
  rw [progressionScaleN_mul_add]
  simpa only [mul_comm] using Nat.mul_le_mul_right (progressionScaleN (t*m)) hK

/-- The constant and the scale threshold depend on the fixed multiplier K. -/
theorem exists_uniform_scaled_rough_error (D : ℕ → Finset ℕ) (a b t K : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hbt : 2*b+5 ≤ t)
    (hD : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, 0 < d ∧ d ≤ progressionScaleN (b*m))
    (hrough : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (a*m) ≤ c) :
    ∃ C : ℕ, ∀ᶠ m : ℕ in atTop, ∀ X : ℕ, X ≤ K*progressionScaleN (t*m) →
      (∑ d ∈ D m, compositeProgressionError d X) ≤
        (C : ℝ)*((m : ℝ)+1)^7*(2 : ℝ)^((64*t-1)*m) := by
  let s := K+1
  let C : ℕ := 1000000000000000*(t+1)^7*(s+1)^7*2^((64*t-1)*s)
  refine ⟨C,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 ((a-1)*s))] with m hm
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hms : (a-1)*s ≤ m := (le_max_right _ _).trans hm
  have hXupper := fixed_multiple_le_shifted_scale t K m (by omega)
  intro X hX
  have hD' (d : ℕ) (hd : d ∈ D m) : 0 < d ∧ d ≤ progressionScaleN (b*(m+s)) :=
    ⟨(hD m hm1 d hd).1,(hD m hm1 d hd).2.trans
      (progressionScaleN_monotone (Nat.mul_le_mul_left b (Nat.le_add_right m s)))⟩
  have hrough' (d : ℕ) (hd : d ∈ D m) (c : ℕ) (hc : c ∈ d.divisors.erase 1) :
      progressionScaleN ((a-1)*(m+s)) ≤ c := by
    apply le_trans _ (hrough m hm1 d hd c hc)
    apply progressionScaleN_monotone
    have ha1 := Nat.sub_add_cancel (by omega : 1 ≤ a)
    nlinarith only [hms,congrArg (fun z : ℕ => z*m) ha1]
  have h := rough_pool_below_half_combined_error_cutoff (D m) (a-1) b t (m+s) X
    (hX.trans hXupper) (by omega) (by omega) ht (by omega) hbt hD' hrough'
  have hnon : 0 ≤ 2*(progressionScaleN (b*(m+s)) : ℝ)*
      Real.sqrt (progressionScaleN (t*(m+s)))*Real.log (progressionScaleN (t*(m+s))) := by positivity
  have hpoly : (m+s : ℕ)+1 ≤ ((s : ℝ)+1)*((m : ℝ)+1) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) s]
  calc
    _ ≤ 1000000000000000*(((t : ℝ)+1)*((m+s : ℕ)+1))^7*(2 : ℝ)^((64*t-1)*(m+s)) := by
      linarith only [h,hnon]
    _ ≤ 1000000000000000*(((t : ℝ)+1)*(((s : ℝ)+1)*((m : ℝ)+1)))^7*
        (2 : ℝ)^((64*t-1)*(m+s)) := by gcongr
    _ = _ := by
      simp only [C,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
        Nat.mul_add,pow_add,mul_pow]
      ring

theorem eventually_uniform_scaled_error_le_divisor (D : ℕ → Finset ℕ) (a b t K W : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hbt : 2*b+5 ≤ t) (hW : 0 < W)
    (hD : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, 0 < d ∧ d ≤ progressionScaleN (b*m))
    (hrough : ∀ m : ℕ, 1 ≤ m → ∀ d ∈ D m, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (a*m) ≤ c) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ, X ≤ K*progressionScaleN (t*m) →
      (∑ d ∈ D m, compositeProgressionError d X) ≤
        (progressionScaleN (t*m) : ℝ)/(W : ℝ) := by
  obtain ⟨C,hC⟩ := exists_uniform_scaled_rough_error D a b t K ha hab ht hbt hD hrough
  filter_upwards [hC,eventually_power_saving_le_divisor t C 7 W (by omega) hW] with m hm he
  intro X hX
  exact (hm X hX).trans (by simpa only [independentN,progressionScaleN,mul_assoc] using he)

lemma widePairPool_rough (a m d : ℕ) (hd : d ∈ widePairPool a m)
    (c : ℕ) (hc : c ∈ d.divisors.erase 1) : independentN a m ≤ c := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have hpb := widePairPools_bounds a m p (Or.inl hp)
  have hqb := widePairPools_bounds a m q (Or.inr hq)
  obtain ⟨hc1,hcd⟩ := mem_erase.mp hc
  rcases prime_pair_divisors (widePairLeft_prime a m p hp) (widePairRight_prime a m q hq)
    (Nat.dvd_of_mem_divisors hcd) with h | h | h | h
  · exact False.elim (hc1 h)
  · exact h ▸ hpb.2.1
  · exact h ▸ hqb.2.1
  · rw [h]
    exact hpb.2.1.trans (Nat.le_mul_of_pos_right p (by omega))

theorem eventually_uniform_widePair_error (a K W : ℕ) (ha : 2 ≤ a) (hW : 0 < W) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ, X ≤ K*independentN (widePairScale a) m →
      (∑ d ∈ widePairPool a m, compositeProgressionError d X) ≤
        (independentN (widePairScale a) m : ℝ)/(W : ℝ) := by
  have H := eventually_uniform_scaled_error_le_divisor (widePairPool a) a (2*a+4)
    (widePairScale a) K W ha (by omega) (by dsimp [widePairScale]; omega)
    (by dsimp [widePairScale]; omega) hW (by
      intro m hm d hd
      have h := widePairPool_bounds a m d hd
      exact ⟨by omega,by simpa only [independentN,progressionScaleN,mul_assoc] using h.2.2⟩) (by
      intro m hm d hd c hc
      simpa only [independentN,progressionScaleN,mul_assoc] using widePairPool_rough a m d hd c hc)
  simpa only [independentN,progressionScaleN,mul_assoc] using H

end Erdos821
