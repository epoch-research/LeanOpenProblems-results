import Submission.RoughSelbergBound

/-! Reciprocal mass of rough integers in a finite dyadic band. The sieve
rounding error is uniform in the sample length and is not discarded. -/
namespace Erdos371.FiniteSieve
open Finset

lemma rough_set_card_le (S : Finset ℕ) (z M : ℕ)
    (hS : ∀ m ∈ S, m < M ∧ ∀ p ∈ (z+1).primesBelow, ¬p ∣ m) :
    S.card ≤ siftedCount z M := by
  classical
  unfold siftedCount avoidanceCount
  apply card_le_card
  intro m hm
  simpa only [mem_filter,mem_range] using hS m hm

lemma rough_dyadic_reciprocal_le (S : Finset ℕ) (z j : ℕ) (hz : 1 ≤ z)
    (hS : ∀ m ∈ S, 2^j ≤ m ∧ m < 2^(j+1) ∧ ∀ p ∈ (z+1).primesBelow, ¬p ∣ m) :
    (∑ m ∈ S, (1 : ℝ)/m) ≤
      4*Real.exp 1/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32/(2 : ℝ)^j := by
  have h2 : (0 : ℝ) < (2 : ℝ)^j := by positivity
  have hc : (S.card : ℝ) ≤ 2*Real.exp 1*(2^(j+1) : ℕ)/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32 :=
    calc
      _ ≤ (siftedCount z (2^(j+1)) : ℝ) := by
        exact_mod_cast rough_set_card_le S z (2^(j+1)) (fun m hm => (hS m hm).2)
      _ ≤ _ := siftedCount_selberg_bound z (2^(j+1)) hz
  calc
    _ ≤ ∑ _m ∈ S, (1 : ℝ)/(2 : ℝ)^j := by
      apply sum_le_sum
      intro m hm
      exact one_div_le_one_div_of_le h2 (by exact_mod_cast (hS m hm).1)
    _ = (S.card : ℝ)/(2 : ℝ)^j := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ (2*Real.exp 1*(2^(j+1) : ℕ)/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32)/(2 : ℝ)^j :=
      div_le_div_of_nonneg_right hc h2.le
    _ = _ := by
      push_cast
      rw [pow_succ]
      field_simp
      <;> ring

/-- Rough reciprocal mass in any finite band of binary exponents. -/
theorem rough_band_reciprocal_le (S : Finset ℕ) (z a b : ℕ) (hz : 1 ≤ z)
    (hS : ∀ m ∈ S, 2^a ≤ m ∧ m < 2^(b+1) ∧ ∀ p ∈ (z+1).primesBelow, ¬p ∣ m) :
    (∑ m ∈ S, (1 : ℝ)/m) ≤ (b+1-a : ℕ)*
      (4*Real.exp 1/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32/(2 : ℝ)^a) := by
  have hm0 (m : ℕ) (hm : m ∈ S) : m ≠ 0 := by
    have hh := (hS m hm).1
    have : 0 < (2 : ℕ)^a := by positivity
    omega
  have hmap : ∀ m ∈ S, Nat.log 2 m ∈ Icc a b := by
    intro m hm
    obtain ⟨hl,hu,_⟩ := hS m hm
    exact mem_Icc.mpr ⟨(Nat.le_log_iff_pow_le (by decide : 1 < 2) (hm0 m hm)).mpr hl,
      Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (hm0 m hm)).mpr hu)⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _j ∈ Icc a b, (4*Real.exp 1/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32/(2 : ℝ)^a) := by
      apply sum_le_sum
      intro j hj
      have hjl := (mem_Icc.mp hj).1
      calc
        _ ≤ 4*Real.exp 1/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32/(2 : ℝ)^j := by
          apply rough_dyadic_reciprocal_le _ z j hz
          intro m hm
          obtain ⟨hm,he⟩ := mem_filter.mp hm
          refine ⟨?_,?_,(hS m hm).2.2⟩
          · simpa only [he] using Nat.pow_log_le_self 2 (hm0 m hm)
          · simpa only [he] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
        _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2*(z+1 : ℝ)^32) (by positivity : (0 : ℝ) < (2 : ℝ)^a)
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjl)) _
    _ = _ := by simp only [sum_const,Nat.card_Icc,nsmul_eq_mul]

lemma dyadic_band_width_le (A N : ℕ) (hA : 1 ≤ A) (hAN : A ≤ N) :
    (Nat.log 2 N+1-Nat.log 2 A : ℕ) ≤
      (Real.log N-Real.log A)/Real.log 2+2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlogN : (Nat.log 2 N : ℝ) ≤ Real.log N/Real.log 2 := by
    simpa only [Real.logb,Nat.cast_ofNat] using Real.natLog_le_logb N 2
  have hlogA : Real.log A < ((Nat.log 2 A : ℝ)+1)*Real.log 2 := by
    have hh := Real.log_lt_log ha0 (show (A : ℝ) < (2 : ℝ)^(Nat.log 2 A+1) by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) A)
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_one] using hh
  have hmono : Nat.log 2 A ≤ Nat.log 2 N := Nat.log_mono_right hAN
  rw [Nat.cast_sub (hmono.trans (Nat.le_succ _)),Nat.cast_succ]
  have hh := (le_div_iff₀ h2).mp hlogN
  have hd := div_mul_cancel₀ (Real.log N-Real.log A) h2.ne'
  nlinarith

/-- The lower dyadic endpoint loses at most a factor of two. -/
lemma inverse_dyadic_floor_le (A : ℕ) (hA : 1 ≤ A) :
    (1 : ℝ)/(2 : ℝ)^(Nat.log 2 A) ≤ 2/A := by
  have ha0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have h2 : (0 : ℝ) < (2 : ℝ)^(Nat.log 2 A) := by positivity
  have hh : (A : ℝ) < (2 : ℝ)^(Nat.log 2 A+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) A
  rw [pow_succ] at hh
  apply (div_le_div_iff₀ h2 ha0).mpr
  nlinarith

/-- A uniform finite bound in a real logarithmic interval. -/
theorem rough_interval_reciprocal_le (S : Finset ℕ) (z A N : ℕ)
    (hz : 1 ≤ z) (hA : 1 ≤ A) (hAN : A ≤ N)
    (hS : ∀ m ∈ S, A ≤ m ∧ m ≤ N ∧ ∀ p ∈ (z+1).primesBelow, ¬p ∣ m) :
    (∑ m ∈ S, (1 : ℝ)/m) ≤
      ((Real.log N-Real.log A)/Real.log 2+2)*
        (4*Real.exp 1/Real.log (z+1 : ℝ)+4*(z+1 : ℝ)^32/A) := by
  have hband := rough_band_reciprocal_le S z (Nat.log 2 A) (Nat.log 2 N) hz (by
    intro m hm
    obtain ⟨hl,hu,hr⟩ := hS m hm
    exact ⟨(Nat.pow_log_le_self 2 (by omega : A ≠ 0)).trans hl,
      hu.trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N),hr⟩)
  apply hband.trans
  have hwidth := dyadic_band_width_le A N hA hAN
  have hb : 0 ≤ (4*Real.exp 1/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32/(2 : ℝ)^(Nat.log 2 A)) := by
    apply add_nonneg (div_nonneg (by positivity) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith)))
    positivity
  apply mul_le_mul hwidth _ hb (by exact le_trans (Nat.cast_nonneg _) hwidth)
  apply add_le_add le_rfl
  have hh := mul_le_mul_of_nonneg_left (inverse_dyadic_floor_le A hA)
    (by positivity : (0 : ℝ) ≤ 2*(z+1 : ℝ)^32)
  convert hh using 1 <;> ring

#print axioms rough_band_reciprocal_le
#print axioms rough_interval_reciprocal_le
end Erdos371.FiniteSieve
