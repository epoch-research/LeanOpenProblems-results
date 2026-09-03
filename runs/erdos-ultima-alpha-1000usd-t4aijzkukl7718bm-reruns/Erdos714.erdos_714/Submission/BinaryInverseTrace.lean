import FormalConjecturesUtil

/-!
A Fourier witness for a nonzero element whose binary trace and reciprocal
trace both vanish. This auxiliary finite-field result does not settle Erdős714.
-/
noncomputable section
open Finset Classical
open scoped CharTwo
set_option maxHeartbeats 2000000
namespace Erdos714BinaryInverseTrace

private lemma power_bounds (k i : ℕ) (hk : 4 ≤ k) (hi : i < k) :
    16 ≤ 2^k ∧ 2^i ≤ 2^(k-1) ∧ 2^k = 2*2^(k-1) := by
  refine ⟨Nat.pow_le_pow_right (n := 2) (i := 4) (by omega) hk,
    Nat.pow_le_pow_right (by omega) (by omega), ?_⟩
  conv_lhs => rw [show k=(k-1)+1 by omega]
  rw [pow_succ, mul_comm]

private lemma three_add_power (i j : ℕ) : 3+2^i = 2^j ↔ i=0 ∧ j=2 := by
  constructor
  · intro h
    have hi0 : i=0 := by
      by_contra hi
      have hdi : 2 ∣ 2^i := Nat.pow_dvd_pow 2 (by omega : 1 ≤ _)
      have hj : 0 < j := by
        by_contra hj
        have he : 2^j=1 := by rw [show j=0 by omega]; rfl
        have hh : 3+2^i=1 := h.trans he
        have hle : 3 ≤ 3+2^i := Nat.le_add_right _ _
        rw [hh] at hle
        norm_num at hle
      have hdj : 2 ∣ 2^j := Nat.pow_dvd_pow 2 (by omega : 1 ≤ _)
      have hmi := Nat.mod_eq_zero_of_dvd hdi
      have hmj := Nat.mod_eq_zero_of_dvd hdj
      omega
    subst i
    refine ⟨rfl, ?_⟩
    have he : 2^j=2^2 := by norm_num at h ⊢; omega
    exact (Nat.pow_right_injective (by decide : 1 < 2)) he
  · rintro ⟨rfl,rfl⟩
    decide

variable {F : Type*} [Field F] [Fintype F]

/-- Orthogonality for a quotient of two powers below the multiplicative order. -/
lemma sum_power_quotient (n m : ℕ) (hn : n < Fintype.card F-1)
    (hm : m < Fintype.card F-1) :
    (∑ t : Fˣ, (t : F)^n * ((t : F)⁻¹)^m) = if n=m then (-1 : F) else 0 := by
  have hinv (t : Fˣ) : ((t : F)⁻¹)^m = (t : F)^(Fintype.card F-1-m) := by
    rw [pow_sub₀ _ (Units.ne_zero t) hm.le, FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero t)]
    simp [inv_pow]
  simp_rw [hinv, ← pow_add]
  rw [FiniteField.sum_pow_units]
  have hdiv : Fintype.card F-1 ∣ n+(Fintype.card F-1-m) ↔ n=m := by
    constructor
    · rintro ⟨a,ha⟩
      have hpos : 0 < n+(Fintype.card F-1-m) := by omega
      have hlt : n+(Fintype.card F-1-m) < 2*(Fintype.card F-1) := by omega
      have ha1 : a=1 := by nlinarith
      rw [ha1,mul_one] at ha
      omega
    · intro he
      subst m
      convert dvd_refl (Fintype.card F-1) using 1; omega
  simp only [hdiv]

variable [CharP F 2]

def traceSum (k : ℕ) (x : F) : F := ∑ i ∈ range k, x^(2^i)

omit [Fintype F] in
lemma traceSum_add (k : ℕ) (x y : F) :
    traceSum k (x+y) = traceSum k x+traceSum k y := by
  simp [traceSum, add_pow_char_pow, sum_add_distrib]

omit [CharP F 2] in
lemma traceSum_square (k : ℕ) (hcard : Fintype.card F=2^k) (x : F) :
    traceSum k (x^2) = traceSum k x := by
  have hp (i : ℕ) : (x^2)^(2^i)=x^(2^(i+1)) := by rw [← pow_mul, pow_succ']
  have ht := sum_range_sub (fun i : ℕ => x^(2^i)) k
  simp_rw [← hp] at ht
  rw [sum_sub_distrib] at ht
  have ht0 : x^(2^k)-x^(2^0)=0 := by simp [← hcard, FiniteField.pow_card]
  rw [ht0] at ht
  exact sub_eq_zero.mp ht

lemma traceSum_zero_or_one (k : ℕ) (hcard : Fintype.card F=2^k) (x : F) :
    traceSum k x=0 ∨ traceSum k x=1 := by
  have hs : (traceSum k x)^2=traceSum k x := by
    rw [traceSum, sum_pow_char]
    simpa [traceSum, ← pow_mul, mul_comm] using traceSum_square k hcard x
  have hz : traceSum k x*(traceSum k x-1)=0 := by linear_combination hs
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The third multiplicative Fourier coefficient is exactly one. -/
theorem weighted_indicator (k : ℕ) (hk : 4 ≤ k) (hcard : Fintype.card F=2^k) :
    (∑ t : Fˣ, (t : F)^3 * (1+traceSum k (t : F)) *
      (1+traceSum k ((t : F)⁻¹))) = 1 := by
  have hq := (power_bounds k 0 hk (by omega)).1
  have hsingle (i : ℕ) (hi : i ∈ range k) :
      (∑ t : Fˣ, (t : F)^(3+2^i))=0 := by
    rw [FiniteField.sum_pow_units, hcard, if_neg]
    have hb := power_bounds k i hk (mem_range.mp hi)
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)
  have hinverse (i : ℕ) (hi : i ∈ range k) :
      (∑ t : Fˣ, (t : F)^3*((t : F)⁻¹)^(2^i))=0 := by
    have hb := power_bounds k i hk (mem_range.mp hi)
    rw [sum_power_quotient 3 (2^i) (by omega) (by omega), if_neg]
    intro he
    by_cases hi0 : i=0
    · simp [hi0] at he
    · have hd : 2 ∣ 2^i := Nat.pow_dvd_pow 2 (by omega : 1 ≤ _)
      rw [← he] at hd
      norm_num at hd
  have hdouble (i j : ℕ) (hi : i ∈ range k) (hj : j ∈ range k) :
      (∑ t : Fˣ, (t : F)^(3+2^i)*((t : F)⁻¹)^(2^j)) =
        if i=0 ∧ j=2 then (1 : F) else 0 := by
    have hbi := power_bounds k i hk (mem_range.mp hi)
    have hbj := power_bounds k j hk (mem_range.mp hj)
    rw [sum_power_quotient (3+2^i) (2^j) (by omega) (by omega)]
    simp only [three_add_power, CharTwo.neg_eq]
  have hconstant : (∑ t : Fˣ, (t : F)^3)=0 := by
    rw [FiniteField.sum_pow_units, hcard, if_neg]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hex (t : Fˣ) :
      (t : F)^3*(1+traceSum k (t : F))*(1+traceSum k ((t : F)⁻¹)) =
      (t : F)^3 + (∑ i ∈ range k, (t : F)^(3+2^i)) +
      (∑ j ∈ range k, (t : F)^3*((t : F)⁻¹)^(2^j)) +
      ∑ i ∈ range k, ∑ j ∈ range k,
        (t : F)^(3+2^i)*((t : F)⁻¹)^(2^j) := by
    simp only [traceSum, pow_add, ← mul_sum, ← sum_mul]
    ring
  simp_rw [hex]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, hconstant]
  have h₁ : (∑ t : Fˣ, ∑ i ∈ range k, (t : F)^(3+2^i))=0 := by
    rw [sum_comm]
    exact sum_eq_zero hsingle
  have h₂ : (∑ t : Fˣ, ∑ j ∈ range k, (t : F)^3*((t : F)⁻¹)^(2^j))=0 := by
    rw [sum_comm]
    exact sum_eq_zero hinverse
  rw [h₁,h₂,zero_add,zero_add,zero_add,sum_comm]
  calc
    _ = ∑ i ∈ range k, ∑ j ∈ range k, if i=0 ∧ j=2 then (1 : F) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
      exact sum_congr rfl (fun j hj => hdouble i j hi hj)
    _ = 1 := by
      rw [sum_eq_single 0]
      · simp only [true_and]
        exact sum_eq_single 2 (by intros; simp_all) (by simp [show 2 < k by omega])
      · intro i hi hi0
        simp [hi0]
      · simp [show 0 < k by omega]

/-- Both traces vanish for some nonzero element of every binary field of size
at least sixteen. There is no numeric search or analytic estimate here. -/
theorem exists_trace_zero_inverse (k : ℕ) (hk : 4 ≤ k)
    (hcard : Fintype.card F=2^k) :
    ∃ a : F, a ≠ 0 ∧ traceSum k a=0 ∧ traceSum k a⁻¹=0 := by
  have hs := weighted_indicator (F := F) k hk hcard
  obtain ⟨t,_,ht⟩ := exists_ne_zero_of_sum_ne_zero (show
      (∑ t : Fˣ, (t : F)^3*(1+traceSum k (t : F))*(1+traceSum k ((t : F)⁻¹))) ≠ 0 by
    rw [hs]; exact one_ne_zero)
  refine ⟨t,Units.ne_zero t,?_,?_⟩
  · rcases traceSum_zero_or_one k hcard (t : F) with h | h
    · exact h
    · simp [h] at ht
  · rcases traceSum_zero_or_one k hcard ((t : F)⁻¹) with h | h
    · exact h
    · simp [h] at ht

#print axioms sum_power_quotient
#print axioms traceSum_square
#print axioms traceSum_zero_or_one
#print axioms weighted_indicator
#print axioms exists_trace_zero_inverse
end Erdos714BinaryInverseTrace
