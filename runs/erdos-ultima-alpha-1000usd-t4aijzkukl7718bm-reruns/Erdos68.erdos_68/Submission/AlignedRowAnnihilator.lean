import Submission.FactorialLambert

/-! Backwards integer elimination for aligned finite Lambert rows.
This is auxiliary arithmetic, not a settlement of Erdős 68. -/

namespace AlignedRowAnnihilator

open Finset Erdos68Development

private lemma next_bounds (N d : ℕ) (hd : 2 ≤ d) (i : Fin (N/d-1)) :
    d < d*(i.val+2) ∧ d*(i.val+2) ≤ N := by
  have hi : i.val+2 ≤ N/d := by omega
  have hl := Nat.mul_le_mul_left d hi
  have hu := Nat.mul_div_le N d
  constructor
  · nlinarith
  · omega

def solve (A : ℤ) (N d : ℕ) : ℤ :=
  if hd : 2 ≤ d then
    A / ((d.factorial : ℤ)-1) -
      ∑ i : Fin (N/d-1),
        (((d*(i.val+2)).factorial / d.factorial^(i.val+2) : ℕ) : ℤ) *
          solve A N (d*(i.val+2))
  else 0
termination_by N-d
decreasing_by
  have h := next_bounds N d hd i
  omega

def value (A : ℤ) (N d : ℕ) : ℤ := (d.factorial : ℤ)*solve A N d

lemma factorial_dvd_value (A : ℤ) (N d : ℕ) : (d.factorial : ℤ) ∣ value A N d :=
  dvd_mul_right _ _

lemma value_equation (A : ℤ) (N d : ℕ) (hd : 2 ≤ d)
    (hA : (d.factorial : ℤ)-1 ∣ A) :
    (value A N d : ℚ) = (A : ℚ)*d.factorial/(d.factorial-1) -
      ∑ i : Fin (N/d-1), (value A N (d*(i.val+2)) : ℚ) /
        (d.factorial : ℚ)^(i.val+1) := by
  have hB : (2 : ℚ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hn : (d.factorial : ℚ)-1 ≠ 0 := by linarith
  have hB0 : (d.factorial : ℚ) ≠ 0 := by positivity
  simp only [value, Int.cast_mul, Int.cast_natCast]
  rw [solve, dif_pos hd, Int.cast_sub, Int.cast_sum]
  rw [Int.cast_div hA (by simpa using hn)]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    rw [Int.cast_mul, Int.cast_natCast,
      Nat.cast_div (factorial_pow_dvd_factorial_mul d (i.val+2)) (by positivity)]
    push_cast
    rw [show i.val+2=(i.val+1)+1 by omega, pow_succ]
    field_simp

private lemma reciprocal_sum_bound (B : ℚ) (hB : 1 < B) (m : ℕ) :
    (∑ i ∈ range m, 1/B^(i+1)) ≤ 1/(B-1) := by
  have h0 : B ≠ 0 := by linarith
  have hn : B-1 ≠ 0 := by linarith
  have hid : (∑ i ∈ range m, 1/B^(i+1)) = (1-1/B^m)/(B-1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih, pow_succ]
      field_simp
      ring
  rw [hid]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have : 0 ≤ 1/B^m := by positivity
  linarith

/-- The recursion has bounded real size despite its exact integrality. -/
theorem value_bounds (A : ℤ) (N : ℕ) (hA : 0 ≤ A)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A)
    (d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N) :
    0 ≤ value A N d ∧ value A N d ≤ 2*A := by
  induction h : N-d using Nat.strong_induction_on generalizing d with
  | h m ih =>
    have hAq : (0 : ℚ) ≤ A := by exact_mod_cast hA
    have hB : (2 : ℚ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
    have hB0 : (0 : ℚ) < d.factorial := by positivity
    have hdpos : (0 : ℚ) < (d.factorial : ℚ)-1 := by linarith
    have hv (i : Fin (N/d-1)) :
        (0 : ℚ) ≤ value A N (d*(i.val+2)) ∧
          (value A N (d*(i.val+2)) : ℚ) ≤ 2*(A : ℚ) := by
      have hb := next_bounds N d hd i
      have ht := ih (N-d*(i.val+2)) (by omega) (d*(i.val+2)) (by omega) hb.2 rfl
      exact_mod_cast ht
    have hlo : (0 : ℚ) ≤ ∑ i : Fin (N/d-1),
        (value A N (d*(i.val+2)) : ℚ)/(d.factorial : ℚ)^(i.val+1) := by
      exact sum_nonneg fun i _ => div_nonneg (hv i).1 (by positivity)
    have hhi : (∑ i : Fin (N/d-1),
        (value A N (d*(i.val+2)) : ℚ)/(d.factorial : ℚ)^(i.val+1)) ≤
        2*(A : ℚ)/((d.factorial : ℚ)-1) := by
      calc
        _ ≤ ∑ i : Fin (N/d-1), 2*(A : ℚ)/(d.factorial : ℚ)^(i.val+1) := by
          apply sum_le_sum
          intro i _
          exact div_le_div_of_nonneg_right (hv i).2 (by positivity)
        _ = 2*(A : ℚ)*(∑ i ∈ range (N/d-1), 1/(d.factorial : ℚ)^(i+1)) := by
          rw [← Fin.sum_univ_eq_sum_range, mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _ ≤ 2*(A : ℚ)*(1/((d.factorial : ℚ)-1)) :=
          mul_le_mul_of_nonneg_left (reciprocal_sum_bound _ (by linarith) _) (by positivity)
        _ = _ := by ring
    have he := value_equation A N d hd (hdiv d hd hdN)
    have hu : (A : ℚ)*d.factorial/(d.factorial-1) ≤ 2*(A : ℚ) := by
      apply (div_le_iff₀ hdpos).mpr
      nlinarith
    have hl : 2*(A : ℚ)/(d.factorial-1) ≤ (A : ℚ)*d.factorial/(d.factorial-1) := by
      apply div_le_div_of_nonneg_right _ hdpos.le
      nlinarith
    have hboth : (0 : ℚ) ≤ value A N d ∧ (value A N d : ℚ) ≤ 2*(A : ℚ) := by
      constructor <;> linarith
    exact_mod_cast hboth

def cutValue (A : ℤ) (N j : ℕ) : ℤ :=
  if j < 2 then A else if j ≤ N then value A N j else 0

def weight (A : ℤ) (N j : ℕ) : ℤ := cutValue A N j-cutValue A N (j+1)

lemma cutValue_eq (A : ℤ) (N d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N) :
    cutValue A N d = value A N d := by
  simp [cutValue, show ¬d<2 by omega, hdN]

lemma cutValue_bounds (A : ℤ) (N : ℕ) (hA : 0 ≤ A)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) (j : ℕ) :
    0 ≤ cutValue A N j ∧ cutValue A N j ≤ 2*A := by
  by_cases hj : j < 2
  · simp only [cutValue, if_pos hj]
    omega
  · by_cases hjN : j ≤ N
    · rw [cutValue_eq A N j (by omega) hjN]
      exact value_bounds A N hA hdiv j (by omega) hjN
    · simp only [cutValue, if_neg hj, if_neg hjN]
      omega

lemma weight_bound (A : ℤ) (N : ℕ) (hA : 0 ≤ A)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) (j : ℕ) :
    |weight A N j| ≤ 2*A := by
  have h0 := cutValue_bounds A N hA hdiv j
  have h1 := cutValue_bounds A N hA hdiv (j+1)
  exact abs_le.mpr (by unfold weight; omega)

lemma weight_sum (A : ℤ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ j ∈ range (N+1), weight A N j = A := by
  simp only [weight, sum_range_sub']
  simp [cutValue, show ¬N+1<2 by omega]

private lemma weighted_floor_sum (v : ℕ → ℚ) (B : ℚ) (hB : B ≠ 0)
    (d N : ℕ) :
    (∑ j ∈ range (N+1), (v j-v (j+1))/B^(j/d)) =
      v 0-v (N+1)/B^(N/d) -
        (B-1)*(∑ k ∈ range (N/d), v (d*(k+1))/B^(k+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    by_cases h : d ∣ N+1
    · have hq := Nat.succ_div_of_dvd h
      have he : d*(N/d+1)=N+1 := by
        rw [← hq, Nat.mul_div_cancel' h]
      rw [hq, sum_range_succ, he, pow_succ]
      field_simp
      ring
    · rw [Nat.succ_div_of_not_dvd h]
      ring

private lemma value_jump_sum (A : ℤ) (N d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N)
    (hdiv : (d.factorial : ℤ)-1 ∣ A) :
    (∑ k ∈ range (N/d), (cutValue A N (d*(k+1)) : ℚ)/(d.factorial : ℚ)^(k+1)) =
      (A : ℚ)/((d.factorial : ℚ)-1) := by
  have hd0 : 0 < d := by omega
  have hB : (2 : ℚ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hB0 : (d.factorial : ℚ) ≠ 0 := by positivity
  have hn : (d.factorial : ℚ)-1 ≠ 0 := by linarith
  have hm : 1 ≤ N/d := (Nat.le_div_iff_mul_le hd0).mpr (by simpa using hdN)
  have he := value_equation A N d hd hdiv
  have hc (k : ℕ) (hk : k < N/d) :
      cutValue A N (d*(k+1)) = value A N (d*(k+1)) := by
    apply cutValue_eq
    · nlinarith
    · have h := Nat.mul_le_mul_left d (show k+1 ≤ N/d by omega)
      have h' := Nat.mul_div_le N d
      omega
  have hsum : (d.factorial : ℚ)*(∑ k ∈ range (N/d),
      (cutValue A N (d*(k+1)) : ℚ)/(d.factorial : ℚ)^(k+1)) =
      (value A N d : ℚ) + ∑ i : Fin (N/d-1),
        (value A N (d*(i.val+2)) : ℚ)/(d.factorial : ℚ)^(i.val+1) := by
    conv_lhs => rw [show N/d = (N/d-1)+1 by omega, sum_range_succ']
    rw [mul_add, mul_sum]
    simp only [zero_add, Nat.mul_one, pow_one]
    rw [cutValue_eq A N d hd hdN]
    rw [mul_div_cancel₀ _ hB0]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      (value A N (d*(i+2)) : ℚ)/(d.factorial : ℚ)^(i+1)) (N/d-1), add_comm]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' : i+1 < N/d := by have := mem_range.mp hi; omega
    rw [show i+1+1=i+2 by omega, hc (i+1) hi']
    rw [show i+2=(i+1)+1 by omega, pow_succ]
    field_simp
  apply (mul_left_cancel₀ hB0)
  rw [hsum]
  rw [he]
  ring

/-- The finite integer weights annihilate every selected row at phase zero. -/
theorem weight_annihilates (A : ℤ) (N d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N)
    (hdiv : (d.factorial : ℤ)-1 ∣ A) :
    (∑ j ∈ range (N+1), (weight A N j : ℚ) /
      ((d.factorial : ℚ)^(j/d)*((d.factorial : ℚ)-1))) = 0 := by
  have hB : (2 : ℚ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hn : (d.factorial : ℚ)-1 ≠ 0 := by linarith
  have hN : 2 ≤ N := hd.trans hdN
  have he := weighted_floor_sum (fun j => (cutValue A N j : ℚ))
    d.factorial (by positivity) d N
  have hz : cutValue A N (N+1)=0 := by
    simp [cutValue, show ¬N+1<2 by omega]
  have hstart : cutValue A N 0=A := by simp [cutValue]
  rw [hz, hstart, Int.cast_zero, zero_div, sub_zero,
    value_jump_sum A N d hd hdN hdiv, mul_div_cancel₀ _ hn, sub_self] at he
  calc
    _ = (∑ j ∈ range (N+1), ((cutValue A N j : ℚ)-(cutValue A N (j+1) : ℚ)) /
        (d.factorial : ℚ)^(j/d))/((d.factorial : ℚ)-1) := by
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      simp only [weight, Int.cast_sub, div_div]
    _ = 0 := by rw [he, zero_div]

/-- Translating by a common multiple of the row periods preserves cancellation. -/
theorem weight_annihilates_aligned (A : ℤ) (N H d : ℕ)
    (hd : 2 ≤ d) (hdN : d ≤ N) (hH : d ∣ H)
    (hdiv : (d.factorial : ℤ)-1 ∣ A) :
    (∑ j ∈ range (N+1), (weight A N j : ℚ) /
      ((d.factorial : ℚ)^((H+j)/d)*((d.factorial : ℚ)-1))) = 0 := by
  have hB0 : (d.factorial : ℚ) ≠ 0 := by positivity
  have hB : (2 : ℚ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hn : (d.factorial : ℚ)-1 ≠ 0 := by linarith
  calc
    _ = (∑ j ∈ range (N+1), (weight A N j : ℚ) /
        ((d.factorial : ℚ)^(j/d)*((d.factorial : ℚ)-1))) /
          (d.factorial : ℚ)^(H/d) := by
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      rw [Nat.add_div_of_dvd_right hH, pow_add]
      field_simp
    _ = 0 := by rw [weight_annihilates A N d hd hdN hdiv, zero_div]

/-- The least arithmetic cost of a nonzero retained coefficient. -/
def commonDenominator (N : ℕ) : ℕ := (Icc 2 N).lcm (fun d => d.factorial-1)

lemma commonDenominator_pos (N : ℕ) : 0 < commonDenominator N := by
  apply Nat.pos_of_ne_zero
  apply lcm_ne_zero_iff.mpr
  intro d hd
  have hf := Nat.one_lt_factorial.mpr (mem_Icc.mp hd).1
  omega

lemma commonDenominator_dvd (N d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N) :
    (d.factorial : ℤ)-1 ∣ (commonDenominator N : ℤ) := by
  have h : d.factorial-1 ∣ commonDenominator N := dvd_lcm (mem_Icc.mpr ⟨hd,hdN⟩)
  have h' := Int.natCast_dvd_natCast.mpr h
  simpa only [Nat.cast_sub (Nat.factorial_pos d), Nat.cast_one] using h'

/-- A positive retained coefficient equal to the lcm is attained on a short
aligned window, with no extra growth in the maximum weight relative to it.
No integrality of the aggregate Lambert boundary is asserted. -/
theorem exists_bounded_aligned_annihilator (N H : ℕ) (hN : 2 ≤ N)
    (hH : ∀ d, 2 ≤ d → d ≤ N → d ∣ H) :
    ∃ z : ℕ → ℤ,
      (∑ j ∈ range (N+1), z j) = (commonDenominator N : ℤ) ∧
      (∀ j, |z j| ≤ 2*(commonDenominator N : ℤ)) ∧
      (∀ d, 2 ≤ d → d ≤ N →
        (∑ j ∈ range (N+1), (z j : ℚ) /
          ((d.factorial : ℚ)^((H+j)/d)*((d.factorial : ℚ)-1))) = 0) := by
  refine ⟨weight (commonDenominator N) N, weight_sum _ _ hN, ?_, ?_⟩
  · exact weight_bound _ _ (by positivity) (commonDenominator_dvd N)
  · intro d hd hdN
    exact weight_annihilates_aligned _ N H d hd hdN (hH d hd hdN)
      (commonDenominator_dvd N d hd hdN)

end AlignedRowAnnihilator

#print axioms AlignedRowAnnihilator.value_bounds
#print axioms AlignedRowAnnihilator.weight_annihilates_aligned
#print axioms AlignedRowAnnihilator.exists_bounded_aligned_annihilator
