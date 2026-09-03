import Submission.BinaryWeightedCertificates

/-! Soundness of a quadratic binary-length potential criterion. The required
strict rate is a hypothesis; no successful certificate is asserted here. -/
namespace Erdos406BinaryQuadratic
open Erdos406BinaryWeighted Erdos406AffineCertificate Erdos406GroupedCertificate

lemma binary_length_le_ternary_length (n : ℕ) :
    ((Nat.digits 2 n).length : ℝ) ≤
      (Real.log 3 / Real.log 2) * (Nat.digits 3 n).length + 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  by_cases hn : n = 0
  · simp [hn]
  have hp : 0 < n := Nat.pos_of_ne_zero hn
  have hbin := Nat.base_pow_length_digits_le 2 n (by decide) hn
  have hter := Nat.lt_base_pow_length_digits (m := n) (by decide : 1 < 3)
  have hpow : (2 : ℝ) ^ (Nat.digits 2 n).length ≤
      2 * 3 ^ (Nat.digits 3 n).length := by
    exact_mod_cast (hbin.trans (Nat.mul_le_mul_left 2 hter.le))
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  have hdiv : (Real.log 3 / Real.log 2) * Real.log 2 = Real.log 3 :=
    div_mul_cancel₀ _ (ne_of_gt h2)
  nlinarith

lemma construction_good_bound (V : ℕ → ℝ) (C : ℝ)
    (hstep : ∀ n d : ℕ, d < 2 →
      V (3*n+d) ≤ V n + 2*(Nat.digits 2 n).length + C)
    (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    V n ≤ V 0 + (Real.log 3 / Real.log 2) * ((Nat.digits 3 n).length : ℝ)^2 +
      (|C|+2) * (Nat.digits 3 n).length := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hb : 0 < Real.log 3 / Real.log 2 := div_pos h3 h2
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    have hq := ih (n/3) (Nat.div_lt_self hp (by decide)) (good_div_three hg)
    have hd : n%3 < 2 := by
      rcases good_unit_mod_three hp hg with h | h <;> omega
    have hs := hstep (n/3) (n%3) hd
    have he : 3*(n/3)+n%3 = n := by omega
    rw [he] at hs
    have hlen := binary_length_le_ternary_length (n/3)
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith [le_abs_self C]

/-- A strictly positive quadratic coefficient eventually dominates any linear
error. This lemma makes the cutoff argument independent of digit functions. -/
lemma quadratic_eventual_positive (g L M : ℝ) (hg : 0 < g) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → L*k+M < g*(k:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 ((|L|+|M|+1)/g))
  have hN1 : (1:ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNg : |L|+|M|+1 < (N:ℝ)*g :=
    (div_lt_iff₀ hg).mp ((le_max_right _ _).trans_lt hN)
  refine ⟨N,?_⟩
  intro k hk
  have hNk : (N:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1:ℝ) < k := hN1.trans_le hNk
  have hkg : |L|+|M|+1 < (k:ℝ)*g :=
    hNg.trans_le (mul_le_mul_of_nonneg_right hNk hg.le)
  have hh := mul_lt_mul_of_pos_right hkg (by linarith : (0:ℝ)<k)
  have hL := mul_nonneg (sub_nonneg.mpr (le_abs_self L))
    (by positivity : (0:ℝ) ≤ k)
  have hM := mul_nonneg (abs_nonneg M) (show (0:ℝ) ≤ k-1 by linarith)
  nlinarith [le_abs_self M]

/-- Quadratic potentials may have linear and constant errors. The strict
condition is the same rate threshold as for the linear binary criterion. -/
theorem quadratic_potential_criterion (V : ℕ → ℝ) (a B D C : ℝ)
    (hstep : ∀ n d : ℕ, d < 2 →
      V (3*n+d) ≤ V n + 2*(Nat.digits 2 n).length + C)
    (hpower : ∀ k : ℕ, a*(k:ℝ)^2-B*k-D ≤ V (2^k))
    (hcrit : Real.log 2 < a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let α : ℝ := Real.log 2 / Real.log 3
  let β : ℝ := Real.log 3 / Real.log 2
  have hα : 0 < α := div_pos h2 h3
  have hβ : 0 < β := div_pos h3 h2
  have hαβ : α*β = 1 := by dsimp [α,β]; field_simp
  have hgap : 0 < a-α := by
    have hh : α < a := (div_lt_iff₀ h3).mpr hcrit
    linarith
  let E : ℝ := |C|+2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨N,hN⟩ := quadratic_eventual_positive (a-α) (B+2+E*α) (V 0+β+E+D) hgap
  have hcut (k : ℕ) (hk : N ≤ k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    have hu := construction_good_bound V C hstep (2^k) hg
    have hl := hpower k
    have hlenlog := ternary_power_length_log k
    have hlen : ((Nat.digits 3 (2^k)).length : ℝ) ≤ α*k+1 := by
      have hdiv : α*Real.log 3 = Real.log 2 := div_mul_cancel₀ _ (ne_of_gt h3)
      nlinarith
    have hlen0 : (0:ℝ) ≤ (Nat.digits 3 (2^k)).length := by positivity
    have hlen2 : ((Nat.digits 3 (2^k)).length : ℝ)^2 ≤ (α*k+1)^2 := by nlinarith
    have hs := mul_le_mul_of_nonneg_left hlen2 hβ.le
    have he := mul_le_mul_of_nonneg_left hlen hE
    change V (2^k) ≤ V 0+β*((Nat.digits 3 (2^k)).length:ℝ)^2+
      E*(Nat.digits 3 (2^k)).length at hu
    have hmain : (a-α)*(k:ℝ)^2 ≤ (B+2+E*α)*k+(V 0+β+E+D) := by
      have hprod : β*(α*k+1)^2 = α*(k:ℝ)^2+2*k+β := by
        calc
          _ = (α*β)*α*(k:ℝ)^2+2*(α*β)*k+β := by ring
          _ = _ := by rw [hαβ]; ring
      rw [hprod] at hs
      nlinarith
    exact (not_lt_of_ge hmain) (hN k hk)
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^N,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  have hk : k < N := by
    by_contra h
    exact hcut k (by omega) hg
  exact Nat.pow_le_pow_right (by decide) (by omega)

#print axioms binary_length_le_ternary_length
#print axioms construction_good_bound
#print axioms quadratic_eventual_positive
#print axioms quadratic_potential_criterion
end Erdos406BinaryQuadratic
