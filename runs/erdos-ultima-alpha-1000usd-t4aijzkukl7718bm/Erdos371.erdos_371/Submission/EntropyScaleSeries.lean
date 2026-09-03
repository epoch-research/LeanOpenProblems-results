import FormalConjecturesUtil

/-! Divergent entropy-decrement weights on factorially growing scales. -/
namespace Erdos371.EntropyScales
open Finset

noncomputable def bertrandWeight (n : ℕ) : ℝ := 1 / ((n+2 : ℝ) * Real.log (n+2))

lemma bertrandWeight_pos (n : ℕ) : 0 < bertrandWeight n := by
  unfold bertrandWeight
  exact one_div_pos.mpr (mul_pos (by positivity) (Real.log_pos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])))

lemma bertrandWeight_antitone : Antitone bertrandWeight := by
  intro m n hmn
  apply one_div_le_one_div_of_le
  · exact mul_pos (by positivity) (Real.log_pos (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
  · have hm : 0 < (m+2 : ℝ) := by positivity
    have hn : (m+2 : ℝ) ≤ n+2 := by exact_mod_cast Nat.add_le_add_right hmn 2
    exact mul_le_mul hn (Real.log_le_log hm hn)
      (Real.log_pos (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)] : (1 : ℝ) < m+2)).le (by positivity)

/-- The positive Bertrand series at exponent one diverges. -/
theorem not_summable_bertrandWeight : ¬Summable bertrandWeight := by
  intro hs
  have hc := (summable_condensed_iff_of_nonneg (fun n => (bertrandWeight_pos n).le)
    (fun _ _ _ hmn => bertrandWeight_antitone hmn)).mpr hs
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcompare (k : ℕ) :
      1 / (3 * Real.log 2) * (1 / (k+2 : ℝ)) ≤ 2 ^ k * bertrandWeight (2 ^ k) := by
    have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hbase : 0 < (2 : ℝ) ^ k + 2 := by positivity
    have hupper : (2 : ℝ) ^ k + 2 ≤ 2 ^ (k+2) := by
      rw [pow_add]
      norm_num
      linarith
    have hlog := Real.log_le_log hbase hupper
    rw [Real.log_pow] at hlog
    push_cast at hlog
    have hden : ((2 : ℝ) ^ k + 2) * Real.log (2 ^ k + 2) ≤
        (3 * Real.log 2) * (k+2) * 2 ^ k := by
      have hlog0 : 0 ≤ Real.log ((2 : ℝ)^k+2) := Real.log_nonneg (by linarith)
      have hm := mul_le_mul (show (2 : ℝ)^k+2 ≤ 3*2^k by linarith)
        hlog hlog0 (by positivity : (0 : ℝ) ≤ 3*2^k)
      nlinarith [hm]
    have hdpos : 0 < ((2 : ℝ)^k+2)*Real.log (2^k+2) :=
      mul_pos hbase (Real.log_pos (by linarith))
    unfold bertrandWeight
    push_cast
    rw [one_div_mul_one_div, mul_one_div]
    apply (div_le_div_iff₀ (by positivity) hdpos).mpr
    simpa only [one_mul, mul_comm (2 ^ k : ℝ)] using hden
  have hw : Summable (fun k : ℕ => 1 / (3 * Real.log 2) * (1 / (k+2 : ℝ))) :=
    hc.of_nonneg_of_le (fun k => by positivity) hcompare
  have hh : Summable (fun k : ℕ => 1 / (k+2 : ℝ)) :=
    (summable_mul_left_iff (by positivity : 1 / (3 * Real.log 2) ≠ 0)).mp hw
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hh

/-- Scales whose successive ratios are `(n+2)^2`. -/
def factorialScale (H : ℕ) (n : ℕ) : ℕ := H * (n+1).factorial ^ 2

lemma factorialScale_succ (H n : ℕ) :
    factorialScale H (n+1) = (n+2)^2 * factorialScale H n := by
  unfold factorialScale
  rw [show n+1+1=n+2 by omega, Nat.factorial_succ (n+1)]
  ring

lemma factorialScale_ge (H n : ℕ) : H ≤ factorialScale H n := by
  unfold factorialScale
  calc
    H = H * 1 := by simp
    _ ≤ _ := Nat.mul_le_mul_left H (one_le_pow₀ (Nat.factorial_pos (n+1)))

lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
  have h := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    (show (n.factorial : ℝ) ≤ (n^n : ℕ) by exact_mod_cast Nat.factorial_le_pow n)
  simpa only [Nat.cast_pow, Real.log_pow] using h

lemma log_factorialScale_le (H n : ℕ) (hH : 1 < H) :
    Real.log (factorialScale H n : ℝ) ≤
      (Real.log H / (2*Real.log 2) + 2) * ((n+2 : ℝ)*Real.log (n+2)) := by
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hHlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast hH)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : 0 < (n+1 : ℝ) := by positivity
  have hn2 : (n+1 : ℝ) ≤ n+2 := by linarith
  have hlog : (n+1 : ℝ)*Real.log (n+1) ≤ (n+2)*Real.log (n+2) :=
    mul_le_mul hn2 (Real.log_le_log hn1 hn2)
      (Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])) (by positivity)
  have hmin : 2*Real.log 2 ≤ (n+2 : ℝ)*Real.log (n+2) := by
    apply mul_le_mul (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      h2.le (by positivity)
  have hconst := mul_le_mul_of_nonneg_left hmin
    (div_nonneg hHlog.le (by positivity : 0 ≤ 2*Real.log 2))
  have hcancel : Real.log (H : ℝ) / (2*Real.log 2) * (2*Real.log 2) = Real.log H := by
    field_simp
  rw [hcancel] at hconst
  have hfac := log_factorial_le (n+1)
  push_cast at hfac
  unfold factorialScale
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hHpos.ne' (pow_ne_zero _ (by
    exact_mod_cast (Nat.factorial_pos (n+1)).ne')), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

lemma log_factorialScale_pos (H n : ℕ) (hH : 1 < H) :
    0 < Real.log (factorialScale H n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast lt_of_lt_of_le hH (factorialScale_ge H n)

/-- The reciprocal logarithms of the factorial scales are not summable. -/
theorem not_summable_inv_log_factorialScale (H : ℕ) (hH : 1 < H) :
    ¬Summable (fun n => 1 / Real.log (factorialScale H n : ℝ)) := by
  intro hs
  let C := Real.log (H : ℝ) / (2*Real.log 2) + 2
  have hC : 0 < C := by
    dsimp [C]
    have hh := Real.log_pos (by exact_mod_cast hH : (1 : ℝ) < H)
    have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hh : Summable (fun n => C⁻¹ * bertrandWeight n) := by
    apply hs.of_nonneg_of_le
    · intro n
      exact mul_nonneg (inv_nonneg.mpr hC.le) (bertrandWeight_pos n).le
    · intro n
      change C⁻¹ * (1 / ((n+2 : ℝ) * Real.log (n+2))) ≤ _
      rw [← one_div, one_div_mul_one_div]
      exact one_div_le_one_div_of_le (log_factorialScale_pos H n hH)
        (log_factorialScale_le H n hH)
  exact not_summable_bertrandWeight ((summable_mul_left_iff (inv_ne_zero hC.ne')).mp hh)

#print axioms not_summable_bertrandWeight
#print axioms not_summable_inv_log_factorialScale
end Erdos371.EntropyScales
