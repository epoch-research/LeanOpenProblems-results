import Submission.LambertTailBarrier
import Submission.FactorialCongruence

/-! Removing finitely many geometric rows still leaves superlinear Lambert
scaled tails. This is an auxiliary obstruction, not a settlement of Erdős 68. -/

namespace Erdos68Development

/-- Keep only the Lambert rows indexed by d>=K (and d>=2). -/
def lambertCoeffFrom (K m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, if 2 ≤ d ∧ K ≤ d then
    m.factorial / d.factorial ^ (m / d) else 0

lemma lambertCoeffFrom_prime {K p : ℕ} (hp : p.Prime) (hK : K ≤ p) :
    lambertCoeffFrom K p = 1 := by
  simp [lambertCoeffFrom, hp.divisors, hp.two_le, hK, hp.ne_one.symm,
    Nat.div_self hp.pos, Nat.div_self (Nat.factorial_pos p)]

lemma lambertCoeffFrom_modEq_pred {K m : ℕ} (hm : 2 ≤ m) (hK : K ≤ m) :
    Nat.ModEq (m - 1) (lambertCoeffFrom K m) 1 := by
  have hsum : (∑ d ∈ m.divisors, if d = m then 1 else 0) = 1 := by
    simp [Nat.mem_divisors, show m ≠ 0 by omega]
  conv_rhs => rw [← hsum]
  apply Nat.ModEq.sum
  intro d hd
  by_cases heq : d = m
  · subst d
    simp only [show 2 ≤ m ∧ K ≤ m from ⟨hm, hK⟩, if_true,
      Nat.div_self (by omega : 0 < m), pow_one, Nat.div_self (Nat.factorial_pos m)]
    rfl
  · rw [if_neg heq]
    by_cases hrow : 2 ≤ d ∧ K ≤ d
    · rw [if_pos hrow]
      exact Nat.modEq_zero_iff_dvd.mpr
        (pred_dvd_proper_lambert_summand hrow.1 (Nat.dvd_of_mem_divisors hd)
          (by omega) heq)
    · simp only [if_neg hrow]
      rfl

lemma lambertCoeffFrom_le (K m : ℕ) : lambertCoeffFrom K m ≤ lambertCoeff m := by
  apply Finset.sum_le_sum
  intro d hd
  by_cases h : 2 ≤ d
  · simp only [h, true_and, if_true]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  · simp [h]

lemma summable_factorial_lambertFrom (K : ℕ) :
    Summable (fun m : ℕ => (lambertCoeffFrom K m : ℝ) / m.factorial) := by
  apply summable_factorial_lambert.of_nonneg_of_le (fun _ => by positivity)
  intro m
  exact div_le_div_of_nonneg_right (by exact_mod_cast lambertCoeffFrom_le K m) (by positivity)

lemma lambertFrom_single_row_lower (K d k : ℕ) (hd : 2 ≤ d) (hKd : K ≤ d)
    (hk : 0 < k) :
    1 / (d.factorial : ℝ) ^ k ≤
      (lambertCoeffFrom K (d * k) : ℝ) / (d * k).factorial := by
  have hmem : d ∈ (d * k).divisors := Nat.mem_divisors.mpr ⟨dvd_mul_right d k, by positivity⟩
  have h := Finset.single_le_sum
    (f := fun r => if 2 ≤ r ∧ K ≤ r then
      (d * k).factorial / r.factorial ^ (d * k / r) else 0)
    (fun r _ => Nat.zero_le _) hmem
  have hlo : (d * k).factorial / d.factorial ^ k ≤ lambertCoeffFrom K (d * k) := by
    simpa [lambertCoeffFrom, hd, hKd, Nat.mul_div_cancel_left k (by omega : 0 < d)] using h
  have hdiv : d.factorial ^ k ∣ (d * k).factorial := factorial_pow_dvd_factorial_mul d k
  have hlr : ((d * k).factorial : ℝ) / (d.factorial : ℝ) ^ k ≤
      lambertCoeffFrom K (d * k) := by
    rw [← Nat.cast_pow, ← Nat.cast_div_charZero hdiv]
    exact_mod_cast hlo
  have hf : (0 : ℝ) < (d * k).factorial := by positivity
  apply (le_div_iff₀ hf).mpr
  simpa [div_eq_mul_inv, mul_comm] using hlr

lemma scaledTail_ge_next (c : ℕ → ℕ)
    (hs : Summable (fun m : ℕ => (c m : ℝ) / m.factorial)) (n : ℕ) :
    (n.factorial : ℝ) * ((c (n + 1) : ℝ) / (n + 1).factorial) ≤
      FactorialTailCriterion.scaledTail (fun m => (c m : ℤ)) n := by
  let f : ℕ → ℝ := fun m => (c m : ℝ) / m.factorial
  have ht : Summable (fun j => f (j + (n + 1))) := (summable_nat_add_iff (n + 1)).mpr hs
  have he := hs.sum_add_tsum_nat_add (n + 1)
  have hsingle : f (n + 1) ≤ ∑' j : ℕ, f (j + (n + 1)) := by
    simpa only [zero_add] using ht.le_tsum 0 (fun _ _ => by dsimp [f]; positivity)
  have he' : (∑' j : ℕ, f (j + (n + 1))) =
      (∑' m : ℕ, f m) - ∑ m ∈ Finset.range (n + 1), f m := by
    change (∑ m ∈ Finset.range (n + 1), f m) + _ = _ at he
    linarith
  have h := mul_le_mul_of_nonneg_left hsingle (show (0 : ℝ) ≤ n.factorial by positivity)
  rw [he'] at h
  simpa [FactorialTailCriterion.scaledTail, f] using h

/-- No fixed finite row removal produces eventually linearly bounded scaled
Lambert tails. The cutoff K and the proposed linear bound C are arbitrary. -/
theorem shifted_lambert_tail_exceeds_linear (K C N : ℕ) :
    ∃ n ≥ N, (C : ℝ) * n <
      FactorialTailCriterion.scaledTail (fun m => (lambertCoeffFrom K m : ℤ)) n := by
  let d := max K 2
  let B := (C + 1) * d.factorial
  have hd : 2 ≤ d := le_max_right _ _
  have hKd : K ≤ d := le_max_left _ _
  have he := Nat.eventually_pow_lt_factorial_sub B 0
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp he
  let k := max M (N + 2)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hMk : M ≤ k := le_max_left _ _
  have hNk : N + 2 ≤ k := le_max_right _ _
  have hpow : B ^ k < k.factorial := by simpa using hM k hMk
  have hC : C ≤ (C + 1) ^ k := by
    calc
      C ≤ C + 1 := by omega
      _ ≤ (C + 1) ^ k := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < C + 1) (show 1 ≤ k by omega)
  have hsmall : C * d.factorial ^ k < k.factorial := by
    calc
      _ ≤ (C + 1) ^ k * d.factorial ^ k := Nat.mul_le_mul_right _ hC
      _ = B ^ k := by simp [B, mul_pow]
      _ < _ := hpow
  let n := d * k - 1
  have hmul : 2 * k ≤ d * k := by nlinarith
  have hdk : n + 1 = d * k := by dsimp [n]; omega
  have hkn : k ≤ n - 1 := by dsimp [n]; omega
  have hnp : 0 < n := by omega
  have hfac : C * d.factorial ^ k < (n - 1).factorial :=
    hsmall.trans_le (Nat.factorial_le hkn)
  have hfac' : (C : ℝ) * (d.factorial : ℝ) ^ k < ((n - 1).factorial : ℝ) := by
    exact_mod_cast hfac
  have hnf : n.factorial = n * (n - 1).factorial := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using Nat.factorial_succ (n - 1)
  have hscl : (C : ℝ) * n < (n.factorial : ℝ) / (d.factorial : ℝ) ^ k := by
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [hnf, Nat.cast_mul]
    have hh := mul_lt_mul_of_pos_left hfac' (show (0 : ℝ) < n by positivity)
    nlinarith
  refine ⟨n, by omega, hscl.trans_le ?_⟩
  have hl := scaledTail_ge_next (lambertCoeffFrom K) (summable_factorial_lambertFrom K) n
  have hr := lambertFrom_single_row_lower K d k hd hKd (by omega)
  rw [← hdk] at hr
  calc
    _ = (n.factorial : ℝ) * (1 / (d.factorial : ℝ) ^ k) := by ring
    _ ≤ (n.factorial : ℝ) * ((lambertCoeffFrom K (n + 1) : ℝ) / (n + 1).factorial) := by
      gcongr
    _ ≤ _ := hl

#print axioms lambertCoeffFrom_modEq_pred
#print axioms shifted_lambert_tail_exceeds_linear

end Erdos68Development
