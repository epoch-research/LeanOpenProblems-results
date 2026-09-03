import Submission.FreshAttack

/-!
# Exact floor and carry arithmetic for the factorial-minus-one series

This is an independent partial development. It does not import `Submission.Spec`
and does not assert irrationality or an infinite nonterminal-residue subsequence.
The index `N` here is the mathematical index: sums run from 2 through N.
In particular, `R` is a sum of individual fractional remainders, NOT the analytic
series tail. The asymptotic exceptional-interval count is documented in the audit
report, not assumed as an axiom in this file.
-/

namespace FloorArithmetic

/-- The positive denominator when `2 ≤ k`. -/
def d (k : ℕ) : ℕ := k.factorial - 1

def floorTerm (N k : ℕ) : ℕ := N.factorial / d k

def I (N : ℕ) : ℕ := ∑ k ∈ Finset.Icc 2 N, floorTerm N k

def rho (N k : ℕ) : ℕ := N.factorial % d k

noncomputable def R (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N, (rho N k : ℝ) / (d k : ℝ)

def carryTerm (N k : ℕ) : ℕ := ((N + 1) * rho N k) / d k

def J (N : ℕ) : ℕ := ∑ k ∈ Finset.Icc 2 N, carryTerm N k

lemma factorial_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ k.factorial := by
  simpa using Nat.factorial_le hk

lemma d_pos (k : ℕ) (hk : 2 ≤ k) : 0 < d k := by
  have := factorial_ge_two k hk
  unfold d
  omega

lemma d_cast (k : ℕ) : (d k : ℝ) = (k.factorial : ℝ) - 1 := by
  rw [d, Nat.cast_sub (Nat.succ_le_of_lt (Nat.factorial_pos k))]
  norm_num

lemma floorTerm_eq_floor (N k : ℕ) :
    floorTerm N k = ⌊(N.factorial : ℝ) / (d k : ℝ)⌋₊ := by
  symm
  exact Nat.floor_div_eq_div _ _

lemma fract_eq_remainder (N k : ℕ) :
    Int.fract ((N.factorial : ℝ) / (d k : ℝ)) = (rho N k : ℝ) / (d k : ℝ) := by
  exact Int.fract_div_natCast_eq_div_natCast_mod

lemma div_decomposition (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) = (a / b : ℕ) + (a % b : ℕ) / (b : ℝ) := by
  have h : (a : ℝ) = (b : ℝ) * (a / b : ℕ) + (a % b : ℕ) := by
    exact_mod_cast (Nat.div_add_mod a b).symm
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  apply (div_eq_iff hb0).mpr
  rw [h]
  field_simp

lemma mul_div_carry (a b c : ℕ) (hc : 0 < c) :
    b * a / c = b * (a / c) + (b * (a % c)) / c := by
  conv_lhs => rw [← Nat.div_add_mod a c]
  rw [Nat.mul_add, show b * (c * (a / c)) = c * (b * (a / c)) by ring]
  exact Nat.mul_add_div hc _ _

lemma floorTerm_succ (N k : ℕ) (hk : 2 ≤ k) :
    floorTerm (N + 1) k = (N + 1) * floorTerm N k + carryTerm N k := by
  simpa [floorTerm, carryTerm, rho, Nat.factorial_succ] using
    mul_div_carry N.factorial (N + 1) (d k) (d_pos k hk)

lemma rho_succ (N k : ℕ) :
    rho (N + 1) k = ((N + 1) * rho N k) % d k := by
  simp [rho, Nat.factorial_succ, Nat.mul_mod]

lemma floorTerm_self (N : ℕ) (hN : 3 ≤ N) : floorTerm N N = 1 := by
  have hfac : 6 ≤ N.factorial := by simpa using Nat.factorial_le hN
  unfold floorTerm d
  apply Nat.div_eq_of_lt_le <;> omega

lemma rho_self (N : ℕ) (hN : 3 ≤ N) : rho N N = 1 := by
  have h := Nat.div_add_mod N.factorial (d N)
  change d N * floorTerm N N + rho N N = N.factorial at h
  rw [floorTerm_self N hN] at h
  have hfac := factorial_ge_two N (by omega)
  unfold d at h
  omega

/-- The endpoint contribution is 1 only for this range; the N=1 step is excluded. -/
theorem I_succ (N : ℕ) (hN : 2 ≤ N) :
    I (N + 1) = (N + 1) * I N + J N + 1 := by
  unfold I
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1), floorTerm_self (N + 1) (by omega)]
  have hs : (∑ k ∈ Finset.Icc 2 N, floorTerm (N + 1) k) =
      ∑ k ∈ Finset.Icc 2 N, ((N + 1) * floorTerm N k + carryTerm N k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact floorTerm_succ N k (Finset.mem_Icc.mp hk).1
  rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma remainder_succ (N k : ℕ) (hk : 2 ≤ k) :
    (rho (N + 1) k : ℝ) / (d k : ℝ) =
      (N + 1 : ℝ) * ((rho N k : ℝ) / (d k : ℝ)) - (carryTerm N k : ℝ) := by
  have h := div_decomposition ((N + 1) * rho N k) (d k) (d_pos k hk)
  rw [rho_succ]
  dsimp [carryTerm]
  push_cast at h
  simp only [mul_div_assoc] at h
  linarith

theorem R_succ (N : ℕ) (hN : 2 ≤ N) :
    R (N + 1) = (N + 1 : ℝ) * R N - (J N : ℝ) + 1 / (d (N + 1) : ℝ) := by
  unfold R
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1), rho_self (N + 1) (by omega)]
  have hs : (∑ k ∈ Finset.Icc 2 N, (rho (N + 1) k : ℝ) / (d k : ℝ)) =
      ∑ k ∈ Finset.Icc 2 N,
        ((N + 1 : ℝ) * ((rho N k : ℝ) / (d k : ℝ)) - (carryTerm N k : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact remainder_succ N k (Finset.mem_Icc.mp hk).1
  rw [hs, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [J]

lemma remainder_nonneg (N k : ℕ) : 0 ≤ (rho N k : ℝ) / (d k : ℝ) := by
  positivity

lemma remainder_lt_one (N k : ℕ) (hk : 2 ≤ k) :
    (rho N k : ℝ) / (d k : ℝ) < 1 := by
  have hd : (0 : ℝ) < d k := by exact_mod_cast d_pos k hk
  apply (div_lt_one hd).mpr
  exact_mod_cast Nat.mod_lt N.factorial (d_pos k hk)

lemma R_nonneg (N : ℕ) : 0 ≤ R N :=
  Finset.sum_nonneg (fun k _ => remainder_nonneg N k)

lemma R_lt_card (N : ℕ) (hN : 2 ≤ N) : R N < ((N - 1 : ℕ) : ℝ) := by
  have hs : R N < ∑ _k ∈ Finset.Icc 2 N, (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact (remainder_lt_one N k (Finset.mem_Icc.mp hk).1).le
    · exact ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, remainder_lt_one N 2 le_rfl⟩
  simpa [Nat.card_Icc, show N + 1 - 2 = N - 1 by omega] using hs

lemma scaled_partial_decomposition (N : ℕ) :
    (N.factorial : ℝ) * (∑ k ∈ Finset.Icc 2 N, 1 / (d k : ℝ)) = (I N : ℝ) + R N := by
  rw [Finset.mul_sum]
  simp only [mul_one_div, I, R, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact div_decomposition N.factorial (d k) (d_pos k (Finset.mem_Icc.mp hk).1)

/-- Multinomial integrality, including arbitrary leftover factorial factors. -/
lemma factorial_pow_dvd_factorial_mul (k m : ℕ) : k.factorial ^ m ∣ (m * k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (mul_dvd_mul ih (dvd_refl k.factorial)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add (m * k) k)

lemma factorial_pow_dvd_of_mul_le (N k m : ℕ) (h : m * k ≤ N) :
    k.factorial ^ m ∣ N.factorial :=
  (factorial_pow_dvd_factorial_mul k m).trans (Nat.factorial_dvd_factorial h)

lemma block_power_dvd (N k : ℕ) : k.factorial ^ (N / k) ∣ N.factorial :=
  factorial_pow_dvd_of_mul_le N k (N / k) (Nat.div_mul_le_self N k)

def blockQuotient (N k : ℕ) : ℕ := N.factorial / k.factorial ^ (N / k)

def geomSum (a m : ℕ) : ℕ := ∑ j ∈ Finset.range m, a ^ j

def residualCarry (N k : ℕ) : ℕ := blockQuotient N k / d k

def H (N : ℕ) : ℕ := ∑ k ∈ Finset.Icc 2 N, residualCarry N k

lemma pow_eq_pred_mul_geom (a m : ℕ) (ha : 1 ≤ a) :
    a ^ m = (a - 1) * geomSum a m + 1 := by
  induction m with
  | zero => simp [geomSum]
  | succ m ih =>
    have he : a - 1 + 1 = a := Nat.sub_add_cancel ha
    simp only [geomSum, Finset.sum_range_succ] at *
    rw [pow_succ]
    calc
      a ^ m * a = a ^ m * ((a - 1) + 1) := congrArg (a ^ m * ·) he.symm
      _ = (a - 1) * a ^ m + a ^ m := by ring
      _ = (a - 1) * a ^ m + ((a - 1) * ∑ j ∈ Finset.range m, a ^ j) + 1 := by
        omega
      _ = (a - 1) * (∑ j ∈ Finset.range m, a ^ j + a ^ m) + 1 := by ring

lemma block_decomposition (N k : ℕ) :
    N.factorial = d k * (blockQuotient N k * geomSum k.factorial (N / k)) + blockQuotient N k := by
  have hF : N.factorial = k.factorial ^ (N / k) * blockQuotient N k := by
    exact (Nat.mul_div_cancel' (block_power_dvd N k)).symm
  calc
    N.factorial = k.factorial ^ (N / k) * blockQuotient N k := hF
    _ = d k * (blockQuotient N k * geomSum k.factorial (N / k)) + blockQuotient N k := by
      rw [pow_eq_pred_mul_geom _ _ (Nat.succ_le_of_lt (Nat.factorial_pos k))]
      unfold d
      ring

lemma floorTerm_geometric (N k : ℕ) (hk : 2 ≤ k) :
    floorTerm N k = blockQuotient N k * geomSum k.factorial (N / k) + residualCarry N k := by
  unfold floorTerm
  rw [block_decomposition N k, Nat.mul_add_div (d_pos k hk)]
  rfl

/-- The original huge dividend may be replaced by the multinomial block quotient. -/
lemma rho_reduction (N k : ℕ) : rho N k = blockQuotient N k % d k := by
  unfold rho
  rw [block_decomposition N k]
  simp [Nat.add_mod]

lemma blockQuotient_cast (N k : ℕ) :
    (blockQuotient N k : ℝ) = (N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k) := by
  simpa [blockQuotient] using (Nat.cast_div_charZero (K := ℝ) (block_power_dvd N k))

lemma remainder_le_geometric (N k : ℕ) (hk : 2 ≤ k) :
    (rho N k : ℝ) / (d k : ℝ) ≤
      2 * (N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k + 1) := by
  have hd : (0 : ℝ) < d k := by exact_mod_cast d_pos k hk
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hf2 : (2 : ℝ) ≤ k.factorial := by exact_mod_cast factorial_ge_two k hk
  have hQ : (0 : ℝ) ≤ blockQuotient N k := Nat.cast_nonneg _
  have hr : (rho N k : ℝ) ≤ blockQuotient N k := by
    rw [rho_reduction]
    exact_mod_cast Nat.mod_le (blockQuotient N k) (d k)
  calc
    (rho N k : ℝ) / (d k : ℝ) ≤ (blockQuotient N k : ℝ) / (d k : ℝ) :=
      div_le_div_of_nonneg_right hr hd.le
    _ ≤ 2 * (blockQuotient N k : ℝ) / (k.factorial : ℝ) := by
      apply (div_le_div_iff₀ hd hf).mpr
      rw [d_cast]
      nlinarith
    _ = 2 * (N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k + 1) := by
      rw [blockQuotient_cast, pow_succ]
      field_simp

lemma fract_le_min (N k : ℕ) (hk : 2 ≤ k) :
    Int.fract ((N.factorial : ℝ) / (d k : ℝ)) ≤
      min 1 (2 * (N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k + 1)) := by
  rw [fract_eq_remainder]
  exact le_min (remainder_lt_one N k hk).le (remainder_le_geometric N k hk)

lemma R_le_sum_min (N : ℕ) :
    R N ≤ ∑ k ∈ Finset.Icc 2 N,
      min 1 (2 * (N.factorial : ℝ) / (k.factorial : ℝ) ^ (N / k + 1)) := by
  apply Finset.sum_le_sum
  intro k hk
  rw [← fract_eq_remainder]
  exact fract_le_min N k (Finset.mem_Icc.mp hk).1

lemma residualCarry_eq_zero (N k : ℕ) (h : blockQuotient N k < d k) :
    residualCarry N k = 0 := Nat.div_eq_of_lt h

/-- A strict block inequality leaves a full factor of the index in the quotient. -/
lemma index_dvd_blockQuotient (N k : ℕ) (hN : 0 < N) (hm : N / k * k < N) :
    N ∣ blockQuotient N k := by
  have hd : k.factorial ^ (N / k) ∣ (N - 1).factorial :=
    factorial_pow_dvd_of_mul_le (N - 1) k (N / k) (by omega)
  have hpred : N - 1 + 1 = N := by omega
  have hfac : N.factorial = N * (N - 1).factorial := by
    nth_rw 1 [← hpred]
    rw [Nat.factorial_succ, hpred]
  rw [blockQuotient, hfac, Nat.mul_div_assoc N hd]
  exact dvd_mul_right N _

lemma floorTerm_mod_eq_residualCarry_mod (N k : ℕ) (hN : 0 < N) (hk : 2 ≤ k)
    (hm : N / k * k < N) : floorTerm N k % N = residualCarry N k % N := by
  rw [floorTerm_geometric N k hk, Nat.add_mod]
  have hd : N ∣ blockQuotient N k * geomSum k.factorial (N / k) :=
    dvd_mul_of_dvd_left (index_dvd_blockQuotient N k hN hm) _
  simp [Nat.mod_eq_zero_of_dvd hd]

lemma prime_strict_block (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) (hkp : k < p) :
    p / k * k < p := by
  have hle := Nat.div_mul_le_self p k
  by_contra h
  have he : p / k * k = p := by omega
  have hd : k ∣ p := ⟨p / k, by simpa [Nat.mul_comm] using he.symm⟩
  rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega

lemma floorTerm_self_geometric (N : ℕ) (hN : 2 ≤ N) :
    floorTerm N N = 1 + residualCarry N N := by
  rw [floorTerm_geometric N N hN]
  simp [blockQuotient, geomSum, Nat.div_self (by omega : 0 < N),
    Nat.div_self (Nat.factorial_pos N)]

/-- At primes, every geometric integer term except the endpoint vanishes modulo p.
The correction H is retained; dropping it would be false already at p=5. -/
theorem prime_residue_formula (p : ℕ) (hp : Nat.Prime p) :
    I p % p = (1 + H p) % p := by
  have hs : Nat.ModEq p (I p)
      (∑ k ∈ Finset.Icc 2 p, (residualCarry p k + if k = p then 1 else 0)) := by
    apply Nat.ModEq.sum
    intro k hk
    obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hk
    by_cases he : k = p
    · subst k
      simp [Nat.ModEq, floorTerm_self_geometric p hp.two_le, add_comm]
    · have hm := prime_strict_block p k hp hk2 (by omega)
      simpa [he] using floorTerm_mod_eq_residualCarry_mod p k hp.pos hk2 hm
  have hmem : p ∈ Finset.Icc 2 p := Finset.mem_Icc.mpr ⟨hp.two_le, le_rfl⟩
  simpa [Nat.ModEq, H, Finset.sum_add_distrib, hmem, add_comm] using hs

/-- Exact agreement with the independently proved analytic foundations. -/
lemma fresh_scaledPartial_decomposition (n : ℕ) :
    FreshFactorialAttack.scaledPartial n = (I (n + 1) : ℝ) + R (n + 1) := by
  rw [← scaled_partial_decomposition]
  unfold FreshFactorialAttack.scaledPartial
  congr 1
  symm
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [show n + 1 + 1 - 2 = n by omega]
  unfold FreshFactorialAttack.partialSum
  apply Finset.sum_congr rfl
  intro k _hk
  rw [d_cast]
  simp [FreshFactorialAttack.term, Nat.add_comm]

/-- The scaled analytic tail, distinct from the fractional remainder sum R. -/
noncomputable def scaledTail (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * FreshFactorialAttack.tail (N - 1)

lemma scaledTail_pos (N : ℕ) : 0 < scaledTail N := by
  exact mul_pos (by exact_mod_cast Nat.factorial_pos N) (FreshFactorialAttack.tail_pos _)

lemma scaledTail_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / (n + 2 : ℝ) < scaledTail (n + 1) ∧ scaledTail (n + 1) < 1 / (n + 1 : ℝ) := by
  simpa [scaledTail] using
    And.intro (FreshFactorialAttack.scaled_tail_lower n) (FreshFactorialAttack.scaled_tail_upper n hn)

lemma scaled_series_decomposition (n : ℕ) :
    ((n + 1).factorial : ℝ) * FreshFactorialAttack.series =
      (I (n + 1) : ℝ) + R (n + 1) + scaledTail (n + 1) := by
  rw [FreshFactorialAttack.series_eq_partialSum_add_tail n, mul_add]
  rw [← FreshFactorialAttack.scaledPartial, fresh_scaledPartial_decomposition]
  simp [scaledTail]

/-- The exact terminal-deficit identity. It uses divisibility by the index, not
just integrality after multiplying the series by the current factorial. -/
lemma residue_identity_of_scaled_integer (n : ℕ) (hn : 2 ≤ n) (z : ℤ)
    (hz : (n.factorial : ℝ) * FreshFactorialAttack.series = z) :
    ((I (n + 1) % (n + 1) : ℕ) : ℝ) + R (n + 1) + scaledTail (n + 1) = n + 1 := by
  let t : ℤ := z - (I (n + 1) / (n + 1) : ℕ)
  have ht : (t : ℝ) = (z : ℝ) - (I (n + 1) / (n + 1) : ℕ) := by
    simp only [t, Int.cast_sub, Int.cast_natCast]
  have hfac : ((n + 1).factorial : ℝ) * FreshFactorialAttack.series =
      (n + 1 : ℝ) * (z : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_assoc, hz]
  have hsum := scaled_series_decomposition n
  have hdiv : (I (n + 1) : ℝ) = ((I (n + 1) % (n + 1) : ℕ) : ℝ) +
      (n + 1 : ℝ) * (I (n + 1) / (n + 1) : ℕ) := by
    exact_mod_cast (Nat.mod_add_div (I (n + 1)) (n + 1)).symm
  have heq : ((I (n + 1) % (n + 1) : ℕ) : ℝ) + R (n + 1) + scaledTail (n + 1) =
      (n + 1 : ℝ) * (t : ℝ) := by
    nlinarith [hfac, hsum, hdiv, ht]
  have hR0 := R_nonneg (n + 1)
  have hR : R (n + 1) < (n : ℝ) := by
    simpa using R_lt_card (n + 1) (by omega)
  have hi0 : (0 : ℝ) ≤ ((I (n + 1) % (n + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hi : ((I (n + 1) % (n + 1) : ℕ) : ℝ) < n + 1 := by
    exact_mod_cast Nat.mod_lt (I (n + 1)) (by omega : 0 < n + 1)
  have hT0 := scaledTail_pos (n + 1)
  have hT : scaledTail (n + 1) < 1 := by
    apply (scaledTail_bounds n hn).2.trans_le
    apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have ht0 : (0 : ℝ) < (t : ℝ) := by nlinarith [heq, hR0, hi0, hT0]
  have ht2 : (t : ℝ) < 2 := by nlinarith [heq, hR, hi, hT]
  have ht0' : 0 < t := by exact_mod_cast ht0
  have ht2' : t < 2 := by exact_mod_cast ht2
  have ht1 : t = 1 := by omega
  simpa [ht1] using heq

lemma rational_residue_identity (q : ℚ) (hq : FreshFactorialAttack.series = (q : ℝ))
    (n : ℕ) (hn : 2 ≤ n) (hden : q.den ≤ n) :
    ((I (n + 1) % (n + 1) : ℕ) : ℝ) + R (n + 1) + scaledTail (n + 1) = n + 1 := by
  have hpred : n - 1 + 1 = n := by omega
  obtain ⟨z, hz⟩ := FreshFactorialAttack.rational_scaled_is_integer q (n - 1) (by omega)
  apply residue_identity_of_scaled_integer n hn z
  rw [hq]
  simpa [hpred] using hz

/-- A finite arithmetic window forced by rationality, without any asymptotic assumption. -/
theorem rational_residue_window (q : ℚ) (hq : FreshFactorialAttack.series = (q : ℝ))
    (n : ℕ) (hn : 2 ≤ n) (hden : q.den ≤ n) :
    (n + 1 : ℝ) - R (n + 1) - 1 / (n + 1 : ℝ) < ((I (n + 1) % (n + 1) : ℕ) : ℝ) ∧
    ((I (n + 1) % (n + 1) : ℕ) : ℝ) < (n + 1 : ℝ) - R (n + 1) - 1 / (n + 2 : ℝ) := by
  have hi := rational_residue_identity q hq n hn hden
  have hb := scaledTail_bounds n hn
  constructor <;> linarith [hb.1, hb.2]

lemma normalized_scaledTail_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => scaledTail (n + 1) / (n + 1 : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ => 1 / (n + 1 : ℝ))
  · filter_upwards [] with n
    exact div_nonneg (scaledTail_pos (n + 1)).le (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (scaledTail_bounds n hn).2.le.trans
    apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The analytic-to-arithmetic implication, with the sublinear estimate exposed
as a hypothesis. The report proves that estimate on paper by an interval count. -/
theorem rational_implies_terminal_limit
    (hR : Filter.Tendsto (fun n : ℕ => R (n + 1) / (n + 1 : ℝ)) Filter.atTop (nhds 0))
    (hr : ¬ Irrational FreshFactorialAttack.series) :
    Filter.Tendsto (fun n : ℕ => ((I (n + 1) % (n + 1) : ℕ) : ℝ) / (n + 1 : ℝ))
      Filter.atTop (nhds 1) := by
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hr
  have heq : (fun n : ℕ => 1 - (R (n + 1) / (n + 1 : ℝ) +
      scaledTail (n + 1) / (n + 1 : ℝ))) =ᶠ[Filter.atTop]
      (fun n : ℕ => ((I (n + 1) % (n + 1) : ℕ) : ℝ) / (n + 1 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 q.den)] with n hn
    have hi := rational_residue_identity q hq n (by omega) (by omega)
    have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
    apply (eq_div_iff hn0).mpr
    field_simp
    linarith
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub (hR.add normalized_scaledTail_tendsto_zero)
  exact Filter.Tendsto.congr' heq (by simpa using hh)

/-- A genuine conditional reduction. The nonterminal-subsequence hypothesis is
NOT proved here; merely being different from N-1 would not suffice. -/
theorem irrational_of_uniformly_nonterminal_subsequence
    (hR : Filter.Tendsto (fun n : ℕ => R (n + 1) / (n + 1 : ℝ)) Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ M : ℕ, ∃ n ≥ M,
      ((I (n + 1) % (n + 1) : ℕ) : ℝ) / (n + 1 : ℝ) ≤ 1 - ε) :
    Irrational FreshFactorialAttack.series := by
  by_contra hr
  have ht := rational_implies_terminal_limit hR hr
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp ht ε hε
  obtain ⟨n, hn, hb⟩ := hbad M
  have h := hM n hn
  rw [Real.dist_eq, abs_lt] at h
  linarith [h.1]

/-- Small exact checks refuting omitted-correction and uniform-special-index shortcuts. -/
lemma prime_five_correction : I 5 = 150 ∧ I 5 % 5 = 0 ∧ H 5 % 5 = 4 := by
  decide +kernel

lemma prime_97_near_terminal : Nat.Prime 97 ∧ I 97 % 97 = 94 := by
  decide +kernel

lemma power_two_terminal : I 128 % 128 = 127 := by
  decide +kernel

lemma power_two_zero : I 64 % 64 = 0 := by
  decide +kernel

end FloorArithmetic
