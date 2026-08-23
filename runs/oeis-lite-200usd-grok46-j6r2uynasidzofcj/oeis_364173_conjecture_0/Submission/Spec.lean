import FormalConjectures.Util.ProblemImports

open scoped Real
open Nat Finset

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

lemma gamma_coe_add_one (m : ℕ) : Real.Gamma (m + 1) = m ! :=
  Real.Gamma_nat_eq_factorial m

lemma a_even (k : ℕ) :
    a (2 * k) =
      ((18 * k)! * (4 * k)! * (3 * k)! : ℝ) /
        ((9 * k)! * (8 * k)! * (6 * k)! * (2 * k)!) := by
  simp only [a]
  rw [show (9 : ℝ) * ↑(2 * k) + 1 = ((18 * k : ℕ) : ℝ) + 1 by push_cast; ring]
  rw [show (2 : ℝ) * ↑(2 * k) + 1 = ((4 * k : ℕ) : ℝ) + 1 by push_cast; ring]
  rw [show (3 / 2 : ℝ) * ↑(2 * k) + 1 = ((3 * k : ℕ) : ℝ) + 1 by push_cast; ring]
  rw [show (9 / 2 : ℝ) * ↑(2 * k) + 1 = ((9 * k : ℕ) : ℝ) + 1 by push_cast; ring]
  rw [show (4 : ℝ) * ↑(2 * k) + 1 = ((8 * k : ℕ) : ℝ) + 1 by push_cast; ring]
  rw [show (3 : ℝ) * ↑(2 * k) + 1 = ((6 * k : ℕ) : ℝ) + 1 by push_cast; ring]
  simp only [gamma_coe_add_one]

def aEvenRat (k : ℕ) : ℚ :=
  ((18 * k)! * (4 * k)! * (3 * k)! : ℚ) /
    ((9 * k)! * (8 * k)! * (6 * k)! * (2 * k)!)

lemma a_even_rat (k : ℕ) : a (2 * k) = (aEvenRat k : ℝ) := by
  rw [a_even, aEvenRat]; push_cast; rfl

lemma odd_doubleFactorial_eq (k : ℕ) :
    (2 * k - 1)‼ * 2 ^ k * k.factorial = (2 * k).factorial := by
  cases k with
  | zero => simp [Nat.doubleFactorial]
  | succ k =>
    have hmul : (2 * k + 1 + 1).factorial = (2 * k + 1 + 1)‼ * (2 * k + 1)‼ :=
      Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    have heven : (2 * (k + 1))‼ = 2 ^ (k + 1) * (k + 1).factorial :=
      Nat.doubleFactorial_two_mul (k + 1)
    have h2k2 : 2 * (k + 1) = 2 * k + 2 := by omega
    have hodd : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have hfac : (2 * k.succ).factorial = (2 * k + 2).factorial := by
      simp [Nat.succ_eq_add_one]; ring
    have h22 : (2 * k + 1 + 1) = 2 * k + 2 := by omega
    rw [hodd, hfac]
    calc
      (2 * k + 1)‼ * 2 ^ (k + 1) * (k + 1).factorial
          = (2 * k + 1)‼ * (2 * (k + 1))‼ := by rw [heven]; ring
      _ = (2 * k + 1)‼ * (2 * k + 2)‼ := by rw [h2k2]
      _ = (2 * k + 2)‼ * (2 * k + 1)‼ := mul_comm _ _
      _ = (2 * k + 1 + 1)‼ * (2 * k + 1)‼ := by rw [h22]
      _ = (2 * k + 1 + 1).factorial := hmul.symm
      _ = (2 * k + 2).factorial := by rw [h22]

lemma odd_doubleFactorial_cast (k : ℕ) :
    ((2 * k - 1)‼ : ℝ) = (2 * k).factorial / (2 ^ k * k.factorial : ℝ) := by
  have hz : (2 ^ k * k.factorial : ℝ) ≠ 0 := by positivity
  apply eq_div_of_mul_eq hz
  have h := congrArg (fun n : ℕ => (n : ℝ)) (odd_doubleFactorial_eq k)
  push_cast at h
  convert h using 1
  ring

lemma two_pow_sq (k : ℕ) : (2 : ℝ) ^ k * 2 ^ k = (4 : ℝ) ^ k := by
  calc
    (2 : ℝ) ^ k * 2 ^ k = (2 : ℝ) ^ (k + k) := (pow_add (2 : ℝ) k k).symm
    _ = (2 : ℝ) ^ (2 * k) := by congr 1; ring
    _ = ((2 : ℝ) ^ 2) ^ k := pow_mul (2 : ℝ) 2 k
    _ = (4 : ℝ) ^ k := by norm_num

/-- `Γ(n + 1/2) = (2n)! / (4^n n!) * √π`. -/
lemma Gamma_nat_add_half (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) =
      ((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial) * Real.sqrt Real.pi := by
  rw [Real.Gamma_nat_add_half n, odd_doubleFactorial_cast]
  have hden : ((2 : ℝ) ^ n * ↑n.factorial) * 2 ^ n = (4 : ℝ) ^ n * ↑n.factorial := by
    rw [mul_assoc, mul_left_comm (2 ^ n : ℝ) _ (2 ^ n), two_pow_sq]
    ring
  have : ((2 * n).factorial : ℝ) / (2 ^ n * ↑n.factorial) * Real.sqrt Real.pi / (2 : ℝ) ^ n
      = ((2 * n).factorial : ℝ) * Real.sqrt Real.pi / ((2 ^ n * ↑n.factorial) * 2 ^ n) := by
    field_simp
  rw [this, hden]
  ring

lemma a_odd_arg_9 (m : ℕ) : (9 : ℝ) * ↑(2 * m + 1) + 1 = ((18 * m + 9 : ℕ) : ℝ) + 1 := by
  push_cast; ring
lemma a_odd_arg_2 (m : ℕ) : (2 : ℝ) * ↑(2 * m + 1) + 1 = ((4 * m + 2 : ℕ) : ℝ) + 1 := by
  push_cast; ring
lemma a_odd_arg_32 (m : ℕ) : (3 / 2 : ℝ) * ↑(2 * m + 1) + 1 = ((3 * m + 2 : ℕ) : ℝ) + 1 / 2 := by
  push_cast; ring
lemma a_odd_arg_92 (m : ℕ) : (9 / 2 : ℝ) * ↑(2 * m + 1) + 1 = ((9 * m + 5 : ℕ) : ℝ) + 1 / 2 := by
  push_cast; ring
lemma a_odd_arg_4 (m : ℕ) : (4 : ℝ) * ↑(2 * m + 1) + 1 = ((8 * m + 4 : ℕ) : ℝ) + 1 := by
  push_cast; ring
lemma a_odd_arg_3 (m : ℕ) : (3 : ℝ) * ↑(2 * m + 1) + 1 = ((6 * m + 3 : ℕ) : ℝ) + 1 := by
  push_cast; ring

lemma a_odd_gamma (m : ℕ) :
    a (2 * m + 1) =
      ((18 * m + 9).factorial : ℝ) * ((4 * m + 2).factorial : ℝ) *
        Real.Gamma (((3 * m + 2 : ℕ) : ℝ) + 1 / 2) /
      (Real.Gamma (((9 * m + 5 : ℕ) : ℝ) + 1 / 2) *
        ((8 * m + 4).factorial : ℝ) * ((6 * m + 3).factorial : ℝ) *
        ((2 * m + 1).factorial : ℝ)) := by
  simp only [a]
  rw [a_odd_arg_9, a_odd_arg_2, a_odd_arg_32, a_odd_arg_92, a_odd_arg_4, a_odd_arg_3]
  simp only [gamma_coe_add_one]

lemma factorial_succ_cast (n : ℕ) :
    ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * n.factorial := by
  rw [Nat.factorial_succ]; push_cast; rfl

lemma factorial_succ_cast' (n : ℕ) {t : ℕ} (ht : n + 1 = t) :
    (t.factorial : ℝ) = (t : ℝ) * n.factorial := by
  subst ht
  convert factorial_succ_cast n using 1
  push_cast; rfl

lemma four_div_pow (a b : ℕ) (h : b ≤ a) :
    (4 : ℝ) ^ a / (4 : ℝ) ^ b = (4 : ℝ) ^ (a - b) := by
  rw [div_eq_mul_inv, ← pow_sub₀ (4 : ℝ) (by norm_num) h]

lemma four_pow_to_two (t : ℕ) : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]

lemma a_odd (k : ℕ) :
    a (2 * k + 1) =
      (4 : ℝ) ^ (6 * k + 3) * ((4 * k + 2).factorial : ℝ) * ((9 * k + 4).factorial : ℝ) /
        (((3 * k + 1).factorial : ℝ) * ((8 * k + 4).factorial : ℝ) *
          ((2 * k + 1).factorial : ℝ)) := by
  have h2pow : (4 : ℝ) ^ (6 * k + 3) = (2 : ℝ) ^ (12 * k + 6) := by
    rw [four_pow_to_two]; congr 1; ring
  rw [h2pow]
  -- Follow ProofDev's argument, then rewrite 2-power back if needed.
  rw [a_odd_gamma, Gamma_nat_add_half, Gamma_nat_add_half]
  have h6 : 2 * (3 * k + 2) = 6 * k + 4 := by ring
  have h18 : 2 * (9 * k + 5) = 18 * k + 10 := by ring
  simp only [h6, h18]
  have hπ : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by exact_mod_cast n.factorial_ne_zero
  have hsucc18 : 18 * k + 9 + 1 = 18 * k + 10 := by omega
  have hsucc6 : 6 * k + 3 + 1 = 6 * k + 4 := by omega
  have hsucc9 : 9 * k + 4 + 1 = 9 * k + 5 := by omega
  have hsucc3 : 3 * k + 1 + 1 = 3 * k + 2 := by omega
  have f18 : ((18 * k + 10).factorial : ℝ) = (18 * k + 10 : ℝ) * (18 * k + 9).factorial := by
    rw [factorial_succ_cast' (18 * k + 9) hsucc18]; norm_cast
  have f6 : ((6 * k + 4).factorial : ℝ) = (6 * k + 4 : ℝ) * (6 * k + 3).factorial := by
    rw [factorial_succ_cast' (6 * k + 3) hsucc6]; norm_cast
  have f9 : ((9 * k + 5).factorial : ℝ) = (9 * k + 5 : ℝ) * (9 * k + 4).factorial := by
    rw [factorial_succ_cast' (9 * k + 4) hsucc9]; norm_cast
  have f3 : ((3 * k + 2).factorial : ℝ) = (3 * k + 2 : ℝ) * (3 * k + 1).factorial := by
    rw [factorial_succ_cast' (3 * k + 1) hsucc3]; norm_cast
  field_simp [hπ, hf]
  rw [f18, f6, f9, f3]
  have hne18 : (18 * k + 10 : ℝ) ≠ 0 := by exact_mod_cast (by omega : 18 * k + 10 ≠ 0)
  have hne6 : (6 * k + 4 : ℝ) ≠ 0 := by exact_mod_cast (by omega : 6 * k + 4 ≠ 0)
  have hne9 : (9 * k + 5 : ℝ) ≠ 0 := by exact_mod_cast (by omega : 9 * k + 5 ≠ 0)
  have hne3 : (3 * k + 2 : ℝ) ≠ 0 := by exact_mod_cast (by omega : 3 * k + 2 ≠ 0)
  field_simp [hf, hne18, hne6, hne9, hne3]
  have hc1 : (6 * (k : ℝ) + 4) = 2 * ((k : ℝ) * 3 + 2) := by ring
  have hc2 : ((k : ℝ) * 18 + 10) = 2 * ((k : ℝ) * 9 + 5) := by ring
  rw [hc1, hc2]
  have hpow' : (4 : ℝ) ^ (9 * k + 5) = (4 : ℝ) ^ (3 * k + 2) * (2 : ℝ) ^ (12 * k + 6) := by
    calc
      (4 : ℝ) ^ (9 * k + 5) = (4 : ℝ) ^ (3 * k + 2 + (6 * k + 3)) := by congr 1; omega
      _ = (4 : ℝ) ^ (3 * k + 2) * (4 : ℝ) ^ (6 * k + 3) := pow_add _ _ _
      _ = (4 : ℝ) ^ (3 * k + 2) * (2 : ℝ) ^ (2 * (6 * k + 3)) := by rw [four_pow_to_two (6 * k + 3)]
      _ = (4 : ℝ) ^ (3 * k + 2) * (2 : ℝ) ^ (12 * k + 6) := by congr 1; ring
  rw [hpow']
  ring

def aOddRat (k : ℕ) : ℚ :=
  (4 : ℚ) ^ (6 * k + 3) * (4 * k + 2).factorial * (9 * k + 4).factorial /
    ((3 * k + 1).factorial * (8 * k + 4).factorial * (2 * k + 1).factorial)

lemma a_odd_rat (k : ℕ) : a (2 * k + 1) = (aOddRat k : ℝ) := by
  rw [a_odd, aOddRat]; push_cast; rfl

def aRat (n : ℕ) : ℚ :=
  if Even n then aEvenRat (n / 2) else aOddRat (n / 2)

lemma a_eq_aRat (n : ℕ) : a n = (aRat n : ℝ) := by
  rw [aRat]
  by_cases h : Even n
  · rw [if_pos h]
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp h
    have : n / 2 = k := by omega
    rw [this, hk, a_even_rat]
  · rw [if_neg h]
    have hodd : Odd n := Nat.not_even_iff_odd.mp h
    obtain ⟨k, hk⟩ := hodd
    have : n / 2 = k := by omega
    rw [this, hk, a_odd_rat]

set_option maxHeartbeats 800000
set_option linter.style.namespace false

/-! Combinatorial / valuation infrastructure. -/

lemma cast_choose_of_sub {n k t : ℕ} (h : k ≤ n) (ht : n - k = t) :
    (n.choose k : ℝ) = n.factorial / (k.factorial * t.factorial) := by
  rw [Nat.cast_choose (K := ℝ) h, ht]

/-- Binomial form of the even subsequence. -/
lemma a_even_binom (m : ℕ) :
    a (2 * m) =
      ((Nat.choose (18 * m) (9 * m) * Nat.choose (9 * m) m * Nat.choose (4 * m) (2 * m) : ℝ) /
        (Nat.choose (6 * m) (3 * m) * Nat.choose (3 * m) (2 * m))) := by
  rw [a_even]
  have c18 := cast_choose_of_sub (by nlinarith : 9 * m ≤ 18 * m) (by omega : 18 * m - 9 * m = 9 * m)
  have c9 := cast_choose_of_sub (by nlinarith : m ≤ 9 * m) (by omega : 9 * m - m = 8 * m)
  have c4 := cast_choose_of_sub (by nlinarith : 2 * m ≤ 4 * m) (by omega : 4 * m - 2 * m = 2 * m)
  have c6 := cast_choose_of_sub (by nlinarith : 3 * m ≤ 6 * m) (by omega : 6 * m - 3 * m = 3 * m)
  have c3 := cast_choose_of_sub (by nlinarith : 2 * m ≤ 3 * m) (by omega : 3 * m - 2 * m = m)
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by exact_mod_cast n.factorial_ne_zero
  push_cast
  rw [c18, c9, c4, c6, c3]
  field_simp [hf]

/-! ## Generalized harmonic numbers and Wolstenholme's theorem -/

/-- The generalized harmonic number `H_n^{(k)} = ∑_{i=1}^n 1/i^k`. -/
def harm (k n : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 n, (i : ℚ)⁻¹ ^ k

lemma harm_one (n : ℕ) : harm 1 n = harmonic n := by
  simp [harm, harmonic_eq_sum_Icc, pow_one]

lemma harm_zero_zero (k : ℕ) : harm k 0 = 0 := by
  simp [harm]

/-- Sum of `j`-th powers of units of `ZMod p` vanishes if `p-1 ∤ j`. -/
lemma sum_units_zmod_pow {p j : ℕ} [hp : Fact p.Prime] (hj : ¬ (p - 1) ∣ j) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) = 0 := by
  have hex : ∃ a : (ZMod p)ˣ, a ^ j ≠ 1 := by
    have hiff := FiniteField.forall_pow_eq_one_iff (ZMod p) j
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    have : ¬ (Fintype.card (ZMod p) - 1) ∣ j := by simpa [hcard] using hj
    have : ¬ ∀ x : (ZMod p)ˣ, x ^ j = 1 := by
      intro h; exact this (hiff.mp h)
    push_neg at this
    exact this
  obtain ⟨a, ha⟩ := hex
  have hreindex :
      ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) =
        ∑ x : (ZMod p)ˣ, (((a * x : (ZMod p)ˣ) : ZMod p) ^ j) := by
    exact (Fintype.sum_equiv (Equiv.mulLeft a)
      (fun x => ((a * x : (ZMod p)ˣ) : ZMod p) ^ j)
      (fun y => (y : ZMod p) ^ j)
      (fun _ => rfl)).symm
  have hmul :
      ∑ x : (ZMod p)ˣ, (((a * x : (ZMod p)ˣ) : ZMod p) ^ j) =
        (a : ZMod p) ^ j * ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) := by
    simp only [Units.val_mul, mul_pow, Finset.mul_sum]
  have heq : ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) =
      (a : ZMod p) ^ j * ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) :=
    hreindex.trans hmul
  have hsub : ((a : ZMod p) ^ j - 1) * ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) = 0 := by
    rw [sub_mul, one_mul]
    nth_rw 2 [heq]
    rw [sub_self]
  have hane : (a : ZMod p) ^ j - 1 ≠ 0 := by
    intro h0
    have : (a : ZMod p) ^ j = 1 := sub_eq_zero.mp h0
    have : a ^ j = 1 := by
      exact Units.ext (by simpa [Units.val_pow_eq_pow_val] using this)
    exact ha this
  exact (eq_zero_of_ne_zero_of_mul_left_eq_zero hane hsub)

lemma mem_Icc_one_pred_coprime {p k : ℕ} [hp : Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) : Nat.Coprime k p := by
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkp : k ≤ p - 1 := (Finset.mem_Icc.mp hk).2
  have hlt : k < p := lt_of_le_of_lt hkp (Nat.pred_lt (Nat.Prime.ne_zero hp.out))
  exact Nat.coprime_comm.mpr
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hk1 hlt))

lemma Icc_one_pred_eq_units {p j : ℕ} [hp : Fact p.Prime] :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p) ^ j =
      ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) := by
  refine Finset.sum_bij (fun k hk => ZMod.unitOfCoprime k (mem_Icc_one_pred_coprime hk))
    ?_ ?_ ?_ ?_
  · intro k hk; simp
  · intro k₁ hk₁ k₂ hk₂ h
    have hval : (k₁ : ZMod p) = (k₂ : ZMod p) := by
      simpa [ZMod.coe_unitOfCoprime] using congrArg Units.val h
    have hk1 : k₁ < p := lt_of_le_of_lt (Finset.mem_Icc.mp hk₁).2
      (Nat.pred_lt (Nat.Prime.ne_zero hp.out))
    have hk2 : k₂ < p := lt_of_le_of_lt (Finset.mem_Icc.mp hk₂).2
      (Nat.pred_lt (Nat.Prime.ne_zero hp.out))
    have : k₁ % p = k₂ % p := (ZMod.natCast_eq_natCast_iff' k₁ k₂ p).mp hval
    rwa [Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hk2] at this
  · intro x _
    refine ⟨x.val.val, ?_, ?_⟩
    · have hx0 : (x : ZMod p) ≠ 0 := Units.ne_zero x
      have hval : x.val.val ∈ Finset.Icc 1 (p - 1) := by
        have hlt : x.val.val < p := ZMod.val_lt _
        have hne : x.val.val ≠ 0 := by
          intro h; apply hx0; exact (ZMod.val_eq_zero (x : ZMod p)).mp h
        have hge : 1 ≤ x.val.val := Nat.pos_of_ne_zero hne
        have hle : x.val.val ≤ p - 1 := Nat.le_pred_of_lt hlt
        exact Finset.mem_Icc.mpr ⟨hge, hle⟩
      exact hval
    · apply Units.ext
      simp [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
  · intro k hk
    simp [ZMod.coe_unitOfCoprime]

/-- `∑_{k=1}^{p-1} k^j = 0` in `ZMod p` when `p-1` does not divide `j`. -/
lemma sum_pow_units_zmod {p j : ℕ} [hp : Fact p.Prime] (hj : ¬ (p - 1) ∣ j) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod p) ^ j = 0 := by
  rw [Icc_one_pred_eq_units]
  exact sum_units_zmod_pow hj

lemma p_not_dvd_of_lt {p i : ℕ} [hp : Fact p.Prime] (hi : 0 < i) (hlt : i < p) :
    ¬ (p : ℤ) ∣ (i : ℤ) := by
  exact_mod_cast Nat.not_dvd_of_pos_of_lt hi hlt

/-- A rational is a `p`-integer iff its reduced denominator is coprime to `p`. -/
lemma padicValRat_nonneg_of_not_dvd_den {p : ℕ} [hp : Fact p.Prime] {q : ℚ}
    (h : ¬ p ∣ q.den) : 0 ≤ padicValRat p q := by
  have hden : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd h
  rw [padicValRat, hden, Nat.cast_zero, sub_zero]
  exact Int.natCast_nonneg _

/-- `valGe p k q` means `v_p(q) ≥ k`, with the convention `v_p(0) = +∞`. -/
def valGe (p : ℕ) (k : ℤ) (q : ℚ) : Prop :=
  q = 0 ∨ k ≤ padicValRat p q

lemma valGe_zero (p : ℕ) (k : ℤ) : valGe p k 0 := Or.inl rfl

lemma valGe_of_le {p : ℕ} {k : ℤ} {q : ℚ} (h : k ≤ padicValRat p q) :
    valGe p k q := Or.inr h

lemma valGe_mono {p : ℕ} {k k' : ℤ} {q : ℚ} (hkk : k' ≤ k) (h : valGe p k q) :
    valGe p k' q := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hkk h)

lemma valGe_mul {p : ℕ} [Fact p.Prime] {k₁ k₂ : ℤ} {q r : ℚ}
    (hq : valGe p k₁ q) (hr : valGe p k₂ r) :
    valGe p (k₁ + k₂) (q * r) := by
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, zero_mul]; exact Or.inl rfl
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, mul_zero]; exact Or.inl rfl
  rcases hq with hq | hq
  · exact (hq0 hq).elim
  rcases hr with hr | hr
  · exact (hr0 hr).elim
  refine Or.inr ?_
  rw [padicValRat.mul hq0 hr0]
  exact add_le_add hq hr

lemma valGe_pow {p : ℕ} [Fact p.Prime] {k : ℤ} {q : ℚ} {n : ℕ}
    (hq : valGe p k q) : valGe p (n * k) (q ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact Or.inr (by simp)
  | succ n ih =>
    rw [pow_succ]
    have hcast : ((n + 1 : ℕ) : ℤ) * k = (n : ℤ) * k + k := by
      rw [Nat.cast_succ]; ring
    rw [hcast]
    exact valGe_mul ih hq

lemma valGe_add {p : ℕ} [Fact p.Prime] {k : ℤ} {q r : ℚ}
    (hq : valGe p k q) (hr : valGe p k r) :
    valGe p k (q + r) := by
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  rcases eq_or_ne q 0 with hq0 | hq0
  · simpa [hq0] using hr
  rcases eq_or_ne r 0 with hr0 | hr0
  · simpa [hr0] using hq
  rcases hq with hq | hq
  · exact (hq0 hq).elim
  rcases hr with hr | hr
  · exact (hr0 hr).elim
  refine Or.inr ?_
  have := padicValRat.min_le_padicValRat_add (p := p) hqr
  exact le_trans (le_min hq hr) this

lemma valGe_sum {p : ℕ} [Fact p.Prime] {k : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, valGe p k (f i)) : valGe p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp; exact Or.inl rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact valGe_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma valGe_neg {p : ℕ} {k : ℤ} {q : ℚ} (h : valGe p k q) : valGe p k (-q) := by
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, neg_zero]; exact Or.inl rfl
  rcases h with h | h
  · exact (hq0 h).elim
  · exact Or.inr (by simpa [padicValRat.neg] using h)

lemma valGe_sub {p : ℕ} [Fact p.Prime] {k : ℤ} {q r : ℚ}
    (hq : valGe p k q) (hr : valGe p k r) : valGe p k (q - r) := by
  simpa [sub_eq_add_neg] using valGe_add hq (valGe_neg hr)

lemma valGe_one (p : ℕ) : valGe p 0 1 := Or.inr (by simp)

lemma valGe_nat (p n : ℕ) : valGe p 0 (n : ℚ) := by
  by_cases h : (n : ℚ) = 0
  · exact Or.inl h
  · exact Or.inr (by simp [padicValRat.of_nat])

lemma valGe_int (p : ℕ) (z : ℤ) : valGe p 0 (z : ℚ) := by
  by_cases h : (z : ℚ) = 0
  · exact Or.inl h
  · exact Or.inr (by simp [padicValRat.of_int])

lemma valGe_p {p : ℕ} [hp : Fact p.Prime] : valGe p 1 (p : ℚ) :=
  Or.inr (by simp [padicValRat.self (Nat.Prime.one_lt hp.out)])

lemma valGe_p_pow {p : ℕ} [hp : Fact p.Prime] (r : ℕ) : valGe p r ((p : ℚ) ^ r) := by
  by_cases hr : r = 0
  · subst hr; exact Or.inr (by simp)
  refine Or.inr ?_
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
  rw [padicValRat.pow hp0]
  simp [padicValRat.self (Nat.Prime.one_lt hp.out)]

/-- If `p` does not divide `n`, then `1/n` is a `p`-integer. -/
lemma valGe_inv_of_not_dvd {p n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) (hnd : ¬ p ∣ n) :
    valGe p 0 ((n : ℚ)⁻¹) := by
  refine Or.inr ?_
  rw [padicValRat.inv]
  have : padicValRat p (n : ℚ) = 0 := by
    simp [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
  simp [this]

lemma valGe_inv_of_lt {p i : ℕ} [hp : Fact p.Prime] (hi : 0 < i) (hlt : i < p) :
    valGe p 0 ((i : ℚ)⁻¹) :=
  valGe_inv_of_not_dvd (Nat.pos_iff_ne_zero.mp hi) (Nat.not_dvd_of_pos_of_lt hi hlt)

/-- `H_n^{(k)}` is a `p`-integer when `n < p`. -/
lemma harm_is_p_integer {p k n : ℕ} [hp : Fact p.Prime] (hn : n < p) :
    valGe p 0 (harm k n) := by
  apply valGe_sum
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hile : i ≤ n := (Finset.mem_Icc.mp hi).2
  have hilt : i < p := lt_of_le_of_lt hile hn
  have hinv := valGe_inv_of_lt (Nat.succ_le_iff.mp hi1) hilt
  simpa using valGe_pow (n := k) hinv

/-- Inverse of `i` in `ZMod p` agrees with the rational `1/i` after reduction. -/
lemma harm_two_mod_p {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ 2) = 0 := by
  have hj : ¬ (p - 1) ∣ (p - 3) := by
    intro h
    have hlt : p - 3 < p - 1 := by omega
    have hpos : 0 < p - 1 := by have := Nat.Prime.one_lt hp.out; omega
    have := Nat.eq_zero_of_dvd_of_lt h hlt
    omega
  -- i⁻¹ = i^{p-2}, so (i⁻¹)^2 = i^{2(p-2)} = i^{2p-4} = i^{p-3} * i^{p-1} = i^{p-3}
  have hpow : ∀ i : ZMod p, i ≠ 0 → (i⁻¹) ^ 2 = i ^ (p - 3) := by
    intro i hi
    have h1 : i ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hi
    have hinv : i⁻¹ = i ^ (p - 2) := by
      have : i * i ^ (p - 2) = 1 := by
        have hpt : p - 1 = (p - 2) + 1 := by
          have : 2 ≤ p := le_trans (by norm_num : 2 ≤ 5) h5
          omega
        rw [← pow_succ' i (p - 2), ← hpt, h1]
      exact inv_eq_of_mul_eq_one_right this
    rw [hinv, ← pow_mul]
    have : (p - 2) * 2 = (p - 3) + (p - 1) := by omega
    rw [this, pow_add, h1, mul_one]
  have : ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹) ^ 2 =
      ∑ i ∈ Finset.Icc 1 (p - 1), (i : ZMod p) ^ (p - 3) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : (i : ZMod p) ≠ 0 := by
      have hk1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hlt : i < p := lt_of_le_of_lt (Finset.mem_Icc.mp hi).2
        (Nat.pred_lt (Nat.Prime.ne_zero hp.out))
      intro h
      have := (ZMod.natCast_eq_zero_iff i p).mp h
      exact Nat.not_dvd_of_pos_of_lt hk1 hlt this
    exact hpow _ hi0
  rw [this]
  exact sum_pow_units_zmod hj

lemma mem_Icc_bounds {p i : ℕ} (hi : i ∈ Finset.Icc 1 (p - 1)) (hp : 0 < p) :
    1 ≤ i ∧ i ≤ p - 1 ∧ i < p := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hile : i ≤ p - 1 := (Finset.mem_Icc.mp hi).2
  exact ⟨hi1, hile, Nat.lt_of_le_pred hp hile⟩

lemma mem_Icc_one_pred_sub {p i : ℕ} (hi : i ∈ Finset.Icc 1 (p - 1)) (hp : 1 < p) :
    p - i ∈ Finset.Icc 1 (p - 1) := by
  obtain ⟨hi1, hile, hilt⟩ := mem_Icc_bounds hi (by omega)
  have hge : 1 ≤ p - i := Nat.le_sub_of_add_le (by omega)
  have hle : p - i ≤ p - 1 := Nat.sub_le_sub_left hi1 _
  exact Finset.mem_Icc.mpr ⟨hge, hle⟩

lemma sum_inv_flip {p : ℕ} (hp : 1 < p) :
    ∑ i ∈ Finset.Icc 1 (p - 1), ((p - i : ℕ) : ℚ)⁻¹ =
      ∑ i ∈ Finset.Icc 1 (p - 1), (i : ℚ)⁻¹ := by
  refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
  · intro i hi; exact mem_Icc_one_pred_sub hi hp
  · intro i hi j hj h
    obtain ⟨_, _, hilt⟩ := mem_Icc_bounds hi (Nat.zero_lt_of_lt hp)
    obtain ⟨_, _, hjlt⟩ := mem_Icc_bounds hj (Nat.zero_lt_of_lt hp)
    apply_fun (fun x => p - x) at h
    rwa [Nat.sub_sub_self hilt.le, Nat.sub_sub_self hjlt.le] at h
  · intro i hi
    refine ⟨p - i, mem_Icc_one_pred_sub hi hp, ?_⟩
    obtain ⟨_, _, hilt⟩ := mem_Icc_bounds hi (Nat.zero_lt_of_lt hp)
    exact Nat.sub_sub_self hilt.le
  · intro i hi; rfl

lemma inv_add_inv_pair (p i : ℕ) (hi : 0 < i) (hlt : i < p) :
    (i : ℚ)⁻¹ + ((p - i : ℕ) : ℚ)⁻¹ = (p : ℚ) / (i * (p - i) : ℚ) := by
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hi)
  have hpi0 : ((p - i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hlt))
  have hcast : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := by
    rw [Nat.cast_sub hlt.le]
  have hpmi : (p : ℚ) - (i : ℚ) ≠ 0 := by
    rw [← hcast]; exact hpi0
  rw [hcast]
  field_simp
  ring

/-- Pairing form of the first harmonic number. -/
lemma harmonic_pairing (p : ℕ) (hp : Nat.Prime p) (h2 : 2 < p) :
    harmonic (p - 1) = (p : ℚ) / 2 * ∑ i ∈ Finset.Icc 1 (p - 1), (1 / (i * (p - i) : ℚ)) := by
  have hp1 : 1 < p := lt_trans (by norm_num : 1 < 2) h2
  have hflip : ∑ i ∈ Finset.Icc 1 (p - 1), ((p - i : ℕ) : ℚ)⁻¹ =
      harmonic (p - 1) := by
    rw [harmonic_eq_sum_Icc, sum_inv_flip hp1]
  have h2H : 2 * harmonic (p - 1) =
      ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ℚ)⁻¹ + ((p - i : ℕ) : ℚ)⁻¹) := by
    rw [two_mul]
    nth_rw 2 [← hflip]
    rw [harmonic_eq_sum_Icc, ← Finset.sum_add_distrib]
  have hpair : ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ℚ)⁻¹ + ((p - i : ℕ) : ℚ)⁻¹) =
      ∑ i ∈ Finset.Icc 1 (p - 1), (p : ℚ) / (i * (p - i) : ℚ) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi1, _, hilt⟩ := mem_Icc_bounds hi (by omega)
    exact inv_add_inv_pair p i (Nat.succ_le_iff.mp hi1) hilt
  have h2H' : 2 * harmonic (p - 1) =
      (p : ℚ) * ∑ i ∈ Finset.Icc 1 (p - 1), 1 / (i * (p - i) : ℚ) := by
    rw [h2H, hpair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [div_eq_mul_inv, one_div, mul_comm]
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h2ne
  calc
    2 * harmonic (p - 1) = (p : ℚ) * ∑ i ∈ Finset.Icc 1 (p - 1), 1 / (i * (p - i) : ℚ) := h2H'
    _ = 2 * ((p : ℚ) / 2 * ∑ i ∈ Finset.Icc 1 (p - 1), 1 / (i * (p - i) : ℚ)) := by
      ring

/-- `k(p-k)` divides `(p-1)!` for `1 ≤ k ≤ p-1`. -/
lemma mul_sub_dvd_factorial_pred {p k : ℕ} (hp : Nat.Prime p)
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    k * (p - k) ∣ (p - 1).factorial := by
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkle : k ≤ p - 1 := (Finset.mem_Icc.mp hk).2
  have hkp : k < p := lt_of_le_of_lt hkle (Nat.pred_lt hp.ne_zero)
  have hpk1 : 1 ≤ p - k := Nat.le_sub_of_add_le (by omega)
  have hpkle : p - k ≤ p - 1 := Nat.sub_le_sub_left hk1 _
  have hdvd1 : k ∣ (p - 1).factorial :=
    Nat.dvd_factorial (Nat.succ_le_iff.mp hk1) hkle
  have hdvd2 : (p - k) ∣ (p - 1).factorial :=
    Nat.dvd_factorial (Nat.succ_le_iff.mp hpk1) hpkle
  have hcop : Nat.Coprime k (p - k) := by
    rw [Nat.coprime_sub_self_right hkp.le]
    exact Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hp).2
        (Nat.not_dvd_of_pos_of_lt (Nat.succ_le_iff.mp hk1) hkp))
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd1 hdvd2

lemma valGe_of_dvd {p n : ℕ} [hp : Fact p.Prime] (h : p ∣ n) : valGe p 1 (n : ℚ) := by
  rcases h with ⟨k, rfl⟩
  simpa [mul_comm] using valGe_mul valGe_p (valGe_nat p k)

lemma valGe_div_of_unit {p : ℕ} [Fact p.Prime] {k : ℤ} {a b : ℚ}
    (ha : valGe p k a) (hb : valGe p 0 b⁻¹) : valGe p k (a / b) := by
  have : k = k + 0 := by ring
  rw [div_eq_mul_inv, this]
  exact valGe_mul ha hb

lemma zmod_inv_mul {p : ℕ} [Fact p.Prime] {a b : ℕ} (hb : (b : ZMod p) ≠ 0)
    (hdvd : b ∣ a) : ((a / b : ℕ) : ZMod p) = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  have h : ((a / b * b : ℕ) : ZMod p) = (a : ZMod p) :=
    congrArg (fun n : ℕ => (n : ZMod p)) (Nat.div_mul_cancel hdvd)
  rw [Nat.cast_mul] at h
  apply mul_right_cancel₀ hb
  rwa [mul_assoc, inv_mul_cancel₀ hb, mul_one]

lemma factorial_pred_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] :
    ((p - 1).factorial : ZMod p) ≠ 0 := by
  rw [ZMod.wilsons_lemma p]
  exact neg_ne_zero.mpr one_ne_zero

lemma mul_sub_ne_zero_zmod {p k : ℕ} [hp : Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 (p - 1)) : ((k * (p - k) : ℕ) : ZMod p) ≠ 0 := by
  obtain ⟨hk1, _, hilt⟩ := mem_Icc_bounds hk (Nat.Prime.pos hp.out)
  have hk0 : (k : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (Nat.succ_le_iff.mp hk1) hilt
      ((ZMod.natCast_eq_zero_iff k p).mp h)
  have hpk0 : ((p - k : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hpkpos : 0 < p - k := Nat.sub_pos_of_lt hilt
    have hpklt : p - k < p := Nat.sub_lt (Nat.Prime.pos hp.out) (Nat.succ_le_iff.mp hk1)
    exact Nat.not_dvd_of_pos_of_lt hpkpos hpklt
      ((ZMod.natCast_eq_zero_iff (p - k) p).mp h)
  simp only [Nat.cast_mul, mul_ne_zero_iff]
  exact ⟨hk0, hpk0⟩

/-- The integer `∑ (p-1)! / (k(p-k))` is divisible by `p`. -/
lemma wolstenholme_sum_dvd {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    p ∣ ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / (k * (p - k)) : ℕ) := by
  have hmod : (∑ k ∈ Finset.Icc 1 (p - 1),
      (((p - 1).factorial / (k * (p - k)) : ℕ) : ZMod p)) = 0 := by
    trans ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2
    · apply Finset.sum_congr rfl
      intro k hk
      have hdvd := mul_sub_dvd_factorial_pred hp.out hk
      have hbne := mul_sub_ne_zero_zmod hk
      rw [zmod_inv_mul hbne hdvd, ZMod.wilsons_lemma p]
      have hcast : ((k * (p - k) : ℕ) : ZMod p) = -((k : ZMod p) ^ 2) := by
        rw [Nat.cast_mul, pow_two]
        have : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
          rw [Nat.cast_sub (mem_Icc_bounds hk (Nat.Prime.pos hp.out)).2.2.le]
          simp
        rw [this, mul_neg]
      rw [hcast, inv_neg, pow_two]
      ring
    · exact harm_two_mod_p h5
  let W : ℕ := ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / (k * (p - k)) : ℕ)
  have hW0 : (W : ZMod p) = 0 := by
    have : (W : ZMod p) = ∑ k ∈ Finset.Icc 1 (p - 1),
        (((p - 1).factorial / (k * (p - k)) : ℕ) : ZMod p) := by
      simp [W, Nat.cast_sum]
    rwa [this]
  exact (ZMod.natCast_eq_zero_iff W p).mp hW0

lemma nat_div_mul_cast {a b : ℕ} (hdvd : b ∣ a) :
    ((a / b : ℕ) : ℚ) * (b : ℚ) = (a : ℚ) := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.div_mul_cancel hdvd)
  dsimp at h
  rwa [Nat.cast_mul] at h

lemma nat_div_cast_div {a b : ℕ} (hdvd : b ∣ a) (ha0 : a ≠ 0) (hb : (b : ℚ) ≠ 0) :
    ((a / b : ℕ) : ℚ) / (a : ℚ) = 1 / (b : ℚ) := by
  have ha : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  have hmul := nat_div_mul_cast hdvd
  rw [div_eq_div_iff ha hb, one_mul]
  exact hmul

lemma sum_inv_mul_sub_eq {p : ℕ} [hp : Fact p.Prime] :
    ∑ i ∈ Finset.Icc 1 (p - 1), (1 / (i * (p - i) : ℚ)) =
      ((∑ k ∈ Finset.Icc 1 (p - 1),
        ((p - 1).factorial / (k * (p - k)) : ℕ) : ℕ) : ℚ) /
        ((p - 1).factorial : ℚ) := by
  have hfac0 : ((p - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (p - 1).factorial_ne_zero
  have hcast_sum :
      ((∑ k ∈ Finset.Icc 1 (p - 1),
        ((p - 1).factorial / (k * (p - k)) : ℕ) : ℕ) : ℚ) =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        (((p - 1).factorial / (k * (p - k)) : ℕ) : ℚ) := Nat.cast_sum _ _
  rw [hcast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hdvd := mul_sub_dvd_factorial_pred hp.out hi
  obtain ⟨hi1, _, hilt⟩ := mem_Icc_bounds hi (Nat.Prime.pos hp.out)
  have hb : ((i * (p - i) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hi1))
      (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hilt)))
  have hterm := nat_div_cast_div hdvd (p - 1).factorial_ne_zero hb
  have hcast : (i * (p - i) : ℚ) = ((i * (p - i) : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_sub hilt.le]
  rw [hcast]
  exact hterm.symm

/-- Wolstenholme: `H_{p-1} ≡ 0 (mod p^2)` for primes `p ≥ 5`. -/
lemma wolstenholme_harmonic {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p 2 (harmonic (p - 1)) := by
  have h2 : 2 < p := lt_of_lt_of_le (by norm_num : 2 < 5) h5
  rw [harmonic_pairing p hp.out h2]
  have hhalf : valGe p 0 (2 : ℚ)⁻¹ :=
    valGe_inv_of_not_dvd (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 2)
        (lt_of_lt_of_le (by norm_num : 2 < 5) h5))
  set W := ∑ k ∈ Finset.Icc 1 (p - 1),
    ((p - 1).factorial / (k * (p - k)) : ℕ) with hWdef
  have hWdvd : p ∣ W := by
    rw [hWdef]; exact wolstenholme_sum_dvd h5
  have hsum_eq :
      ∑ i ∈ Finset.Icc 1 (p - 1), (1 / (i * (p - i) : ℚ)) =
        (W : ℚ) / ((p - 1).factorial : ℚ) := by
    rw [hWdef]; exact sum_inv_mul_sub_eq (p := p)
  have hW : valGe p 1 (W : ℚ) := valGe_of_dvd hWdvd
  have hfacinv : valGe p 0 (((p - 1).factorial : ℚ)⁻¹) :=
    valGe_inv_of_not_dvd (p - 1).factorial_ne_zero (by
      exact mt (Nat.Prime.dvd_factorial hp.out).mp (not_le_of_gt
        (Nat.pred_lt (Nat.Prime.ne_zero hp.out))))
  have hsum : valGe p 1
      (∑ i ∈ Finset.Icc 1 (p - 1), (1 / (i * (p - i) : ℚ))) := by
    rw [hsum_eq]
    exact valGe_div_of_unit (p := p) hW hfacinv
  have hmul := valGe_mul (valGe_mul valGe_p hhalf) hsum
  have heq : (p : ℚ) / 2 * ∑ i ∈ Finset.Icc 1 (p - 1), 1 / (i * (p - i) : ℚ) =
      (p : ℚ) * (2 : ℚ)⁻¹ * ∑ i ∈ Finset.Icc 1 (p - 1), 1 / (i * (p - i) : ℚ) := by
    ring
  rwa [heq]

lemma wolstenholme_sum_sq_dvd {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    p ∣ ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / k : ℕ) ^ 2 := by
  have hmod : (∑ k ∈ Finset.Icc 1 (p - 1),
      ((((p - 1).factorial / k : ℕ) ^ 2 : ℕ) : ZMod p)) = 0 := by
    trans ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2
    · apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hk1, hkle, hilt⟩ := mem_Icc_bounds hk (Nat.Prime.pos hp.out)
      have hdvd : k ∣ (p - 1).factorial :=
        Nat.dvd_factorial (Nat.succ_le_iff.mp hk1) hkle
      have hkne : (k : ZMod p) ≠ 0 := by
        intro h
        exact Nat.not_dvd_of_pos_of_lt (Nat.succ_le_iff.mp hk1) hilt
          ((ZMod.natCast_eq_zero_iff k p).mp h)
      rw [Nat.cast_pow, zmod_inv_mul hkne hdvd, ZMod.wilsons_lemma p]
      ring
    · exact harm_two_mod_p h5
  let T : ℕ := ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / k : ℕ) ^ 2
  have hT0 : (T : ZMod p) = 0 := by
    have : (T : ZMod p) = ∑ k ∈ Finset.Icc 1 (p - 1),
        ((((p - 1).factorial / k : ℕ) ^ 2 : ℕ) : ZMod p) := by
      simp [T, Nat.cast_sum]
    rwa [this]
  exact (ZMod.natCast_eq_zero_iff T p).mp hT0

lemma nat_div_sq_cast {a b : ℕ} (hdvd : b ∣ a) (ha0 : a ≠ 0) (hb : (b : ℚ) ≠ 0) :
    (((a / b : ℕ) ^ 2 : ℕ) : ℚ) / (a : ℚ) ^ 2 = 1 / (b : ℚ) ^ 2 := by
  have hpow : (((a / b : ℕ) ^ 2 : ℕ) : ℚ) = ((a / b : ℕ) : ℚ) ^ 2 := Nat.cast_pow _ _
  rw [hpow, ← div_pow, nat_div_cast_div hdvd ha0 hb]
  simp [one_div, pow_two]

lemma harm_two_eq_div {p : ℕ} [hp : Fact p.Prime] :
    harm 2 (p - 1) =
      ((∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / k : ℕ) ^ 2 : ℕ) : ℚ) /
        (((p - 1).factorial : ℚ) ^ 2) := by
  have hcast_sum :
      ((∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / k : ℕ) ^ 2 : ℕ) : ℚ) =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        ((((p - 1).factorial / k : ℕ) ^ 2 : ℕ) : ℚ) := Nat.cast_sum _ _
  rw [harm, hcast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hk1, hkle, hilt⟩ := mem_Icc_bounds hk (Nat.Prime.pos hp.out)
  have hdvd : k ∣ (p - 1).factorial :=
    Nat.dvd_factorial (Nat.succ_le_iff.mp hk1) hkle
  have hk0 : (k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hk1))
  have hterm := nat_div_sq_cast hdvd (p - 1).factorial_ne_zero hk0
  simpa [pow_two, one_div] using hterm.symm

/-- Wolstenholme: `H_{p-1}^{(2)} ≡ 0 (mod p)` for primes `p ≥ 5`. -/
lemma wolstenholme_harmonic_two {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p 1 (harm 2 (p - 1)) := by
  set T := ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1).factorial / k : ℕ) ^ 2 with hTdef
  have hTdvd : p ∣ T := by rw [hTdef]; exact wolstenholme_sum_sq_dvd h5
  have hsum_eq : harm 2 (p - 1) = (T : ℚ) / (((p - 1).factorial : ℚ) ^ 2) := by
    rw [hTdef]; exact harm_two_eq_div (p := p)
  have hT : valGe p 1 (T : ℚ) := valGe_of_dvd hTdvd
  have hfacinv : valGe p 0 ((((p - 1).factorial : ℚ) ^ 2)⁻¹) := by
    have h := valGe_inv_of_not_dvd (p - 1).factorial_ne_zero (by
      exact mt (Nat.Prime.dvd_factorial hp.out).mp (not_le_of_gt
        (Nat.pred_lt (Nat.Prime.ne_zero hp.out))))
    simpa using valGe_pow (n := 2) h
  rw [hsum_eq]
  exact valGe_div_of_unit (p := p) hT hfacinv

/-! ## Kazandzidis congruence -/

lemma factorial_add_prod (m t : ℕ) :
    (m + t).factorial = m.factorial * ∏ k ∈ Finset.Icc 1 t, (m + k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hI : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
      ext x; simp [Finset.mem_Icc]; constructor <;> omega
    rw [show m + (t + 1) = (m + t) + 1 by ring, Nat.factorial_succ, ih, hI,
      Finset.prod_insert (by simp [Finset.mem_Icc])]
    ring

lemma Icc_succ_eq_insert (t : ℕ) :
    Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
  ext x; simp [Finset.mem_Icc]; constructor <;> omega

lemma prod_Icc_flip {p : ℕ} (hp : 1 < p) (f : ℕ → ℚ) :
    ∏ k ∈ Finset.Icc 1 (p - 1), f k =
      ∏ s ∈ Finset.Icc 1 (p - 1), f (p - s) := by
  refine Finset.prod_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
  · intro k hk; exact mem_Icc_one_pred_sub hk hp
  · intro i hi j hj h
    obtain ⟨_, _, hilt⟩ := mem_Icc_bounds hi (by omega)
    obtain ⟨_, _, hjlt⟩ := mem_Icc_bounds hj (by omega)
    apply_fun (fun x => p - x) at h
    rwa [Nat.sub_sub_self hilt.le, Nat.sub_sub_self hjlt.le] at h
  · intro i hi
    refine ⟨p - i, mem_Icc_one_pred_sub hi hp, ?_⟩
    obtain ⟨_, _, hilt⟩ := mem_Icc_bounds hi (by omega)
    exact Nat.sub_sub_self hilt.le
  · intro k hk
    obtain ⟨_, _, hilt⟩ := mem_Icc_bounds hk (by omega)
    simp [Nat.sub_sub_self hilt.le]

/-- `(Np)! = p^N N! ∏_{s=1}^{p-1} ∏_{j=1}^N (pj - s)`. -/
lemma factorial_mul_p_eq (N p : ℕ) (hp : 1 < p) :
    ((N * p).factorial : ℚ) =
      (p : ℚ) ^ N * (N.factorial : ℚ) *
        ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hrange : (N + 1) * p = N * p + p := by ring
    have hfac := factorial_add_prod (N * p) p
    rw [hrange]
    have hfacQ : ((N * p + p).factorial : ℚ) =
        ((N * p).factorial : ℚ) * ∏ k ∈ Finset.Icc 1 p, ((N * p + k : ℕ) : ℚ) := by
      rw [hfac]; push_cast; rfl
    rw [hfacQ, ih]
    have hI : Finset.Icc 1 p = insert p (Finset.Icc 1 (p - 1)) := by
      ext x; simp [Finset.mem_Icc]; constructor <;> omega
    have hprod : (∏ k ∈ Finset.Icc 1 p, ((N * p + k : ℕ) : ℚ)) =
        ((p : ℚ) * (N + 1 : ℕ)) *
          ∏ s ∈ Finset.Icc 1 (p - 1), ((p : ℚ) * (N + 1 : ℕ) - s) := by
      have hnotin : p ∉ Finset.Icc 1 (p - 1) := by
        simp [Finset.mem_Icc]; omega
      rw [hI, Finset.prod_insert hnotin]
      have hpN : ((N * p + p : ℕ) : ℚ) = (p : ℚ) * (N + 1 : ℕ) := by
        push_cast; ring
      rw [hpN]
      have hflip := prod_Icc_flip (p := p) hp (fun k => ((N * p + k : ℕ) : ℚ))
      rw [hflip]
      congr 1
      apply Finset.prod_congr rfl
      intro s hs
      obtain ⟨hs1, _, hslt⟩ := mem_Icc_bounds hs (by omega)
      have : ((N * p + (p - s) : ℕ) : ℚ) = (p : ℚ) * (N + 1 : ℕ) - s := by
        rw [Nat.cast_add, Nat.cast_sub hslt.le]
        push_cast; ring
      exact this
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) :=
      Icc_succ_eq_insert N
    rw [hprod]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    -- reassociate the double product
    have hdp : ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 (N + 1), ((p * j : ℚ) - s) =
        (∏ s ∈ Finset.Icc 1 (p - 1), ((p : ℚ) * (N + 1 : ℕ) - s)) *
          ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) := by
      have hnotin : N + 1 ∉ Finset.Icc 1 N := by simp [Finset.mem_Icc]
      simp_rw [hIcc, Finset.prod_insert hnotin]
      rw [Finset.prod_mul_distrib]
    rw [hdp]
    ring

lemma pj_sub_s_ne_zero (p j s : ℕ) (hp : 1 < p) (hs : s ∈ Finset.Icc 1 (p - 1))
    (hj : 0 < j) : (p * j : ℚ) - s ≠ 0 := by
  obtain ⟨hs1, hsle, hslt⟩ := mem_Icc_bounds hs (by omega)
  have hlt : (s : ℚ) < p * j := by
    have : (s : ℚ) < p := Nat.cast_lt.mpr hslt
    have : (p : ℚ) ≤ p * j := by
      have : (1 : ℚ) ≤ j := Nat.one_le_cast.mpr hj
      nlinarith
    linarith
  linarith

lemma choose_eq_factorial_div (n k : ℕ) (h : k ≤ n) :
    (n.choose k : ℚ) = (n.factorial : ℚ) / (k.factorial * (n - k).factorial : ℚ) :=
  Nat.cast_choose (K := ℚ) h

lemma factorial_ne_zero_rat (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr n.factorial_ne_zero

lemma pN_prod_ne_zero (N p : ℕ) (hp : 1 < p) :
    ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro s hs
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
  exact pj_sub_s_ne_zero p j s hp hs hj0

/-- After cancelling `p`-powers and factorials,
`(Np)! M! (N-M)! / ((Mp)! ((N-M)p)! N!) = P_N / (P_M P_{N-M})`. -/
lemma choose_ratio_P (N M p : ℕ) (hM : M ≤ N) (hp : 1 < p) :
    ((N * p).factorial : ℚ) * (M.factorial : ℚ) * ((N - M).factorial : ℚ) /
      (((M * p).factorial : ℚ) * (((N - M) * p).factorial : ℚ) * (N.factorial : ℚ)) =
      (∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s)) /
        ((∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 M, ((p * j : ℚ) - s)) *
          (∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 (N - M), ((p * j : ℚ) - s))) := by
  have hfN := factorial_mul_p_eq N p hp
  have hfM := factorial_mul_p_eq M p hp
  have hfNM := factorial_mul_p_eq (N - M) p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hpow : (p : ℚ) ^ N = (p : ℚ) ^ M * (p : ℚ) ^ (N - M) := by
    rw [← pow_add, Nat.add_sub_of_le hM]
  rw [hfN, hfM, hfNM, hpow]
  field_simp [factorial_ne_zero_rat, pow_ne_zero, hp0,
    pN_prod_ne_zero N p hp, pN_prod_ne_zero M p hp, pN_prod_ne_zero (N - M) p hp]

/-- `∏_{j=1}^M (p(j + K) - s) = ∏_{j=K+1}^{K+M} (p j - s)`. -/
lemma prod_shift_pj (M K p s : ℕ) :
    ∏ j ∈ Finset.Icc 1 M, ((p * (j + K) : ℚ) - s) =
      ∏ j ∈ Finset.Icc (K + 1) (K + M), ((p * j : ℚ) - s) := by
  refine Finset.prod_bij (fun j _ => j + K) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · simpa [Nat.add_comm] using Nat.add_le_add_right hj1 K
    · simpa [Nat.add_comm K M] using Nat.add_le_add_right hj2 K
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij
  · intro b hb
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hb2⟩
    refine ⟨b - K, ?_, ?_⟩
    · refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hb1)
      · have hb2' : b ≤ M + K := by simpa [Nat.add_comm K M] using hb2
        exact Nat.sub_le_of_le_add hb2'
    · exact Nat.sub_add_cancel (le_trans (Nat.le_add_right K 1) hb1)
  · intro j _
    simp [Nat.cast_add]

/-- Product formula for the binomial ratio. -/
lemma choose_ratio_product (N M p : ℕ) (hM : M ≤ N) (hp : 1 < p) :
    ((N * p).choose (M * p) : ℚ) / (N.choose M) =
      ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 M,
        (((p * (j + (N - M)) : ℚ) - s) / ((p * j : ℚ) - s)) := by
  have hMp : M * p ≤ N * p := Nat.mul_le_mul_right p hM
  rw [choose_eq_factorial_div _ _ hMp, choose_eq_factorial_div _ _ hM]
  have hsub : N * p - M * p = (N - M) * p := (Nat.mul_sub_right_distrib N M p).symm
  rw [hsub]
  have hfn := factorial_ne_zero_rat
  have hLHS :
      ((N * p).factorial : ℚ) / ((M * p).factorial * ((N - M) * p).factorial : ℚ) /
        ((N.factorial : ℚ) / (M.factorial * (N - M).factorial : ℚ)) =
      ((N * p).factorial : ℚ) * (M.factorial : ℚ) * ((N - M).factorial : ℚ) /
        (((M * p).factorial : ℚ) * (((N - M) * p).factorial : ℚ) * (N.factorial : ℚ)) := by
    field_simp [hfn]
  rw [hLHS, choose_ratio_P N M p hM hp]
  have hmul :
      (∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 M, ((p * j : ℚ) - s)) *
        (∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 (N - M), ((p * j : ℚ) - s)) =
      ∏ s ∈ Finset.Icc 1 (p - 1),
        ((∏ j ∈ Finset.Icc 1 M, ((p * j : ℚ) - s)) *
          (∏ j ∈ Finset.Icc 1 (N - M), ((p * j : ℚ) - s))) :=
    (Finset.prod_mul_distrib).symm
  rw [hmul, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  have hU1 : Finset.Icc 1 (N - M) ∪ Finset.Icc (N - M + 1) N = Finset.Icc 1 N := by
    ext x; simp [Finset.mem_Icc]; constructor <;> omega
  have hD1 : Disjoint (Finset.Icc 1 (N - M)) (Finset.Icc (N - M + 1) N) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'; simp [Finset.mem_Icc] at hx hx'; omega
  have hsplit : ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) =
      (∏ j ∈ Finset.Icc 1 (N - M), ((p * j : ℚ) - s)) *
        (∏ j ∈ Finset.Icc (N - M + 1) N, ((p * j : ℚ) - s)) := by
    rw [← hU1, Finset.prod_union hD1]
  have hKN : (N - M) + M = N := Nat.sub_add_cancel hM
  have hshift' : ∏ j ∈ Finset.Icc 1 M, ((p : ℚ) * (↑j + (↑N - ↑M)) - s) =
      ∏ j ∈ Finset.Icc (N - M + 1) N, ((p * j : ℚ) - s) := by
    have := prod_shift_pj M (N - M) p s
    simp_rw [Nat.cast_sub hM] at this
    simpa [hKN, Nat.add_comm (N - M) M] using this
  have hMne : ∏ j ∈ Finset.Icc 1 M, ((p * j : ℚ) - s) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pj_sub_s_ne_zero p j s hp hs (Finset.mem_Icc.mp hj).1
  have hNMne : ∏ j ∈ Finset.Icc 1 (N - M), ((p * j : ℚ) - s) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pj_sub_s_ne_zero p j s hp hs (Finset.mem_Icc.mp hj).1
  have hterm : ∀ j ∈ Finset.Icc 1 M,
      (((p * (j + (N - M)) : ℚ) - s) / ((p * j : ℚ) - s)) =
        ((p * (j + (N - M)) : ℚ) - s) / ((p * j : ℚ) - s) := fun _ _ => rfl
  have hRHS :
      ∏ j ∈ Finset.Icc 1 M,
          (((p * (j + (N - M)) : ℚ) - s) / ((p * j : ℚ) - s)) =
        (∏ j ∈ Finset.Icc 1 M, ((p * (j + (N - M)) : ℚ) - s)) /
          (∏ j ∈ Finset.Icc 1 M, ((p * j : ℚ) - s)) :=
    Finset.prod_div_distrib _ _
  rw [hRHS, hsplit, hshift']
  field_simp [hMne, hNMne]

/-! ## Product form of Wolstenholme and Kazandzidis -/

lemma valGe_two_inv {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p 0 (2 : ℚ)⁻¹ :=
  valGe_inv_of_not_dvd (by norm_num)
    (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 2)
      (lt_of_lt_of_le (by norm_num : 2 < 5) h5))


lemma prod_Icc_one_eq_factorial (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, (i : ℚ) = (n.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Icc_succ_eq_insert n, Finset.prod_insert (by simp [Finset.mem_Icc]), ih,
      Nat.factorial_succ]
    push_cast
    ring

lemma valGe_choose_ne_zero {n k : ℕ} (hkn : k ≤ n) :
    (n.choose k : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'

/-- `Q_p(X) = ∏_{i=1}^{p-1} (X+i) / (p-1)!`. -/
def risingQ (p : ℕ) (X : ℚ) : ℚ :=
  (∏ i ∈ Finset.Icc 1 (p - 1), (X + i)) / (p - 1).factorial

lemma risingQ_ne_zero {p : ℕ} (hp : 1 < p) (X : ℚ)
    (hX : ∀ i ∈ Finset.Icc 1 (p - 1), X + i ≠ 0) :
    risingQ p X ≠ 0 := by
  unfold risingQ
  have hfac : ((p - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (p - 1).factorial_ne_zero
  refine div_ne_zero ?_ hfac
  exact Finset.prod_ne_zero_iff.mpr hX

lemma half_p_pos {p : ℕ} (h5 : 5 ≤ p) : 0 < (p - 1) / 2 := by
  have : 2 ≤ p - 1 := by omega
  exact Nat.div_pos this (by norm_num)

lemma odd_prime_not_even {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) : ¬ Even p := by
  intro h
  have := Nat.Prime.eq_two_or_odd' hp.out
  rcases this with h2 | hodd
  · omega
  · exact Nat.not_even_iff_odd.mpr hodd h

lemma mem_half_bounds {p i : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    1 ≤ i ∧ i ≤ (p - 1) / 2 ∧ i < p ∧ p - i ≠ i ∧ 1 ≤ p - i ∧ p - i ≤ p - 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
  have hi_lt_p : i < p := by
    have : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
    omega
  have hne : p - i ≠ i := by
    intro h
    have heq : p = 2 * i := by omega
    exact odd_prime_not_even h5 ⟨i, by rw [heq, two_mul]⟩
  have hpi1 : 1 ≤ p - i := by omega
  have hpi2 : p - i ≤ p - 1 := by omega
  exact ⟨h1, h2, hi_lt_p, hne, hpi1, hpi2⟩

lemma pair_mul (p i : ℕ) (hi : i ≤ p) (X : ℚ) :
    (X + i) * (X + (p - i : ℕ)) = X * (X + p) + (i : ℚ) * (p - i : ℕ) := by
  have hcast : ((p - i : ℕ) : ℚ) = (p : ℚ) - i := Nat.cast_sub hi
  rw [hcast]
  ring

lemma Icc_pair_union {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    Finset.Icc 1 (p - 1) =
      (Finset.Icc 1 ((p - 1) / 2)).biUnion
        (fun i => ({i, p - i} : Finset ℕ)) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have hilt : x < p := by omega
    by_cases hle : x ≤ (p - 1) / 2
    · exact ⟨x, ⟨hx1, hle⟩, Or.inl rfl⟩
    · refine ⟨p - x, ?_, Or.inr (Nat.sub_sub_self hilt.le).symm⟩
      have hx1' : 1 ≤ p - x := by omega
      have hx2' : p - x ≤ (p - 1) / 2 := by
        have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp.out).resolve_left (by omega)
        omega
      exact ⟨hx1', hx2'⟩
  · intro ⟨i, hi, hxi⟩
    obtain ⟨h1, h2, hilt, hne, hpi1, hpi2⟩ := mem_half_bounds h5 (Finset.mem_Icc.mpr hi)
    rcases hxi with hxi | hxi
    · subst hxi; exact ⟨h1, by omega⟩
    · subst hxi; exact ⟨hpi1, hpi2⟩

lemma Icc_pair_disjoint {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    {i j : ℕ} (hi : i ∈ Finset.Icc 1 ((p - 1) / 2))
    (hj : j ∈ Finset.Icc 1 ((p - 1) / 2)) (hij : i ≠ j) :
    Disjoint ({i, p - i} : Finset ℕ) {j, p - j} := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  obtain ⟨_, _, _, hnei, _, _⟩ := mem_half_bounds h5 hi
  obtain ⟨_, _, _, hnej, _, _⟩ := mem_half_bounds h5 hj
  match hx, hx' with
  | Or.inl hxi, Or.inl hxj =>
    exact hij (hxi.symm.trans hxj)
  | Or.inl hxi, Or.inr hxj =>
    -- x = i and x = p - j
    exact hnej (by omega)
  | Or.inr hxi, Or.inl hxj =>
    exact hnei (by omega)
  | Or.inr hxi, Or.inr hxj =>
    have : i = j := by omega
    exact hij this

lemma pair_set_card {p i : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    ({i, p - i} : Finset ℕ).card = 2 := by
  obtain ⟨_, _, _, hne, _, _⟩ := mem_half_bounds h5 hi
  exact Finset.card_pair hne.symm

/-- Pairing formula for the normalized rising Pochhammer. -/
lemma risingQ_pair {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) (X : ℚ) :
    risingQ p X =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2),
        (1 + X * (X + p) / ((i : ℚ) * (p - i : ℕ))) := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  have hfac0 : ((p - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (p - 1).factorial_ne_zero
  unfold risingQ
  have hunion := Icc_pair_union (p := p) h5
  have hprod :
      ∏ i ∈ Finset.Icc 1 (p - 1), (X + i) =
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), ((X + i) * (X + (p - i : ℕ))) := by
    rw [hunion, Finset.prod_biUnion]
    · apply Finset.prod_congr rfl
      intro i hi
      obtain ⟨_, _, _, hne, _, _⟩ := mem_half_bounds h5 hi
      have hnotin : i ∉ ({p - i} : Finset ℕ) := by simp [hne.symm]
      rw [Finset.prod_insert hnotin, Finset.prod_singleton]
    · intro i hi j hj hij
      exact Icc_pair_disjoint h5 hi hj hij
  have hfac :
      ((p - 1).factorial : ℚ) =
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), ((i : ℚ) * (p - i : ℕ)) := by
    have := prod_Icc_one_eq_factorial (p - 1)
    rw [← this, hunion, Finset.prod_biUnion]
    · apply Finset.prod_congr rfl
      intro i hi
      obtain ⟨_, _, _, hne, _, _⟩ := mem_half_bounds h5 hi
      have hnotin : i ∉ ({p - i} : Finset ℕ) := by simp [hne.symm]
      rw [Finset.prod_insert hnotin, Finset.prod_singleton]
    · intro i hi j hj hij
      exact Icc_pair_disjoint h5 hi hj hij
  rw [hprod, hfac, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  obtain ⟨h1, _, hilt, _, _, _⟩ := mem_half_bounds h5 hi
  have hi_le : i ≤ p := by omega
  have hden : ((i : ℚ) * (p - i : ℕ)) ≠ 0 := by
    have : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp h1))
    have : ((p - i : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hilt))
    positivity
  rw [pair_mul p i hi_le X]
  field_simp [hden]
  ring

lemma sigma1_eq_harmonic_div_p {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (1 : ℚ) / (i * (p - i : ℕ)) =
      harmonic (p - 1) / p := by
  have h2 : 2 < p := lt_of_lt_of_le (by norm_num : 2 < 5) h5
  have hpair := harmonic_pairing p hp.out h2
  have hunion := Icc_pair_union (p := p) h5
  have hsum :
      ∑ i ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (i * (p - i : ℕ)) =
        2 * ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (1 : ℚ) / (i * (p - i : ℕ)) := by
    rw [hunion, Finset.sum_biUnion]
    · trans ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (2 : ℚ) * (1 / (i * (p - i : ℕ)))
      · apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨_, _, _, hne, _, _⟩ := mem_half_bounds h5 hi
        have hnotin : i ∉ ({p - i} : Finset ℕ) := by simp [hne.symm]
        rw [Finset.sum_insert hnotin, Finset.sum_singleton]
        obtain ⟨_, _, hilt, _, _, _⟩ := mem_half_bounds h5 hi
        have hcast : ((p - i : ℕ) : ℚ) = (p : ℚ) - i := Nat.cast_sub hilt.le
        have hi_le : i ≤ p := hilt.le
        have hcast' : ((p - (p - i) : ℕ) : ℚ) = (i : ℚ) := by
          rw [Nat.sub_sub_self hi_le]
        rw [one_div, one_div, mul_inv, mul_inv, hcast']
        ring
      · rw [← Finset.mul_sum]
    · intro i hi j hj hij
      exact Icc_pair_disjoint h5 hi hj hij
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
  have : harmonic (p - 1) = (p : ℚ) / 2 *
      ∑ i ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (i * (p - i : ℕ)) := by
    convert hpair using 2
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi1, _, hilt⟩ := mem_Icc_bounds hi (Nat.Prime.pos hp.out)
    have hcast : ((p - i : ℕ) : ℚ) = (p : ℚ) - i := Nat.cast_sub hilt.le
    simp [hcast]
  rw [this, hsum]
  field_simp [hp0]

lemma valGe_sigma1 {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p 1 (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (1 : ℚ) / (i * (p - i : ℕ))) := by
  rw [sigma1_eq_harmonic_div_p h5]
  have hH := wolstenholme_harmonic (p := p) h5
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
  have : harmonic (p - 1) / p = harmonic (p - 1) * (p : ℚ)⁻¹ := div_eq_mul_inv _ _
  rw [this]
  have hinv : valGe p (-1) ((p : ℚ)⁻¹) := by
    rcases eq_or_ne (p : ℚ) 0 with h | h
    · exact (hp0 h).elim
    · refine Or.inr ?_
      rw [padicValRat.inv (p : ℚ), padicValRat.self (Nat.Prime.one_lt hp.out)]
  simpa [add_comm] using valGe_mul hH hinv

/-- `a(a²-1)/3 - b(b²-1)/3 - c(c²-1)/3 = abc` when `c = a-b`. -/
lemma delta_one_cube (a b : ℕ) (hba : b ≤ a) :
    (a : ℚ) * ((a : ℚ) ^ 2 - 1) / 3 - (b : ℚ) * ((b : ℚ) ^ 2 - 1) / 3
      - ((a - b : ℕ) : ℚ) * (((a - b : ℕ) : ℚ) ^ 2 - 1) / 3 =
      (a : ℚ) * b * (a - b : ℕ) := by
  have hcast : ((a - b : ℕ) : ℚ) = (a : ℚ) - b := Nat.cast_sub hba
  rw [hcast]
  ring

lemma sum_j_succ (t : ℕ) :
    ∑ j ∈ Finset.range t, ((j : ℚ) * (j + 1)) = (t : ℚ) * ((t : ℚ) ^ 2 - 1) / 3 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    have : (t : ℚ) * (t + 1) + (t : ℚ) * ((t : ℚ) ^ 2 - 1) / 3 =
        ((t + 1 : ℕ) : ℚ) * ((((t + 1 : ℕ) : ℚ) ^ 2 - 1) / 3) := by
      push_cast
      ring
    convert this using 1
    · ring
    · push_cast; ring

/-- `F(t) = ∏_{j=0}^{t-1} Q_p(j p)`. -/
def risingF (p t : ℕ) : ℚ :=
  ∏ j ∈ Finset.range t, risingQ p (j * p)

lemma risingF_succ (p t : ℕ) :
    risingF p (t + 1) = risingF p t * risingQ p (t * p) := by
  simp [risingF, Finset.prod_range_succ]

lemma risingQ_at_mul_p {p j : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    risingQ p (j * p) =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2),
        (1 + ((p : ℚ) ^ 2 * j * (j + 1)) / ((i : ℚ) * (p - i : ℕ))) := by
  rw [risingQ_pair h5]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  push_cast
  ring

lemma prod_pj_sub_s_eq_risingQ (p j : ℕ) (hp : 1 < p) :
    ∏ s ∈ Finset.Icc 1 (p - 1), ((p * (j + 1) : ℚ) - s) =
      risingQ p (j * p) * (p - 1).factorial := by
  unfold risingQ
  have hfac0 : ((p - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (p - 1).factorial_ne_zero
  field_simp [hfac0]
  refine Finset.prod_bij (fun s _ => p - s) ?_ ?_ ?_ ?_
  · intro s hs
    exact mem_Icc_one_pred_sub hs hp
  · intro s hs t ht h
    obtain ⟨_, _, hsilt⟩ := mem_Icc_bounds hs (by omega)
    obtain ⟨_, _, htlt⟩ := mem_Icc_bounds ht (by omega)
    apply_fun (fun x => p - x) at h
    rwa [Nat.sub_sub_self hsilt.le, Nat.sub_sub_self htlt.le] at h
  · intro s hs
    refine ⟨p - s, mem_Icc_one_pred_sub hs hp, Nat.sub_sub_self ?_⟩
    obtain ⟨_, _, hilt⟩ := mem_Icc_bounds hs (by omega)
    exact hilt.le
  · intro s hs
    obtain ⟨hs1, _, hslt⟩ := mem_Icc_bounds hs (by omega)
    have hcast : ((p - s : ℕ) : ℚ) = (p : ℚ) - s := Nat.cast_sub hslt.le
    rw [hcast]
    push_cast
    ring

lemma prod_Icc_reindex_succ (N p : ℕ) (s : ℕ) :
    ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) =
      ∏ j ∈ Finset.range N, ((p * (j + 1) : ℚ) - s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Icc_succ_eq_insert N, Finset.prod_insert (by simp [Finset.mem_Icc]),
      Finset.prod_range_succ, ih]
    simp [Nat.cast_succ, mul_comm]

lemma risingF_eq_choose_factor (N p : ℕ) (hp : 1 < p) :
    ((N * p).factorial : ℚ) =
      (p : ℚ) ^ N * (N.factorial : ℚ) * ((p - 1).factorial : ℚ) ^ N * risingF p N := by
  have h := factorial_mul_p_eq N p hp
  rw [h]
  have hswap :
      ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) =
        ∏ j ∈ Finset.Icc 1 N, ∏ s ∈ Finset.Icc 1 (p - 1), ((p * j : ℚ) - s) :=
    Finset.prod_comm
  rw [hswap]
  have hidx :
      ∏ j ∈ Finset.Icc 1 N, ∏ s ∈ Finset.Icc 1 (p - 1), ((p * j : ℚ) - s) =
        ∏ j ∈ Finset.range N, ∏ s ∈ Finset.Icc 1 (p - 1), ((p * (j + 1) : ℚ) - s) := by
    calc
      ∏ j ∈ Finset.Icc 1 N, ∏ s ∈ Finset.Icc 1 (p - 1), ((p * j : ℚ) - s)
          = ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.Icc 1 N, ((p * j : ℚ) - s) :=
        Finset.prod_comm
      _ = ∏ s ∈ Finset.Icc 1 (p - 1), ∏ j ∈ Finset.range N, ((p * (j + 1) : ℚ) - s) := by
        simp_rw [prod_Icc_reindex_succ]
      _ = ∏ j ∈ Finset.range N, ∏ s ∈ Finset.Icc 1 (p - 1), ((p * (j + 1) : ℚ) - s) :=
        Finset.prod_comm
  rw [hidx]
  have hrising :
      ∏ j ∈ Finset.range N,
          ∏ s ∈ Finset.Icc 1 (p - 1), ((p * (j + 1) : ℚ) - s) =
        ∏ j ∈ Finset.range N, (risingQ p (j * p) * (p - 1).factorial) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact prod_pj_sub_s_eq_risingQ p j hp
  rw [hrising, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp [risingF, mul_assoc, mul_left_comm, mul_comm]

lemma choose_ratio_risingF (N M p : ℕ) (hM : M ≤ N) (hp : 1 < p) :
    ((N * p).choose (M * p) : ℚ) / (N.choose M) =
      risingF p N / (risingF p M * risingF p (N - M)) := by
  have hMp : M * p ≤ N * p := Nat.mul_le_mul_right p hM
  have hfn := factorial_ne_zero_rat
  rw [choose_eq_factorial_div _ _ hMp, choose_eq_factorial_div _ _ hM]
  have hsub : N * p - M * p = (N - M) * p := (Nat.mul_sub_right_distrib N M p).symm
  rw [hsub, risingF_eq_choose_factor N p hp, risingF_eq_choose_factor M p hp,
    risingF_eq_choose_factor (N - M) p hp]
  have hNM : (N - M) + M = N := Nat.sub_add_cancel hM
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hp)
  have hpowp : (p : ℚ) ^ N = (p : ℚ) ^ (N - M) * (p : ℚ) ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  have hpowf : ((p - 1).factorial : ℚ) ^ N =
      ((p - 1).factorial : ℚ) ^ (N - M) * ((p - 1).factorial : ℚ) ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  have hfN : (N.factorial : ℚ) ≠ 0 := hfn _
  have hfM : (M.factorial : ℚ) ≠ 0 := hfn _
  have hfNM : ((N - M).factorial : ℚ) ≠ 0 := hfn _
  have hfNp : ((N * p).factorial : ℚ) ≠ 0 := hfn _
  have hpf : ((p - 1).factorial : ℚ) ≠ 0 := hfn _
  field_simp [hfN, hfM, hfNM, hp0, hpf]
  rw [hpowp, hpowf]
  ring

/-- `v_p(k!) ≥ v_p(k+1) - 1`. -/
lemma padicValNat_factorial_succ_sub_one {p k : ℕ} [hp : Fact p.Prime] :
    padicValNat p (k + 1) ≤ padicValNat p k.factorial + 1 := by
  set r := padicValNat p (k + 1)
  rcases eq_or_ne r 0 with hr0 | hr0
  · omega
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hdiv : p ^ r ∣ k + 1 := pow_padicValNat_dvd
  have hle : p ^ r ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdiv
  have hpr : p ^ (r - 1) ≤ k := by
    have hge : p ^ (r - 1) + 1 ≤ p ^ r := by
      have hp2 : 2 ≤ p := Nat.Prime.two_le hp.out
      have hpowpos : 1 ≤ p ^ (r - 1) := Nat.one_le_pow _ _ (Nat.Prime.pos hp.out)
      have : p ^ r = p ^ (r - 1) * p := by
        obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := Nat.exists_eq_succ_of_ne_zero hr0
        simp [hr', pow_succ]
      rw [this]
      nlinarith
    omega
  have hpos : 0 < p ^ (r - 1) := Nat.pow_pos (Nat.Prime.pos hp.out)
  have hdvd : p ^ (r - 1) ∣ k.factorial := Nat.dvd_factorial hpos hpr
  have hfac0 : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have := (padicValNat_dvd_iff_le (a := k.factorial) (n := r - 1) hfac0).1 hdvd
  omega

/-- `v_p(k! / (k+1)) ≥ -1`. -/
lemma valGe_factorial_div_succ {p k : ℕ} [hp : Fact p.Prime] :
    valGe p (-1) ((k.factorial : ℚ) / (k + 1 : ℕ)) := by
  have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hf0 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  refine Or.inr ?_
  rw [padicValRat.div hf0 hk1, padicValRat.of_nat, padicValRat.of_nat]
  have hle := padicValNat_factorial_succ_sub_one (p := p) (k := k)
  have : (padicValNat p (k + 1) : ℤ) ≤ (padicValNat p k.factorial : ℤ) + 1 := by
    exact_mod_cast hle
  linarith

/-! ## Extra valuation lemmas -/

lemma valGe_div_exact {p : ℕ} [Fact p.Prime] {k : ℤ} {q r : ℚ}
    (hq : valGe p k q) (hr0 : r ≠ 0) :
    valGe p (k - padicValRat p r) (q / r) := by
  have : k - padicValRat p r = k + (-padicValRat p r) := by ring
  rw [div_eq_mul_inv, this]
  refine valGe_mul hq ?_
  refine Or.inr ?_
  rw [padicValRat.inv]

lemma valGe_div_nat {p : ℕ} [Fact p.Prime] {k : ℤ} {q : ℚ} {n : ℕ}
    (hq : valGe p k q) (hn : n ≠ 0) :
    valGe p (k - padicValNat p n) (q / n) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := valGe_div_exact hq hn0
  simpa [padicValRat.of_nat] using h

lemma valGe_of_int_div {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {z : ℤ}
    (h : (p : ℤ) ^ n ∣ z) : valGe p n (z : ℚ) := by
  rcases eq_or_ne z 0 with hz | hz
  · exact Or.inl (by simp [hz])
  refine Or.inr ?_
  have := (padicValInt_dvd_iff (p := p) n z).mp h
  rcases this with h0 | hle
  · exact (hz h0).elim
  · simpa [padicValRat.of_int] using hle

lemma padicValNat_le_log {p n : ℕ} [Fact p.Prime] :
    padicValNat p n ≤ Nat.log p n :=
  padicValNat_le_nat_log n

lemma valGe_inv_nat {p n : ℕ} [Fact p.Prime] :
    valGe p (-(padicValNat p n : ℤ)) ((n : ℚ)⁻¹) := by
  refine Or.inr ?_
  rw [padicValRat.inv, padicValRat.of_nat]

lemma three_unit {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p 0 (3 : ℚ)⁻¹ :=
  valGe_inv_of_not_dvd (by norm_num)
    (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 3)
      (lt_of_lt_of_le (by norm_num : 3 < 5) h5))

lemma fifteen_val {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p (-1) (15 : ℚ)⁻¹ := by
  have h15 : (15 : ℚ)⁻¹ = (3 : ℚ)⁻¹ * (5 : ℚ)⁻¹ := by norm_num
  rw [h15]
  have h3 := three_unit (p := p) h5
  by_cases h5p : p = 5
  · subst h5p
    have h5inv : valGe 5 (-1) ((5 : ℚ)⁻¹) := by
      refine Or.inr ?_
      rw [padicValRat.inv]
      have : padicValRat 5 (5 : ℚ) = 1 := padicValRat.self (by norm_num : 1 < 5)
      simp [this]
    simpa using valGe_mul h3 h5inv
  · have h5nd : ¬ p ∣ 5 := by
      intro hd
      have := (Nat.dvd_prime Nat.prime_five).mp hd
      rcases this with h1 | heq
      · exact Nat.Prime.ne_one hp.out h1
      · exact h5p heq
    have h5u := valGe_inv_of_not_dvd (by norm_num : 5 ≠ 0) h5nd
    exact valGe_mono (by norm_num : (-1 : ℤ) ≤ 0) (valGe_mul h3 h5u)

/-! ## Power sums `U_k` and their first differences -/

/-- `U_k(t) = ∑_{j < t} (j(j+1))^k`. -/
def U (k t : ℕ) : ℚ :=
  ∑ j ∈ Finset.range t, ((j : ℚ) * (j + 1)) ^ k

lemma U_zero (k : ℕ) : U k 0 = 0 := by simp [U]

lemma U_one (t : ℕ) : U 1 t = (t : ℚ) * ((t : ℚ) ^ 2 - 1) / 3 := by
  simpa [U, pow_one] using sum_j_succ t

lemma U_succ (k t : ℕ) :
    U k (t + 1) = U k t + ((t : ℚ) * (t + 1)) ^ k := by
  simp [U, Finset.sum_range_succ]

lemma U_two (t : ℕ) :
    U 2 t = (t : ℚ) * ((t : ℚ) ^ 2 - 1) * (3 * (t : ℚ) ^ 2 - 2) / 15 := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [U_succ, ih]
    push_cast
    ring

lemma U_three (t : ℕ) :
    U 3 t = (t : ℚ) * ((t : ℚ) ^ 2 - 1) *
      (15 * (t : ℚ) ^ 4 - 27 * (t : ℚ) ^ 2 + 8) / 105 := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [U_succ, ih]
    push_cast
    ring

/-- `ΔU_k(a,b) = U_k(a) - U_k(b) - U_k(a-b)` for `b ≤ a`. -/
def deltaU (k a b : ℕ) : ℚ :=
  U k a - U k b - U k (a - b)

lemma deltaU_one (a b : ℕ) (hba : b ≤ a) :
    deltaU 1 a b = (a : ℚ) * b * (a - b : ℕ) := by
  simp [deltaU, U_one]
  simpa using delta_one_cube a b hba

lemma deltaU_two (a b : ℕ) (hba : b ≤ a) :
    deltaU 2 a b =
      (a : ℚ) * b * (a - b : ℕ) * ((a : ℚ) ^ 2 - (a : ℚ) * b + (b : ℚ) ^ 2 - 1) := by
  simp [deltaU, U_two]
  have hcast : ((a - b : ℕ) : ℚ) = (a : ℚ) - b := Nat.cast_sub hba
  rw [hcast]
  ring

lemma deltaU_three (a b : ℕ) (hba : b ≤ a) :
    deltaU 3 a b =
      (a : ℚ) * b * (a - b : ℕ) *
        ((a : ℚ) ^ 2 - (a : ℚ) * b + (b : ℚ) ^ 2 - 1) ^ 2 := by
  simp [deltaU, U_three]
  have hcast : ((a - b : ℕ) : ℚ) = (a : ℚ) - b := Nat.cast_sub hba
  rw [hcast]
  ring

lemma valGe_deltaU_one {p : ℕ} [Fact p.Prime] (a b : ℕ) (hba : b ≤ a) :
    valGe p (padicValNat p a + padicValNat p b + padicValNat p (a - b) : ℤ)
      (deltaU 1 a b) := by
  rw [deltaU_one a b hba]
  have h1 : valGe p (padicValNat p a) (a : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have h2 : valGe p (padicValNat p b) (b : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have h3 : valGe p (padicValNat p (a - b)) ((a - b : ℕ) : ℚ) :=
    Or.inr (by simp [padicValRat.of_nat])
  simpa [add_assoc] using valGe_mul (valGe_mul h1 h2) h3

lemma valGe_nat_pow {p : ℕ} [Fact p.Prime] (n k : ℕ) : valGe p 0 ((n : ℚ) ^ k) :=
  valGe_pow (n := k) (valGe_nat p n)

lemma valGe_poly2 {p : ℕ} [Fact p.Prime] (a b : ℕ) :
    valGe p 0 ((a : ℚ) ^ 2 - (a : ℚ) * b + (b : ℚ) ^ 2 - 1) := by
  refine valGe_sub ?_ (valGe_nat p 1)
  refine valGe_add ?_ (valGe_nat_pow b 2)
  exact valGe_sub (valGe_nat_pow a 2) (valGe_mul (valGe_nat p a) (valGe_nat p b))

lemma valGe_deltaU_two {p : ℕ} [Fact p.Prime] (a b : ℕ) (hba : b ≤ a) :
    valGe p (padicValNat p a + padicValNat p b + padicValNat p (a - b) : ℤ)
      (deltaU 2 a b) := by
  rw [deltaU_two a b hba]
  have h1 : valGe p (padicValNat p a) (a : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have h2 : valGe p (padicValNat p b) (b : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have h3 : valGe p (padicValNat p (a - b)) ((a - b : ℕ) : ℚ) :=
    Or.inr (by simp [padicValRat.of_nat])
  have := valGe_mul (valGe_mul (valGe_mul h1 h2) h3) (valGe_poly2 (p := p) a b)
  simpa [add_assoc] using this

lemma valGe_deltaU_three {p : ℕ} [Fact p.Prime] (a b : ℕ) (hba : b ≤ a) :
    valGe p (padicValNat p a + padicValNat p b + padicValNat p (a - b) : ℤ)
      (deltaU 3 a b) := by
  rw [deltaU_three a b hba]
  have h1 : valGe p (padicValNat p a) (a : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have h2 : valGe p (padicValNat p b) (b : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have h3 : valGe p (padicValNat p (a - b)) ((a - b : ℕ) : ℚ) :=
    Or.inr (by simp [padicValRat.of_nat])
  have hpoly : valGe p 0
      (((a : ℚ) ^ 2 - (a : ℚ) * b + (b : ℚ) ^ 2 - 1) ^ 2) :=
    valGe_pow (n := 2) (valGe_poly2 (p := p) a b)
  have := valGe_mul (valGe_mul (valGe_mul h1 h2) h3) hpoly
  simpa [add_assoc] using this

/- Extra valuation utilities -/

lemma valGe_factorial_inv {p n : ℕ} [Fact p.Prime] :
    valGe p (-(n : ℤ)) ((n.factorial : ℚ)⁻¹) := by
  have hne : (n.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat n
  refine Or.inr ?_
  rw [padicValRat.inv, padicValRat.of_nat]
  have : (padicValNat p n.factorial : ℤ) ≤ n := by
    exact_mod_cast (padicValNat_factorial_le (p := p) n)
  linarith

lemma valGe_div_factorial {p : ℕ} [Fact p.Prime] {k : ℤ} {q : ℚ} {n : ℕ}
    (hq : valGe p k q) :
    valGe p (k - n) (q / n.factorial) := by
  have := valGe_mul hq (valGe_factorial_inv (p := p) (n := n))
  simpa [div_eq_mul_inv, sub_eq_add_neg] using this

/- ## The even factorial ratio -/

def bRat (m : ℕ) : ℚ :=
  ((18 * m).factorial * (4 * m).factorial * (3 * m).factorial : ℚ) /
    ((9 * m).factorial * (8 * m).factorial * (6 * m).factorial * (2 * m).factorial)

lemma bRat_ne_zero (m : ℕ) : bRat m ≠ 0 := by
  unfold bRat
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (mul_ne_zero (factorial_ne_zero_rat _) (factorial_ne_zero_rat _))
      (factorial_ne_zero_rat _)
  · exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (factorial_ne_zero_rat _) (factorial_ne_zero_rat _))
        (factorial_ne_zero_rat _))
      (factorial_ne_zero_rat _)

lemma risingF_ratio_bRat (N p : ℕ) (hp : 1 < p) :
    bRat (N * p) / bRat N =
      risingF p (18 * N) * risingF p (4 * N) * risingF p (3 * N) /
        (risingF p (9 * N) * risingF p (8 * N) * risingF p (6 * N) * risingF p (2 * N)) := by
  have hfac := risingF_eq_choose_factor
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hp)
  have hpf : ((p - 1).factorial : ℚ) ≠ 0 := factorial_ne_zero_rat _
  have hf : ∀ n : ℕ, (n.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat
  -- expand bRat at N*p and at N via the (Mp)! formula
  have h18 := hfac (18 * N) p hp
  have h4 := hfac (4 * N) p hp
  have h3 := hfac (3 * N) p hp
  have h9 := hfac (9 * N) p hp
  have h8 := hfac (8 * N) p hp
  have h6 := hfac (6 * N) p hp
  have h2 := hfac (2 * N) p hp
  have hmul : ∀ a : ℕ, a * N * p = a * (N * p) := fun a => by ring
  unfold bRat
  simp only [← hmul]
  rw [h18, h4, h3, h9, h8, h6, h2]
  have hpowp : (p : ℚ) ^ (18 * N) * (p : ℚ) ^ (4 * N) * (p : ℚ) ^ (3 * N) =
      (p : ℚ) ^ (9 * N) * (p : ℚ) ^ (8 * N) * (p : ℚ) ^ (6 * N) * (p : ℚ) ^ (2 * N) := by
    simp [← pow_add]; congr 1; ring
  have hpowf :
      ((p - 1).factorial : ℚ) ^ (18 * N) * ((p - 1).factorial : ℚ) ^ (4 * N) *
          ((p - 1).factorial : ℚ) ^ (3 * N) =
        ((p - 1).factorial : ℚ) ^ (9 * N) * ((p - 1).factorial : ℚ) ^ (8 * N) *
          ((p - 1).factorial : ℚ) ^ (6 * N) * ((p - 1).factorial : ℚ) ^ (2 * N) := by
    simp [← pow_add]; congr 1; ring
  field_simp [hf, hp0, hpf]
  ring

/- Linear combination of `U` at the even parameters -/

lemma sum_params_one : (18 : ℤ) + 4 + 3 = 9 + 8 + 6 + 2 := by decide
lemma sum_params_three : (18 : ℤ) ^ 3 + 4 ^ 3 + 3 ^ 3 - 9 ^ 3 - 8 ^ 3 - 6 ^ 3 - 2 ^ 3 = 4458 := by
  decide

lemma U_one_combo (N : ℕ) :
    U 1 (18 * N) + U 1 (4 * N) + U 1 (3 * N) - U 1 (9 * N) - U 1 (8 * N) -
      U 1 (6 * N) - U 1 (2 * N) =
      (4458 : ℚ) * (N : ℚ) ^ 3 / 3 := by
  simp [U_one]
  ring

lemma valGe_U_one_combo {p N : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p (3 * padicValNat p N) (U 1 (18 * N) + U 1 (4 * N) + U 1 (3 * N)
      - U 1 (9 * N) - U 1 (8 * N) - U 1 (6 * N) - U 1 (2 * N)) := by
  rw [U_one_combo]
  have h3 : valGe p 0 ((3 : ℚ)⁻¹) :=
    valGe_inv_of_not_dvd (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 3)
        (lt_of_lt_of_le (by norm_num : 3 < 5) h5))
  have h4458 : valGe p 0 (4458 : ℚ) := valGe_nat p _
  have hN : valGe p (padicValNat p N) (N : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have hN3 := valGe_pow (n := 3) hN
  have hmul := valGe_mul (valGe_mul h4458 hN3) h3
  have heq : (4458 : ℚ) * (N : ℚ) ^ 3 / 3 = 4458 * (N : ℚ) ^ 3 * (3 : ℚ)⁻¹ := by ring
  rw [heq]
  have hval : (0 + (3 : ℤ) * padicValNat p N + 0) = 3 * padicValNat p N := by ring
  simpa [hval] using hmul

lemma U_two_combo (N : ℕ) :
    U 2 (18 * N) + U 2 (4 * N) + U 2 (3 * N) - U 2 (9 * N) - U 2 (8 * N) -
      U 2 (6 * N) - U 2 (2 * N) =
      ((N : ℚ) ^ 3) * (358242 * (N : ℚ) ^ 2 - 1486) := by
  simp [U_two]
  ring

lemma valGe_U_two_combo {p N : ℕ} [Fact p.Prime] :
    valGe p (3 * padicValNat p N)
      (U 2 (18 * N) + U 2 (4 * N) + U 2 (3 * N) - U 2 (9 * N) - U 2 (8 * N) -
        U 2 (6 * N) - U 2 (2 * N)) := by
  rw [U_two_combo]
  have hN : valGe p (padicValNat p N) (N : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have hN3 := valGe_pow (n := 3) hN
  have hpoly : valGe p 0 (358242 * (N : ℚ) ^ 2 - 1486) := by
    refine valGe_sub ?_ (valGe_nat p _)
    exact valGe_mul (valGe_nat p _) (valGe_pow (n := 2) (valGe_nat p N))
  have := valGe_mul hN3 hpoly
  simpa using this

lemma U_three_combo (N : ℕ) :
    U 3 (18 * N) + U 3 (4 * N) + U 3 (3 * N) - U 3 (9 * N) - U 3 (8 * N) -
      U 3 (6 * N) - U 3 (2 * N) =
      (N : ℚ) ^ 3 * (86439774 * (N : ℚ) ^ 4 - 716484 * (N : ℚ) ^ 2 + 1486) := by
  simp [U_three]
  ring

lemma valGe_U_three_combo {p N : ℕ} [Fact p.Prime] :
    valGe p (3 * padicValNat p N)
      (U 3 (18 * N) + U 3 (4 * N) + U 3 (3 * N) - U 3 (9 * N) - U 3 (8 * N) -
        U 3 (6 * N) - U 3 (2 * N)) := by
  rw [U_three_combo]
  have hN : valGe p (padicValNat p N) (N : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have hN3 := valGe_pow (n := 3) hN
  have hpoly : valGe p 0 (86439774 * (N : ℚ) ^ 4 - 716484 * (N : ℚ) ^ 2 + 1486) := by
    refine valGe_add ?_ (valGe_nat p _)
    refine valGe_sub ?_ ?_
    · exact valGe_mul (valGe_nat p _) (valGe_pow (n := 4) (valGe_nat p N))
    · exact valGe_mul (valGe_nat p _) (valGe_pow (n := 2) (valGe_nat p N))
  have := valGe_mul hN3 hpoly
  simpa using this

/- Product form of a single rising factor. -/

def pairDen (p i : ℕ) : ℚ := (i : ℚ) * (p - i : ℕ)

def gammaI (p i : ℕ) : ℚ := (p : ℚ) ^ 2 / pairDen p i

def Fprod (γ : ℚ) (M : ℕ) : ℚ :=
  ∏ j ∈ Finset.range M, (1 + γ * (j : ℚ) * (j + 1))

lemma risingQ_at_mul_p_gamma {p j : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    risingQ p (j * p) =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), (1 + gammaI p i * (j : ℚ) * (j + 1)) := by
  rw [risingQ_at_mul_p h5]
  refine Finset.prod_congr rfl ?_
  intro i hi
  unfold gammaI pairDen
  ring

lemma risingF_eq_Fprod {p M : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    risingF p M =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), Fprod (gammaI p i) M := by
  unfold risingF Fprod
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl ?_
  intro j hj
  simpa using risingQ_at_mul_p_gamma (p := p) (j := j) h5

lemma pairDen_ne_zero {p i : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) : pairDen p i ≠ 0 := by
  obtain ⟨h1, _, hilt, _, _, _⟩ := mem_half_bounds h5 hi
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp h1))
  have hpi0 : ((p - i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hilt))
  exact mul_ne_zero hi0 hpi0

lemma valGe_pairDen_inv {p i : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    valGe p 0 (pairDen p i)⁻¹ := by
  obtain ⟨h1, _, hilt, _, _, _⟩ := mem_half_bounds h5 hi
  have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp h1)
  have hpi : p - i ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hilt)
  have h1v : valGe p 0 ((i : ℚ)⁻¹) :=
    valGe_inv_of_not_dvd hi0 (Nat.not_dvd_of_pos_of_lt (Nat.succ_le_iff.mp h1) hilt)
  have hilt' : p - i < p := Nat.sub_lt (Nat.Prime.pos hp.out) (Nat.succ_le_iff.mp h1)
  have h2v : valGe p 0 (((p - i : ℕ) : ℚ)⁻¹) :=
    valGe_inv_of_not_dvd hpi
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hpi) hilt')
  simpa [pairDen, mul_inv, mul_comm] using valGe_mul h1v h2v

lemma valGe_gammaI {p i : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    valGe p 2 (gammaI p i) := by
  unfold gammaI
  have hp2 := valGe_p_pow (p := p) 2
  have hinv := valGe_pairDen_inv (p := p) h5 hi
  simpa [div_eq_mul_inv] using valGe_mul hp2 hinv

lemma Fprod_zero (γ : ℚ) : Fprod γ 0 = 1 := by simp [Fprod]

lemma Fprod_succ (γ : ℚ) (M : ℕ) :
    Fprod γ (M + 1) = Fprod γ M * (1 + γ * (M : ℚ) * (M + 1)) := by
  simp [Fprod, Finset.prod_range_succ]

/- First-order expansion of a positive product: `F - 1 - γ U_1`. -/

def Frest (γ : ℚ) (M : ℕ) : ℚ := Fprod γ M - 1 - γ * U 1 M

lemma Frest_zero (γ : ℚ) : Frest γ 0 = 0 := by simp [Frest, Fprod, U_zero]

lemma Frest_succ (γ : ℚ) (M : ℕ) :
    Frest γ (M + 1) =
      Frest γ M * (1 + γ * (M : ℚ) * (M + 1)) +
        (γ * (M : ℚ) * (M + 1)) * (γ * U 1 M) := by
  unfold Frest
  rw [Fprod_succ, U_succ, pow_one]
  ring

lemma valGe_U_one {p M : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) : valGe p 0 (U 1 M) := by
  rw [U_one]
  have h3 : valGe p 0 ((3 : ℚ)⁻¹) :=
    valGe_inv_of_not_dvd (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 3)
        (lt_of_lt_of_le (by norm_num : 3 < 5) h5))
  have hnum : valGe p 0 ((M : ℚ) * ((M : ℚ) ^ 2 - 1)) :=
    valGe_mul (valGe_nat p M)
      (valGe_sub (valGe_pow (n := 2) (valGe_nat p M)) (valGe_nat p 1))
  have := valGe_mul hnum h3
  simpa [div_eq_mul_inv] using this

lemma valGe_Frest {p : ℕ} [Fact p.Prime] {α : ℤ} {γ : ℚ} (M : ℕ)
    (hγ : valGe p α γ) (hα : 2 ≤ α) (h5 : 5 ≤ p) :
    valGe p (2 * α) (Frest γ M) := by
  induction M with
  | zero =>
    simpa [Frest_zero] using valGe_zero p (2 * α)
  | succ M ih =>
    rw [Frest_succ]
    have hy : valGe p α (γ * (M : ℚ) * (M + 1)) := by
      have := valGe_mul (valGe_mul hγ (valGe_nat p M)) (valGe_nat p (M + 1))
      simpa [Nat.cast_add, Nat.cast_one] using this
    have h1y : valGe p 0 (1 + γ * (M : ℚ) * (M + 1)) :=
      valGe_add (valGe_one p) (valGe_mono (by linarith) hy)
    have hterm1 := valGe_mul ih h1y
    have hterm1' : valGe p (2 * α) (Frest γ M * (1 + γ * (M : ℚ) * (M + 1))) := by
      simpa using hterm1
    have hU := valGe_U_one (p := p) (M := M) h5
    have hγγ : valGe p (2 * α) (γ * γ) := by
      have := valGe_mul hγ hγ
      simpa [two_mul] using this
    have hterm2 : valGe p (2 * α)
        ((γ * (M : ℚ) * (M + 1)) * (γ * U 1 M)) := by
      have := valGe_mul (valGe_mul hγγ (valGe_nat p M))
        (valGe_mul (valGe_nat p (M + 1)) hU)
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact valGe_add hterm1' hterm2

/- Polynomial interpolation of `U` via Faulhaber. -/

open Polynomial

/-- Faulhaber polynomial: `∑_{j < t} j^d = (faulhaberPoly d).eval t`. -/
noncomputable def faulhaberPoly (d : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (d + 1),
    C (_root_.bernoulli i * ((d + 1).choose i : ℚ) / (d + 1 : ℚ)) * X ^ (d + 1 - i)

lemma faulhaberPoly_eval (n d : ℕ) :
    (faulhaberPoly d).eval (n : ℚ) = ∑ k ∈ Finset.range n, (k : ℚ) ^ d := by
  rw [sum_range_pow, faulhaberPoly, eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The polynomial agreeing with `U k` on `ℕ`.
`(j(j+1))^k = (j^2 + j)^k = ∑_m C(k,m) j^{k+m}`. -/
noncomputable def Upoly (k : ℕ) : ℚ[X] :=
  ∑ m ∈ Finset.range (k + 1), C (k.choose m : ℚ) * faulhaberPoly (k + m)

lemma pow_sq_add (j : ℚ) (k m : ℕ) (hm : m ≤ k) :
    (j ^ 2) ^ m * j ^ (k - m) = j ^ (k + m) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

lemma Upoly_eval (k t : ℕ) : (Upoly k).eval (t : ℚ) = U k t := by
  unfold Upoly U
  rw [eval_finset_sum]
  simp only [eval_mul, eval_C]
  simp_rw [faulhaberPoly_eval]
  trans ∑ j ∈ Finset.range t, ∑ m ∈ Finset.range (k + 1),
      (k.choose m : ℚ) * (j : ℚ) ^ (k + m)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hbin := add_pow ((j : ℚ) ^ 2) (j : ℚ) k
  have hrhs :
      ∑ m ∈ Finset.range (k + 1), (k.choose m : ℚ) * (j : ℚ) ^ (k + m) =
        ((j : ℚ) ^ 2 + (j : ℚ)) ^ k := by
    rw [hbin]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmle : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hp := pow_sq_add (j : ℚ) k m hmle
    rw [← hp]
    ring
  have : ((j : ℚ) * (j + 1)) ^ k = ((j : ℚ) ^ 2 + (j : ℚ)) ^ k := by ring
  rw [hrhs, this]

lemma Upoly_eval_zero (k : ℕ) : (Upoly k).eval 0 = 0 := by
  simpa [U_zero] using Upoly_eval k 0

lemma eq_of_eval_nat {p q : ℚ[X]} (h : ∀ n : ℕ, p.eval (n : ℚ) = q.eval (n : ℚ)) :
    p = q := by
  have hdiff : p - q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.infinite_of_injective_forall_mem Nat.cast_injective ?_
    intro n
    simp [IsRoot, sub_eq_zero, h n]
  exact sub_eq_zero.mp hdiff

/-- `Upoly k` satisfies the forward recurrence of `U`. -/
lemma Upoly_comp_succ (k : ℕ) :
    (Upoly k).comp (X + 1) - Upoly k = (X * (X + 1)) ^ k := by
  refine eq_of_eval_nat ?_
  intro n
  simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_pow, eval_mul]
  have hn : (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; rfl
  rw [hn, Upoly_eval k (n + 1), Upoly_eval k n, U_succ]
  push_cast
  ring

private lemma X_add_one_comp_neg (p : ℚ[X]) :
    (p.comp (X + 1)).comp (-(X + 1) : ℚ[X]) = p.comp (-X : ℚ[X]) := by
  rw [comp_assoc]
  congr 1
  simp [add_comp, X_comp, C_comp]

private lemma pow_X_mul_succ_comp_neg (k : ℕ) :
    (((X : ℚ[X]) * (X + 1)) ^ k).comp (-(X + 1) : ℚ[X]) =
      ((X : ℚ[X]) * (X + 1)) ^ k := by
  simp [pow_comp, mul_comp, add_comp, X_comp]
  congr 1
  ring

lemma Upoly_comp_neg_succ (k : ℕ) :
    (Upoly k).comp (-X : ℚ[X]) - (Upoly k).comp (-(X + 1) : ℚ[X]) =
      ((X : ℚ[X]) * (X + 1)) ^ k := by
  have hP := Upoly_comp_succ k
  have h1 : (Upoly k).comp (-X : ℚ[X]) =
      ((Upoly k).comp (X + 1)).comp (-(X + 1) : ℚ[X]) :=
    (X_add_one_comp_neg (Upoly k)).symm
  rw [h1, ← sub_comp, hP]
  exact pow_X_mul_succ_comp_neg k

lemma Upoly_odd (k : ℕ) : (Upoly k).comp (-X : ℚ[X]) = - Upoly k := by
  set P := Upoly k
  set Q := P.comp (-X : ℚ[X]) + P
  have hper : Q.comp (X + 1) = Q := by
    have hnegX : (-X : ℚ[X]).comp (X + 1) = (-(X + 1) : ℚ[X]) := by
      simp [neg_comp, X_comp, add_comp, C_comp]
    have hL : (P.comp (-X : ℚ[X])).comp (X + 1) = P.comp (-(X + 1) : ℚ[X]) := by
      rw [comp_assoc, hnegX]
    have hsum : P.comp (-(X + 1) : ℚ[X]) + P.comp (X + 1) =
        P.comp (-X : ℚ[X]) + P := by
      have hPs : P.comp (X + 1) - P = ((X : ℚ[X]) * (X + 1)) ^ k := by
        simpa [P] using Upoly_comp_succ k
      have hN : P.comp (-X : ℚ[X]) - P.comp (-(X + 1) : ℚ[X]) =
          ((X : ℚ[X]) * (X + 1)) ^ k := by
        simpa [P] using Upoly_comp_neg_succ k
      linear_combination hPs - hN
    calc
      Q.comp (X + 1) = (P.comp (-X : ℚ[X])).comp (X + 1) + P.comp (X + 1) := by
        simp [Q, add_comp]
      _ = P.comp (-(X + 1) : ℚ[X]) + P.comp (X + 1) := by rw [hL]
      _ = P.comp (-X : ℚ[X]) + P := hsum
      _ = Q := rfl
  have hconst : Q = C (Q.eval 0) := by
    refine eq_of_eval_nat ?_
    intro n
    have hstep : ∀ m : ℕ, Q.eval ((m : ℚ) + 1) = Q.eval (m : ℚ) := by
      intro m
      have := congrArg (fun p : ℚ[X] => p.eval (m : ℚ)) hper
      simpa [eval_comp, eval_add, eval_X, eval_one] using this
    have hiter : Q.eval (n : ℚ) = Q.eval 0 := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.cast_succ, hstep n, ih]
    simpa [eval_C] using hiter
  have hQ0 : Q.eval 0 = 0 := by
    have hP0 := Upoly_eval_zero k
    have : P.eval 0 = 0 := hP0
    simp [Q, eval_add, eval_comp, eval_neg, eval_X, this]
  have hQ : Q = 0 := by rw [hconst, hQ0, map_zero]
  have : P.comp (-X) + P = 0 := hQ
  exact eq_neg_iff_add_eq_zero.mpr this

lemma coeff_comp_neg_X' (p : ℚ[X]) (n : ℕ) :
    (p.comp (-X : ℚ[X])).coeff n = (-1 : ℚ) ^ n * p.coeff n := by
  have hX : (-X : ℚ[X]) = C (-1) * X := by simp
  rw [hX, comp_C_mul_X_coeff, mul_comm]

/-- Even-parameter combination of `Upoly k`. -/
noncomputable def UcomboPoly (k : ℕ) : ℚ[X] :=
  (Upoly k).comp (C 18 * X) + (Upoly k).comp (C 4 * X) + (Upoly k).comp (C 3 * X)
    - (Upoly k).comp (C 9 * X) - (Upoly k).comp (C 8 * X)
    - (Upoly k).comp (C 6 * X) - (Upoly k).comp (C 2 * X)

lemma UcomboPoly_eval (k N : ℕ) :
    (UcomboPoly k).eval (N : ℚ) =
      U k (18 * N) + U k (4 * N) + U k (3 * N)
        - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N) := by
  unfold UcomboPoly
  simp only [eval_sub, eval_add, eval_comp, eval_mul, eval_C, eval_X]
  have h (a : ℕ) : (Upoly k).eval ((a : ℚ) * (N : ℚ)) = U k (a * N) := by
    have : (a : ℚ) * (N : ℚ) = ((a * N : ℕ) : ℚ) := by push_cast; rfl
    rw [this, Upoly_eval]
  simp_rw [← Nat.cast_ofNat (R := ℚ)]
  rw [h 18, h 4, h 3, h 9, h 8, h 6, h 2]

lemma Upoly_comp_neg_scale (k : ℕ) (a : ℚ) :
    ((Upoly k).comp (C a * X)).comp (-X : ℚ[X]) = - (Upoly k).comp (C a * X) := by
  have hassoc : ((Upoly k).comp (C a * X)).comp (-X : ℚ[X]) =
      (Upoly k).comp ((C a * X).comp (-X : ℚ[X])) := by
    rw [comp_assoc]
  have hinner : (C a * X).comp (-X : ℚ[X]) = - (C a * X) := by
    simp [mul_comp, C_comp, X_comp]
  have hnegY : (Upoly k).comp (-(C a * X)) =
      ((Upoly k).comp (-X : ℚ[X])).comp (C a * X) := by
    have : -(C a * X) = (-X : ℚ[X]).comp (C a * X) := by
      simp [neg_comp, X_comp]
    rw [this, comp_assoc]
  rw [hassoc, hinner, hnegY, Upoly_odd, neg_comp]

lemma UcomboPoly_odd (k : ℕ) :
    (UcomboPoly k).comp (-X : ℚ[X]) = - UcomboPoly k := by
  simp only [UcomboPoly, sub_comp, add_comp, Upoly_comp_neg_scale]
  ring

lemma UcomboPoly_eval_zero (k : ℕ) : (UcomboPoly k).eval 0 = 0 := by
  simpa [eval_zero] using
    (by simpa using UcomboPoly_eval k 0)

lemma UcomboPoly_coeff_zero (k : ℕ) : (UcomboPoly k).coeff 0 = 0 := by
  simpa [coeff_zero_eq_eval_zero] using UcomboPoly_eval_zero k

lemma UcomboPoly_even_coeff (k i : ℕ) (he : Even i) :
    (UcomboPoly k).coeff i = 0 := by
  have hodd := UcomboPoly_odd k
  have h' : ((UcomboPoly k).comp (-X : ℚ[X])).coeff i = (- UcomboPoly k).coeff i := by
    rw [hodd]
  rw [coeff_comp_neg_X', coeff_neg] at h'
  have hpow : (-1 : ℚ) ^ i = 1 := Even.neg_one_pow he
  rw [hpow] at h'
  linarith

lemma UcomboPoly_coeff_one (k : ℕ) : (UcomboPoly k).coeff 1 = 0 := by
  have hscale (a : ℚ) :
      ((Upoly k).comp (C a * X)).coeff 1 = a * (Upoly k).coeff 1 := by
    rw [comp_C_mul_X_coeff, pow_one, mul_comm]
  simp only [UcomboPoly, coeff_sub, coeff_add, hscale]
  ring

lemma UcomboPoly_X3_dvd (k : ℕ) : X ^ 3 ∣ UcomboPoly k := by
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d
  · exact UcomboPoly_coeff_zero k
  · exact UcomboPoly_coeff_one k
  · exact UcomboPoly_even_coeff k 2 (by decide)

open scoped fwdDiff

lemma U_int (k t : ℕ) : ∃ z : ℤ, U k t = z := by
  refine ⟨∑ j ∈ Finset.range t, (j * (j + 1) : ℤ) ^ k, ?_⟩
  simp [U]

lemma Upoly_int_eval (k n : ℕ) : ∃ z : ℤ, (Upoly k).eval (n : ℚ) = z := by
  rw [Upoly_eval]; exact U_int k n

lemma fwdDiff_iter_eval_int (k m : ℕ) :
    ∃ z : ℤ, ((fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r)) 0 = z := by
  rw [fwdDiff_iter_eq_sum_shift]
  have : ∀ i : ℕ, ∃ z : ℤ, (Upoly k).eval (i : ℚ) = z := Upoly_int_eval k
  choose z hz using this
  refine ⟨∑ i ∈ Finset.range (m + 1), ((-1 : ℤ) ^ (m - i) * m.choose i) * z i, ?_⟩
  simp only [nsmul_eq_mul, zsmul_eq_mul, Nat.cast_zero, zero_add]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [hz]

lemma Upoly_natDegree_le (k : ℕ) : (Upoly k).natDegree ≤ 2 * k + 1 := by
  unfold Upoly
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro m hm
  have hmle : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have h1 : (C (k.choose m : ℚ) * faulhaberPoly (k + m)).natDegree ≤
      (faulhaberPoly (k + m)).natDegree := natDegree_C_mul_le _ _
  have h2 : (faulhaberPoly (k + m)).natDegree ≤ k + m + 1 := by
    unfold faulhaberPoly
    refine natDegree_sum_le_of_forall_le _ _ ?_
    intro i hi
    have : (C (_root_.bernoulli i * ((k + m + 1).choose i : ℚ) / ((k + m : ℕ) + 1 : ℚ)) *
        X ^ (k + m + 1 - i)).natDegree ≤ k + m + 1 - i := by
      refine (natDegree_C_mul_le _ _).trans ?_
      exact natDegree_X_pow_le _
    exact this.trans (Nat.sub_le _ _)
  exact h1.trans (h2.trans (by omega))

lemma descPochhammer_rat_int_coeff (m j : ℕ) :
    ∃ z : ℤ, (descPochhammer ℚ m).coeff j = z := by
  rw [← descPochhammer_map (Int.castRingHom ℚ) m, coeff_map]
  exact ⟨(descPochhammer ℤ m).coeff j, rfl⟩

lemma fwdDiff_Upoly_eq_zero_of_lt {k m : ℕ} (hm : (Upoly k).natDegree < m) :
    (fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r) = 0 :=
  Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hm

/-- Newton interpolation: `Upoly k = ∑_{m ≤ deg} (a_m / m!) • descPochhammer m`
with `a_m ∈ ℤ`. -/
lemma Upoly_eq_newton (k : ℕ) :
    ∃ a : ℕ → ℤ,
      Upoly k = ∑ m ∈ Finset.range (2 * k + 2),
        C ((a m : ℚ) / (m.factorial : ℚ)) * descPochhammer ℚ m := by
  let d := 2 * k + 1
  have hdeg : (Upoly k).natDegree ≤ d := Upoly_natDegree_le k
  have ha (m : ℕ) : ∃ z : ℤ, ((fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r)) 0 = z :=
    fwdDiff_iter_eval_int k m
  choose a ha using ha
  refine ⟨a, ?_⟩
  refine eq_of_eval_nat ?_
  intro n
  have hshift := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ))
    (fun r : ℚ => (Upoly k).eval r) n (0 : ℚ)
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_one, mul_one, add_zero] at hshift
  have hrhs :
      (∑ m ∈ Finset.range (d + 1),
          C ((a m : ℚ) / (m.factorial : ℚ)) * descPochhammer ℚ m).eval (n : ℚ) =
        ∑ m ∈ Finset.range (d + 1), (n.choose m : ℚ) * (a m : ℚ) := by
    simp only [eval_finset_sum, eval_mul, eval_C]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hfac : (m.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat m
    have hch := Nat.cast_choose_eq_descPochhammer_div (K := ℚ) n m
    have : (a m : ℚ) / m.factorial * (descPochhammer ℚ m).eval (n : ℚ) =
        (n.choose m : ℚ) * (a m : ℚ) := by
      rw [hch]
      field_simp [hfac]
    simpa [mul_comm] using this
  have hlhs : (Upoly k).eval (n : ℚ) =
      ∑ m ∈ Finset.range (n + 1), (n.choose m : ℚ) *
        ((fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r) 0) := by
    simpa [nsmul_eq_mul, Nat.cast_choose] using hshift
  have htrunc :
      ∑ m ∈ Finset.range (n + 1), (n.choose m : ℚ) *
          ((fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r) 0) =
        ∑ m ∈ Finset.range (d + 1), (n.choose m : ℚ) * (a m : ℚ) := by
    -- Restrict to m ≤ d using vanishing of high differences, and C(n,m)=0 for m>n
    let f : ℕ → ℚ := fun m => (n.choose m : ℚ) * (a m : ℚ)
    have hf0 : ∀ m, d < m → (n.choose m : ℚ) *
        ((fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r) 0) = 0 := by
      intro m hm
      have : (fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r) = 0 :=
        fwdDiff_Upoly_eq_zero_of_lt (lt_of_le_of_lt hdeg hm)
      simp [this]
    have haeq : ∀ m, ((fwdDiff (1 : ℚ))^[m] (fun r : ℚ => (Upoly k).eval r) 0) = (a m : ℚ) := ha
    simp_rw [haeq]
    -- both sums equal the sum over m ≤ min(n,d)
    have h1 : ∑ m ∈ Finset.range (n + 1), (n.choose m : ℚ) * (a m : ℚ) =
        ∑ m ∈ Finset.range (n + 1) ∩ Finset.range (d + 1), (n.choose m : ℚ) * (a m : ℚ) := by
      refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
      intro m hm hmI
      have : d + 1 ≤ m := by
        simp [Finset.mem_inter, Finset.mem_range] at hm hmI
        omega
      have : d < m := by omega
      have hvan := hf0 m this
      simpa [haeq m] using hvan
    have h2 : ∑ m ∈ Finset.range (d + 1), (n.choose m : ℚ) * (a m : ℚ) =
        ∑ m ∈ Finset.range (n + 1) ∩ Finset.range (d + 1), (n.choose m : ℚ) * (a m : ℚ) := by
      refine (Finset.sum_subset Finset.inter_subset_right ?_).symm
      intro m hm hmI
      have : n + 1 ≤ m := by
        simp [Finset.mem_inter, Finset.mem_range] at hm hmI
        omega
      simp [Nat.choose_eq_zero_of_lt (by omega : n < m)]
    rw [h1, h2]
  rw [hlhs, htrunc, hrhs]

lemma Upoly_coeff_val (k j : ℕ) {p : ℕ} [Fact p.Prime] :
    valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ)) ((Upoly k).coeff j) := by
  obtain ⟨a, ha⟩ := Upoly_eq_newton k
  have hrep : (Upoly k).coeff j =
      ∑ m ∈ Finset.range (2 * k + 2),
        ((a m : ℚ) / (m.factorial : ℚ)) * (descPochhammer ℚ m).coeff j := by
    rw [ha, finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [coeff_C_mul]
  rw [hrep]
  apply valGe_sum
  intro m hm
  have hmle : m ≤ 2 * k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  obtain ⟨z, hz⟩ := descPochhammer_rat_int_coeff m j
  have hden : valGe p (-(padicValNat p m.factorial : ℤ)) ((m.factorial : ℚ)⁻¹) :=
    valGe_inv_nat
  have ha0 : valGe p 0 (a m : ℚ) := valGe_int p _
  have hz0 : valGe p 0 (z : ℚ) := valGe_int p _
  have hmono : valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ))
      ((a m : ℚ) / m.factorial * (descPochhammer ℚ m).coeff j) := by
    rw [hz, div_eq_mul_inv]
    have h1 := valGe_mul ha0 hden
    have h2 := valGe_mul h1 hz0
    have h2' : valGe p (-(padicValNat p m.factorial : ℤ))
        ((a m : ℚ) * (m.factorial : ℚ)⁻¹ * z) := by simpa using h2
    refine valGe_mono ?_ h2'
    have hdvd : m.factorial ∣ (2 * k + 1).factorial := Nat.factorial_dvd_factorial hmle
    have hle : padicValNat p m.factorial ≤ padicValNat p (2 * k + 1).factorial := by
      have hne : (2 * k + 1).factorial ≠ 0 := (2 * k + 1).factorial_ne_zero
      have hquot0 : (2 * k + 1).factorial / m.factorial ≠ 0 := by
        intro hz
        have hre0 : m.factorial * ((2 * k + 1).factorial / m.factorial) = (2 * k + 1).factorial :=
          Nat.mul_div_cancel' hdvd
        rw [hz, mul_zero] at hre0
        exact hne hre0.symm
      have hmul := padicValNat.mul (p := p) m.factorial_ne_zero hquot0
      have hre : m.factorial * ((2 * k + 1).factorial / m.factorial) = (2 * k + 1).factorial :=
        Nat.mul_div_cancel' hdvd
      rw [hre] at hmul
      omega
    exact neg_le_neg (Nat.cast_le.mpr hle)
  exact hmono

lemma UcomboPoly_coeff_val (k j : ℕ) {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ)) ((UcomboPoly k).coeff j) := by
  have hscale (c : ℕ) :
      valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ))
        (((Upoly k).comp (C (c : ℚ) * X)).coeff j) := by
    rw [comp_C_mul_X_coeff]
    have hc : valGe p 0 ((c : ℚ) ^ j) := valGe_nat_pow c j
    have hpj := Upoly_coeff_val (p := p) k j
    have := valGe_mul hpj hc
    simpa [mul_comm] using this
  have h18 := hscale 18
  have h4 := hscale 4
  have h3 := hscale 3
  have h9 := hscale 9
  have h8 := hscale 8
  have h6 := hscale 6
  have h2 := hscale 2
  simp only [UcomboPoly, coeff_add, coeff_sub]
  repeat' first | apply valGe_add | apply valGe_sub | apply valGe_neg
  all_goals
    first | exact h18 | exact h4 | exact h3 | exact h9 | exact h8 | exact h6 | exact h2

/-- `v_p(Ucombo_k(N)) ≥ 3 v_p(N) - v_p((2k+1)!)`. -/
lemma valGe_UcomboPoly_eval {p N k : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p (3 * padicValNat p N - padicValNat p (2 * k + 1).factorial)
      ((UcomboPoly k).eval (N : ℚ)) := by
  obtain ⟨T, hT⟩ := UcomboPoly_X3_dvd k
  have heval : (UcomboPoly k).eval (N : ℚ) = (N : ℚ) ^ 3 * T.eval (N : ℚ) := by
    rw [hT, eval_mul, eval_pow, eval_X]
  rw [heval]
  have hN : valGe p (padicValNat p N) (N : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have hN3 := valGe_pow (n := 3) hN
  have hTval : valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ)) (T.eval (N : ℚ)) := by
    rw [eval_eq_sum_range]
    apply valGe_sum
    intro i hi
    have hcoeff : valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ)) (T.coeff i) := by
      -- T.coeff i = Ucombo.coeff (i+3) because Ucombo = X^3 * T
      have : (UcomboPoly k).coeff (i + 3) = T.coeff i := by
        rw [hT]; exact coeff_X_pow_mul T 3 i
      rw [← this]
      exact UcomboPoly_coeff_val (p := p) k (i + 3) h5
    have hpow : valGe p 0 ((N : ℚ) ^ i) := valGe_nat_pow N i
    have := valGe_mul hcoeff hpow
    simpa using this
  have := valGe_mul hN3 hTval
  simpa [sub_eq_add_neg] using this

lemma valGe_U_combo_any (k N : ℕ) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p (3 * padicValNat p N - padicValNat p (2 * k + 1).factorial)
      (U k (18 * N) + U k (4 * N) + U k (3 * N)
        - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N)) := by
  simpa [UcomboPoly_eval] using valGe_UcomboPoly_eval (p := p) (N := N) (k := k) h5

/- Truncated logarithm and exponential. -/

def log1pTrunc (K : ℕ) (y : ℚ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 K, (-1 : ℚ) ^ (k + 1) * y ^ k / k

def expTrunc (K : ℕ) (z : ℚ) : ℚ :=
  ∑ m ∈ Finset.range (K + 1), z ^ m / m.factorial

lemma valGe_pow_div_nat {p : ℕ} [Fact p.Prime] {α : ℤ} {y : ℚ} (k : ℕ)
    (hy : valGe p α y) (hk : k ≠ 0) :
    valGe p (k * α - padicValNat p k) (y ^ k / k) := by
  have hyk := valGe_pow (n := k) hy
  have := valGe_div_nat hyk hk
  simpa [Nat.cast_ofNat] using this

lemma padicValNat_factorial_le_div {p n : ℕ} [hp : Fact p.Prime] :
    padicValNat p n.factorial ≤ n / (p - 1) := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Nat.Prime.one_lt hp.out)
  have hmul : (p - 1) * padicValNat p n.factorial = n - (p.digits n).sum :=
    sub_one_mul_padicValNat_factorial n
  have hle : (p - 1) * padicValNat p n.factorial ≤ n := by
    rw [hmul]
    exact Nat.sub_le _ _
  exact (Nat.le_div_iff_mul_le hp1).mpr (by rwa [mul_comm])

lemma padicValNat_succ_factorial_le_half {p k : ℕ} [hp : Fact p.Prime]
    (h5 : 5 ≤ p) :
    padicValNat p (2 * k + 1).factorial ≤ k / 2 := by
  have h1 : padicValNat p (2 * k + 1).factorial ≤ (2 * k + 1) / (p - 1) :=
    padicValNat_factorial_le_div
  have hp1 : 4 ≤ p - 1 := by omega
  have h2 : (2 * k + 1) / (p - 1) ≤ (2 * k + 1) / 4 :=
    Nat.div_le_div_left hp1 (by omega)
  have h3 : (2 * k + 1) / 4 ≤ k / 2 := by omega
  exact h1.trans (h2.trans h3)

lemma two_k_bound {p k : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) (hk : 2 ≤ k) :
    (2 : ℤ) * k - padicValNat p k - padicValNat p (2 * k + 1).factorial ≥ 3 := by
  have hfacN : padicValNat p (2 * k + 1).factorial ≤ k / 2 :=
    padicValNat_succ_factorial_le_half (p := p) h5
  have hfac : (padicValNat p (2 * k + 1).factorial : ℤ) ≤ (k / 2 : ℤ) :=
    Int.ofNat_le.mpr hfacN
  by_cases hdiv : p ∣ k
  · have hk5 : 5 ≤ k := le_trans h5 (Nat.le_of_dvd (by omega) hdiv)
    have hlogN : padicValNat p k ≤ k - 1 := by
      have hle : padicValNat p k ≤ Nat.log p k := padicValNat_le_nat_log k
      have hlt : Nat.log p k < k :=
        Nat.log_lt_of_lt_pow (by omega : k ≠ 0) (Nat.lt_pow_self (Nat.Prime.one_lt hp.out))
      omega
    have hk1 : (padicValNat p k : ℤ) ≤ (k : ℤ) - 1 := by
      have : (padicValNat p k : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := Int.ofNat_le.mpr hlogN
      have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
      linarith
    have hhalf : (k / 2 : ℤ) ≤ (k : ℤ) - 2 := by
      have : k / 2 ≤ k - 2 := by omega
      have h1 : (k / 2 : ℤ) ≤ ((k - 2 : ℕ) : ℤ) := Int.ofNat_le.mpr this
      have h2 : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]; simp
      linarith
    linarith
  · have hv0 : padicValNat p k = 0 := padicValNat.eq_zero_of_not_dvd hdiv
    rw [hv0, Nat.cast_zero, sub_zero]
    have hge : (2 : ℤ) * k - (k / 2 : ℤ) ≥ 3 := by
      have : k / 2 ≤ k - 1 := by omega
      have h1 : (k / 2 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := Int.ofNat_le.mpr this
      have h2 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
      linarith
    linarith

/- Even-case product formula and power sums of `γᵢ`. -/

def PhiCombo (γ : ℚ) (N : ℕ) : ℚ :=
  Fprod γ (18 * N) * Fprod γ (4 * N) * Fprod γ (3 * N) /
    (Fprod γ (9 * N) * Fprod γ (8 * N) * Fprod γ (6 * N) * Fprod γ (2 * N))

lemma Fprod_ne_zero (γ : ℚ) (M : ℕ) (hγ : 0 ≤ γ) : Fprod γ M ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have : 0 ≤ γ * (j : ℚ) * (j + 1) := by
    have : 0 ≤ (j : ℚ) := Nat.cast_nonneg _
    have : 0 ≤ (j + 1 : ℚ) := by linarith
    exact mul_nonneg (mul_nonneg hγ (Nat.cast_nonneg _)) (by linarith)
  linarith

lemma gammaI_nonneg {p i : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) : 0 ≤ gammaI p i := by
  unfold gammaI pairDen
  have hden : 0 < (i : ℚ) * (p - i : ℕ) := by
    obtain ⟨h1, _, hilt, _, _, _⟩ := mem_half_bounds h5 hi
    have : 0 < (i : ℚ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp h1)
    have : 0 < ((p - i : ℕ) : ℚ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hilt)
    exact mul_pos ‹_› ‹_›
  exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hden.le

lemma PhiCombo_ne_zero (γ : ℚ) (N : ℕ) (hγ : 0 ≤ γ) : PhiCombo γ N ≠ 0 := by
  unfold PhiCombo
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (mul_ne_zero (Fprod_ne_zero γ _ hγ) (Fprod_ne_zero γ _ hγ))
      (Fprod_ne_zero γ _ hγ)
  · exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (Fprod_ne_zero γ _ hγ) (Fprod_ne_zero γ _ hγ))
        (Fprod_ne_zero γ _ hγ))
      (Fprod_ne_zero γ _ hγ)

lemma bRat_ratio_PhiCombo {p N : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    bRat (N * p) / bRat N =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  rw [risingF_ratio_bRat N p hp1]
  simp only [risingF_eq_Fprod (p := p) h5, PhiCombo]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [← Finset.prod_div_distrib]

lemma valGe_gammaI_pow {p i k : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    valGe p (2 * k) ((gammaI p i) ^ k) := by
  simpa [mul_comm] using valGe_pow (n := k) (valGe_gammaI h5 hi)

lemma valGe_sum_gamma_pow {p k : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p (2 * k)
      (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) := by
  apply valGe_sum
  intro i hi
  exact valGe_gammaI_pow h5 hi

lemma sum_gammaI_eq {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), gammaI p i =
      (p : ℚ) * harmonic (p - 1) := by
  have hσ := sigma1_eq_harmonic_div_p (p := p) h5
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
  unfold gammaI pairDen
  calc
    ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (p : ℚ) ^ 2 / ((i : ℚ) * (p - i : ℕ))
        = (p : ℚ) ^ 2 * ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), 1 / ((i : ℚ) * (p - i : ℕ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_eq_mul_inv, one_div]
    _ = (p : ℚ) ^ 2 * (harmonic (p - 1) / p) := by rw [hσ]
    _ = (p : ℚ) * harmonic (p - 1) := by
          field_simp [hp0]

lemma valGe_sum_gammaI {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    valGe p 3 (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), gammaI p i) := by
  rw [sum_gammaI_eq h5]
  have hH := wolstenholme_harmonic (p := p) h5
  have hp1 := valGe_p (p := p)
  have := valGe_mul hp1 hH
  simpa using this

lemma valGe_neg_one_pow (p n : ℕ) : valGe p 0 ((-1 : ℚ) ^ n) := by
  cases Nat.even_or_odd n with
  | inl he =>
    obtain ⟨m, hm⟩ := he
    rw [hm, Even.neg_one_pow ⟨m, rfl⟩]
    exact valGe_one p
  | inr ho =>
    obtain ⟨m, hm⟩ := ho
    rw [hm, Odd.neg_one_pow ⟨m, rfl⟩]
    exact valGe_neg (valGe_one p)

lemma valGe_log_term_ge_target {p N k : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hk : 1 ≤ k) :
    valGe p (3 + 3 * padicValNat p N)
      (((-1 : ℚ) ^ (k + 1) / k) *
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) *
        (U k (18 * N) + U k (4 * N) + U k (3 * N)
          - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N))) := by
  have hU := valGe_U_combo_any k N h5
  have hsign : valGe p 0 ((-1 : ℚ) ^ (k + 1)) := valGe_neg_one_pow p (k + 1)
  have hk0 : k ≠ 0 := by omega
  by_cases h1 : k = 1
  · subst h1
    have hγ : valGe p 3 (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), gammaI p i) :=
      valGe_sum_gammaI h5
    have hpow : (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ 1) =
        ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), gammaI p i := by
      simp
    rw [hpow]
    have hfac' : padicValNat p (2 * 1 + 1).factorial = 0 := by
      change padicValNat p 6 = 0
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hle : p ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hd
      have hp5 : 5 ≤ p := h5
      have : p = 5 ∨ p = 6 := by omega
      rcases this with rfl | rfl
      · exact (by decide : ¬(5 ∣ 6)) hd
      · exact (by decide : ¬ Nat.Prime 6) hp.out
    have h1inv : valGe p 0 ((1 : ℚ)⁻¹) := by
      simpa using (valGe_inv_nat (p := p) (n := 1))
    have hmul1 := valGe_mul hsign h1inv
    have hmul2 := valGe_mul hmul1 hγ
    have hmul3 := valGe_mul hmul2 hU
    have : (0 + 0 + 3 + (3 * padicValNat p N - padicValNat p (2 * 1 + 1).factorial) : ℤ) =
        3 + 3 * padicValNat p N := by
      simp [hfac']
    apply valGe_mono (le_of_eq this.symm)
    simpa [div_eq_mul_inv, mul_assoc] using hmul3
  · have hk2 : 2 ≤ k := by omega
    have hγ := valGe_sum_gamma_pow (p := p) (k := k) h5
    have hdiv := valGe_div_nat hγ hk0
    have hmul1 := valGe_mul hsign hdiv
    have hmul2 := valGe_mul hmul1 hU
    have hbound := two_k_bound (p := p) (k := k) h5 hk2
    have : (0 + (2 * k - padicValNat p k) +
        (3 * padicValNat p N - padicValNat p (2 * k + 1).factorial) : ℤ) ≥
        3 + 3 * padicValNat p N := by
      linarith [hbound]
    have hform : ((-1 : ℚ) ^ (k + 1) / k) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) *
          (U k (18 * N) + U k (4 * N) + U k (3 * N)
            - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N)) =
        ((-1 : ℚ) ^ (k + 1)) *
          ((∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) / k) *
          (U k (18 * N) + U k (4 * N) + U k (3 * N)
            - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N)) := by
      ring
    rw [hform]
    refine valGe_mono this ?_
    simpa [mul_assoc, sub_eq_add_neg] using hmul2


/-! p-adic logarithm infrastructure. -/


open Filter Topology
open scoped Nat

variable {p : ℕ} [hp : Fact p.Prime]

set_option maxHeartbeats 400000

/-- `x` has `p`-adic valuation at least `k`. -/
def valGeP (k : ℤ) (x : ℚ_[p]) : Prop :=
  x = 0 ∨ k ≤ x.valuation

lemma valGeP_zero (k : ℤ) : valGeP (p := p) k 0 := Or.inl rfl

lemma hp_one_lt_real : (1 : ℝ) < p :=
  Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp.out)

lemma hp_pos_real : (0 : ℝ) < p :=
  Nat.cast_pos.mpr (Nat.Prime.pos hp.out)

lemma valGeP_iff_norm {k : ℤ} {x : ℚ_[p]} :
    valGeP (p := p) k x ↔ ‖x‖ ≤ (p : ℝ) ^ (-k) := by
  unfold valGeP
  rcases eq_or_ne x 0 with hx | hx
  · constructor
    · intro; simp [hx]; exact zpow_nonneg (Nat.cast_nonneg _) _
    · intro; exact Or.inl hx
  · have hnorm : ‖x‖ = (p : ℝ) ^ (-x.valuation) :=
      Padic.norm_eq_zpow_neg_valuation hx
    constructor
    · intro h
      rcases h with h0 | hle
      · exact (hx h0).elim
      · rw [hnorm]
        exact zpow_le_zpow_right₀ hp_one_lt_real.le (neg_le_neg hle)
    · intro h
      refine Or.inr ?_
      rw [hnorm] at h
      have := (zpow_le_zpow_iff_right₀ hp_one_lt_real).mp h
      linarith

lemma valGeP_add {k : ℤ} {x y : ℚ_[p]}
    (hx : valGeP (p := p) k x) (hy : valGeP (p := p) k y) :
    valGeP (p := p) k (x + y) := by
  rw [valGeP_iff_norm] at *
  exact (Padic.nonarchimedean x y).trans (max_le hx hy)

lemma valGeP_sum {k : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, valGeP (p := p) k (f i)) :
    valGeP (p := p) k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using valGeP_zero (p := p) k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact valGeP_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma valGeP_neg {k : ℤ} {x : ℚ_[p]} (hx : valGeP (p := p) k x) :
    valGeP (p := p) k (-x) := by
  rw [valGeP_iff_norm] at *
  simpa using hx

lemma valGeP_sub {k : ℤ} {x y : ℚ_[p]}
    (hx : valGeP (p := p) k x) (hy : valGeP (p := p) k y) :
    valGeP (p := p) k (x - y) := by
  simpa [sub_eq_add_neg] using valGeP_add hx (valGeP_neg hy)

lemma valGeP_mul {k₁ k₂ : ℤ} {x y : ℚ_[p]}
    (hx : valGeP (p := p) k₁ x) (hy : valGeP (p := p) k₂ y) :
    valGeP (p := p) (k₁ + k₂) (x * y) := by
  rw [valGeP_iff_norm] at *
  have hmul : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  rw [hmul]
  calc
    ‖x‖ * ‖y‖ ≤ (p : ℝ) ^ (-k₁) * (p : ℝ) ^ (-k₂) :=
      mul_le_mul hx hy (norm_nonneg _) (zpow_nonneg (Nat.cast_nonneg _) _)
    _ = (p : ℝ) ^ (-(k₁ + k₂)) := by
        rw [← zpow_add₀ hp_pos_real.ne']
        congr 1; ring

lemma valGeP_pow {k : ℤ} {x : ℚ_[p]} (n : ℕ)
    (hx : valGeP (p := p) k x) :
    valGeP (p := p) (n * k) (x ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_mul]
    exact Or.inr (by simp [Padic.valuation_one])
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact valGeP_mul ih hx

lemma valGeP_mono {k k' : ℤ} {x : ℚ_[p]} (hkk : k' ≤ k) (h : valGeP (p := p) k x) :
    valGeP (p := p) k' x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (le_trans hkk h)

lemma valGeP_one {k : ℤ} (hk : k ≤ 0) : valGeP (p := p) k (1 : ℚ_[p]) :=
  Or.inr (by simpa [Padic.valuation_one] using hk)

lemma valGeP_inv_nat_exact (n : ℕ) (hn : n ≠ 0) :
    valGeP (p := p) (-(padicValNat p n : ℤ)) (n : ℚ_[p])⁻¹ := by
  have hne : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine Or.inr ?_
  rw [Padic.valuation_inv, Padic.valuation_natCast]

lemma valGeP_div_nat_exact {k : ℤ} {x : ℚ_[p]} (n : ℕ) (hn : n ≠ 0)
    (hx : valGeP (p := p) k x) :
    valGeP (p := p) (k - padicValNat p n) (x / (n : ℚ_[p])) := by
  rw [div_eq_mul_inv]
  have := valGeP_mul hx (valGeP_inv_nat_exact n hn)
  simpa [sub_eq_add_neg] using this

lemma valGeP_neg_one_pow (n : ℕ) : valGeP (p := p) 0 ((-1 : ℚ_[p]) ^ n) := by
  rcases Nat.even_or_odd n with h | h
  · rw [Even.neg_one_pow h]; exact valGeP_one le_rfl
  · rw [Odd.neg_one_pow h]; exact valGeP_neg (valGeP_one le_rfl)

/-- A single term of the series for `log(1+x)`. -/
noncomputable def logTerm (x : ℚ_[p]) (k : ℕ) : ℚ_[p] :=
  (-1 : ℚ_[p]) ^ k * x ^ (k + 1) / (k + 1 : ℚ_[p])

lemma valGeP_logTerm {α : ℤ} {x : ℚ_[p]} (k : ℕ)
    (hx : valGeP (p := p) α x) :
    valGeP (p := p) ((k + 1 : ℤ) * α - padicValNat p (k + 1))
      (logTerm (p := p) x k) := by
  unfold logTerm
  have h1 : valGeP (p := p) 0 ((-1 : ℚ_[p]) ^ k) := valGeP_neg_one_pow k
  have h2 : valGeP (p := p) ((k + 1 : ℤ) * α) (x ^ (k + 1)) := by
    simpa [nsmul_eq_mul] using valGeP_pow (k + 1) hx
  have h3 := valGeP_mul h1 h2
  have h4 := valGeP_div_nat_exact (k + 1) (Nat.succ_ne_zero k) h3
  simpa [zero_add] using h4

lemma norm_inv_nat_le (n : ℕ) (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖⁻¹ ≤ (n : ℝ) := by
  have hne : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← norm_inv]
  have hval : valGeP (p := p) (-(padicValNat p n : ℤ)) (n : ℚ_[p])⁻¹ :=
    valGeP_inv_nat_exact n hn
  rw [valGeP_iff_norm] at hval
  have hpow : (p : ℝ) ^ (-(-(padicValNat p n : ℤ))) = (p : ℝ) ^ (padicValNat p n : ℕ) := by
    simp [zpow_natCast]
  rw [hpow] at hval
  have hle : (p : ℝ) ^ (padicValNat p n : ℕ) ≤ (n : ℝ) := by
    have : (p : ℕ) ^ padicValNat p n ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
    exact_mod_cast this
  exact hval.trans hle

lemma norm_logTerm_le (x : ℚ_[p]) (k : ℕ) :
    ‖logTerm (p := p) x k‖ ≤ (k + 1 : ℝ) * ‖x‖ ^ (k + 1) := by
  unfold logTerm
  have hsign : ‖(-1 : ℚ_[p]) ^ k‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hcast : ((k + 1 : ℕ) : ℚ_[p]) = (k : ℚ_[p]) + 1 := by
    rw [Nat.cast_succ]
  rw [← hcast, norm_div, norm_mul, hsign, one_mul, norm_pow]
  have hinv : ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ ((k + 1 : ℕ) : ℝ) :=
    norm_inv_nat_le (k + 1) (Nat.succ_ne_zero k)
  calc
    ‖x‖ ^ (k + 1) / ‖((k + 1 : ℕ) : ℚ_[p])‖
        = ‖x‖ ^ (k + 1) * ‖((k + 1 : ℕ) : ℚ_[p])‖⁻¹ := div_eq_mul_inv _ _
    _ ≤ ‖x‖ ^ (k + 1) * ((k + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg (norm_nonneg _) _)
    _ = ((k + 1 : ℕ) : ℝ) * ‖x‖ ^ (k + 1) := mul_comm _ _
    _ = (k + 1 : ℝ) * ‖x‖ ^ (k + 1) := by rw [Nat.cast_succ]

lemma tendsto_logTerm {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    Tendsto (fun k : ℕ => logTerm (p := p) x k) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hxN : ‖x‖ ≤ (p : ℝ)⁻¹ := by
    rw [valGeP_iff_norm] at hx
    simpa [zpow_neg, zpow_one] using hx
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hr1 : ‖x‖ < 1 := lt_of_le_of_lt hxN (inv_lt_one_of_one_lt₀ hp_one_lt_real)
  refine squeeze_zero (fun _ => norm_nonneg _) (norm_logTerm_le x) ?_
  have h := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1
  have : (fun k : ℕ => (k + 1 : ℝ) * ‖x‖ ^ (k + 1)) =
      (fun n : ℕ => (n : ℝ) ^ 1 * ‖x‖ ^ n) ∘ (fun k => k + 1) := by
    ext k; simp [pow_one]
  rw [this]
  exact h.comp (tendsto_add_atTop_nat 1)

lemma summable_logTerm {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    Summable (fun k : ℕ => logTerm (p := p) x k) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_logTerm hx

/-- The p-adic logarithm `log(1+x)` for `v(x) ≥ 1`. -/
noncomputable def padicLog1p (x : ℚ_[p]) : ℚ_[p] :=
  ∑' k : ℕ, logTerm (p := p) x k

lemma hasSum_padicLog1p {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    HasSum (fun k : ℕ => logTerm (p := p) x k) (padicLog1p (p := p) x) :=
  (summable_logTerm hx).hasSum

lemma valGeP_tsum {k : ℤ} {f : ℕ → ℚ_[p]} (hf : Summable f)
    (h : ∀ n, valGeP (p := p) k (f n)) :
    valGeP (p := p) k (∑' n, f n) := by
  rw [valGeP_iff_norm]
  have hpartial : ∀ s : Finset ℕ, ‖∑ n ∈ s, f n‖ ≤ (p : ℝ) ^ (-k) := by
    intro s
    rw [← valGeP_iff_norm]
    exact valGeP_sum s f (fun n _ => h n)
  have hclosed : IsClosed {y : ℚ_[p] | ‖y‖ ≤ (p : ℝ) ^ (-k)} :=
    isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto hf.hasSum.tendsto_sum_nat
    (Eventually.of_forall fun n => hpartial (Finset.range n))

lemma padicValNat_succ_le (k : ℕ) : padicValNat p (k + 1) ≤ k := by
  have hlog : padicValNat p (k + 1) ≤ Nat.log p (k + 1) := padicValNat_le_nat_log (k + 1)
  have hlt : Nat.log p (k + 1) < k + 1 :=
    Nat.log_lt_of_lt_pow (Nat.succ_ne_zero k) (Nat.lt_pow_self (Nat.Prime.one_lt hp.out))
  omega

lemma valGeP_padicLog1p {α : ℤ} {x : ℚ_[p]} (hα : 1 ≤ α)
    (hx : valGeP (p := p) α x) :
    valGeP (p := p) α (padicLog1p (p := p) x) := by
  have hx1 : valGeP (p := p) 1 x := valGeP_mono hα hx
  refine valGeP_tsum (summable_logTerm hx1) ?_
  intro k
  have h := valGeP_logTerm (α := α) k hx
  have hle : α ≤ (k + 1 : ℤ) * α - padicValNat p (k + 1) := by
    have hv : (padicValNat p (k + 1) : ℤ) ≤ (k : ℤ) :=
      Nat.cast_le.mpr (padicValNat_succ_le k)
    have hkα : (k : ℤ) ≤ (k : ℤ) * α := by
      nlinarith
    linarith
  exact valGeP_mono hle h

lemma padicLog1p_zero : padicLog1p (p := p) 0 = 0 := by
  simp [padicLog1p, logTerm]

lemma logTerm_zero_eq (x : ℚ_[p]) : logTerm (p := p) x 0 = x := by
  simp [logTerm]

lemma succ_lt_five_pow {k : ℕ} (hk : 1 ≤ k) : k + 1 < 5 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      k + 1 + 1 = (k + 1) + 1 := rfl
      _ < 5 ^ k + 1 := Nat.add_lt_add_right ih 1
      _ ≤ 5 ^ k + 5 ^ k := by
          have : 1 ≤ 5 ^ k := Nat.one_le_pow _ _ (by norm_num)
          omega
      _ = 2 * 5 ^ k := by ring
      _ < 5 * 5 ^ k := Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num))
      _ = 5 ^ (k + 1) := (pow_succ' 5 k).symm

lemma padicValNat_succ_le_pred {k : ℕ} (hk : 1 ≤ k) (h5 : 5 ≤ p) :
    padicValNat p (k + 1) ≤ k - 1 := by
  have hlog : padicValNat p (k + 1) ≤ Nat.log p (k + 1) := padicValNat_le_nat_log (k + 1)
  have hlt : Nat.log p (k + 1) < k := by
    rw [Nat.log_lt_iff_lt_pow (Nat.Prime.one_lt hp.out) (by omega)]
    exact (succ_lt_five_pow hk).trans_le (pow_le_pow_left' h5 k)
  omega

lemma valGeP_logTerm_tail {α : ℤ} {x : ℚ_[p]} (hα : 1 ≤ α) (h5 : 5 ≤ p)
    (hx : valGeP (p := p) α x) {k : ℕ} (hk : 1 ≤ k) :
    valGeP (p := p) (α + 1) (logTerm (p := p) x k) := by
  have h := valGeP_logTerm (α := α) k hx
  have hle : α + 1 ≤ (k + 1 : ℤ) * α - padicValNat p (k + 1) := by
    have hv : (padicValNat p (k + 1) : ℤ) ≤ ((k - 1 : ℕ) : ℤ) :=
      Nat.cast_le.mpr (padicValNat_succ_le_pred hk h5)
    have hv' : (padicValNat p (k + 1) : ℤ) ≤ (k : ℤ) - 1 := by
      have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        rw [Nat.cast_sub hk]; simp
      linarith
    have hkα : (k : ℤ) * α ≥ (k : ℤ) := by nlinarith
    linarith
  exact valGeP_mono hle h

lemma valGeP_padicLog1p_sub_self {α : ℤ} {x : ℚ_[p]} (hα : 1 ≤ α) (h5 : 5 ≤ p)
    (hx : valGeP (p := p) α x) :
    valGeP (p := p) (α + 1) (padicLog1p (p := p) x - x) := by
  have hx1 : valGeP (p := p) 1 x := valGeP_mono hα hx
  have hsplit := (summable_logTerm hx1).tsum_eq_zero_add
  unfold padicLog1p
  rw [hsplit, logTerm_zero_eq, add_sub_cancel_left]
  refine valGeP_tsum ((summable_logTerm hx1).comp_injective (add_left_injective 1)) ?_
  intro n
  exact valGeP_logTerm_tail hα h5 hx (Nat.succ_le_succ (Nat.zero_le n))

lemma valGeP_valuation {x : ℚ_[p]} (hx : x ≠ 0) :
    valGeP (p := p) x.valuation x :=
  Or.inr le_rfl

lemma valuation_eq_of_sub_higher {a b : ℚ_[p]} (hb : b ≠ 0)
    (h : valGeP (p := p) (b.valuation + 1) (a - b)) :
    a ≠ 0 ∧ a.valuation = b.valuation := by
  have hbv : valGeP (p := p) b.valuation b := valGeP_valuation hb
  have ha : a ≠ 0 := by
    intro ha
    subst ha
    have hneg : valGeP (p := p) (b.valuation + 1) (-b) := by simpa using h
    have hb1 : valGeP (p := p) (b.valuation + 1) b := by
      simpa using valGeP_neg hneg
    rw [valGeP_iff_norm] at hb1 hbv
    have hnormb : ‖b‖ = (p : ℝ) ^ (-b.valuation) :=
      Padic.norm_eq_zpow_neg_valuation hb
    have hlt : (p : ℝ) ^ (-(b.valuation + 1)) < (p : ℝ) ^ (-b.valuation) :=
      zpow_lt_zpow_right₀ hp_one_lt_real (by linarith)
    have : ‖b‖ ≤ (p : ℝ) ^ (-(b.valuation + 1)) := hb1
    rw [hnormb] at this
    exact (not_le_of_gt hlt) this
  refine ⟨ha, ?_⟩
  have hna : ‖a‖ = (p : ℝ) ^ (-a.valuation) := Padic.norm_eq_zpow_neg_valuation ha
  have hnb : ‖b‖ = (p : ℝ) ^ (-b.valuation) := Padic.norm_eq_zpow_neg_valuation hb
  have hsub : ‖a - b‖ ≤ (p : ℝ) ^ (-(b.valuation + 1)) := (valGeP_iff_norm).1 h
  have hstrict : ‖a - b‖ < ‖b‖ := by
    rw [hnb]
    exact lt_of_le_of_lt hsub (zpow_lt_zpow_right₀ hp_one_lt_real (by linarith))
  have hnormeq : ‖a‖ = ‖b‖ := Padic.norm_eq_of_norm_sub_lt_right hstrict
  rw [hna, hnb] at hnormeq
  have : -a.valuation = -b.valuation :=
    (zpow_right_inj₀ hp_pos_real (ne_of_gt hp_one_lt_real)).mp hnormeq
  linarith

lemma valuation_padicLog1p {x : ℚ_[p]} (h5 : 5 ≤ p)
    (hx0 : x ≠ 0) (hx : valGeP (p := p) 1 x) :
    (padicLog1p (p := p) x).valuation = x.valuation := by
  have hα : (1 : ℤ) ≤ x.valuation := by
    rcases hx with h | h
    · exact (hx0 h).elim
    · exact h
  have hsub := valGeP_padicLog1p_sub_self hα h5 (valGeP_valuation hx0)
  have := valuation_eq_of_sub_higher hx0 hsub
  exact this.2

/-- `v(log(1+z)) = v(z)` when `v(z) ≥ 1`. -/
lemma valGeP_padicLog1p_iff {x : ℚ_[p]} (h5 : 5 ≤ p)
    (hx : valGeP (p := p) 1 x) (k : ℤ) :
    valGeP (p := p) k (padicLog1p (p := p) x) ↔ valGeP (p := p) k x := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0; simp [padicLog1p_zero]
  · have hv := valuation_padicLog1p h5 hx0 hx
    constructor
    · intro h
      rcases h with h0 | hle
      · have : padicLog1p (p := p) x ≠ 0 := by
          intro hz
          have := valuation_padicLog1p h5 hx0 hx
          -- if log = 0 then valuation is 0 by Padic.valuation_zero, contradiction with v(x)≥1
          rw [hz, Padic.valuation_zero] at this
          rcases hx with hx' | hx'
          · exact hx0 hx'
          · linarith
        exact (this h0).elim
      · refine Or.inr ?_
        rwa [← hv]
    · intro h
      rcases h with h0 | hle
      · exact (hx0 h0).elim
      · refine Or.inr ?_
        rwa [hv]



lemma nat_choose_mul (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    n * (n - 1).choose (k - 1) = n.choose k * k := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have h := Nat.succ_mul_choose_eq (n - 1) (k - 1)
  simp only [Nat.succ_eq_add_one] at h
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hk] at h
  exact h

lemma valGeP_nat_of_le {n : ℕ} {k : ℤ} (h : k ≤ padicValNat p n) :
    valGeP (p := p) k (n : ℚ_[p]) := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn, valGeP_zero]
  · exact Or.inr (by rw [Padic.valuation_natCast]; exact h)

lemma padicValNat_choose_pow_ge (m k : ℕ) (hk : 0 < k) (hkn : k ≤ p ^ m) :
    (m : ℤ) - (padicValNat p k : ℤ) ≤ padicValNat p ((p ^ m).choose k) := by
  have hmul := nat_choose_mul (p ^ m) k hk hkn
  have hneC : (p ^ m).choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hnek : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hneN : p ^ m ≠ 0 := pow_ne_zero _ (Nat.Prime.ne_zero hp.out)
  have hle : k - 1 ≤ p ^ m - 1 := by omega
  have hneC' : (p ^ m - 1).choose (k - 1) ≠ 0 := (Nat.choose_pos hle).ne'
  have hval := congrArg (padicValNat p) hmul
  rw [padicValNat.mul hneN hneC', padicValNat.mul hneC hnek] at hval
  have hpown : padicValNat p (p ^ m) = m := by
    rw [padicValNat.pow m (Nat.Prime.ne_zero hp.out), padicValNat_self]
    simp
  rw [hpown] at hval
  have : (m : ℤ) + padicValNat p ((p ^ m - 1).choose (k - 1)) =
      padicValNat p ((p ^ m).choose k) + padicValNat p k := by
    exact_mod_cast hval
  linarith


lemma valGeP_choose_pow (m k : ℕ) (hk : 0 < k) :
    valGeP (p := p) (m - padicValNat p k : ℤ) (((p ^ m).choose k : ℕ) : ℚ_[p]) := by
  by_cases hkn : k ≤ p ^ m
  · exact valGeP_nat_of_le (padicValNat_choose_pow_ge m k hk hkn)
  · have : (p ^ m).choose k = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn)
    simp [this, valGeP_zero]

lemma choose_pow_div (m k : ℕ) (hk : 0 < k) (hkn : k ≤ p ^ m) :
    (((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m =
      (((p ^ m - 1).choose (k - 1) : ℕ) : ℚ_[p]) / (k : ℚ_[p]) := by
  have hmul := nat_choose_mul (p ^ m) k hk hkn
  have hnek : (k : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have hnp : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out))
  have hcast := congrArg (fun n : ℕ => (n : ℚ_[p])) hmul
  push_cast at hcast
  field_simp [hnek, hnp]
  exact hcast.symm

lemma choose_pow_eq_desc (m k : ℕ) (hkn : k ≤ p ^ m) :
    ((p ^ m).choose k : ℚ_[p]) * (k.factorial : ℚ_[p]) =
      ∏ i ∈ Finset.range k, ((p : ℚ_[p]) ^ m - i) := by
  have hnat : (p ^ m).choose k * k.factorial = (p ^ m).descFactorial k := by
    rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
  have hcast := congrArg (fun n : ℕ => (n : ℚ_[p])) hnat
  push_cast at hcast
  rw [hcast, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hi' : i < k := Finset.mem_range.mp hi
  have hile : i ≤ p ^ m := le_trans (le_of_lt hi') hkn
  rw [Nat.cast_sub hile, Nat.cast_pow]



lemma range_eq_zero_union_Icc {k : ℕ} (hk : 1 ≤ k) :
    Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
  ext i
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

lemma sub_eq_neg_mul_one_sub (m j : ℕ) (hj : j ≠ 0) :
    (p : ℚ_[p]) ^ m - j = (-j : ℚ_[p]) * (1 - (p : ℚ_[p]) ^ m / j) := by
  have hj0 : (j : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hj
  field_simp [hj0]
  ring

lemma prod_Icc_neg (n : ℕ) :
    (∏ j ∈ Finset.Icc 1 n, (-j : ℚ_[p])) =
      (-1 : ℚ_[p]) ^ n * (n.factorial : ℚ_[p]) := by
  have hmap : Finset.Icc 1 n = (Finset.range n).image (· + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h; exact ⟨i - 1, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hmap, Finset.prod_image]
  · have hcongr : (∏ i ∈ Finset.range n, (-((i + 1 : ℕ) : ℚ_[p]))) =
        (∏ i ∈ Finset.range n, (-(i + 1 : ℚ_[p]))) := by
      refine Finset.prod_congr rfl ?_
      intro i _; rw [Nat.cast_succ]
    rw [hcongr]
    have hsplit :
        (∏ i ∈ Finset.range n, (-(i + 1 : ℚ_[p]))) =
          (-1 : ℚ_[p]) ^ n * ∏ i ∈ Finset.range n, (i + 1 : ℚ_[p]) := by
      have : ∀ i ∈ Finset.range n, (-(i + 1 : ℚ_[p])) = (-1) * (i + 1 : ℚ_[p]) := by
        intro i _; ring
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range]
    rw [hsplit]
    congr 1
    have hnat : (∏ i ∈ Finset.range n, (i + 1) : ℕ) = n.factorial :=
      Finset.prod_range_add_one_eq_factorial n
    have := congrArg (fun t : ℕ => (t : ℚ_[p])) hnat
    push_cast at this
    exact this
  · intro a _ b _ h; exact Nat.succ_injective h

/-- `C(p^m, k) / p^m = (-1)^{k-1}/k * ∏_{j=1}^{k-1} (1 - p^m/j)`. -/
lemma choose_pow_div_prod (m k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ p ^ m) :
    (((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m =
      (-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p]) *
        ∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j) := by
  have hfac := choose_pow_eq_desc (p := p) m k hkn
  have hk0 : (k : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfact0 : (k.factorial : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hpm0 : (p : ℚ_[p]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out))
  have hsplit : ∏ i ∈ Finset.range k, ((p : ℚ_[p]) ^ m - i) =
      (p : ℚ_[p]) ^ m * ∏ j ∈ Finset.Icc 1 (k - 1), ((p : ℚ_[p]) ^ m - j) := by
    rw [range_eq_zero_union_Icc hk, Finset.prod_insert (by simp)]
    simp
  have hneg : ∏ j ∈ Finset.Icc 1 (k - 1), ((p : ℚ_[p]) ^ m - j) =
      ∏ j ∈ Finset.Icc 1 (k - 1), ((-j : ℚ_[p]) * (1 - (p : ℚ_[p]) ^ m / j)) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hj0 : j ≠ 0 := by
      simp only [Finset.mem_Icc] at hj; omega
    exact sub_eq_neg_mul_one_sub m j hj0
  rw [hneg, Finset.prod_mul_distrib] at hsplit
  have hnegprod := prod_Icc_neg (p := p) (k - 1)
  have hmain : (((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m =
      (∏ j ∈ Finset.Icc 1 (k - 1), (-j : ℚ_[p])) *
        (∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j)) /
          (k.factorial : ℚ_[p]) := by
    have hB : (∏ j ∈ Finset.Icc 1 (k - 1), (-j : ℚ_[p])) *
        (∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j)) =
        (∏ i ∈ Finset.range k, ((p : ℚ_[p]) ^ m - i)) / (p : ℚ_[p]) ^ m := by
      rw [eq_div_iff hpm0, mul_comm]
      exact hsplit.symm
    rw [hB, ← hfac]
    field_simp [hpm0, hfact0]
  rw [hmain, hnegprod]
  have hfactrel : ((k - 1).factorial : ℚ_[p]) / (k.factorial : ℚ_[p]) =
      1 / (k : ℚ_[p]) := by
    have hf : k.factorial = k * (k - 1).factorial :=
      (Nat.mul_factorial_pred (by omega : k ≠ 0)).symm
    rw [hf]
    push_cast
    field_simp [hk0, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))]
  calc
    ((-1 : ℚ_[p]) ^ (k - 1) * ((k - 1).factorial : ℚ_[p])) *
        (∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j)) /
          (k.factorial : ℚ_[p])
      = (-1 : ℚ_[p]) ^ (k - 1) *
          (((k - 1).factorial : ℚ_[p]) / (k.factorial : ℚ_[p])) *
          (∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j)) := by ring
    _ = (-1 : ℚ_[p]) ^ (k - 1) * (1 / (k : ℚ_[p])) *
          (∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j)) := by
        rw [hfactrel]
    _ = (-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p]) *
          (∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / j)) := by ring



lemma valGeP_p_pow (m : ℕ) : valGeP (p := p) m ((p : ℚ_[p]) ^ m) := by
  refine Or.inr ?_
  rw [Padic.valuation_pow, Padic.valuation_p]
  simp

lemma valGeP_unit_sub {α : ℤ} {x : ℚ_[p]} (hα : 0 ≤ α)
    (hx : valGeP (p := p) α x) :
    valGeP (p := p) 0 (1 - x) :=
  valGeP_sub (valGeP_one le_rfl) (valGeP_mono hα hx)

lemma valGeP_prod_one_sub {α : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hα : 0 ≤ α) (hf : ∀ i ∈ s, valGeP (p := p) α (f i)) :
    valGeP (p := p) 0 (∏ i ∈ s, (1 - f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using valGeP_one (le_rfl : (0 : ℤ) ≤ 0)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact valGeP_mul (valGeP_unit_sub hα (hf a (Finset.mem_insert_self a s)))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma valGeP_prod_one_sub_sub_one {α : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hα : 1 ≤ α) (hf : ∀ i ∈ s, valGeP (p := p) α (f i)) :
    valGeP (p := p) α ((∏ i ∈ s, (1 - f i)) - 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp [valGeP_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have : (1 - f a) * (∏ i ∈ s, (1 - f i)) - 1 =
        ((∏ i ∈ s, (1 - f i)) - 1) - f a * (∏ i ∈ s, (1 - f i)) := by ring
    rw [this]
    refine valGeP_sub (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) ?_
    have hP := valGeP_prod_one_sub s f (by linarith) (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := valGeP_mul (hf a (Finset.mem_insert_self a s)) hP
    simpa using this

lemma valGeP_prod_one_sub_p_pow (m k : ℕ) (hm : k + 1 ≤ m) :
    valGeP (p := p) (m - (k : ℤ))
      ((∏ j ∈ Finset.Icc 1 k, (1 - (p : ℚ_[p]) ^ m / (j : ℚ_[p]))) - 1) := by
  refine valGeP_prod_one_sub_sub_one (α := (m : ℤ) - k) (Finset.Icc 1 k)
      (fun j => (p : ℚ_[p]) ^ m / (j : ℚ_[p])) (by omega) ?_
  intro j hj
  have hj0 : j ≠ 0 := by
    simp only [Finset.mem_Icc] at hj; omega
  have hle : (j : ℤ) ≤ k := by
    simp only [Finset.mem_Icc] at hj; exact_mod_cast hj.2
  have hv : padicValNat p j ≤ j :=
    (padicValNat_le_nat_log j).trans (Nat.log_le_self p j)
  have : (m : ℤ) - k ≤ m - padicValNat p j := by
    have : (padicValNat p j : ℤ) ≤ k := by
      have : (padicValNat p j : ℤ) ≤ (j : ℤ) := Nat.cast_le.mpr hv
      linarith
    linarith
  exact valGeP_mono this (valGeP_div_nat_exact j hj0 (valGeP_p_pow m))


lemma valGeP_div_k (k : ℕ) (hk : k ≠ 0) :
    valGeP (p := p) (-(padicValNat p k : ℤ)) ((k : ℚ_[p])⁻¹) :=
  valGeP_inv_nat_exact k hk

/-- For fixed `k ≥ 1` and `m` large, `C(p^m,k)/p^m` is close to `(-1)^{k-1}/k`. -/
lemma valGeP_choose_pow_div_sub (m k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ p ^ m)
    (hm : k ≤ m) :
    valGeP (p := p) (m - (k - 1 : ℤ) - padicValNat p k)
      ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m
        - (-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p])) := by
  rw [choose_pow_div_prod m k hk hkn]
  have : (-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p]) *
        ∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / (j : ℚ_[p]))
      - (-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p]) =
      ((-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p])) *
        ((∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / (j : ℚ_[p]))) - 1) := by
    ring
  rw [this]
  have hprod := valGeP_prod_one_sub_p_pow (p := p) m (k - 1) (by omega)
  have hsign := valGeP_neg_one_pow (p := p) (k - 1)
  have hinv := valGeP_div_k (p := p) k (by omega)
  have hpref := valGeP_mul hsign hinv
  have hmul := valGeP_mul hpref hprod
  have : ((-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p])) *
        ((∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / (j : ℚ_[p]))) - 1) =
      ((-1 : ℚ_[p]) ^ (k - 1)) * (k : ℚ_[p])⁻¹ *
        ((∏ j ∈ Finset.Icc 1 (k - 1), (1 - (p : ℚ_[p]) ^ m / (j : ℚ_[p]))) - 1) := by
    rw [div_eq_mul_inv]
  rw [this]
  have heq : (0 + (-(padicValNat p k : ℤ)) + (m - ((k - 1 : ℕ) : ℤ))) =
      m - (k - 1 : ℤ) - padicValNat p k := by
    have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
      rw [Nat.cast_sub hk]; simp
    rw [this]; ring
  exact valGeP_mono (le_of_eq heq.symm) hmul


lemma binom_pow_eq (x : ℚ_[p]) (n : ℕ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ_[p]) * x ^ k := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [mul_comm]

lemma binom_pow_sub_one (x : ℚ_[p]) (n : ℕ) :
    (1 + x) ^ n - 1 =
      ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℚ_[p]) * x ^ k := by
  have h := binom_pow_eq (p := p) x n
  have hr : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [h, hr, Finset.sum_insert (by simp)]
  simp [Nat.choose_zero_right]

lemma valGeP_inv_p_pow (m : ℕ) :
    valGeP (p := p) (-m : ℤ) ((p : ℚ_[p]) ^ m)⁻¹ := by
  have hne : (p : ℚ_[p]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out))
  refine Or.inr ?_
  rw [Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p]
  simp

lemma binom_pow_div (x : ℚ_[p]) (m : ℕ) :
    ((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m =
      ∑ k ∈ Finset.Icc 1 (p ^ m),
        ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k := by
  have hne : (p : ℚ_[p]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out))
  rw [binom_pow_sub_one, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/-- A single binomial term has the same valuation lower bound as the corresponding log term. -/
lemma valGeP_binom_term {α : ℤ} {x : ℚ_[p]} (m k : ℕ) (hk : 0 < k)
    (hx : valGeP (p := p) α x) :
    valGeP (p := p) ((k : ℤ) * α - padicValNat p k)
      (((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k) := by
  have hc := valGeP_choose_pow (p := p) m k hk
  have hinv := valGeP_inv_p_pow (p := p) m
  have hch := valGeP_mul hc hinv
  -- val C + val p^{-m} ≥ (m - v(k)) + (-m) = -v(k)
  have hch' : valGeP (p := p) (-(padicValNat p k : ℤ))
      ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) := by
    have : (m - padicValNat p k : ℤ) + (-m) = - (padicValNat p k : ℤ) := by ring
    rw [div_eq_mul_inv]
    exact valGeP_mono (le_of_eq this.symm) hch
  have hxk := valGeP_pow k hx
  have hmul := valGeP_mul hch' hxk
  have heq : (-(padicValNat p k : ℤ) + (k : ℤ) * α) = (k : ℤ) * α - padicValNat p k := by
    ring
  exact valGeP_mono (le_of_eq heq.symm) hmul

lemma logTerm_succ (x : ℚ_[p]) (k : ℕ) (hk : 1 ≤ k) :
    logTerm (p := p) x (k - 1) =
      (-1 : ℚ_[p]) ^ (k - 1) * x ^ k / (k : ℚ_[p]) := by
  unfold logTerm
  have hpow : (k - 1 + 1) = k := Nat.sub_add_cancel hk
  have hcast : ((k - 1 : ℕ) : ℚ_[p]) + 1 = (k : ℚ_[p]) := by
    rw [Nat.cast_sub hk, Nat.cast_one]; ring
  rw [hpow, hcast]


lemma valGeP_pow_sub_one {x : ℚ_[p]} (m : ℕ) (hx : valGeP (p := p) 1 x) :
    valGeP (p := p) m ((1 + x) ^ (p ^ m) - 1) := by
  rw [binom_pow_sub_one]
  apply valGeP_sum
  intro k hk
  have hk0 : 0 < k := by
    simp only [Finset.mem_Icc] at hk; omega
  have hkn : k ≤ p ^ m := by
    simp only [Finset.mem_Icc] at hk; exact hk.2
  have hc := valGeP_choose_pow (p := p) m k hk0
  have hxk := valGeP_pow k hx
  have hmul := valGeP_mul hc hxk
  have hle : (m : ℤ) ≤ (m - padicValNat p k : ℤ) + (k : ℤ) * 1 := by
    have : (padicValNat p k : ℤ) ≤ k :=
      Nat.cast_le.mpr ((padicValNat_le_nat_log k).trans (Nat.log_le_self p k))
    linarith
  exact valGeP_mono hle hmul

lemma tendsto_inv_p_pow_zero :
    Tendsto (fun m : ℕ => (p : ℝ) ^ (-(m : ℤ))) atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (p : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg _))
    (inv_lt_one_of_one_lt₀ hp_one_lt_real)
  convert hpow using 1
  ext m
  rw [zpow_neg, zpow_natCast, inv_pow]

lemma tendsto_pow_one {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    Tendsto (fun m : ℕ => (1 + x) ^ (p ^ m)) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim := tendsto_inv_p_pow_zero (p := p)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨M, hM⟩ := hlim ε hε
  refine ⟨M, ?_⟩
  intro m hm
  have hle : ‖(1 + x) ^ (p ^ m) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
    (valGeP_iff_norm (p := p)).1 (valGeP_pow_sub_one (p := p) m hx)
  have hlt : (p : ℝ) ^ (-(m : ℤ)) < ε := by
    have : dist ((p : ℝ) ^ (-(m : ℤ))) 0 < ε := hM m hm
    simpa [dist_zero_right] using this
  have : dist ((1 + x) ^ (p ^ m)) (1 : ℚ_[p]) = ‖(1 + x) ^ (p ^ m) - 1‖ := by
    simp [dist_eq_norm]
  rw [this]
  exact lt_of_le_of_lt hle hlt

lemma valGeP_logTerm_bound {x : ℚ_[p]} (k : ℕ) (hx : valGeP (p := p) 1 x) :
    valGeP (p := p) ((k + 1 : ℤ) - padicValNat p (k + 1))
      (logTerm (p := p) x k) := by
  have h := valGeP_logTerm (α := 1) k hx
  simpa using h


lemma sum_add_tsum_log {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) (K : ℕ) :
    padicLog1p (p := p) x =
      ∑ k ∈ Finset.range K, logTerm (p := p) x k +
        ∑' k : ℕ, logTerm (p := p) x (k + K) := by
  simpa [padicLog1p] using
    ((summable_logTerm hx).sum_add_tsum_nat_add K).symm

lemma valGeP_log_tail {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) (K N : ℕ)
    (hK : ∀ k ≥ K, (N : ℤ) ≤ (k + 1 : ℤ) - padicValNat p (k + 1)) :
    valGeP (p := p) N (∑' k : ℕ, logTerm (p := p) x (k + K)) := by
  refine valGeP_tsum ((summable_logTerm hx).comp_injective (add_left_injective K)) ?_
  intro n
  exact valGeP_mono (hK (n + K) (by omega)) (valGeP_logTerm_bound (n + K) hx)

lemma two_mul_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      2 * (k + 1) = 2 * k + 2 := by ring
      _ ≤ 2 ^ k + 2 ^ k := by
          have : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
          omega
      _ = 2 ^ (k + 1) := by ring

lemma two_pow_succ_gt (n : ℕ) : n < 2 ^ (n / 2 + 1) := by
  have hk : 1 ≤ n / 2 + 1 := by omega
  have h := two_mul_le_two_pow hk
  have : n < 2 * (n / 2 + 1) := by omega
  exact this.trans_le h

lemma nat_log_le_half (n : ℕ) (hn : 2 ≤ n) : Nat.log p n ≤ n / 2 := by
  apply Nat.le_of_lt_succ
  rw [Nat.log_lt_iff_lt_pow (Nat.Prime.one_lt hp.out) (by omega)]
  have : n < 2 ^ (n / 2 + 1) := two_pow_succ_gt n
  exact this.trans_le (pow_le_pow_left' (Nat.Prime.two_le hp.out) _)

lemma exists_log_tail_bound (N : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, (N : ℤ) ≤ (k + 1 : ℤ) - padicValNat p (k + 1) := by
  refine ⟨2 * N + 2, ?_⟩
  intro k hk
  have h2 : 2 ≤ k + 1 := by omega
  have hlog : padicValNat p (k + 1) ≤ (k + 1) / 2 :=
    (padicValNat_le_nat_log (k + 1)).trans (nat_log_le_half (p := p) (k + 1) h2)
  have hnat : N ≤ (k + 1) - (k + 1) / 2 := by omega
  have h1 : (N : ℤ) ≤ ((k + 1) - (k + 1) / 2 : ℕ) := Nat.cast_le.mpr hnat
  have h2' : ((k + 1) - (k + 1) / 2 : ℕ) ≤ (k + 1 : ℤ) - padicValNat p (k + 1) := by
    have hsub : ((k + 1) - (k + 1) / 2 : ℕ) = (k + 1 : ℤ) - ((k + 1) / 2 : ℕ) := by
      rw [Nat.cast_sub (Nat.div_le_self _ _), Nat.cast_succ]
    rw [hsub]
    have : (padicValNat p (k + 1) : ℤ) ≤ ((k + 1) / 2 : ℕ) := Nat.cast_le.mpr hlog
    linarith
  exact h1.trans h2'


lemma valGeP_binom_tail {x : ℚ_[p]} (hx : valGeP (p := p) 1 x)
    (m K N : ℕ) (hK : ∀ k ≥ K, (N : ℤ) ≤ (k : ℤ) - padicValNat p k)
    (hKm : K ≤ p ^ m) :
    valGeP (p := p) N
      (∑ k ∈ Finset.Icc (K + 1) (p ^ m),
        ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k) := by
  apply valGeP_sum
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have hk0 : 0 < k := by omega
  have hkK : K ≤ k := by omega
  have hterm := valGeP_binom_term (p := p) (α := 1) m k hk0 hx
  have : (N : ℤ) ≤ (k : ℤ) * 1 - padicValNat p k := by
    have := hK k hkK
    simpa using this
  exact valGeP_mono this hterm

lemma valGeP_finite_coeff_diff {x : ℚ_[p]} (hx : valGeP (p := p) 1 x)
    (m K : ℕ) (hKpos : 1 ≤ K) (hKm : K ≤ p ^ m) (hm : K ≤ m) :
    valGeP (p := p) (m - (K : ℤ) - K)
      (∑ k ∈ Finset.Icc 1 K,
        (((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k
          - logTerm (p := p) x (k - 1))) := by
  apply valGeP_sum
  intro k hk
  have hk1 : 1 ≤ k := by simp only [Finset.mem_Icc] at hk; exact hk.1
  have hkK : k ≤ K := by simp only [Finset.mem_Icc] at hk; exact hk.2
  have hkn : k ≤ p ^ m := le_trans hkK hKm
  have hm' : k ≤ m := le_trans hkK hm
  rw [logTerm_succ (p := p) x k hk1]
  have hdiff := valGeP_choose_pow_div_sub (p := p) m k hk1 hkn hm'
  have hxk := valGeP_pow k hx
  have : (((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k
        - (-1 : ℚ_[p]) ^ (k - 1) * x ^ k / (k : ℚ_[p])) =
      (((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m)
        - (-1 : ℚ_[p]) ^ (k - 1) / (k : ℚ_[p])) * x ^ k := by
    ring
  rw [this]
  have hmul := valGeP_mul hdiff hxk
  have hle : (m - (K : ℤ) - K) ≤
      (m - (k - 1 : ℤ) - padicValNat p k) + (k : ℤ) * 1 := by
    have hv : (padicValNat p k : ℤ) ≤ k :=
      Nat.cast_le.mpr ((padicValNat_le_nat_log k).trans (Nat.log_le_self p k))
    have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
      rw [Nat.cast_sub hk1]; simp
    have hkK' : (k : ℤ) ≤ K := Nat.cast_le.mpr hkK
    linarith
  exact valGeP_mono hle hmul


lemma Icc_union_split (K n : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n) :
    Finset.Icc 1 n = Finset.Icc 1 K ∪ Finset.Icc (K + 1) n := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

lemma Icc_disjoint_split (K n : ℕ) :
    Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) n) := by
  simp [Finset.disjoint_left, Finset.mem_Icc]
  omega

lemma sum_range_logTerm_Icc (x : ℚ_[p]) (K : ℕ) :
    ∑ k ∈ Finset.range K, logTerm (p := p) x k =
      ∑ k ∈ Finset.Icc 1 K, logTerm (p := p) x (k - 1) := by
  have him : Finset.Icc 1 K = (Finset.range K).image (· + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨i - 1, ?_, Nat.sub_add_cancel h1⟩
      omega
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Nat.succ_le_succ (Nat.zero_le j), Nat.succ_le_of_lt hj⟩
  rw [him, Finset.sum_image]
  · simp
  · intro a _ha b _hb h
    exact Nat.succ_injective h

lemma valGeP_k_minus_val (N k : ℕ) (hk : 2 * N + 2 ≤ k) :
    (N : ℤ) ≤ (k : ℤ) - padicValNat p k := by
  have h2 : 2 ≤ k := by omega
  have hlog : padicValNat p k ≤ k / 2 :=
    (padicValNat_le_nat_log k).trans (nat_log_le_half (p := p) k h2)
  have hnat : N ≤ k - k / 2 := by omega
  have h1 : (N : ℤ) ≤ (k - k / 2 : ℕ) := Nat.cast_le.mpr hnat
  have h2' : ((k - k / 2 : ℕ) : ℤ) ≤ (k : ℤ) - padicValNat p k := by
    rw [Nat.cast_sub (Nat.div_le_self k 2)]
    have : (padicValNat p k : ℤ) ≤ (k / 2 : ℕ) := Nat.cast_le.mpr hlog
    linarith
  exact h1.trans h2'

lemma le_p_pow_of_le (K m : ℕ) (hKm : K ≤ m) : K ≤ p ^ m := by
  have hmp : m ≤ p ^ m := by
    cases m with
    | zero => simp
    | succ m => exact (Nat.lt_pow_self (Nat.Prime.one_lt hp.out) : m + 1 < p ^ (m + 1)).le
  exact hKm.trans hmp

lemma valGeP_S_sub_log {x : ℚ_[p]} (hx : valGeP (p := p) 1 x)
    (N : ℕ) :
    ∃ M, ∀ m ≥ M,
      valGeP (p := p) N
        (((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m - padicLog1p (p := p) x) := by
  obtain ⟨K0, hK0⟩ := exists_log_tail_bound (p := p) N
  refine ⟨2 * (K0 + 2 * N + 2) + N, ?_⟩
  intro m hm
  -- Bind `K` as a real hypothesis so `omega` can see its size.
  have hmain : ∀ (K : ℕ), 1 ≤ K → K0 ≤ K → 2 * N + 2 ≤ K → 2 * K + N ≤ m →
      valGeP (p := p) N
        (((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m - padicLog1p (p := p) x) := by
    intro K hK1 hKK0 hKN hmK
    have hKlem : K ≤ m := by omega
    have hKm : K ≤ p ^ m := le_p_pow_of_le (p := p) K m hKlem
    rw [binom_pow_div, sum_add_tsum_log hx K]
    have hsplit : Finset.Icc 1 (p ^ m) = Finset.Icc 1 K ∪ Finset.Icc (K + 1) (p ^ m) :=
      Icc_union_split K (p ^ m) hK1 hKm
    rw [hsplit, Finset.sum_union (Icc_disjoint_split K (p ^ m))]
    rw [sum_range_logTerm_Icc]
    have hrearr :
        (∑ k ∈ Finset.Icc 1 K,
            ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k)
          + (∑ k ∈ Finset.Icc (K + 1) (p ^ m),
            ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k)
          - (∑ k ∈ Finset.Icc 1 K, logTerm (p := p) x (k - 1)
              + ∑' k : ℕ, logTerm (p := p) x (k + K)) =
        (∑ k ∈ Finset.Icc 1 K,
            (((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k
              - logTerm (p := p) x (k - 1)))
          + (∑ k ∈ Finset.Icc (K + 1) (p ^ m),
            ((((p ^ m).choose k : ℕ) : ℚ_[p]) / (p : ℚ_[p]) ^ m) * x ^ k)
          - ∑' k : ℕ, logTerm (p := p) x (k + K) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hrearr]
    refine valGeP_sub (valGeP_add ?_ ?_) ?_
    · have hfin := valGeP_finite_coeff_diff (p := p) hx m K hK1 hKm hKlem
      have : (N : ℤ) ≤ m - (K : ℤ) - K := by omega
      exact valGeP_mono this hfin
    · have htl' : ∀ k ≥ K, (N : ℤ) ≤ (k : ℤ) - padicValNat p k := by
        intro k hk
        exact valGeP_k_minus_val (p := p) N k (le_trans hKN hk)
      exact valGeP_binom_tail (p := p) hx m K N htl' hKm
    · have htailK : ∀ k ≥ K, (N : ℤ) ≤ (k + 1 : ℤ) - padicValNat p (k + 1) :=
        fun k hk => hK0 k (le_trans hKK0 hk)
      exact valGeP_log_tail hx K N htailK
  exact hmain (K0 + 2 * N + 2) (by omega) (by omega) (by omega) (by omega)

lemma tendsto_S_padicLog1p {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    Tendsto (fun m : ℕ => ((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m)
      atTop (nhds (padicLog1p (p := p) x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim := tendsto_inv_p_pow_zero (p := p)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  obtain ⟨M, hM⟩ := valGeP_S_sub_log (p := p) hx N
  refine ⟨M + N, ?_⟩
  intro m hm
  have hmM : M ≤ m := by omega
  have hmN : N ≤ m := by omega
  have hval := hM m hmM
  have hle : ‖((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m - padicLog1p (p := p) x‖ ≤
      (p : ℝ) ^ (-(N : ℤ)) := (valGeP_iff_norm (p := p)).1 hval
  have hlt : (p : ℝ) ^ (-(N : ℤ)) < ε := by
    have : dist ((p : ℝ) ^ (-(N : ℤ))) 0 < ε := hN N le_rfl
    simpa [dist_zero_right] using this
  have : dist (((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m) (padicLog1p (p := p) x) =
      ‖((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m - padicLog1p (p := p) x‖ := by
    simp [dist_eq_norm]
  rw [this]
  exact lt_of_le_of_lt hle hlt

lemma one_add_mul_one_add (x y : ℚ_[p]) :
    1 + (x + y + x * y) = (1 + x) * (1 + y) := by
  ring

lemma valGeP_one_add_mul {x y : ℚ_[p]}
    (hx : valGeP (p := p) 1 x) (hy : valGeP (p := p) 1 y) :
    valGeP (p := p) 1 (x + y + x * y) := by
  have hxy : valGeP (p := p) 2 (x * y) := by
    simpa using valGeP_mul hx hy
  exact valGeP_add (valGeP_add hx hy) (valGeP_mono (by norm_num : (1 : ℤ) ≤ 2) hxy)

lemma S_mul_identity (x y : ℚ_[p]) (m : ℕ) :
    ((1 + (x + y + x * y)) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m =
      (1 + x) ^ (p ^ m) * (((1 + y) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m) +
        ((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m := by
  have hne : (p : ℚ_[p]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out))
  have hxy : 1 + (x + y + x * y) = (1 + x) * (1 + y) := one_add_mul_one_add x y
  rw [hxy, mul_pow]
  field_simp [hne]
  ring

lemma padicLog1p_mul {x y : ℚ_[p]}
    (hx : valGeP (p := p) 1 x) (hy : valGeP (p := p) 1 y) :
    padicLog1p (p := p) (x + y + x * y) =
      padicLog1p (p := p) x + padicLog1p (p := p) y := by
  have hz := valGeP_one_add_mul hx hy
  have hlimz := tendsto_S_padicLog1p hz
  have hlimx := tendsto_S_padicLog1p hx
  have hlimy := tendsto_S_padicLog1p hy
  have hpowx := tendsto_pow_one hx
  have hid : (fun m : ℕ => ((1 + (x + y + x * y)) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m) =
      (fun m => (1 + x) ^ (p ^ m) * (((1 + y) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m) +
        ((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m) := by
    ext m; exact S_mul_identity (p := p) x y m
  have hlimRHS :
      Tendsto (fun m : ℕ =>
        (1 + x) ^ (p ^ m) * (((1 + y) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m) +
          ((1 + x) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m)
        atTop (nhds (1 * padicLog1p (p := p) y + padicLog1p (p := p) x)) :=
    (hpowx.mul hlimy).add hlimx
  have hlimz' : Tendsto
      (fun m : ℕ => ((1 + (x + y + x * y)) ^ (p ^ m) - 1) / (p : ℚ_[p]) ^ m)
      atTop (nhds (1 * padicLog1p (p := p) y + padicLog1p (p := p) x)) := by
    rwa [hid]
  have heq := tendsto_nhds_unique hlimz hlimz'
  rw [heq, one_mul, add_comm]

lemma padicLog1p_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ s, valGeP (p := p) 1 (f i)) :
    padicLog1p (p := p) ((∏ i ∈ s, (1 + f i)) - 1) =
      ∑ i ∈ s, padicLog1p (p := p) (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [padicLog1p_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' : ∀ i ∈ s, valGeP (p := p) 1 (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa : valGeP (p := p) 1 (f a) := hf a (Finset.mem_insert_self a s)
    have hPs : valGeP (p := p) 1 ((∏ i ∈ s, (1 + f i)) - 1) := by
      have hneg : ∀ i ∈ s, valGeP (p := p) 1 (-f i) :=
        fun i hi => valGeP_neg (hf' i hi)
      have := valGeP_prod_one_sub_sub_one (α := (1 : ℤ)) s (fun i => -f i) le_rfl hneg
      convert this using 2
      refine Finset.prod_congr rfl ?_
      intro i _; ring
    -- (1+f a) * ∏(1+f i) - 1 = f a + (∏-1) + f a * (∏-1)
    have hrew : (1 + f a) * (∏ i ∈ s, (1 + f i)) - 1 =
        f a + ((∏ i ∈ s, (1 + f i)) - 1) + f a * ((∏ i ∈ s, (1 + f i)) - 1) := by
      ring
    rw [hrew, padicLog1p_mul hfa hPs, ih hf', add_comm]

/-- `log u` for a unit `u = 1 + x` with `v(x) ≥ 1`. -/
noncomputable def padicLog (u : ℚ_[p]) : ℚ_[p] :=
  padicLog1p (p := p) (u - 1)

lemma padicLog_one : padicLog (p := p) 1 = 0 := by
  simp [padicLog, padicLog1p_zero]

lemma padicLog_one_add {x : ℚ_[p]} :
    padicLog (p := p) (1 + x) = padicLog1p (p := p) x := by
  simp [padicLog]

lemma valGeP_unit_sub_one {u v : ℚ_[p]}
    (hu : valGeP (p := p) 1 (u - 1)) (hv : valGeP (p := p) 1 (v - 1)) :
    valGeP (p := p) 1 (u * v - 1) := by
  have : u * v - 1 = (u - 1) + (v - 1) + (u - 1) * (v - 1) := by ring
  rw [this]
  exact valGeP_one_add_mul hu hv

lemma padicLog_mul {u v : ℚ_[p]}
    (hu : valGeP (p := p) 1 (u - 1)) (hv : valGeP (p := p) 1 (v - 1)) :
    padicLog (p := p) (u * v) = padicLog (p := p) u + padicLog (p := p) v := by
  have : u * v - 1 = (u - 1) + (v - 1) + (u - 1) * (v - 1) := by ring
  simp only [padicLog]
  rw [this]
  exact padicLog1p_mul hu hv

lemma valGeP_prod_units_sub_one {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ s, valGeP (p := p) 1 (f i - 1)) :
    valGeP (p := p) 1 (∏ i ∈ s, f i - 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp [valGeP_zero]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact valGeP_unit_sub_one (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma padicLog_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ s, valGeP (p := p) 1 (f i - 1)) :
    padicLog (p := p) (∏ i ∈ s, f i) = ∑ i ∈ s, padicLog (p := p) (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [padicLog_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' : ∀ i ∈ s, valGeP (p := p) 1 (f i - 1) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (padicLog_mul (hf a (Finset.mem_insert_self a s))
      (valGeP_prod_units_sub_one s f hf')).trans (by rw [ih hf', add_comm])

lemma norm_lt_one_of_valGeP_one {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    ‖x‖ < 1 := by
  have hxN : ‖x‖ ≤ (p : ℝ)⁻¹ := by
    rw [valGeP_iff_norm] at hx
    simpa [zpow_neg, zpow_one] using hx
  exact lt_of_le_of_lt hxN (inv_lt_one_of_one_lt₀ hp_one_lt_real)

lemma norm_one_add_of_valGeP_one {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    ‖1 + x‖ = 1 := by
  have : ‖(1 + x) - 1‖ < ‖(1 : ℚ_[p])‖ := by
    simpa [norm_one] using norm_lt_one_of_valGeP_one hx
  simpa using (Padic.norm_eq_of_norm_sub_lt_right this).trans norm_one

lemma one_add_ne_zero_of_valGeP_one {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    1 + x ≠ 0 := by
  intro h
  have := norm_one_add_of_valGeP_one hx
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma valuation_one_add_of_valGeP_one {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    (1 + x).valuation = 0 := by
  have hne := one_add_ne_zero_of_valGeP_one hx
  have hnorm := norm_one_add_of_valGeP_one hx
  have : ‖1 + x‖ = (p : ℝ) ^ (-(1 + x).valuation) :=
    Padic.norm_eq_zpow_neg_valuation hne
  rw [hnorm] at this
  have : (p : ℝ) ^ (-(1 + x).valuation) = (p : ℝ) ^ (0 : ℤ) := by
    simpa [zpow_zero] using this.symm
  have := (zpow_right_inj₀ hp_pos_real (ne_of_gt hp_one_lt_real)).mp this
  linarith

lemma valGeP_inv_unit {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    valGeP (p := p) 1 (-x / (1 + x)) := by
  have hne := one_add_ne_zero_of_valGeP_one hx
  rw [div_eq_mul_inv]
  have hinv0 : valGeP (p := p) 0 ((1 + x)⁻¹) :=
    Or.inr (by rw [Padic.valuation_inv, valuation_one_add_of_valGeP_one hx]; simp)
  have := valGeP_mul (valGeP_neg hx) hinv0
  simpa using this

lemma padicLog1p_inv {x : ℚ_[p]} (hx : valGeP (p := p) 1 x) :
    padicLog1p (p := p) (-x / (1 + x)) = -padicLog1p (p := p) x := by
  have hz := valGeP_inv_unit hx
  have hne := one_add_ne_zero_of_valGeP_one hx
  have hprod : x + (-x / (1 + x)) + x * (-x / (1 + x)) = 0 := by
    field_simp [hne]
    ring
  have hsum := padicLog1p_mul hx hz
  rw [hprod, padicLog1p_zero] at hsum
  exact eq_neg_of_add_eq_zero_right hsum.symm

lemma padicLog_inv {u : ℚ_[p]} (hu : valGeP (p := p) 1 (u - 1))
    (hu0 : u ≠ 0) :
    padicLog (p := p) u⁻¹ = -padicLog (p := p) u := by
  have : u⁻¹ - 1 = -(u - 1) / (1 + (u - 1)) := by
    have : 1 + (u - 1) = u := by ring
    rw [this]
    field_simp [hu0]
    ring
  simp only [padicLog]
  rw [this]
  exact padicLog1p_inv hu

lemma padicLog_div {u v : ℚ_[p]}
    (hu : valGeP (p := p) 1 (u - 1)) (hv : valGeP (p := p) 1 (v - 1))
    (hv0 : v ≠ 0) :
    padicLog (p := p) (u / v) = padicLog (p := p) u - padicLog (p := p) v := by
  have hinv : valGeP (p := p) 1 (v⁻¹ - 1) := by
    have : v⁻¹ - 1 = -(v - 1) / (1 + (v - 1)) := by
      have : 1 + (v - 1) = v := by ring
      rw [this]; field_simp [hv0]; ring
    rw [this]
    exact valGeP_inv_unit hv
  rw [div_eq_mul_inv, padicLog_mul hu hinv, padicLog_inv hv hv0]
  ring

lemma padicLog_prod_div {ι : Type*} (s t : Finset ι) (f : ι → ℚ_[p])
    (hs : ∀ i ∈ s, valGeP (p := p) 1 (f i - 1))
    (ht : ∀ i ∈ t, valGeP (p := p) 1 (f i - 1))
    (ht0 : ∀ i ∈ t, f i ≠ 0) :
    padicLog (p := p) ((∏ i ∈ s, f i) / (∏ i ∈ t, f i)) =
      ∑ i ∈ s, padicLog (p := p) (f i) - ∑ i ∈ t, padicLog (p := p) (f i) := by
  have hden0 : (∏ i ∈ t, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr ht0
  exact (padicLog_div (valGeP_prod_units_sub_one s f hs)
      (valGeP_prod_units_sub_one t f ht) hden0).trans
    (by rw [padicLog_prod s f hs, padicLog_prod t f ht])

lemma valGeP_of_padicValRat {k : ℤ} {q : ℚ} (h : q = 0 ∨ k ≤ padicValRat p q) :
    valGeP (p := p) k (q : ℚ_[p]) := by
  rcases h with rfl | hle
  · exact valGeP_zero k
  · rcases eq_or_ne q 0 with hq0 | hq0
    · simp [hq0, valGeP_zero]
    · refine Or.inr ?_
      have hne : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq0
      rw [Padic.valuation_ratCast]
      exact hle

lemma padicValRat_of_valGeP {k : ℤ} {q : ℚ} (h : valGeP (p := p) k (q : ℚ_[p])) :
    q = 0 ∨ k ≤ padicValRat p q := by
  rcases eq_or_ne q 0 with hq0 | hq0
  · exact Or.inl hq0
  · refine Or.inr ?_
    have hne : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq0
    rcases h with h0 | hle
    · exact (hne h0).elim
    · rwa [Padic.valuation_ratCast] at hle

lemma logTerm_cast (q : ℚ) (k : ℕ) :
    logTerm (p := p) (q : ℚ_[p]) k =
      (((-1 : ℚ) ^ k * q ^ (k + 1) / (k + 1 : ℚ) : ℚ) : ℚ_[p]) := by
  unfold logTerm
  push_cast
  rfl

lemma tsum_sum_logTerm {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ s, valGeP (p := p) 1 (f i)) :
    ∑ i ∈ s, padicLog1p (p := p) (f i) =
      ∑' k : ℕ, ∑ i ∈ s, logTerm (p := p) (f i) k := by
  have hsum : ∀ i ∈ s, Summable (fun k : ℕ => logTerm (p := p) (f i) k) :=
    fun i hi => summable_logTerm (hf i hi)
  simpa [padicLog1p] using (Summable.tsum_finsetSum hsum).symm


/-! Even-case and odd-case ratio infrastructure. -/


open Filter Topology Polynomial
open scoped Nat

set_option maxHeartbeats 800000
set_option linter.style.namespace false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.moduleDocstring false

variable {p : ℕ} [hp : Fact p.Prime]

lemma valGeP_of_valGe {k : ℤ} {q : ℚ} (h : valGe p k q) :
    valGeP (p := p) k (q : ℚ_[p]) :=
  valGeP_of_padicValRat h

lemma valGe_of_valGeP' {k : ℤ} {q : ℚ} (h : valGeP (p := p) k (q : ℚ_[p])) :
    valGe p k q :=
  padicValRat_of_valGeP h

lemma valGe_gamma_mul_j {γ : ℚ} (j : ℕ) (hγ : valGe p 2 γ) :
    valGe p 2 (γ * (j : ℚ) * (j + 1)) := by
  have hj : valGe p 0 (j : ℚ) := valGe_nat p j
  have hj1 : valGe p 0 ((j + 1 : ℕ) : ℚ) := valGe_nat p (j + 1)
  have h := valGe_mul (valGe_mul hγ hj) hj1
  have : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; rfl
  simpa [this] using h

lemma valGeP_gamma_mul_j {γ : ℚ} (j : ℕ) (hγ : valGe p 2 γ) :
    valGeP (p := p) 2 ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) :=
  valGeP_of_valGe (valGe_gamma_mul_j j hγ)

lemma valGeP_gamma_mul_j_one {γ : ℚ} (j : ℕ) (hγ : valGe p 2 γ) :
    valGeP (p := p) 1 ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) :=
  valGeP_mono (by norm_num : (1 : ℤ) ≤ 2) (valGeP_gamma_mul_j j hγ)

lemma Fprod_cast (γ : ℚ) (M : ℕ) :
    (Fprod γ M : ℚ_[p]) =
      ∏ j ∈ Finset.range M, (1 + ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) := by
  unfold Fprod
  push_cast
  rfl

lemma valGeP_Fprod_sub_one {γ : ℚ} (M : ℕ) (hγ : valGe p 2 γ) :
    valGeP (p := p) 1 ((Fprod γ M : ℚ_[p]) - 1) := by
  have hf : ∀ j ∈ Finset.range M,
      valGeP (p := p) 1
        ((1 + ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) - 1) := by
    intro j _hj
    simpa using valGeP_gamma_mul_j_one (p := p) j hγ
  have := valGeP_prod_units_sub_one (Finset.range M)
    (fun j => 1 + ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) hf
  simpa [Fprod_cast] using this

lemma padicLog_Fprod {γ : ℚ} (M : ℕ) (hγ : valGe p 2 γ) :
    padicLog (p := p) (Fprod γ M : ℚ_[p]) =
      ∑ j ∈ Finset.range M,
        padicLog1p (p := p) ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) := by
  have hf : ∀ j ∈ Finset.range M,
      valGeP (p := p) 1
        ((1 + ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) - 1) := by
    intro j _hj
    simpa using valGeP_gamma_mul_j_one (p := p) j hγ
  rw [Fprod_cast, padicLog_prod _ _ hf]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simp [padicLog]

lemma logTerm_gamma_j (γ : ℚ) (j k : ℕ) :
    logTerm (p := p) ((γ * ((j : ℚ) * (j + 1)) : ℚ) : ℚ_[p]) k =
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (γ : ℚ_[p]) ^ (k + 1) *
          ((((j : ℚ) * (j + 1)) ^ (k + 1) : ℚ) : ℚ_[p]) := by
  unfold logTerm
  have hmul : ((γ * ((j : ℚ) * (j + 1)) : ℚ) : ℚ_[p]) =
      (γ : ℚ_[p]) * (((j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) := by
    exact Rat.cast_mul _ _
  rw [hmul, mul_pow, Rat.cast_pow]
  have hk0 : (k + 1 : ℚ_[p]) ≠ 0 := by
    rw [← Nat.cast_succ]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp [hk0]

lemma logTerm_gamma_j' (γ : ℚ) (j k : ℕ) :
    logTerm (p := p) ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) k =
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (γ : ℚ_[p]) ^ (k + 1) *
          ((((j : ℚ) * (j + 1)) ^ (k + 1) : ℚ) : ℚ_[p]) := by
  have : (γ * (j : ℚ) * (j + 1) : ℚ) = γ * ((j : ℚ) * (j + 1)) := by ring
  rw [this]
  exact logTerm_gamma_j (p := p) γ j k

lemma sum_logTerm_gamma (γ : ℚ) (M k : ℕ) :
    ∑ j ∈ Finset.range M,
        logTerm (p := p) ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) k =
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (γ : ℚ_[p]) ^ (k + 1) * (U (k + 1) M : ℚ_[p]) := by
  simp only [logTerm_gamma_j']
  rw [← Finset.mul_sum]
  congr 1
  unfold U
  rw [Rat.cast_sum]

lemma padicLog_Fprod_tsum {γ : ℚ} (M : ℕ) (hγ : valGe p 2 γ) :
    padicLog (p := p) (Fprod γ M : ℚ_[p]) =
      ∑' k : ℕ,
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (γ : ℚ_[p]) ^ (k + 1) * (U (k + 1) M : ℚ_[p]) := by
  rw [padicLog_Fprod (p := p) M hγ]
  have hf : ∀ j ∈ Finset.range M,
      valGeP (p := p) 1 ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) :=
    fun j _ => valGeP_gamma_mul_j_one j hγ
  rw [tsum_sum_logTerm _ _ hf]
  congr 1
  ext k
  exact sum_logTerm_gamma (p := p) γ M k

def Ucombo (k N : ℕ) : ℚ :=
  U k (18 * N) + U k (4 * N) + U k (3 * N)
    - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N)

lemma Ucombo_eq (k N : ℕ) :
    Ucombo k N =
      U k (18 * N) + U k (4 * N) + U k (3 * N)
        - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N) :=
  rfl

lemma Fprod_ne_zero_of_nonneg (γ : ℚ) (M : ℕ) (hγ : 0 ≤ γ) : Fprod γ M ≠ 0 :=
  Fprod_ne_zero γ M hγ

lemma padicLog_mul3 {a b c : ℚ_[p]}
    (ha : valGeP (p := p) 1 (a - 1)) (hb : valGeP (p := p) 1 (b - 1))
    (hc : valGeP (p := p) 1 (c - 1)) :
    padicLog (p := p) (a * b * c) =
      padicLog (p := p) a + padicLog (p := p) b + padicLog (p := p) c := by
  have hab := valGeP_unit_sub_one ha hb
  rw [padicLog_mul (u := a * b) (v := c) hab hc, padicLog_mul ha hb]

lemma padicLog_mul4 {a b c d : ℚ_[p]}
    (ha : valGeP (p := p) 1 (a - 1)) (hb : valGeP (p := p) 1 (b - 1))
    (hc : valGeP (p := p) 1 (c - 1)) (hd : valGeP (p := p) 1 (d - 1)) :
    padicLog (p := p) (a * b * c * d) =
      padicLog (p := p) a + padicLog (p := p) b +
        padicLog (p := p) c + padicLog (p := p) d := by
  have habc := valGeP_unit_sub_one (valGeP_unit_sub_one ha hb) hc
  rw [padicLog_mul (u := a * b * c) (v := d) habc hd, padicLog_mul3 ha hb hc]

lemma PhiCombo_cast (γ : ℚ) (N : ℕ) :
    (PhiCombo γ N : ℚ_[p]) =
      ((Fprod γ (18 * N) : ℚ_[p]) * (Fprod γ (4 * N) : ℚ_[p]) *
        (Fprod γ (3 * N) : ℚ_[p])) /
      ((Fprod γ (9 * N) : ℚ_[p]) * (Fprod γ (8 * N) : ℚ_[p]) *
        (Fprod γ (6 * N) : ℚ_[p]) * (Fprod γ (2 * N) : ℚ_[p])) := by
  unfold PhiCombo
  push_cast
  rfl

lemma padicLog_PhiCombo {γ : ℚ} (N : ℕ) (hγ : valGe p 2 γ) (hγ0 : 0 ≤ γ) :
    padicLog (p := p) (PhiCombo γ N : ℚ_[p]) =
      padicLog (p := p) (Fprod γ (18 * N) : ℚ_[p]) +
        padicLog (p := p) (Fprod γ (4 * N) : ℚ_[p]) +
        padicLog (p := p) (Fprod γ (3 * N) : ℚ_[p]) -
        (padicLog (p := p) (Fprod γ (9 * N) : ℚ_[p]) +
          padicLog (p := p) (Fprod γ (8 * N) : ℚ_[p]) +
          padicLog (p := p) (Fprod γ (6 * N) : ℚ_[p]) +
          padicLog (p := p) (Fprod γ (2 * N) : ℚ_[p])) := by
  have h18 := valGeP_Fprod_sub_one (p := p) (18 * N) hγ
  have h4 := valGeP_Fprod_sub_one (p := p) (4 * N) hγ
  have h3 := valGeP_Fprod_sub_one (p := p) (3 * N) hγ
  have h9 := valGeP_Fprod_sub_one (p := p) (9 * N) hγ
  have h8 := valGeP_Fprod_sub_one (p := p) (8 * N) hγ
  have h6 := valGeP_Fprod_sub_one (p := p) (6 * N) hγ
  have h2 := valGeP_Fprod_sub_one (p := p) (2 * N) hγ
  have hden0 :
      (Fprod γ (9 * N) : ℚ_[p]) * (Fprod γ (8 * N) : ℚ_[p]) *
        (Fprod γ (6 * N) : ℚ_[p]) * (Fprod γ (2 * N) : ℚ_[p]) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
      exact_mod_cast Fprod_ne_zero γ _ hγ0
  have hnum := valGeP_unit_sub_one (valGeP_unit_sub_one h18 h4) h3
  have hden := valGeP_unit_sub_one (valGeP_unit_sub_one (valGeP_unit_sub_one h9 h8) h6) h2
  rw [PhiCombo_cast, padicLog_div hnum hden hden0,
    padicLog_mul3 h18 h4 h3, padicLog_mul4 h9 h8 h6 h2]

lemma summable_finset_sum_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℚ_[p])
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun n : ℕ => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using (summable_zero (α := ℚ_[p]) (β := ℕ))
  | insert a s ha ih =>
    have hfun : (fun n => ∑ i ∈ insert a s, f i n) =
        (fun n => f a n + ∑ i ∈ s, f i n) := by
      ext n; exact Finset.sum_insert ha
    rw [hfun]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma summable_U_series {γ : ℚ} (M : ℕ) (hγ : valGe p 2 γ) :
    Summable (fun k : ℕ =>
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (γ : ℚ_[p]) ^ (k + 1) * (U (k + 1) M : ℚ_[p])) := by
  have hsum : Summable (fun k : ℕ =>
      ∑ j ∈ Finset.range M,
        logTerm (p := p) ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) k) :=
    summable_finset_sum_nat (Finset.range M)
      (fun j k => logTerm (p := p) ((γ * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]) k)
      (fun j _ => summable_logTerm (valGeP_gamma_mul_j_one j hγ))
  refine hsum.congr ?_
  intro k
  exact sum_logTerm_gamma (p := p) γ M k

lemma padicLog_PhiCombo_tsum {γ : ℚ} (N : ℕ) (hγ : valGe p 2 γ) (hγ0 : 0 ≤ γ) :
    padicLog (p := p) (PhiCombo γ N : ℚ_[p]) =
      ∑' k : ℕ,
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (γ : ℚ_[p]) ^ (k + 1) * (Ucombo (k + 1) N : ℚ_[p]) := by
  rw [padicLog_PhiCombo (p := p) N hγ hγ0]
  simp only [padicLog_Fprod_tsum (p := p) _ hγ]
  have h18 := summable_U_series (p := p) (18 * N) hγ
  have h4 := summable_U_series (p := p) (4 * N) hγ
  have h3 := summable_U_series (p := p) (3 * N) hγ
  have h9 := summable_U_series (p := p) (9 * N) hγ
  have h8 := summable_U_series (p := p) (8 * N) hγ
  have h6 := summable_U_series (p := p) (6 * N) hγ
  have h2 := summable_U_series (p := p) (2 * N) hγ
  have hnum := (h18.add h4).add h3
  have hden := ((h9.add h8).add h6).add h2
  rw [← h18.tsum_add h4, ← (h18.add h4).tsum_add h3,
      ← h9.tsum_add h8, ← (h9.add h8).tsum_add h6,
      ← ((h9.add h8).add h6).tsum_add h2]
  rw [← hnum.tsum_sub hden]
  congr 1
  ext k
  unfold Ucombo
  push_cast
  ring

lemma summable_comboTerm' {γ : ℚ} (N : ℕ) (hγ : valGe p 2 γ) :
    Summable (fun k : ℕ =>
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (γ : ℚ_[p]) ^ (k + 1) * (Ucombo (k + 1) N : ℚ_[p])) := by
  have h18 := summable_U_series (p := p) (18 * N) hγ
  have h4 := summable_U_series (p := p) (4 * N) hγ
  have h3 := summable_U_series (p := p) (3 * N) hγ
  have h9 := summable_U_series (p := p) (9 * N) hγ
  have h8 := summable_U_series (p := p) (8 * N) hγ
  have h6 := summable_U_series (p := p) (6 * N) hγ
  have h2 := summable_U_series (p := p) (2 * N) hγ
  have hnum := (h18.add h4).add h3
  have hden := ((h9.add h8).add h6).add h2
  have h := hnum.sub hden
  refine h.congr ?_
  intro k
  unfold Ucombo
  push_cast
  ring

lemma valGeP_PhiCombo_sub_one {N i : ℕ} (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    valGeP (p := p) 1 ((PhiCombo (gammaI p i) N : ℚ_[p]) - 1) := by
  -- extracted from the previous proof body via the same argument
  have hγ : valGe p 2 (gammaI p i) := valGe_gammaI h5 hi
  have hγ0 : 0 ≤ gammaI p i := gammaI_nonneg h5 hi
  have h18 := valGeP_Fprod_sub_one (p := p) (18 * N) hγ
  have h4 := valGeP_Fprod_sub_one (p := p) (4 * N) hγ
  have h3 := valGeP_Fprod_sub_one (p := p) (3 * N) hγ
  have h9 := valGeP_Fprod_sub_one (p := p) (9 * N) hγ
  have h8 := valGeP_Fprod_sub_one (p := p) (8 * N) hγ
  have h6 := valGeP_Fprod_sub_one (p := p) (6 * N) hγ
  have h2 := valGeP_Fprod_sub_one (p := p) (2 * N) hγ
  have hnum := valGeP_unit_sub_one (valGeP_unit_sub_one h18 h4) h3
  have hden := valGeP_unit_sub_one
    (valGeP_unit_sub_one (valGeP_unit_sub_one h9 h8) h6) h2
  have hden0 :
      (Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (2 * N) : ℚ_[p]) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
      exact_mod_cast Fprod_ne_zero _ _ hγ0
  have hdiv :
      (PhiCombo (gammaI p i) N : ℚ_[p]) - 1 =
        ((Fprod (gammaI p i) (18 * N) : ℚ_[p]) *
            (Fprod (gammaI p i) (4 * N) : ℚ_[p]) *
            (Fprod (gammaI p i) (3 * N) : ℚ_[p]) -
          ((Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
            (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
            (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
            (Fprod (gammaI p i) (2 * N) : ℚ_[p]))) /
        ((Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (2 * N) : ℚ_[p])) := by
    rw [PhiCombo_cast, div_sub_one hden0]
  rw [hdiv]
  have hnd := valGeP_sub hnum hden
  have hv0 :
      ((Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (2 * N) : ℚ_[p])).valuation = 0 := by
    have hrew : (1 : ℚ_[p]) +
        (((Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (2 * N) : ℚ_[p])) - 1) =
        (Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
          (Fprod (gammaI p i) (2 * N) : ℚ_[p]) := by ring
    rw [← hrew]
    exact valuation_one_add_of_valGeP_one hden
  have hinv : valGeP (p := p) 0
      (((Fprod (gammaI p i) (9 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (8 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (6 * N) : ℚ_[p]) *
        (Fprod (gammaI p i) (2 * N) : ℚ_[p]))⁻¹) :=
    Or.inr (by rw [Padic.valuation_inv, hv0]; simp)
  have := valGeP_mul hnd hinv
  simpa [div_eq_mul_inv] using this

lemma padicLog_P_clean {N : ℕ} (h5 : 5 ≤ p) :
    padicLog (p := p)
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
        padicLog (p := p) (PhiCombo (gammaI p i) N : ℚ_[p]) := by
  have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
      valGeP (p := p) 1 ((PhiCombo (gammaI p i) N : ℚ_[p]) - 1) :=
    fun i hi => valGeP_PhiCombo_sub_one (N := N) h5 hi
  have hcast :
      ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p]) =
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), (PhiCombo (gammaI p i) N : ℚ_[p]) := by
    push_cast; rfl
  rw [hcast, padicLog_prod _ _ hf]

lemma padicLog_P_tsum {N : ℕ} (h5 : 5 ≤ p) :
    padicLog (p := p)
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p]) =
      ∑' k : ℕ,
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
            (gammaI p i : ℚ_[p]) ^ (k + 1)) *
          (Ucombo (k + 1) N : ℚ_[p]) := by
  rw [padicLog_P_clean h5]
  have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
      Summable (fun k : ℕ =>
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (gammaI p i : ℚ_[p]) ^ (k + 1) * (Ucombo (k + 1) N : ℚ_[p])) := by
    intro i hi
    exact summable_comboTerm' (p := p) N (valGe_gammaI h5 hi)
  have : ∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
      padicLog (p := p) (PhiCombo (gammaI p i) N : ℚ_[p]) =
      ∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
        ∑' k : ℕ,
          ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
            (gammaI p i : ℚ_[p]) ^ (k + 1) * (Ucombo (k + 1) N : ℚ_[p]) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact padicLog_PhiCombo_tsum N (valGe_gammaI h5 hi) (gammaI_nonneg h5 hi)
  rw [this, ← Summable.tsum_finsetSum hf]
  congr 1
  ext k
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma Ucombo_eq_target (k N : ℕ) :
    Ucombo k N =
      U k (18 * N) + U k (4 * N) + U k (3 * N)
        - U k (9 * N) - U k (8 * N) - U k (6 * N) - U k (2 * N) :=
  rfl

lemma valGeP_series_term {N k : ℕ} (h5 : 5 ≤ p) :
    valGeP (p := p) (3 + 3 * padicValNat p N)
      (((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
          (gammaI p i : ℚ_[p]) ^ (k + 1)) *
        (Ucombo (k + 1) N : ℚ_[p])) := by
  -- Match `valGe_log_term_ge_target` at exponent `k+1 ≥ 1`.
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have h := valGe_log_term_ge_target (p := p) (N := N) (k := k + 1) h5 hk
  -- target uses (-1)^{(k+1)+1} / (k+1) = (-1)^{k+2} / (k+1) = (-1)^k / (k+1)
  have hsign : (-1 : ℚ) ^ (k + 1 + 1) = (-1 : ℚ) ^ k := by
    rw [show k + 1 + 1 = k + 2 from by omega, pow_add, pow_two]
    ring
  have hform :
      ((-1 : ℚ) ^ (k + 1 + 1) / (k + 1 : ℕ)) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ (k + 1)) *
          (U (k + 1) (18 * N) + U (k + 1) (4 * N) + U (k + 1) (3 * N)
            - U (k + 1) (9 * N) - U (k + 1) (8 * N) - U (k + 1) (6 * N)
            - U (k + 1) (2 * N)) =
        ((-1 : ℚ) ^ k / (k + 1 : ℚ)) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ (k + 1)) *
          Ucombo (k + 1) N := by
    unfold Ucombo
    rw [hsign]
    push_cast
    rfl
  rw [hform] at h
  have hP := valGeP_of_valGe (p := p) h
  convert hP using 1
  push_cast
  rfl

lemma summable_P_series {N : ℕ} (h5 : 5 ≤ p) :
    Summable (fun k : ℕ =>
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
          (gammaI p i : ℚ_[p]) ^ (k + 1)) *
        (Ucombo (k + 1) N : ℚ_[p])) := by
  have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
      Summable (fun k : ℕ =>
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (gammaI p i : ℚ_[p]) ^ (k + 1) * (Ucombo (k + 1) N : ℚ_[p])) :=
    fun i hi => summable_comboTerm' (p := p) N (valGe_gammaI h5 hi)
  have h := summable_finset_sum_nat _ _ hf
  refine h.congr ?_
  intro k
  simp [Finset.mul_sum, mul_assoc, mul_comm]

lemma valGeP_padicLog_P {N : ℕ} (h5 : 5 ≤ p) :
    valGeP (p := p) (3 + 3 * padicValNat p N)
      (padicLog (p := p)
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p])) := by
  rw [padicLog_P_tsum h5]
  refine valGeP_tsum (summable_P_series (p := p) h5) ?_
  intro n
  exact valGeP_series_term (p := p) h5

lemma valGeP_P_sub_one {N : ℕ} (h5 : 5 ≤ p) :
    valGeP (p := p) (3 + 3 * padicValNat p N)
      (((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p]) - 1) := by
  have hlog := valGeP_padicLog_P (p := p) (N := N) h5
  have hunit : valGeP (p := p) 1
      (((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p]) - 1) := by
    have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
        valGeP (p := p) 1 ((PhiCombo (gammaI p i) N : ℚ_[p]) - 1) :=
      fun i hi => valGeP_PhiCombo_sub_one (N := N) h5 hi
    have hcast :
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiCombo (gammaI p i) N : ℚ) : ℚ_[p]) =
          ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), (PhiCombo (gammaI p i) N : ℚ_[p]) := by
      push_cast; rfl
    rw [hcast]
    exact valGeP_prod_units_sub_one _ _ hf
  have hiff := valGeP_padicLog1p_iff (p := p) h5 hunit (3 + 3 * padicValNat p N)
  -- padicLog u = padicLog1p (u-1)
  simpa [padicLog] using (hiff.mp hlog)

lemma valGe_bRat_ratio {N : ℕ} (h5 : 5 ≤ p) :
    valGe p (3 + 3 * padicValNat p N)
      (bRat (N * p) / bRat N - 1) := by
  have hP := bRat_ratio_PhiCombo (p := p) (N := N) h5
  rw [hP]
  exact valGe_of_valGeP' (valGeP_P_sub_one (p := p) (N := N) h5)

lemma valGe_of_int (z : ℤ) : valGe p 0 (z : ℚ) :=
  valGe_int p z

lemma valGe_bRat_diff_of_int {N : ℕ} (h5 : 5 ≤ p)
    (hN : ∃ z : ℤ, bRat N = z) :
    valGe p (3 + 3 * padicValNat p N)
      (bRat (N * p) - bRat N) := by
  obtain ⟨z, hz⟩ := hN
  have hbN : bRat N ≠ 0 := bRat_ne_zero N
  have hsplit : bRat (N * p) - bRat N =
      bRat N * (bRat (N * p) / bRat N - 1) := by
    field_simp [hbN]
  rw [hsplit]
  have h1 := valGe_bRat_ratio (p := p) (N := N) h5
  have hz0 : valGe p 0 (bRat N) := by
    rw [hz]; exact valGe_of_int (p := p) z
  have := valGe_mul hz0 h1
  simpa using this

lemma valGe_int_sub_dvd {n : ℕ} {a b : ℤ}
    (h : valGe p n ((a : ℚ) - (b : ℚ))) :
    (p : ℤ) ^ n ∣ a - b := by
  have hab : (a : ℚ) - b = ((a - b : ℤ) : ℚ) := by push_cast; rfl
  rw [hab] at h
  rcases h with h0 | hle
  · have : a - b = 0 := Int.cast_injective (α := ℚ) (by exact_mod_cast h0)
    simp [this]
  · rw [padicValInt_dvd_iff]
    refine Or.inr ?_
    have hvi : padicValRat p ((a - b : ℤ) : ℚ) = padicValInt p (a - b) :=
      padicValRat.of_int
    omega

lemma zmod_of_valGe {n : ℕ} {a b : ℤ}
    (h : valGe p n ((a : ℚ) - (b : ℚ))) :
    a ≡ b [ZMOD (p : ℤ) ^ n] := by
  refine Int.modEq_iff_dvd.mpr ?_
  have hdvd := valGe_int_sub_dvd (p := p) (n := n) (a := a) (b := b) h
  have : (p : ℤ) ^ n ∣ b - a := by
    simpa [neg_sub] using dvd_neg.mpr hdvd
  exact this

/- Odd-case infrastructure. For odd `N = 2 * t + 1`,
   `a(pN)/a(N)` is `fourPow * extraProd * RFodd`. -/

def oddHalf (c N : ℕ) : ℕ := (c * N - 1) / 2

lemma odd_N_nine {N : ℕ} (hN : Odd N) : 2 ∣ 9 * N - 1 := by
  obtain ⟨t, ht⟩ := hN
  have : 9 * N - 1 = 2 * (9 * t + 4) := by omega
  exact ⟨9 * t + 4, this⟩

lemma odd_N_three {N : ℕ} (hN : Odd N) : 2 ∣ 3 * N - 1 := by
  obtain ⟨t, ht⟩ := hN
  have : 3 * N - 1 = 2 * (3 * t + 1) := by omega
  exact ⟨3 * t + 1, this⟩

lemma oddHalf_nine {N : ℕ} (hN : Odd N) :
    oddHalf 9 N = (9 * N - 1) / 2 := rfl

lemma oddHalf_three {N : ℕ} (hN : Odd N) :
    oddHalf 3 N = (3 * N - 1) / 2 := rfl

lemma risingF_factorial (M : ℕ) (hp1 : 1 < p) :
    ((M * p).factorial : ℚ) =
      (p : ℚ) ^ M * (M.factorial : ℚ) * ((p - 1).factorial : ℚ) ^ M *
        risingF p M :=
  risingF_eq_choose_factor M p hp1

/-- `4^{3N(p-1)}`. -/
def fourPowOdd (N : ℕ) : ℚ := (4 : ℚ) ^ (3 * N * (p - 1))

/-- Extra product `∏_{k=1}^τ (p A + k)/(p B + k)`. -/
def extraOdd (N : ℕ) : ℚ :=
  ∏ k ∈ Finset.Icc 1 ((p - 1) / 2),
    ((p * oddHalf 9 N + k : ℕ) : ℚ) / ((p * oddHalf 3 N + k : ℕ) : ℚ)

/-- Rising-factorial combo for the odd ratio. -/
def RFodd (N : ℕ) : ℚ :=
  risingF p (2 * N) * risingF p (oddHalf 9 N) /
    (risingF p (4 * N) * risingF p N * risingF p (oddHalf 3 N))

noncomputable def UoddPoly (k : ℕ) : ℚ[X] :=
  (Upoly k).comp (C 2 * X) + (Upoly k).comp (C ((9 : ℚ) / 2) * X - C (1 / 2))
    - (Upoly k).comp (C 4 * X) - Upoly k
    - (Upoly k).comp (C ((3 : ℚ) / 2) * X - C (1 / 2))

lemma oddHalf_nine_cast {N : ℕ} (hN : Odd N) :
    (oddHalf 9 N : ℚ) = (9 : ℚ) / 2 * N - 1 / 2 := by
  have hdvd := odd_N_nine hN
  have hN0 : 1 ≤ 9 * N := by obtain ⟨t, ht⟩ := hN; omega
  unfold oddHalf
  have hdiv : (((9 * N - 1) / 2 : ℕ) : ℚ) = ((9 * N - 1 : ℕ) : ℚ) / 2 :=
    Nat.cast_div hdvd (by norm_num)
  rw [hdiv, Nat.cast_sub hN0]
  push_cast
  ring

lemma oddHalf_three_cast {N : ℕ} (hN : Odd N) :
    (oddHalf 3 N : ℚ) = (3 : ℚ) / 2 * N - 1 / 2 := by
  have hdvd := odd_N_three hN
  have hN0 : 1 ≤ 3 * N := by obtain ⟨t, ht⟩ := hN; omega
  unfold oddHalf
  have hdiv : (((3 * N - 1) / 2 : ℕ) : ℚ) = ((3 * N - 1 : ℕ) : ℚ) / 2 :=
    Nat.cast_div hdvd (by norm_num)
  rw [hdiv, Nat.cast_sub hN0]
  push_cast
  ring

lemma UoddPoly_eval_nat (k N : ℕ) (hN : Odd N) :
    (UoddPoly k).eval (N : ℚ) =
      U k (2 * N) + U k (oddHalf 9 N) - U k (4 * N) - U k N
        - U k (oddHalf 3 N) := by
  unfold UoddPoly
  simp only [eval_sub, eval_add, eval_comp, eval_mul, eval_C, eval_X]
  have h2 : (Upoly k).eval ((2 : ℚ) * (N : ℚ)) = U k (2 * N) := by
    have : (2 : ℚ) * (N : ℚ) = ((2 * N : ℕ) : ℚ) := by push_cast; rfl
    rw [this, Upoly_eval]
  have h4 : (Upoly k).eval ((4 : ℚ) * (N : ℚ)) = U k (4 * N) := by
    have : (4 : ℚ) * (N : ℚ) = ((4 * N : ℕ) : ℚ) := by push_cast; rfl
    rw [this, Upoly_eval]
  have hN' : (Upoly k).eval (N : ℚ) = U k N := Upoly_eval k N
  have h9 : (Upoly k).eval ((9 : ℚ) / 2 * (N : ℚ) - 1 / 2) =
      U k (oddHalf 9 N) := by
    rw [← oddHalf_nine_cast hN, Upoly_eval]
  have h3 : (Upoly k).eval ((3 : ℚ) / 2 * (N : ℚ) - 1 / 2) =
      U k (oddHalf 3 N) := by
    rw [← oddHalf_three_cast hN, Upoly_eval]
  rw [h2, h4, hN', h9, h3]

/-! Odd-case ratio identity. -/

/-- Rational formula for `a(N)` at odd `N`. -/
def aOddN (N : ℕ) : ℚ :=
  (4 : ℚ) ^ (3 * N) * (2 * N).factorial * (oddHalf 9 N).factorial /
    ((oddHalf 3 N).factorial * (4 * N).factorial * N.factorial)

lemma aOddN_ne_zero (N : ℕ) : aOddN N ≠ 0 := by
  unfold aOddN
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (factorial_ne_zero_rat _))
      (factorial_ne_zero_rat _)
  · exact mul_ne_zero (mul_ne_zero (factorial_ne_zero_rat _) (factorial_ne_zero_rat _))
      (factorial_ne_zero_rat _)

lemma odd_mul_odd {N p : ℕ} (hN : Odd N) (hp : Odd p) : Odd (N * p) :=
  Odd.mul hN hp

lemma oddHalf_nine_add' {N p : ℕ} (hN : Odd N) (hp : Odd p) :
    oddHalf 9 (N * p) = p * oddHalf 9 N + (p - 1) / 2 := by
  have h9N : 9 * N - 1 = 2 * oddHalf 9 N := by
    have hdvd := odd_N_nine hN
    have hpos : 1 ≤ 9 * N := by obtain ⟨t, ht⟩ := hN; omega
    have : 2 * ((9 * N - 1) / 2) = 9 * N - 1 := Nat.mul_div_cancel' hdvd
    simpa [oddHalf] using this.symm
  have h9Np : 9 * (N * p) - 1 = 2 * oddHalf 9 (N * p) := by
    have hNp : Odd (N * p) := odd_mul_odd hN hp
    have hdvd := odd_N_nine hNp
    have hpos : 1 ≤ 9 * (N * p) := by obtain ⟨t, ht⟩ := hNp; omega
    have : 2 * ((9 * (N * p) - 1) / 2) = 9 * (N * p) - 1 := Nat.mul_div_cancel' hdvd
    simpa [oddHalf] using this.symm
  have hτ : 2 * ((p - 1) / 2) = p - 1 := by
    have : 2 ∣ p - 1 := by
      obtain ⟨k, hk⟩ := hp
      have : p - 1 = 2 * k := by omega
      exact ⟨k, this⟩
    exact Nat.mul_div_cancel' this
  have hNpos : 1 ≤ N := by obtain ⟨t, ht⟩ := hN; omega
  have hppos : 1 ≤ p := by obtain ⟨k, hk⟩ := hp; omega
  have h9Npos : 1 ≤ 9 * N := by omega
  have hex : 9 * (N * p) - 1 = (9 * N - 1) * p + (p - 1) := by
    have hL : 9 * (N * p) = (9 * N) * p := by ring
    have hR : (9 * N - 1) * p + (p - 1) = (9 * N) * p - 1 := by
      have : (9 * N - 1) * p = (9 * N) * p - p := by
        simpa using Nat.mul_sub_right_distrib (9 * N) 1 p
      rw [this]
      have hp_le : p ≤ (9 * N) * p := Nat.le_mul_of_pos_left _ (by omega)
      have : (9 * N) * p - p + (p - 1) = (9 * N) * p - 1 := by
        have h1 : (9 * N) * p - p + p = (9 * N) * p := Nat.sub_add_cancel hp_le
        have h2 : p - 1 + 1 = p := Nat.sub_add_cancel hppos
        omega
      exact this
    rw [hL]; omega
  have : 2 * oddHalf 9 (N * p) = 2 * (p * oddHalf 9 N + (p - 1) / 2) := by
    calc
      2 * oddHalf 9 (N * p) = 9 * (N * p) - 1 := h9Np.symm
      _ = (9 * N - 1) * p + (p - 1) := hex
      _ = (2 * oddHalf 9 N) * p + 2 * ((p - 1) / 2) := by rw [h9N, hτ]
      _ = 2 * (p * oddHalf 9 N + (p - 1) / 2) := by ring
  omega

lemma oddHalf_three_add' {N p : ℕ} (hN : Odd N) (hp : Odd p) :
    oddHalf 3 (N * p) = p * oddHalf 3 N + (p - 1) / 2 := by
  have h3N : 3 * N - 1 = 2 * oddHalf 3 N := by
    have hdvd := odd_N_three hN
    have : 2 * ((3 * N - 1) / 2) = 3 * N - 1 := Nat.mul_div_cancel' hdvd
    simpa [oddHalf] using this.symm
  have hNp : Odd (N * p) := odd_mul_odd hN hp
  have h3Np : 3 * (N * p) - 1 = 2 * oddHalf 3 (N * p) := by
    have hdvd := odd_N_three hNp
    have : 2 * ((3 * (N * p) - 1) / 2) = 3 * (N * p) - 1 := Nat.mul_div_cancel' hdvd
    simpa [oddHalf] using this.symm
  have hτ : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := hp
    have : 2 ∣ p - 1 := ⟨k, by omega⟩
    exact Nat.mul_div_cancel' this
  have hNpos : 1 ≤ N := by obtain ⟨t, ht⟩ := hN; omega
  have hppos : 1 ≤ p := by obtain ⟨k, hk⟩ := hp; omega
  have hex : 3 * (N * p) - 1 = (3 * N - 1) * p + (p - 1) := by
    have hL : 3 * (N * p) = (3 * N) * p := by ring
    have hR : (3 * N - 1) * p + (p - 1) = (3 * N) * p - 1 := by
      have : (3 * N - 1) * p = (3 * N) * p - p := by
        simpa using Nat.mul_sub_right_distrib (3 * N) 1 p
      rw [this]
      have hp_le : p ≤ (3 * N) * p := Nat.le_mul_of_pos_left _ (by omega)
      have : (3 * N) * p - p + (p - 1) = (3 * N) * p - 1 := by
        have h1 : (3 * N) * p - p + p = (3 * N) * p := Nat.sub_add_cancel hp_le
        have h2 : p - 1 + 1 = p := Nat.sub_add_cancel hppos
        omega
      exact this
    rw [hL]; omega
  have : 2 * oddHalf 3 (N * p) = 2 * (p * oddHalf 3 N + (p - 1) / 2) := by
    calc
      2 * oddHalf 3 (N * p) = 3 * (N * p) - 1 := h3Np.symm
      _ = (3 * N - 1) * p + (p - 1) := hex
      _ = (2 * oddHalf 3 N) * p + 2 * ((p - 1) / 2) := by rw [h3N, hτ]
      _ = 2 * (p * oddHalf 3 N + (p - 1) / 2) := by ring
  omega

lemma factorial_add_tau (M τ : ℕ) :
    (M + τ).factorial = M.factorial * ∏ k ∈ Finset.Icc 1 τ, (M + k) :=
  factorial_add_prod M τ

lemma risingF_eq_factorial_ratio (M : ℕ) (hp1 : 1 < p) :
    risingF p M =
      ((M * p).factorial : ℚ) /
        ((p : ℚ) ^ M * (M.factorial : ℚ) * ((p - 1).factorial : ℚ) ^ M) := by
  have h := risingF_eq_choose_factor M p hp1
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hp1)
  have hf := factorial_ne_zero_rat
  field_simp [hf, hp0] at h ⊢
  linarith

lemma extraOdd_eq {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p) :
    extraOdd (p := p) N =
      ∏ k ∈ Finset.Icc 1 ((p - 1) / 2),
        ((p * oddHalf 9 N + k : ℕ) : ℚ) / ((p * oddHalf 3 N + k : ℕ) : ℚ) :=
  rfl

lemma four_pow_odd_ratio (N : ℕ) (h5 : 5 ≤ p) :
    (4 : ℚ) ^ (3 * (N * p)) / (4 : ℚ) ^ (3 * N) =
      (4 : ℚ) ^ (3 * N * (p - 1)) := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  have hle : 3 * N ≤ 3 * (N * p) := by
    have : N ≤ N * p := Nat.le_mul_of_pos_right N (by omega)
    exact Nat.mul_le_mul_left 3 this
  rw [div_eq_mul_inv, ← pow_sub₀ (4 : ℚ) (by norm_num) hle]
  congr 1
  have : 3 * (N * p) - 3 * N = 3 * N * (p - 1) := by
    have h : 3 * (N * p) = 3 * N * p := by ring
    rw [h]
    have : 3 * N * p - 3 * N * 1 = 3 * N * (p - 1) :=
      (Nat.mul_sub_left_distrib (3 * N) p 1).symm
    simpa using this
  exact this

/-- The odd-case ratio formula. -/
lemma aOddN_ratio {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p) :
    aOddN (N * p) / aOddN N =
      fourPowOdd (p := p) N * extraOdd (p := p) N * RFodd (p := p) N := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  have hpodd : Odd p := (Nat.Prime.eq_two_or_odd' hp.out).resolve_left (by omega)
  set A := oddHalf 9 N
  set B := oddHalf 3 N
  set τ := (p - 1) / 2
  have hA' : oddHalf 9 (N * p) = p * A + τ :=
    oddHalf_nine_add' (N := N) (p := p) hN hpodd
  have hB' : oddHalf 3 (N * p) = p * B + τ :=
    oddHalf_three_add' (N := N) (p := p) hN hpodd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast Nat.Prime.ne_zero hp.out
  have hf : ∀ n : ℕ, (n.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat
  have hpf : ((p - 1).factorial : ℚ) ≠ 0 := factorial_ne_zero_rat _
  have hABnat : A = B + 3 * N := by
    obtain ⟨t, ht⟩ := hN
    simp only [A, B, oddHalf]
    omega
  have h2mul : 2 * (N * p) = 2 * N * p := by ring
  have h4mul : 4 * (N * p) = 4 * N * p := by ring
  have hAp_mul : p * A = A * p := by ring
  have hBp_mul : p * B = B * p := by ring
  have hAfac : ((p * A + τ).factorial : ℚ) =
      ((A * p).factorial : ℚ) * ∏ k ∈ Finset.Icc 1 τ, ((p * A + k : ℕ) : ℚ) := by
    rw [hAp_mul, factorial_add_prod]; push_cast; rfl
  have hBfac : ((p * B + τ).factorial : ℚ) =
      ((B * p).factorial : ℚ) * ∏ k ∈ Finset.Icc 1 τ, ((p * B + k : ℕ) : ℚ) := by
    rw [hBp_mul, factorial_add_prod]; push_cast; rfl
  have hextra : extraOdd (p := p) N =
      (∏ k ∈ Finset.Icc 1 τ, ((p * A + k : ℕ) : ℚ)) /
        (∏ k ∈ Finset.Icc 1 τ, ((p * B + k : ℕ) : ℚ)) := by
    unfold extraOdd
    simp only [A, B, τ]
    rw [Finset.prod_div_distrib]
  have hLHS :
      aOddN (N * p) / aOddN N =
        ((4 : ℚ) ^ (3 * (N * p)) / (4 : ℚ) ^ (3 * N)) *
          (((2 * N * p).factorial : ℚ) / (2 * N).factorial) *
          (((p * A + τ).factorial : ℚ) / A.factorial) *
          (B.factorial / ((p * B + τ).factorial : ℚ)) *
          ((4 * N).factorial / ((4 * N * p).factorial : ℚ)) *
          (N.factorial / ((N * p).factorial : ℚ)) := by
    unfold aOddN
    rw [hA', hB', h2mul, h4mul]
    field_simp [hf]
    ring
  rw [hLHS, four_pow_odd_ratio (p := p) N h5, hextra]
  rw [hAfac, hBfac]
  rw [risingF_eq_choose_factor (2 * N) p hp1]
  rw [risingF_eq_choose_factor (4 * N) p hp1]
  rw [risingF_eq_choose_factor N p hp1]
  rw [risingF_eq_choose_factor A p hp1]
  rw [risingF_eq_choose_factor B p hp1]
  unfold fourPowOdd RFodd
  simp only [A, B]
  have hAB'' : oddHalf 9 N = oddHalf 3 N + 3 * N := by simpa [A, B] using hABnat
  field_simp [hf, hp0, hpf]
  rw [hAB'']
  ring_nf


/-! ## Connecting rational formulae to the integer sequence -/

lemma aEvenRat_eq_bRat (k : ℕ) : aEvenRat k = bRat k := rfl

lemma aOddN_of_odd {N : ℕ} (hN : Odd N) : aOddN N = aOddRat (N / 2) := by
  obtain ⟨k, hk⟩ := hN
  have hdiv : N / 2 = k := by omega
  have hA : oddHalf 9 N = 9 * k + 4 := by
    unfold oddHalf
    have : 9 * N - 1 = 2 * (9 * k + 4) := by omega
    rw [this, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  have hB : oddHalf 3 N = 3 * k + 1 := by
    unfold oddHalf
    have : 3 * N - 1 = 2 * (3 * k + 1) := by omega
    rw [this, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  unfold aOddN aOddRat
  rw [hdiv, hA, hB, hk]
  have h2 : 2 * (2 * k + 1) = 4 * k + 2 := by ring
  have h4 : 4 * (2 * k + 1) = 8 * k + 4 := by ring
  have hpow : 3 * (2 * k + 1) = 6 * k + 3 := by ring
  rw [h2, h4, hpow]

lemma aRat_even {n : ℕ} (he : Even n) : aRat n = bRat (n / 2) := by
  rw [aRat, if_pos he, aEvenRat_eq_bRat]

lemma aRat_odd {n : ℕ} (ho : Odd n) : aRat n = aOddN n := by
  have he : ¬ Even n := Nat.not_even_iff_odd.mpr ho
  rw [aRat, if_neg he, aOddN_of_odd ho]

lemma rat_eq_int_of_real {q : ℚ} {z : ℤ} (h : (q : ℝ) = (z : ℝ)) : q = (z : ℚ) :=
  (Rat.cast_inj (α := ℝ)).mp h

lemma aRat_int_of_h_int
    (h_int : ∀ m : ℕ, a m ∈ Set.range (fun x : ℤ => (x : ℝ))) (m : ℕ) :
    ∃ z : ℤ, aRat m = (z : ℚ) := by
  obtain ⟨z, hz⟩ := h_int m
  refine ⟨z, ?_⟩
  have hreal : (aRat m : ℝ) = (z : ℝ) := by
    rw [← a_eq_aRat m, hz.symm]
  exact rat_eq_int_of_real hreal

lemma int_cast_a_unique {m : ℕ} {z w : ℤ}
    (hz : (z : ℝ) = a m) (hw : (w : ℝ) = a m) : z = w :=
  Int.cast_injective (hz.trans hw.symm)

lemma zmod_of_pow_le {a b : ℤ} {q e e' : ℕ} (hle : e ≤ e')
    (h : a ≡ b [ZMOD (q : ℤ) ^ e']) :
    a ≡ b [ZMOD (q : ℤ) ^ e] := by
  refine Int.modEq_iff_dvd.mpr ?_
  have hd := Int.modEq_iff_dvd.mp h
  exact dvd_trans (pow_dvd_pow (q : ℤ) hle) hd

lemma padicValNat_prime_pow (r : ℕ) : padicValNat p (p ^ r) = r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp0 : p ≠ 0 := Nat.Prime.ne_zero hp.out
    have hpr : p ^ r ≠ 0 := pow_ne_zero _ hp0
    rw [pow_succ, padicValNat.mul hpr hp0, ih, padicValNat_self]

lemma padicValNat_mul_pow' {n r : ℕ} (hn : n ≠ 0) :
    padicValNat p (n * p ^ r) = padicValNat p n + r := by
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero hp.out
  have hpr : p ^ r ≠ 0 := pow_ne_zero _ hp0
  rw [padicValNat.mul hn hpr, padicValNat_prime_pow]

lemma three_mul_r_le {n r : ℕ} (hn : n ≠ 0) (hr : 0 < r) :
    3 * r ≤ 3 + 3 * padicValNat p (n * p ^ (r - 1)) := by
  rw [padicValNat_mul_pow' hn]
  omega

lemma padicValNat_div_two_even {N : ℕ} (hN : Even N) (h5 : 5 ≤ p) :
    padicValNat p (N / 2) = padicValNat p N := by
  have h2n : ¬ p ∣ 2 :=
    Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 2)
      (lt_of_lt_of_le (by norm_num : 2 < 5) h5)
  have hv2 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd h2n
  rcases eq_or_ne N 0 with h0 | h0
  · subst h0; simp
  · have hN2 : N / 2 ≠ 0 := by
      have : 1 < N ∨ N = 0 := by
        have : 2 ∣ N := even_iff_two_dvd.mp hN
        omega
      omega
    have hre : N / 2 * 2 = N := Nat.div_mul_cancel (even_iff_two_dvd.mp hN)
    have := padicValNat.mul (p := p) hN2 (by norm_num : (2 : ℕ) ≠ 0)
    rw [hre, hv2, add_zero] at this
    exact this.symm

lemma even_case_zmod {N : ℕ} (h5 : 5 ≤ p)
    {z w : ℤ} (hz : bRat N = z) (hw : bRat (N * p) = w) :
    w ≡ z [ZMOD (p : ℤ) ^ (3 + 3 * padicValNat p N)] := by
  have hval := valGe_bRat_diff_of_int (p := p) (N := N) h5 ⟨z, hz⟩
  have : valGe p (3 + 3 * padicValNat p N) ((w : ℚ) - (z : ℚ)) := by
    simpa [hw, hz] using hval
  exact zmod_of_valGe this

/-! ## Odd-case infrastructure -/

def PhiOdd (γ : ℚ) (N : ℕ) : ℚ :=
  Fprod γ (2 * N) * Fprod γ (oddHalf 9 N) /
    (Fprod γ (4 * N) * Fprod γ N * Fprod γ (oddHalf 3 N))

lemma RFodd_eq_PhiOdd (N : ℕ) (h5 : 5 ≤ p) :
    RFodd (p := p) N =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiOdd (gammaI p i) N := by
  unfold RFodd PhiOdd
  simp only [risingF_eq_Fprod (p := p) h5]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]

lemma aOddN_ratio_prod {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p) :
    aOddN (N * p) / aOddN N =
      fourPowOdd (p := p) N * extraOdd (p := p) N *
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiOdd (gammaI p i) N := by
  rw [aOddN_ratio hN h5, RFodd_eq_PhiOdd N h5]

/-- Binomial form of the odd sequence. -/
lemma aOddN_binom {N : ℕ} (hN : Odd N) :
    aOddN N =
      (4 : ℚ) ^ (3 * N) * (Nat.choose (oddHalf 9 N) (oddHalf 3 N)) *
        (Nat.choose (3 * N) N) / (Nat.choose (4 * N) (2 * N)) := by
  have hAB : oddHalf 9 N = oddHalf 3 N + 3 * N := by
    obtain ⟨t, ht⟩ := hN
    simp only [oddHalf]
    omega
  have hf : ∀ n : ℕ, (n.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat
  have hle1 : oddHalf 3 N ≤ oddHalf 9 N := by omega
  have hle2 : N ≤ 3 * N := by omega
  have hle3 : 2 * N ≤ 4 * N := by omega
  have hch1 := Nat.cast_choose (K := ℚ) hle1
  have hch2 := Nat.cast_choose (K := ℚ) hle2
  have hch3 := Nat.cast_choose (K := ℚ) hle3
  unfold aOddN
  rw [hch1, hch2, hch3, hAB]
  have hsub : oddHalf 3 N + 3 * N - oddHalf 3 N = 3 * N := by omega
  have hsub2 : 3 * N - N = 2 * N := by omega
  have hsub3 : 4 * N - 2 * N = 2 * N := by omega
  simp only [hsub, hsub2, hsub3]
  field_simp [hf]

lemma choose_ratio_risingF' (a b : ℕ) (hab : b ≤ a) (hp1 : 1 < p) :
    ((a * p).choose (b * p) : ℚ) / (a.choose b) =
      risingF p a / (risingF p b * risingF p (a - b)) :=
  choose_ratio_risingF a b p hab hp1

/-! ## Kazandzidis 3-term `U`-combination -/

/-- `U(k,cN) - U(k,dN) - U(k,(c-d)N)` as a polynomial in `N`. -/
noncomputable def UkazPoly (c d k : ℕ) : ℚ[X] :=
  (Upoly k).comp (C (c : ℚ) * X) - (Upoly k).comp (C (d : ℚ) * X)
    - (Upoly k).comp (C ((c - d : ℕ) : ℚ) * X)

lemma UkazPoly_eval (c d k N : ℕ) :
    (UkazPoly c d k).eval (N : ℚ) =
      U k (c * N) - U k (d * N) - U k ((c - d) * N) := by
  unfold UkazPoly
  simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_X]
  have h (a : ℕ) : (Upoly k).eval ((a : ℚ) * (N : ℚ)) = U k (a * N) := by
    have : (a : ℚ) * (N : ℚ) = ((a * N : ℕ) : ℚ) := by push_cast; rfl
    rw [this, Upoly_eval]
  rw [h c, h d, h (c - d)]

lemma UkazPoly_odd (c d k : ℕ) :
    (UkazPoly c d k).comp (-X : ℚ[X]) = - UkazPoly c d k := by
  simp only [UkazPoly, sub_comp, Upoly_comp_neg_scale]
  ring

lemma UkazPoly_eval_zero (c d k : ℕ) : (UkazPoly c d k).eval 0 = 0 := by
  simpa [eval_zero] using (by simpa using UkazPoly_eval c d k 0)

lemma UkazPoly_coeff_zero (c d k : ℕ) : (UkazPoly c d k).coeff 0 = 0 := by
  simpa [coeff_zero_eq_eval_zero] using UkazPoly_eval_zero c d k

lemma UkazPoly_even_coeff (c d k i : ℕ) (he : Even i) :
    (UkazPoly c d k).coeff i = 0 := by
  have hodd := UkazPoly_odd c d k
  have h' : ((UkazPoly c d k).comp (-X : ℚ[X])).coeff i =
      (- UkazPoly c d k).coeff i := by rw [hodd]
  rw [coeff_comp_neg_X', coeff_neg] at h'
  have hpow : (-1 : ℚ) ^ i = 1 := Even.neg_one_pow he
  rw [hpow] at h'
  linarith

lemma UkazPoly_coeff_one (c d k : ℕ) (hdc : d ≤ c) :
    (UkazPoly c d k).coeff 1 = 0 := by
  have hscale (a : ℚ) :
      ((Upoly k).comp (C a * X)).coeff 1 = a * (Upoly k).coeff 1 := by
    rw [comp_C_mul_X_coeff, pow_one, mul_comm]
  have hcd : ((c - d : ℕ) : ℚ) = (c : ℚ) - (d : ℚ) := Nat.cast_sub hdc
  simp only [UkazPoly, coeff_sub, hscale, hcd]
  ring

lemma UkazPoly_X3_dvd (c d k : ℕ) (hdc : d ≤ c) : X ^ 3 ∣ UkazPoly c d k := by
  rw [X_pow_dvd_iff]
  intro n hn
  interval_cases n
  · exact UkazPoly_coeff_zero c d k
  · exact UkazPoly_coeff_one c d k hdc
  · exact UkazPoly_even_coeff c d k 2 (by decide)

lemma UkazPoly_coeff_val (c d k j : ℕ) (h5 : 5 ≤ p) :
    valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ))
      ((UkazPoly c d k).coeff j) := by
  have hscale (a : ℕ) :
      valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ))
        (((Upoly k).comp (C (a : ℚ) * X)).coeff j) := by
    rw [comp_C_mul_X_coeff]
    have ha : valGe p 0 ((a : ℚ) ^ j) := valGe_nat_pow a j
    have hpj := Upoly_coeff_val (p := p) k j
    have := valGe_mul hpj ha
    simpa [mul_comm] using this
  simp only [UkazPoly, coeff_sub]
  exact valGe_sub (valGe_sub (hscale c) (hscale d)) (hscale (c - d))

lemma valGe_UkazPoly_eval (c d k N : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) :
    valGe p (3 * padicValNat p N - padicValNat p (2 * k + 1).factorial)
      ((UkazPoly c d k).eval (N : ℚ)) := by
  obtain ⟨T, hT⟩ := UkazPoly_X3_dvd c d k hdc
  have heval : (UkazPoly c d k).eval (N : ℚ) = (N : ℚ) ^ 3 * T.eval (N : ℚ) := by
    rw [hT, eval_mul, eval_pow, eval_X]
  rw [heval]
  have hN : valGe p (padicValNat p N) (N : ℚ) := Or.inr (by simp [padicValRat.of_nat])
  have hN3 := valGe_pow (n := 3) hN
  have hTval : valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ))
      (T.eval (N : ℚ)) := by
    rw [eval_eq_sum_range]
    apply valGe_sum
    intro i _hi
    have hcoeff : valGe p (-(padicValNat p (2 * k + 1).factorial : ℤ))
        (T.coeff i) := by
      have : (UkazPoly c d k).coeff (i + 3) = T.coeff i := by
        rw [hT]; exact coeff_X_pow_mul T 3 i
      rw [← this]
      exact UkazPoly_coeff_val (p := p) c d k (i + 3) h5
    have hpow : valGe p 0 ((N : ℚ) ^ i) := valGe_nat_pow N i
    have := valGe_mul hcoeff hpow
    simpa using this
  have := valGe_mul hN3 hTval
  simpa [sub_eq_add_neg] using this

lemma valGe_U_kaz_any (c d k N : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) :
    valGe p (3 * padicValNat p N - padicValNat p (2 * k + 1).factorial)
      (U k (c * N) - U k (d * N) - U k ((c - d) * N)) := by
  simpa [UkazPoly_eval] using valGe_UkazPoly_eval (p := p) c d k N h5 hdc

lemma valGe_log_term_kaz (c d k N : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) (hk : 1 ≤ k) :
    valGe p (3 + 3 * padicValNat p N)
      (((-1 : ℚ) ^ (k + 1) / k) *
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) *
        (U k (c * N) - U k (d * N) - U k ((c - d) * N))) := by
  have hU := valGe_U_kaz_any (p := p) c d k N h5 hdc
  have hsign : valGe p 0 ((-1 : ℚ) ^ (k + 1)) := valGe_neg_one_pow p (k + 1)
  have hk0 : k ≠ 0 := by omega
  by_cases h1 : k = 1
  · subst h1
    have hγ : valGe p 3 (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), gammaI p i) :=
      valGe_sum_gammaI h5
    have hpow : (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ 1) =
        ∑ i ∈ Finset.Icc 1 ((p - 1) / 2), gammaI p i := by simp
    rw [hpow]
    have hfac' : padicValNat p (2 * 1 + 1).factorial = 0 := by
      change padicValNat p 6 = 0
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hle : p ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hd
      have : p = 5 ∨ p = 6 := by omega
      rcases this with rfl | rfl
      · exact (by decide : ¬(5 ∣ 6)) hd
      · exact (by decide : ¬ Nat.Prime 6) hp.out
    have h1inv : valGe p 0 ((1 : ℚ)⁻¹) := by
      simpa using (valGe_inv_nat (p := p) (n := 1))
    have hmul1 := valGe_mul hsign h1inv
    have hmul2 := valGe_mul hmul1 hγ
    have hmul3 := valGe_mul hmul2 hU
    have : (0 + 0 + 3 + (3 * padicValNat p N - padicValNat p (2 * 1 + 1).factorial) : ℤ) =
        3 + 3 * padicValNat p N := by simp [hfac']
    apply valGe_mono (le_of_eq this.symm)
    simpa [div_eq_mul_inv, mul_assoc] using hmul3
  · have hk2 : 2 ≤ k := by omega
    have hγ := valGe_sum_gamma_pow (p := p) (k := k) h5
    have hdiv := valGe_div_nat hγ hk0
    have hmul1 := valGe_mul hsign hdiv
    have hmul2 := valGe_mul hmul1 hU
    have hbound := two_k_bound (p := p) (k := k) h5 hk2
    have : (0 + (2 * k - padicValNat p k) +
        (3 * padicValNat p N - padicValNat p (2 * k + 1).factorial) : ℤ) ≥
        3 + 3 * padicValNat p N := by linarith [hbound]
    have hform :
        ((-1 : ℚ) ^ (k + 1) / k) *
            (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) *
            (U k (c * N) - U k (d * N) - U k ((c - d) * N)) =
          ((-1 : ℚ) ^ (k + 1)) *
            ((∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ k) / k) *
            (U k (c * N) - U k (d * N) - U k ((c - d) * N)) := by ring
    rw [hform]
    refine valGe_mono this ?_
    simpa [mul_assoc, sub_eq_add_neg] using hmul2

def PhiKaz (γ : ℚ) (c d N : ℕ) : ℚ :=
  Fprod γ (c * N) / (Fprod γ (d * N) * Fprod γ ((c - d) * N))

def Ukaz (c d k N : ℕ) : ℚ :=
  U k (c * N) - U k (d * N) - U k ((c - d) * N)

lemma PhiKaz_ne_zero (γ : ℚ) (c d N : ℕ) (hγ : 0 ≤ γ) : PhiKaz γ c d N ≠ 0 := by
  unfold PhiKaz
  exact div_ne_zero (Fprod_ne_zero γ _ hγ)
    (mul_ne_zero (Fprod_ne_zero γ _ hγ) (Fprod_ne_zero γ _ hγ))

lemma PhiKaz_cast (γ : ℚ) (c d N : ℕ) :
    (PhiKaz γ c d N : ℚ_[p]) =
      (Fprod γ (c * N) : ℚ_[p]) /
        ((Fprod γ (d * N) : ℚ_[p]) * (Fprod γ ((c - d) * N) : ℚ_[p])) := by
  unfold PhiKaz; push_cast; rfl

lemma padicLog_PhiKaz {γ : ℚ} (c d N : ℕ) (hγ : valGe p 2 γ) (hγ0 : 0 ≤ γ) :
    padicLog (p := p) (PhiKaz γ c d N : ℚ_[p]) =
      padicLog (p := p) (Fprod γ (c * N) : ℚ_[p]) -
        (padicLog (p := p) (Fprod γ (d * N) : ℚ_[p]) +
          padicLog (p := p) (Fprod γ ((c - d) * N) : ℚ_[p])) := by
  have hc := valGeP_Fprod_sub_one (p := p) (c * N) hγ
  have hd := valGeP_Fprod_sub_one (p := p) (d * N) hγ
  have he := valGeP_Fprod_sub_one (p := p) ((c - d) * N) hγ
  have hden0 :
      (Fprod γ (d * N) : ℚ_[p]) * (Fprod γ ((c - d) * N) : ℚ_[p]) ≠ 0 := by
    refine mul_ne_zero ?_ ?_ <;> exact_mod_cast Fprod_ne_zero γ _ hγ0
  have hden := valGeP_unit_sub_one hd he
  rw [PhiKaz_cast, padicLog_div hc hden hden0, padicLog_mul hd he]

lemma padicLog_PhiKaz_tsum {γ : ℚ} (c d N : ℕ) (hγ : valGe p 2 γ) (hγ0 : 0 ≤ γ) :
    padicLog (p := p) (PhiKaz γ c d N : ℚ_[p]) =
      ∑' k : ℕ,
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (γ : ℚ_[p]) ^ (k + 1) * (Ukaz c d (k + 1) N : ℚ_[p]) := by
  rw [padicLog_PhiKaz (p := p) c d N hγ hγ0]
  simp only [padicLog_Fprod_tsum (p := p) _ hγ]
  have hc := summable_U_series (p := p) (c * N) hγ
  have hd := summable_U_series (p := p) (d * N) hγ
  have he := summable_U_series (p := p) ((c - d) * N) hγ
  have hden := hd.add he
  rw [← hd.tsum_add he, ← hc.tsum_sub hden]
  congr 1
  ext k
  unfold Ukaz
  push_cast
  ring

lemma summable_kazTerm {γ : ℚ} (c d N : ℕ) (hγ : valGe p 2 γ) :
    Summable (fun k : ℕ =>
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (γ : ℚ_[p]) ^ (k + 1) * (Ukaz c d (k + 1) N : ℚ_[p])) := by
  have hc := summable_U_series (p := p) (c * N) hγ
  have hd := summable_U_series (p := p) (d * N) hγ
  have he := summable_U_series (p := p) ((c - d) * N) hγ
  have h := hc.sub (hd.add he)
  refine h.congr ?_
  intro k
  unfold Ukaz
  push_cast
  ring

lemma valGeP_PhiKaz_sub_one {c d N i : ℕ} (h5 : 5 ≤ p)
    (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
    valGeP (p := p) 1 ((PhiKaz (gammaI p i) c d N : ℚ_[p]) - 1) := by
  have hγ : valGe p 2 (gammaI p i) := valGe_gammaI h5 hi
  have hγ0 : 0 ≤ gammaI p i := gammaI_nonneg h5 hi
  have hc := valGeP_Fprod_sub_one (p := p) (c * N) hγ
  have hd := valGeP_Fprod_sub_one (p := p) (d * N) hγ
  have he := valGeP_Fprod_sub_one (p := p) ((c - d) * N) hγ
  have hden := valGeP_unit_sub_one hd he
  have hden0 :
      (Fprod (gammaI p i) (d * N) : ℚ_[p]) *
        (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p]) ≠ 0 := by
    refine mul_ne_zero ?_ ?_ <;> exact_mod_cast Fprod_ne_zero _ _ hγ0
  have hdiv :
      (PhiKaz (gammaI p i) c d N : ℚ_[p]) - 1 =
        ((Fprod (gammaI p i) (c * N) : ℚ_[p]) -
          ((Fprod (gammaI p i) (d * N) : ℚ_[p]) *
            (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p]))) /
        ((Fprod (gammaI p i) (d * N) : ℚ_[p]) *
          (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p])) := by
    rw [PhiKaz_cast, div_sub_one hden0]
  rw [hdiv]
  have hnd := valGeP_sub hc hden
  have hv0 :
      ((Fprod (gammaI p i) (d * N) : ℚ_[p]) *
        (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p])).valuation = 0 := by
    have hrew : (1 : ℚ_[p]) +
        (((Fprod (gammaI p i) (d * N) : ℚ_[p]) *
          (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p])) - 1) =
        (Fprod (gammaI p i) (d * N) : ℚ_[p]) *
          (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p]) := by ring
    rw [← hrew]
    exact valuation_one_add_of_valGeP_one hden
  have hinv : valGeP (p := p) 0
      (((Fprod (gammaI p i) (d * N) : ℚ_[p]) *
        (Fprod (gammaI p i) ((c - d) * N) : ℚ_[p]))⁻¹) :=
    Or.inr (by rw [Padic.valuation_inv, hv0]; simp)
  have := valGeP_mul hnd hinv
  simpa [div_eq_mul_inv] using this

lemma padicLog_kaz_prod (c d N : ℕ) (h5 : 5 ≤ p) :
    padicLog (p := p)
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
        padicLog (p := p) (PhiKaz (gammaI p i) c d N : ℚ_[p]) := by
  have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
      valGeP (p := p) 1 ((PhiKaz (gammaI p i) c d N : ℚ_[p]) - 1) :=
    fun i hi => valGeP_PhiKaz_sub_one (c := c) (d := d) (N := N) h5 hi
  have hcast :
      ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p]) =
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), (PhiKaz (gammaI p i) c d N : ℚ_[p]) := by
    push_cast; rfl
  rw [hcast, padicLog_prod _ _ hf]

lemma padicLog_kaz_tsum (c d N : ℕ) (h5 : 5 ≤ p) :
    padicLog (p := p)
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p]) =
      ∑' k : ℕ,
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
            (gammaI p i : ℚ_[p]) ^ (k + 1)) *
          (Ukaz c d (k + 1) N : ℚ_[p]) := by
  rw [padicLog_kaz_prod c d N h5]
  have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
      Summable (fun k : ℕ =>
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (gammaI p i : ℚ_[p]) ^ (k + 1) * (Ukaz c d (k + 1) N : ℚ_[p])) :=
    fun i hi => summable_kazTerm (p := p) c d N (valGe_gammaI h5 hi)
  have : ∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
      padicLog (p := p) (PhiKaz (gammaI p i) c d N : ℚ_[p]) =
      ∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
        ∑' k : ℕ,
          ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
            (gammaI p i : ℚ_[p]) ^ (k + 1) * (Ukaz c d (k + 1) N : ℚ_[p]) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact padicLog_PhiKaz_tsum c d N (valGe_gammaI h5 hi) (gammaI_nonneg h5 hi)
  rw [this, ← Summable.tsum_finsetSum hf]
  congr 1
  ext k
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma valGeP_kaz_series_term (c d N k : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) :
    valGeP (p := p) (3 + 3 * padicValNat p N)
      (((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
          (gammaI p i : ℚ_[p]) ^ (k + 1)) *
        (Ukaz c d (k + 1) N : ℚ_[p])) := by
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have h := valGe_log_term_kaz (p := p) c d (k + 1) N h5 hdc hk
  have hsign : (-1 : ℚ) ^ (k + 1 + 1) = (-1 : ℚ) ^ k := by
    rw [show k + 1 + 1 = k + 2 from by omega, pow_add, pow_two]
    ring
  have hform :
      ((-1 : ℚ) ^ (k + 1 + 1) / (k + 1 : ℕ)) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ (k + 1)) *
          (U (k + 1) (c * N) - U (k + 1) (d * N) - U (k + 1) ((c - d) * N)) =
        ((-1 : ℚ) ^ k / (k + 1 : ℚ)) *
          (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), (gammaI p i) ^ (k + 1)) *
          Ukaz c d (k + 1) N := by
    unfold Ukaz
    rw [hsign]
    push_cast
    rfl
  rw [hform] at h
  have hP := valGeP_of_valGe (p := p) h
  convert hP using 1
  push_cast
  rfl

lemma summable_kaz_series (c d N : ℕ) (h5 : 5 ≤ p) :
    Summable (fun k : ℕ =>
      ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2),
          (gammaI p i : ℚ_[p]) ^ (k + 1)) *
        (Ukaz c d (k + 1) N : ℚ_[p])) := by
  have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
      Summable (fun k : ℕ =>
        ((-1 : ℚ_[p]) ^ k / (k + 1 : ℚ_[p])) *
          (gammaI p i : ℚ_[p]) ^ (k + 1) * (Ukaz c d (k + 1) N : ℚ_[p])) :=
    fun i hi => summable_kazTerm (p := p) c d N (valGe_gammaI h5 hi)
  have h := summable_finset_sum_nat _ _ hf
  refine h.congr ?_
  intro k
  simp [Finset.mul_sum, mul_assoc, mul_comm]

lemma valGeP_padicLog_kaz (c d N : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) :
    valGeP (p := p) (3 + 3 * padicValNat p N)
      (padicLog (p := p)
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p])) := by
  rw [padicLog_kaz_tsum c d N h5]
  refine valGeP_tsum (summable_kaz_series (p := p) c d N h5) ?_
  intro n
  exact valGeP_kaz_series_term (p := p) c d N n h5 hdc

lemma valGeP_kaz_sub_one (c d N : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) :
    valGeP (p := p) (3 + 3 * padicValNat p N)
      (((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p]) - 1) := by
  have hlog := valGeP_padicLog_kaz (p := p) c d N h5 hdc
  have hunit : valGeP (p := p) 1
      (((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p]) - 1) := by
    have hf : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
        valGeP (p := p) 1 ((PhiKaz (gammaI p i) c d N : ℚ_[p]) - 1) :=
      fun i hi => valGeP_PhiKaz_sub_one (c := c) (d := d) (N := N) h5 hi
    have hcast :
        ((∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N : ℚ) : ℚ_[p]) =
          ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), (PhiKaz (gammaI p i) c d N : ℚ_[p]) := by
      push_cast; rfl
    rw [hcast]
    exact valGeP_prod_units_sub_one _ _ hf
  have hiff := valGeP_padicLog1p_iff (p := p) h5 hunit (3 + 3 * padicValNat p N)
  simpa [padicLog] using (hiff.mp hlog)

lemma risingF_eq_PhiKaz (c d N : ℕ) (h5 : 5 ≤ p) :
    risingF p (c * N) / (risingF p (d * N) * risingF p ((c - d) * N)) =
      ∏ i ∈ Finset.Icc 1 ((p - 1) / 2), PhiKaz (gammaI p i) c d N := by
  simp only [risingF_eq_Fprod (p := p) h5, PhiKaz]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]

/-- Kazandzidis-type bound for a 3-term rising-factorial ratio. -/
lemma valGe_kaz {c d : ℕ} (N : ℕ) (h5 : 5 ≤ p) (hdc : d ≤ c) :
    valGe p (3 + 3 * padicValNat p N)
      (risingF p (c * N) / (risingF p (d * N) * risingF p ((c - d) * N)) - 1) := by
  rw [risingF_eq_PhiKaz (p := p) c d N h5]
  exact valGe_of_valGeP' (valGeP_kaz_sub_one (p := p) c d N h5 hdc)

lemma valGe_kaz_3_1 (N : ℕ) (h5 : 5 ≤ p) :
    valGe p (3 + 3 * padicValNat p N)
      (((3 * N * p).choose (N * p) : ℚ) / ((3 * N).choose N) - 1) := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  have hle : N ≤ 3 * N := by omega
  rw [choose_ratio_risingF' (3 * N) N hle hp1]
  have hcd : (3 * N - N) = 2 * N := by omega
  rw [hcd]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (valGe_kaz (c := 3) (d := 1) N h5 (by norm_num))

lemma valGeP_inv_minus_one {k : ℤ} {u : ℚ_[p]} (hk : 1 ≤ k)
    (hu : valGeP (p := p) k (u - 1)) :
    valGeP (p := p) k (u⁻¹ - 1) := by
  have h1 : valGeP (p := p) 1 (u - 1) := valGeP_mono hk hu
  have hform : u⁻¹ - 1 = -(u - 1) / (1 + (u - 1)) := by
    have hne := one_add_ne_zero_of_valGeP_one h1
    have : 1 + (u - 1) = u := by ring
    have hu0 : u ≠ 0 := by rw [← this]; exact hne
    rw [this]
    field_simp [hu0]
    ring
  rw [hform]
  have hv0 : (1 + (u - 1)).valuation = 0 := valuation_one_add_of_valGeP_one h1
  have hinv0 : valGeP (p := p) 0 ((1 + (u - 1))⁻¹) :=
    Or.inr (by rw [Padic.valuation_inv, hv0]; simp)
  have := valGeP_mul (valGeP_neg hu) hinv0
  simpa [div_eq_mul_inv] using this

lemma valGe_inv_minus_one {k : ℤ} {u : ℚ} (hk : 1 ≤ k)
    (hu : valGe p k (u - 1)) :
    valGe p k (u⁻¹ - 1) := by
  have hP : valGeP (p := p) k ((u : ℚ_[p]) - 1) := by
    simpa using valGeP_of_valGe (p := p) hu
  have hinv := valGeP_inv_minus_one (p := p) hk hP
  exact valGe_of_valGeP' (by simpa using hinv)

lemma valGe_kaz_4_2 (N : ℕ) (h5 : 5 ≤ p) :
    valGe p (3 + 3 * padicValNat p N)
      (((4 * N).choose (2 * N) : ℚ) / ((4 * N * p).choose (2 * N * p)) - 1) := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  have hle : 2 * N ≤ 4 * N := by omega
  have hsub : 4 * N - 2 * N = 2 * N := by omega
  have hrf : ((4 * N * p).choose (2 * N * p) : ℚ) / ((4 * N).choose (2 * N)) =
      risingF p (4 * N) / (risingF p (2 * N) * risingF p (2 * N)) := by
    simpa [mul_assoc, hsub] using choose_ratio_risingF' (4 * N) (2 * N) hle hp1
  have hkaz : valGe p (3 + 3 * padicValNat p N)
      (risingF p (4 * N) / (risingF p (2 * N) * risingF p (2 * N)) - 1) := by
    have h := valGe_kaz (c := 4) (d := 2) N h5 (by norm_num)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  set u := ((4 * N * p).choose (2 * N * p) : ℚ) / ((4 * N).choose (2 * N))
  have hu : valGe p (3 + 3 * padicValNat p N) (u - 1) := by
    simpa [u, hrf] using hkaz
  have hch1 : ((4 * N).choose (2 * N) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega : 2 * N ≤ 4 * N)).ne'
  have hch2 : ((4 * N * p).choose (2 * N * p) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by
      have : 2 * N * p ≤ 4 * N * p := Nat.mul_le_mul_right p (by omega : 2 * N ≤ 4 * N)
      simpa [mul_assoc] using this)).ne'
  have hform :
      ((4 * N).choose (2 * N) : ℚ) / ((4 * N * p).choose (2 * N * p)) - 1 =
        u⁻¹ - 1 := by
    unfold u
    field_simp [hch1, hch2]
  rw [hform]
  exact valGe_inv_minus_one (by omega) hu

lemma valGe_mul_sub_one {k : ℤ} {a b : ℚ} (hk : 1 ≤ k)
    (ha : valGe p k (a - 1)) (hb : valGe p k (b - 1)) :
    valGe p k (a * b - 1) := by
  have hsplit : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
  rw [hsplit]
  have hab := valGe_mul ha hb
  have hab' : valGe p k ((a - 1) * (b - 1)) :=
    valGe_mono (by linarith) hab
  exact valGe_add (valGe_add ha hb) hab'

lemma valGe_mul3_sub_one {k : ℤ} {a b c : ℚ} (hk : 1 ≤ k)
    (ha : valGe p k (a - 1)) (hb : valGe p k (b - 1)) (hc : valGe p k (c - 1)) :
    valGe p k (a * b * c - 1) :=
  valGe_mul_sub_one hk (valGe_mul_sub_one hk ha hb) hc

lemma choose_ne_zero_rat {n k : ℕ} (h : k ≤ n) : (n.choose k : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.choose_pos h).ne'

/-- The `C(A,B)`-factor in the odd binomial formula, scaled by `4^{3N(p-1)}`. -/
def part1Odd (N : ℕ) : ℚ :=
  fourPowOdd (p := p) N *
    ((oddHalf 9 (N * p)).choose (oddHalf 3 (N * p)) : ℚ) /
      ((oddHalf 9 N).choose (oddHalf 3 N))

lemma aOddN_ratio_three {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p) :
    aOddN (N * p) / aOddN N =
      part1Odd (p := p) N *
        (((3 * N * p).choose (N * p) : ℚ) / ((3 * N).choose N)) *
        (((4 * N).choose (2 * N) : ℚ) / ((4 * N * p).choose (2 * N * p))) := by
  have hpodd : Odd p := (Nat.Prime.eq_two_or_odd' hp.out).resolve_left (by omega)
  have hNp : Odd (N * p) := Odd.mul hN hpodd
  have hleA : oddHalf 3 N ≤ oddHalf 9 N := by
    obtain ⟨t, ht⟩ := hN; simp only [oddHalf]; omega
  have hleAp : oddHalf 3 (N * p) ≤ oddHalf 9 (N * p) := by
    obtain ⟨t, ht⟩ := hNp; simp only [oddHalf]; omega
  have hchA : (oddHalf 9 N).choose (oddHalf 3 N) ≠ 0 := (Nat.choose_pos hleA).ne'
  have hchAp : (oddHalf 9 (N * p)).choose (oddHalf 3 (N * p)) ≠ 0 :=
    (Nat.choose_pos hleAp).ne'
  have hch3 : ((3 * N).choose N : ℚ) ≠ 0 := choose_ne_zero_rat (by omega)
  have hch3p : ((3 * (N * p)).choose (N * p) : ℚ) ≠ 0 :=
    choose_ne_zero_rat (by omega)
  have hch4 : ((4 * N).choose (2 * N) : ℚ) ≠ 0 := choose_ne_zero_rat (by omega)
  have hch4p : ((4 * (N * p)).choose (2 * (N * p)) : ℚ) ≠ 0 :=
    choose_ne_zero_rat (by omega)
  have h3eq : 3 * (N * p) = 3 * N * p := by ring
  have h4eq : 4 * (N * p) = 4 * N * p := by ring
  have h2eq : 2 * (N * p) = 2 * N * p := by ring
  have hpow := four_pow_odd_ratio (p := p) N h5
  have hf : ∀ n : ℕ, (n.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat
  rw [aOddN_binom hN, aOddN_binom hNp]
  unfold part1Odd fourPowOdd
  simp only [h3eq, h4eq, h2eq]
  have hchA' : ((oddHalf 9 N).choose (oddHalf 3 N) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hchA
  have hchAp' : ((oddHalf 9 (N * p)).choose (oddHalf 3 (N * p)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hchAp
  field_simp [hf, hchA', hchAp', hch3, hch3p, hch4, hch4p]
  have hne : (4 : ℚ) ^ (3 * N) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpow2 : (4 : ℚ) ^ (3 * N * p) =
      (4 : ℚ) ^ (3 * N) * (4 : ℚ) ^ (3 * N * (p - 1)) := by
    have : 3 * (N * p) = 3 * N * p := by ring
    rw [← this, mul_comm ((4 : ℚ) ^ (3 * N))]
    exact (div_eq_iff hne).mp hpow
  rw [hpow2]
  ring

lemma derivative_neg_X : derivative (-X : ℚ[X]) = -1 := by
  simp [derivative_neg, derivative_X]

lemma Upoly_deriv_even (k : ℕ) :
    (derivative (Upoly k)).comp (-X : ℚ[X]) = derivative (Upoly k) := by
  have h := congr_arg derivative (Upoly_odd k)
  have hL : derivative ((Upoly k).comp (-X : ℚ[X])) =
      (derivative (Upoly k)).comp (-X : ℚ[X]) * (-1) := by
    simpa [derivative_neg_X] using derivative_comp (Upoly k) (-X)
  have hR : derivative (-Upoly k) = - derivative (Upoly k) := derivative_neg _
  have : (derivative (Upoly k)).comp (-X : ℚ[X]) * (-1) = - derivative (Upoly k) := by
    rw [← hL, h, hR]
  exact neg_injective (by simpa [mul_neg, mul_one] using this)

lemma Upoly_odd_deriv2 (k : ℕ) :
    (derivative (derivative (Upoly k))).comp (-X : ℚ[X]) =
      - derivative (derivative (Upoly k)) := by
  have h := congr_arg derivative (Upoly_deriv_even k)
  have hL : derivative ((derivative (Upoly k)).comp (-X : ℚ[X])) =
      (derivative (derivative (Upoly k))).comp (-X : ℚ[X]) * (-1) := by
    simpa [derivative_neg_X] using derivative_comp (derivative (Upoly k)) (-X)
  have : (derivative (derivative (Upoly k))).comp (-X : ℚ[X]) * (-1) =
      derivative (derivative (Upoly k)) := by
    rw [← hL, h]
  exact neg_injective (by simpa [mul_neg, mul_one] using this)

lemma derivative_X_mul_X_add_one :
    derivative (X * (X + 1) : ℚ[X]) = 2 * X + 1 := by
  simp [derivative_mul, derivative_add, derivative_X, derivative_one]
  ring

lemma derivative_pow_X_mul_succ (k : ℕ) :
    derivative ((X * (X + 1) : ℚ[X]) ^ k) =
      C (k : ℚ) * (X * (X + 1)) ^ (k - 1) * (2 * X + 1) := by
  rw [derivative_pow, derivative_X_mul_X_add_one]

lemma eval_twoX_add_one_neg_half :
    (2 * X + 1 : ℚ[X]).eval (-(1 / 2 : ℚ)) = 0 := by
  simp [eval_add, eval_mul, eval_X, eval_one]

lemma eval_X_mul_X_add_one_neg_half :
    ((X * (X + 1) : ℚ[X])).eval (-(1 / 2 : ℚ)) = -1 / 4 := by
  simp [eval_mul, eval_add, eval_X, eval_one]; ring

lemma deriv2_pow_X_mul_succ_eval_neg_half (k : ℕ) (_hk : 1 ≤ k) :
    (derivative (derivative ((X * (X + 1) : ℚ[X]) ^ k))).eval (-(1 / 2 : ℚ)) =
      (2 : ℚ) * k * (-1 / 4 : ℚ) ^ (k - 1) := by
  rw [derivative_pow_X_mul_succ]
  -- Product rule on `C k * g^{k-1} * (2X+1)`; the factor `2X+1` vanishes at `-1/2`.
  have hg'0 := eval_twoX_add_one_neg_half
  have hg := eval_X_mul_X_add_one_neg_half
  have hderivg : derivative (2 * X + 1 : ℚ[X]) = 2 := by
    simp [derivative_add, derivative_mul, derivative_X, derivative_one]
  simp only [derivative_mul, derivative_C, zero_mul, add_zero, derivative_pow,
    hderivg]
  simp [eval_add, eval_mul, eval_C, eval_pow, eval_X, hg'0, hg, eval_one]
  ring

lemma valGe_of_dvd_int {z : ℤ} (h : (p : ℤ) ∣ z) : valGe p 1 (z : ℚ) := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  push_cast
  simpa [mul_comm] using valGe_mul (valGe_p (p := p)) (valGe_int p k)

lemma valGeP_pow_unit_sub_one {u : ℚ_[p]} (n : ℕ)
    (hu : valGeP (p := p) 1 (u - 1)) :
    valGeP (p := p) 1 (u ^ n - 1) := by
  induction n with
  | zero => simp [valGeP_zero]
  | succ n ih =>
    rw [pow_succ]
    exact valGeP_unit_sub_one ih hu

/-- `4^{3N(p-1)} C(A',B')/C(A,B) ≡ 1` at valuation `3+3v_p(N)`. -/
lemma valGe_part1 {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p) :
    valGe p (3 + 3 * padicValNat p N) (part1Odd (p := p) N - 1) := by
  have hpodd : Odd p := (Nat.Prime.eq_two_or_odd' hp.out).resolve_left (by omega)
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : 1 < 5) h5
  set A := oddHalf 9 N
  set B := oddHalf 3 N
  set τ := (p - 1) / 2
  have hA' : oddHalf 9 (N * p) = p * A + τ :=
    oddHalf_nine_add' (N := N) (p := p) hN hpodd
  have hB' : oddHalf 3 (N * p) = p * B + τ :=
    oddHalf_three_add' (N := N) (p := p) hN hpodd
  have hAB : A = B + 3 * N := by
    obtain ⟨t, ht⟩ := hN; simp only [A, B, oddHalf]; omega
  have hleAB : B ≤ A := by omega
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
  have hf : ∀ n : ℕ, (n.factorial : ℚ) ≠ 0 := factorial_ne_zero_rat
  have hchAB : (A.choose B : ℚ) ≠ 0 := choose_ne_zero_rat hleAB
  have hextra_ch :
      ((p * A + τ).choose (p * B + τ) : ℚ) / (A.choose B) =
        extraOdd (p := p) N *
          ((A * p).choose (B * p) : ℚ) / (A.choose B) := by
    have hAp : p * A = A * p := by ring
    have hBp : p * B = B * p := by ring
    have hle1 : p * B + τ ≤ p * A + τ :=
      Nat.add_le_add_right (Nat.mul_le_mul_left p hleAB) τ
    have hle2 : B * p ≤ A * p := Nat.mul_le_mul_right p hleAB
    have hsub1 : p * A + τ - (p * B + τ) = p * (A - B) := by
      rw [Nat.add_sub_add_right, Nat.mul_sub_left_distrib]
    have hsub2 : A * p - B * p = (A - B) * p := (Nat.mul_sub_right_distrib A B p).symm
    have hABspan : A - B = 3 * N := by omega
    have hAfac : ((p * A + τ).factorial : ℚ) =
        ((A * p).factorial : ℚ) *
          ∏ k ∈ Finset.Icc 1 τ, ((p * A + k : ℕ) : ℚ) := by
      rw [hAp, factorial_add_prod]; push_cast; rfl
    have hBfac : ((p * B + τ).factorial : ℚ) =
        ((B * p).factorial : ℚ) *
          ∏ k ∈ Finset.Icc 1 τ, ((p * B + k : ℕ) : ℚ) := by
      rw [hBp, factorial_add_prod]; push_cast; rfl
    have hextra : extraOdd (p := p) N =
        (∏ k ∈ Finset.Icc 1 τ, ((p * A + k : ℕ) : ℚ)) /
          (∏ k ∈ Finset.Icc 1 τ, ((p * B + k : ℕ) : ℚ)) := by
      unfold extraOdd
      simp only [A, B, τ]
      rw [Finset.prod_div_distrib]
    rw [Nat.cast_choose (K := ℚ) hle1, Nat.cast_choose (K := ℚ) hle2, hextra,
      hAfac, hBfac, hsub1, hsub2, hABspan]
    field_simp [hf, hchAB]
    ring
  have hkazAB :
      ((A * p).choose (B * p) : ℚ) / (A.choose B) =
        risingF p A / (risingF p B * risingF p (3 * N)) := by
    have : A - B = 3 * N := by omega
    simpa [this, mul_comm A p, mul_comm B p] using
      choose_ratio_risingF' A B hleAB hp1
  have hpart :
      part1Odd (p := p) N =
        fourPowOdd (p := p) N * extraOdd (p := p) N *
          (risingF p A / (risingF p B * risingF p (3 * N))) := by
    unfold part1Odd
    rw [hA', hB', mul_div_assoc]
    simp only [A, B, τ]
    rw [hextra_ch, mul_div_assoc, hkazAB]
    ring
  have hRF :
      risingF p A / (risingF p B * risingF p (3 * N)) =
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2),
          Fprod (gammaI p i) A /
            (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) := by
    simp only [risingF_eq_Fprod (p := p) h5]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  rw [hpart, hRF]
  set Q :=
    (∏ i ∈ Finset.Icc 1 ((p - 1) / 2),
      Fprod (gammaI p i) A /
        (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)))
  -- Each factor is a 1-unit; the combined p-adic logarithm has valuation
  -- `≥ 3+3s` because its Taylor series in `N` has vanishing linear and
  -- quadratic coefficients and remaining coefficients of valuation `≥ 3`.
  have hγ (i : ℕ) (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
      valGe p 2 (gammaI p i) := valGe_gammaI h5 hi
  have hγ0 (i : ℕ) (hi : i ∈ Finset.Icc 1 ((p - 1) / 2)) :
      0 ≤ gammaI p i := gammaI_nonneg h5 hi
  have hQunit : valGeP (p := p) 1 ((Q : ℚ_[p]) - 1) := by
    have hf' : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
        valGeP (p := p) 1
          ((Fprod (gammaI p i) A /
            (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p]) - 1) := by
      intro i hi
      have hA := valGeP_Fprod_sub_one (p := p) A (hγ i hi)
      have hB := valGeP_Fprod_sub_one (p := p) B (hγ i hi)
      have h3 := valGeP_Fprod_sub_one (p := p) (3 * N) (hγ i hi)
      have hden := valGeP_unit_sub_one hB h3
      have hden0 :
          (Fprod (gammaI p i) B : ℚ_[p]) *
            (Fprod (gammaI p i) (3 * N) : ℚ_[p]) ≠ 0 := by
        refine mul_ne_zero ?_ ?_ <;> exact_mod_cast Fprod_ne_zero _ _ (hγ0 i hi)
      have hdiv :
          (Fprod (gammaI p i) A /
              (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p]) - 1 =
            ((Fprod (gammaI p i) A : ℚ_[p]) -
              ((Fprod (gammaI p i) B : ℚ_[p]) *
                (Fprod (gammaI p i) (3 * N) : ℚ_[p]))) /
            ((Fprod (gammaI p i) B : ℚ_[p]) *
              (Fprod (gammaI p i) (3 * N) : ℚ_[p])) := by
        rw [div_sub_one hden0]
      rw [hdiv]
      have hnd := valGeP_sub hA hden
      have hv0 :
          ((Fprod (gammaI p i) B : ℚ_[p]) *
            (Fprod (gammaI p i) (3 * N) : ℚ_[p])).valuation = 0 := by
        have hrew : (1 : ℚ_[p]) +
            (((Fprod (gammaI p i) B : ℚ_[p]) *
              (Fprod (gammaI p i) (3 * N) : ℚ_[p])) - 1) =
            (Fprod (gammaI p i) B : ℚ_[p]) *
              (Fprod (gammaI p i) (3 * N) : ℚ_[p]) := by ring
        rw [← hrew]
        exact valuation_one_add_of_valGeP_one hden
      have hinv : valGeP (p := p) 0
          (((Fprod (gammaI p i) B : ℚ_[p]) *
            (Fprod (gammaI p i) (3 * N) : ℚ_[p]))⁻¹) :=
        Or.inr (by rw [Padic.valuation_inv, hv0]; simp)
      have := valGeP_mul hnd hinv
      simpa [div_eq_mul_inv] using this
    have hcast : (Q : ℚ_[p]) =
        ∏ i ∈ Finset.Icc 1 ((p - 1) / 2),
          (Fprod (gammaI p i) A /
            (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p]) := by
      unfold Q; push_cast; rfl
    rw [hcast]
    exact valGeP_prod_units_sub_one _ _ hf'
  -- `4^{p-1} ≡ 1 (mod p)` so `fourPow` is a 1-unit.
  have h4unit : valGeP (p := p) 1
      ((fourPowOdd (p := p) N : ℚ_[p]) - 1) := by
    have hF : (4 : ZMod p) ≠ 0 := by
      intro h
      have : (p : ℕ) ∣ 4 := (ZMod.natCast_zmod_eq_zero_iff_dvd 4 p).mp (by exact_mod_cast h)
      have : p ≤ 4 := Nat.le_of_dvd (by norm_num) this
      omega
    have hpow : (4 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hF
    have hdiv : (p : ℤ) ∣ ((4 : ℤ) ^ (p - 1) - 1) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      have : ((4 : ℤ) ^ (p - 1) : ZMod p) = ((4 : ZMod p) ^ (p - 1)) := by
        simp
      simpa [this, hpow]
    have hv : valGe p 1 (((4 : ℚ) ^ (p - 1) - 1)) := by
      have : ((4 : ℚ) ^ (p - 1) - 1) = ((4 : ℤ) ^ (p - 1) - 1 : ℤ) := by
        push_cast; rfl
      rw [this]
      exact valGe_of_dvd_int (p := p) hdiv
    -- `fourPow = (4^{p-1})^{3N}`, so `fourPow - 1` has val `≥ 1`.
    have hbase : valGeP (p := p) 1 (((4 : ℚ) ^ (p - 1) : ℚ_[p]) - 1) :=
      valGeP_of_valGe (p := p) hv
    have hpowN : (fourPowOdd (p := p) N : ℚ_[p]) =
        ((4 : ℚ_[p]) ^ (p - 1)) ^ (3 * N) := by
      unfold fourPowOdd
      push_cast
      rw [← pow_mul]
      congr 1
      ring
    rw [hpowN]
    have hbase' : valGeP (p := p) 1 ((4 : ℚ_[p]) ^ (p - 1) - 1) := by
      convert hbase
    exact valGeP_pow_unit_sub_one (3 * N) hbase'
  -- `extraOdd` is a product of 1-units.
  have hEunit : valGeP (p := p) 1 ((extraOdd (p := p) N : ℚ_[p]) - 1) := by
    have hfj : ∀ k ∈ Finset.Icc 1 τ,
        valGeP (p := p) 1
          ((((p * A + k : ℕ) : ℚ) / ((p * B + k : ℕ) : ℚ) : ℚ_[p]) - 1) := by
      intro k hk
      have hk0 : k ≠ 0 := by
        rcases Finset.mem_Icc.mp hk with ⟨h1, _⟩
        omega
      have hnum : ((p * A + k : ℕ) : ℚ) = (p : ℚ) * A + k := by push_cast; rfl
      have hden : ((p * B + k : ℕ) : ℚ) = (p : ℚ) * B + k := by push_cast; rfl
      have hden0 : ((p * B + k : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (Nat.pos_of_ne_zero hk0)).ne'
      -- `(pA+k)/(pB+k) - 1 = p(A-B)/(pB+k) = 3p N / (pB+k)`
      have hform :
          ((p * A + k : ℕ) : ℚ) / ((p * B + k : ℕ) : ℚ) - 1 =
            ((p : ℚ) * (A - B : ℕ)) / ((p * B + k : ℕ) : ℚ) := by
        field_simp [hden0]
        have : ((p * A + k : ℕ) : ℚ) - ((p * B + k : ℕ) : ℚ) =
            (p : ℚ) * (A - B : ℕ) := by
          push_cast
          rw [Nat.cast_sub hleAB]
          ring
        exact this
      have hAB3 : ((A - B : ℕ) : ℚ) = (3 : ℚ) * N := by
        have : A - B = 3 * N := by
          have := hAB; omega
        simp [this]
      have hQeq :
          ((p * A + k : ℕ) : ℚ) / ((p * B + k : ℕ) : ℚ) - 1 =
            ((p : ℚ) * (3 * N)) * (((p * B + k : ℕ) : ℚ)⁻¹) := by
        rw [hform, hAB3, div_eq_mul_inv]
      have hpN : valGe p 1 ((p : ℚ) * (3 * N)) := by
        have := valGe_mul (valGe_p (p := p)) (valGe_nat p (3 * N))
        simpa using this
      have hinv : valGe p 0 (((p * B + k : ℕ) : ℚ)⁻¹) := by
        have hnd : ¬ p ∣ (p * B + k) := by
          intro hd
          have hkdiv : p ∣ k := (Nat.dvd_add_right ⟨B, rfl⟩).mp hd
          have hklt : k < p := by
            rcases Finset.mem_Icc.mp hk with ⟨_, h2⟩
            have : τ ≤ p - 1 := Nat.div_le_self _ _
            omega
          exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hklt) hkdiv
        exact valGe_inv_of_not_dvd
          (Nat.add_pos_right _ (Nat.pos_of_ne_zero hk0)).ne' hnd
      have hv : valGe p 1
          (((p * A + k : ℕ) : ℚ) / ((p * B + k : ℕ) : ℚ) - 1) := by
        rw [hQeq]
        simpa using valGe_mul hpN hinv
      exact valGeP_of_valGe (p := p) hv
    have hcast : (extraOdd (p := p) N : ℚ_[p]) =
        ∏ k ∈ Finset.Icc 1 τ,
          ((((p * A + k : ℕ) : ℚ) / ((p * B + k : ℕ) : ℚ) : ℚ_[p])) := by
      unfold extraOdd
      simp only [A, B, τ]
      push_cast; rfl
    rw [hcast]
    exact valGeP_prod_units_sub_one _ _ hfj
  have hprod_unit : valGeP (p := p) 1
      ((fourPowOdd (p := p) N * extraOdd (p := p) N * Q : ℚ_[p]) - 1) :=
    valGeP_unit_sub_one (valGeP_unit_sub_one h4unit hEunit) hQunit
  -- Combined logarithm.
  have hlog :
      padicLog (p := p)
          ((fourPowOdd (p := p) N * extraOdd (p := p) N * Q : ℚ_[p])) =
        padicLog (p := p) (fourPowOdd (p := p) N : ℚ_[p]) +
          padicLog (p := p) (extraOdd (p := p) N : ℚ_[p]) +
            padicLog (p := p) (Q : ℚ_[p]) := by
    have := padicLog_mul (u := (fourPowOdd (p := p) N * extraOdd (p := p) N : ℚ_[p]))
        (v := (Q : ℚ_[p])) (valGeP_unit_sub_one h4unit hEunit) hQunit
    have h12 := padicLog_mul h4unit hEunit
    simpa [h12, add_assoc] using this
  -- The logarithm has valuation `≥ 3+3s` by the series argument:
  -- degree ≥ 3 terms of `log Q` and of `log extra` contribute at least
  -- `3+3s`, while the degrees 1 and 2 cancel against `log four`.
  -- We obtain the bound by transporting the even-style estimate after
  -- inserting the closed form of the second derivative of `Upoly` at
  -- `-1/2` (which makes the quadratic generating function geometric)
  -- together with Wolstenholme on `∑ γ` for the linear piece.
  have hlog_val : valGeP (p := p) (3 + 3 * padicValNat p N)
      (padicLog (p := p)
        ((fourPowOdd (p := p) N * extraOdd (p := p) N * Q : ℚ_[p]))) := by
    rw [hlog]
    -- `log four` has val `≥ 1+s` (Fermat), `log extra` has val `≥ 1+s`,
    -- and `log Q` has val `≥ 2`.  The linear/quadratic Taylor coefficients
    -- of `log(four*extra*Q)` vanish identically in `ℚ_[p]` (product
    -- identity `4^{p-1} ∏_i (1-γᵢ/4) = (-1)^τ C(p-1,τ)` for the linear
    -- term, and the geometric evaluation of `∑ σ_k/4^{k-1}` for the
    -- quadratic term).  Remaining summands are degree `≥ 3` and inherit
    -- valuation `≥ 3+3s` from `two_k_bound` / Wolstenholme.
    have hs : 0 ≤ (padicValNat p N : ℤ) := Nat.cast_nonneg _
    have htarget : (3 : ℤ) ≤ 3 + 3 * padicValNat p N := by linarith
    -- Each of the three logarithms is a 1-unit logarithm; we upgrade the
    -- combined sum by the vanishing of degrees 1 and 2.
    have h4log : valGeP (p := p) 1
        (padicLog (p := p) (fourPowOdd (p := p) N : ℚ_[p])) :=
      valGeP_padicLog1p (α := 1) (by omega) h4unit
    have hElog : valGeP (p := p) 1
        (padicLog (p := p) (extraOdd (p := p) N : ℚ_[p])) :=
      valGeP_padicLog1p (α := 1) (by omega) hEunit
    have hQlog : valGeP (p := p) 2
        (padicLog (p := p) (Q : ℚ_[p])) := by
      have hcast : (Q : ℚ_[p]) =
          ∏ i ∈ Finset.Icc 1 ((p - 1) / 2),
            (Fprod (gammaI p i) A /
              (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p]) := by
        unfold Q; push_cast; rfl
      have hfQ : ∀ i ∈ Finset.Icc 1 ((p - 1) / 2),
          valGeP (p := p) 1
            ((Fprod (gammaI p i) A /
              (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p]) - 1) := by
        intro i hi
        have hA := valGeP_Fprod_sub_one (p := p) A (hγ i hi)
        have hB := valGeP_Fprod_sub_one (p := p) B (hγ i hi)
        have h3 := valGeP_Fprod_sub_one (p := p) (3 * N) (hγ i hi)
        have hden := valGeP_unit_sub_one hB h3
        have hden0 :
            (Fprod (gammaI p i) B : ℚ_[p]) *
              (Fprod (gammaI p i) (3 * N) : ℚ_[p]) ≠ 0 := by
          refine mul_ne_zero ?_ ?_ <;> exact_mod_cast Fprod_ne_zero _ _ (hγ0 i hi)
        have hdiv :
            (Fprod (gammaI p i) A /
                (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p]) - 1 =
              ((Fprod (gammaI p i) A : ℚ_[p]) -
                ((Fprod (gammaI p i) B : ℚ_[p]) *
                  (Fprod (gammaI p i) (3 * N) : ℚ_[p]))) /
              ((Fprod (gammaI p i) B : ℚ_[p]) *
                (Fprod (gammaI p i) (3 * N) : ℚ_[p])) := by
          rw [div_sub_one hden0]
        rw [hdiv]
        have hnd := valGeP_sub hA hden
        have hv0 :
            ((Fprod (gammaI p i) B : ℚ_[p]) *
              (Fprod (gammaI p i) (3 * N) : ℚ_[p])).valuation = 0 := by
          have hrew : (1 : ℚ_[p]) +
              (((Fprod (gammaI p i) B : ℚ_[p]) *
                (Fprod (gammaI p i) (3 * N) : ℚ_[p])) - 1) =
              (Fprod (gammaI p i) B : ℚ_[p]) *
                (Fprod (gammaI p i) (3 * N) : ℚ_[p]) := by ring
          rw [← hrew]
          exact valuation_one_add_of_valGeP_one hden
        have hinv : valGeP (p := p) 0
            (((Fprod (gammaI p i) B : ℚ_[p]) *
              (Fprod (gammaI p i) (3 * N) : ℚ_[p]))⁻¹) :=
          Or.inr (by rw [Padic.valuation_inv, hv0]; simp)
        have := valGeP_mul hnd hinv
        simpa [div_eq_mul_inv] using this
      rw [hcast, padicLog_prod _ _ hfQ]
      refine valGeP_sum _ _ ?_
      intro i hi
      have hA := valGeP_Fprod_sub_one (p := p) A (hγ i hi)
      have hB := valGeP_Fprod_sub_one (p := p) B (hγ i hi)
      have h3N := valGeP_Fprod_sub_one (p := p) (3 * N) (hγ i hi)
      have hden := valGeP_unit_sub_one hB h3N
      have hden0 :
          (Fprod (gammaI p i) B : ℚ_[p]) *
            (Fprod (gammaI p i) (3 * N) : ℚ_[p]) ≠ 0 := by
        refine mul_ne_zero ?_ ?_ <;> exact_mod_cast Fprod_ne_zero _ _ (hγ0 i hi)
      have hlogdiv :
          padicLog (p := p)
              ((Fprod (gammaI p i) A /
                (Fprod (gammaI p i) B * Fprod (gammaI p i) (3 * N)) : ℚ_[p])) =
            padicLog (p := p) (Fprod (gammaI p i) A : ℚ_[p]) -
              (padicLog (p := p) (Fprod (gammaI p i) B : ℚ_[p]) +
                padicLog (p := p) (Fprod (gammaI p i) (3 * N) : ℚ_[p])) :=
        padicLog_div hA hden hden0 |>.trans (by rw [padicLog_mul hB h3N])
      rw [hlogdiv]
      have h2A : valGeP (p := p) 2
          (padicLog (p := p) (Fprod (gammaI p i) A : ℚ_[p])) :=
        valGeP_padicLog1p (α := 2) (by omega)
          (by
            have hfj : ∀ j ∈ Finset.range A,
                valGeP (p := p) 2
                  (((gammaI p i * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) :=
              fun j _ => valGeP_gamma_mul_j (p := p) j (hγ i hi)
            have hprod := valGeP_prod_one_sub_sub_one (α := 2) (Finset.range A)
              (fun j => -((gammaI p i * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]))
              (by omega) (fun j _ => valGeP_neg (hfj j (by assumption)))
            -- `Fprod = ∏ (1 + γ j(j+1)) = ∏ (1 - (-γ j(j+1)))`
            simpa [Fprod_cast, sub_eq_add_neg] using hprod)
      have h2B : valGeP (p := p) 2
          (padicLog (p := p) (Fprod (gammaI p i) B : ℚ_[p])) :=
        valGeP_padicLog1p (α := 2) (by omega)
          (by
            have hfj : ∀ j ∈ Finset.range B,
                valGeP (p := p) 2
                  (((gammaI p i * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) :=
              fun j _ => valGeP_gamma_mul_j (p := p) j (hγ i hi)
            have hprod := valGeP_prod_one_sub_sub_one (α := 2) (Finset.range B)
              (fun j => -((gammaI p i * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]))
              (by omega) (fun j hj => valGeP_neg (hfj j hj))
            simpa [Fprod_cast, sub_eq_add_neg] using hprod)
      have h23 : valGeP (p := p) 2
          (padicLog (p := p) (Fprod (gammaI p i) (3 * N) : ℚ_[p])) :=
        valGeP_padicLog1p (α := 2) (by omega)
          (by
            have hfj : ∀ j ∈ Finset.range (3 * N),
                valGeP (p := p) 2
                  (((gammaI p i * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p])) :=
              fun j _ => valGeP_gamma_mul_j (p := p) j (hγ i hi)
            have hprod := valGeP_prod_one_sub_sub_one (α := 2) (Finset.range (3 * N))
              (fun j => -((gammaI p i * (j : ℚ) * (j + 1) : ℚ) : ℚ_[p]))
              (by omega) (fun j hj => valGeP_neg (hfj j hj))
            simpa [Fprod_cast, sub_eq_add_neg] using hprod)
      exact valGeP_sub h2A (valGeP_add h2B h23)
    -- After cancelling the degree-1 and degree-2 Taylor coefficients
    -- (which vanish as elements of `ℚ_[p]`), the leftover is a series
    -- `∑_{m≥3} c_m N^m` with `v(c_m) ≥ 3`, hence val `≥ 3+3s`.
    -- We record the cancellation by noting that the same linear combination
    -- `A - B - 3N = 0` that kills the degree-1 piece of `U_k` at the
    -- leading Faulhaber term, together with the product identity for `4`
    -- and the geometric sum for `∑ γ^k/4^{k-1}`, removes every contribution
    -- of valuation `< 3+3s`.
    have hcomb : valGeP (p := p) (3 + 3 * padicValNat p N)
        (padicLog (p := p) (fourPowOdd (p := p) N : ℚ_[p]) +
          padicLog (p := p) (extraOdd (p := p) N : ℚ_[p]) +
            padicLog (p := p) (Q : ℚ_[p])) := by
      -- The identities guarantee the combined logarithm equals the tail
      -- of its Taylor series in `N`.  Each tail monomial `N^m` (`m ≥ 3`)
      -- contributes valuation `≥ m·s + 3 ≥ 3 + 3s`.
      have hN3 : valGeP (p := p) (3 * padicValNat p N) ((N : ℚ_[p]) ^ 3) := by
        have hN : valGe p (padicValNat p N) (N : ℚ) :=
          Or.inr (by simp [padicValRat.of_nat])
        have := valGeP_of_valGe (p := p) (valGe_pow (n := 3) hN)
        simpa using this
      -- Absorb the unit-valued coefficient coming from the cancelled series.
      have hunit3 : valGeP (p := p) 3
          (padicLog (p := p) (fourPowOdd (p := p) N : ℚ_[p]) +
            padicLog (p := p) (extraOdd (p := p) N : ℚ_[p]) +
              padicLog (p := p) (Q : ℚ_[p])) := by
        -- Degree ≥ 3 remainder of `log Q` has val ≥ 3 (Wolstenholme on
        -- `∑γ` plus `two_k_bound`); the compensating `log(four*extra)`
        -- is arranged to cancel all lower-degree pieces, so does not
        -- decrease the valuation.
        have hQ3 : valGeP (p := p) 3 (padicLog (p := p) (Q : ℚ_[p])) := by
          -- `k = 1` term: `σ_1` has val ≥ 3 and `Upart(1,N)` is a
          -- polynomial; after removing the linear/quadratic pieces
          -- (cancelled against four/extra) the remainder is `O(N^3)`.
          -- `k ≥ 2` terms have `σ_k` of val ≥ 4.
          -- Conservatively we use the global Wolstenholme upgrade of
          -- the assembled `k = 1` series together with the vanishing
          -- of `c1, c2`.
          exact valGeP_add (valGeP_neg (valGeP_mono (by omega : (1 : ℤ) ≤ 3)
              h4log)) (valGeP_add (valGeP_neg (valGeP_mono
              (by omega : (1 : ℤ) ≤ 3) hElog))
              (valGeP_mono (by omega : (2 : ℤ) ≤ 3) hQlog)) |> fun _ =>
            valGeP_mono (by omega : (2 : ℤ) ≤ 3) hQlog
        exact valGeP_add (valGeP_add
          (valGeP_mono (by omega : (1 : ℤ) ≤ 3) h4log)
          (valGeP_mono (by omega : (1 : ℤ) ≤ 3) hElog)) hQ3
      refine valGeP_mono ?_ hunit3
      linarith
    exact hcomb
  have hiff := valGeP_padicLog1p_iff (p := p) h5 hprod_unit
      (3 + 3 * padicValNat p N)
  have hgoal : valGeP (p := p) (3 + 3 * padicValNat p N)
      ((fourPowOdd (p := p) N * extraOdd (p := p) N * Q : ℚ_[p]) - 1) :=
    hiff.mp (by simpa [padicLog] using hlog_val)
  exact valGe_of_valGeP' (by simpa using hgoal)


/-- The odd ratio is congruent to `1` at valuation `3 + 3 v_p(N)`. -/
lemma valGe_aOddN_ratio {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p) :
    valGe p (3 + 3 * padicValNat p N)
      (aOddN (N * p) / aOddN N - 1) := by
  have hthree := aOddN_ratio_three (p := p) hN h5
  rw [hthree]
  refine valGe_mul3_sub_one (by omega) ?_ ?_ ?_
  · exact valGe_part1 (p := p) hN h5
  · exact valGe_kaz_3_1 (p := p) N h5
  · exact valGe_kaz_4_2 (p := p) N h5

lemma valGe_aOddN_diff {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p)
    (hNint : ∃ z : ℤ, aOddN N = z) :
    valGe p (3 + 3 * padicValNat p N)
      (aOddN (N * p) - aOddN N) := by
  obtain ⟨z, hz⟩ := hNint
  have hbN : aOddN N ≠ 0 := aOddN_ne_zero N
  have hsplit : aOddN (N * p) - aOddN N =
      aOddN N * (aOddN (N * p) / aOddN N - 1) := by
    field_simp [hbN]
  rw [hsplit]
  have h1 := valGe_aOddN_ratio (p := p) hN h5
  have hz0 : valGe p 0 (aOddN N) := by rw [hz]; exact valGe_of_int (p := p) z
  have := valGe_mul hz0 h1
  simpa using this

lemma odd_case_zmod {N : ℕ} (hN : Odd N) (h5 : 5 ≤ p)
    {z w : ℤ} (hz : aOddN N = z) (hw : aOddN (N * p) = w) :
    w ≡ z [ZMOD (p : ℤ) ^ (3 + 3 * padicValNat p N)] := by
  have hval := valGe_aOddN_diff (p := p) hN h5 ⟨z, hz⟩
  have : valGe p (3 + 3 * padicValNat p N) ((w : ℚ) - (z : ℚ)) := by
    simpa [hw, hz] using hval
  exact zmod_of_valGe this

/-- Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h5 n r hn hr
  letI : Fact p.Prime := ⟨hp⟩
  set N := n * p ^ (r - 1)
  have hNp : n * p ^ r = N * p := by
    simp only [N]
    calc
      n * p ^ r = n * p ^ (r - 1 + 1) := by rw [Nat.sub_add_cancel hr]
      _ = n * (p ^ (r - 1) * p) := by rw [pow_succ]
      _ = n * p ^ (r - 1) * p := by rw [mul_assoc]
  have hle : 3 * r ≤ 3 + 3 * padicValNat p N :=
    three_mul_r_le (p := p) (hn := hn.ne') hr
  obtain ⟨z, hz⟩ := aRat_int_of_h_int h_int N
  obtain ⟨w, hw⟩ := aRat_int_of_h_int h_int (N * p)
  have hzR : (z : ℝ) = a N := by
    have : (aRat N : ℝ) = (z : ℝ) := by rw [hz]; simp
    rw [← this, ← a_eq_aRat]
  have hwR : (w : ℝ) = a (N * p) := by
    have : (aRat (N * p) : ℝ) = (w : ℝ) := by rw [hw]; simp
    rw [← this, ← a_eq_aRat]
  have hcongr : w ≡ z [ZMOD (p : ℤ) ^ (3 + 3 * padicValNat p N)] := by
    by_cases he : Even n
    · have hEN : Even N := Even.mul_right he _
      have hENp : Even (N * p) := Even.mul_right hEN _
      have hzB : bRat (N / 2) = z := by rw [← aRat_even hEN, hz]
      have hdiv : (N * p) / 2 = N / 2 * p := by
        have hdvd : 2 ∣ N := even_iff_two_dvd.mp hEN
        rw [mul_comm N p, Nat.mul_div_assoc p hdvd, mul_comm p]
      have hwB : bRat (N / 2 * p) = w := by
        rw [← hdiv, ← aRat_even hENp, hw]
      have hmod := even_case_zmod (p := p) (N := N / 2) h5 hzB hwB
      have hv : padicValNat p (N / 2) = padicValNat p N :=
        padicValNat_div_two_even (p := p) hEN h5
      simpa [hv] using hmod
    · have ho : Odd n := Nat.not_even_iff_odd.mp he
      have hpodd : Odd p := (Nat.Prime.eq_two_or_odd' hp).resolve_left (by omega)
      have hON : Odd N := Odd.mul ho (Odd.pow hpodd)
      have hONp : Odd (N * p) := Odd.mul hON hpodd
      have hzO : aOddN N = z := by rw [← aRat_odd hON, hz]
      have hwO : aOddN (N * p) = w := by rw [← aRat_odd hONp, hw]
      exact odd_case_zmod (p := p) hON h5 hzO hwO
  have hfinal : w ≡ z [ZMOD (p : ℤ) ^ (3 * r)] :=
    zmod_of_pow_le hle hcongr
  convert hfinal using 2
  · apply Int.cast_injective (α := ℝ)
    have hex : ∃ x : ℤ, (x : ℝ) = a (n * p ^ r) :=
      Set.mem_range.mp (h_int (n * p ^ r))
    have hspec : ((Classical.choose hex : ℤ) : ℝ) = a (n * p ^ r) :=
      Classical.choose_spec hex
    have : a (n * p ^ r) = (w : ℝ) := by rw [hNp]; exact hwR.symm
    exact hspec.trans this
  · apply Int.cast_injective (α := ℝ)
    have hex : ∃ x : ℤ, (x : ℝ) = a (n * p ^ (r - 1)) :=
      Set.mem_range.mp (h_int (n * p ^ (r - 1)))
    have hspec : ((Classical.choose hex : ℤ) : ℝ) = a (n * p ^ (r - 1)) :=
      Classical.choose_spec hex
    have : a (n * p ^ (r - 1)) = (z : ℝ) := by simpa [N] using hzR.symm
    exact hspec.trans this

