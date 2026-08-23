import FormalConjectures.Util.ProblemImports

/--
A190969: The sequence defined by the linear recurrence relation
$$a(n) = 5 a(n-1) - 8 a(n-2)$$
with initial conditions $a(0)=0$ and $a(1)=1$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n

open Finset Nat
open scoped BigOperators

/- Basic properties of the sequence `a`. -/

@[simp] lemma a_zero : a 0 = 0 := rfl
@[simp] lemma a_one : a 1 = 1 := rfl

lemma a_succ_succ (n : ℕ) : a (n + 2) = 5 * a (n + 1) - 8 * a n := by
  cases n with
  | zero => simp [a]
  | succ n => simp [a]

/-- Linear-time evaluation of `a`. -/
def aGo : ℕ → ℤ → ℤ → ℤ
| 0, x, _ => x
| n + 1, x, y => aGo n y (5 * y - 8 * x)

def aFast (n : ℕ) : ℤ := aGo n 0 1

lemma aGo_shift : ∀ n m, aGo n (a m) (a (m + 1)) = a (m + n) := by
  intro n
  induction n with
  | zero =>
    intro m; simp [aGo]
  | succ n ih =>
    intro m
    rw [aGo, show 5 * a (m + 1) - 8 * a m = a (m + 2) from (a_succ_succ m).symm]
    simpa [Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm] using ih (m + 1)

lemma a_eq_fast (n : ℕ) : a n = aFast n := by
  simpa [aFast, a_zero, a_one] using (aGo_shift n 0).symm

/-- `a` is the Lucas sequence `U_n(5, 8)`. -/
lemma a_eq_lucas (n : ℕ) : a n = LucasSequence.U 5 8 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      rw [a_succ_succ, LucasSequence.U]
      rw [ih (n + 1) (by omega), ih n (by omega)]

/- Auxiliary arithmetic. -/

lemma odd_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h : p ≠ 2) : Odd p :=
  hp.odd_of_ne_two h

lemma two_not_dvd_odd_prime {p : ℕ} (hp : p.Prime) (h : p ≠ 2) : ¬ 2 ∣ p := by
  intro hdvd
  exact h (hp.dvd_iff_eq (by norm_num : 2 ≠ 1) |>.mp hdvd)

lemma coprime_two_odd_prime {p : ℕ} (hp : p.Prime) (h : p ≠ 2) : Nat.Coprime 2 p := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  exact two_not_dvd_odd_prime hp h

lemma coprime_4096_odd_prime_nat {p : ℕ} (hp : p.Prime) (h : p ≠ 2) : Nat.Coprime 4096 p := by
  have h4096 : 4096 = 2 ^ 12 := by norm_num
  rw [h4096, Nat.coprime_pow_left_iff (by norm_num : 0 < 12)]
  exact coprime_two_odd_prime hp h

lemma isUnit_neg_4096 {p n : ℕ} (hp : p.Prime) (h : p ≠ 2) (hn : 0 < n) :
    IsUnit ((-4096 : ℤ) : ZMod (p ^ n)) := by
  have hunit : IsUnit ((4096 : ℕ) : ZMod (p ^ n)) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_pow_right_iff hn]
    exact coprime_4096_odd_prime_nat hp h
  have : ((-4096 : ℤ) : ZMod (p ^ n)) = -((4096 : ℕ) : ZMod (p ^ n)) := by
    simp
  rw [this]
  exact hunit.neg

/- Vanishing of central binomials for large `k`. -/

lemma p_le_two_mul_of_large {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk1 : (p + 1) / 2 ≤ k) : p ≤ 2 * k := by
  have hodd' : Odd p := odd_of_prime_ne_two hp hodd
  obtain ⟨m, hm⟩ := hodd'
  have hpeven : 2 ∣ p + 1 := ⟨m + 1, by omega⟩
  have : p + 1 = 2 * ((p + 1) / 2) := (Nat.mul_div_cancel' hpeven).symm
  omega

lemma prime_dvd_centralBinom_of_large {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk1 : (p + 1) / 2 ≤ k) (hk2 : k < p) : p ∣ (2 * k).choose k := by
  have h2k : p ≤ 2 * k := p_le_two_mul_of_large hp hodd hk1
  have hsub : 2 * k - k < p := by
    have : 2 * k - k = k := by omega
    omega
  exact hp.dvd_choose hk2 hsub h2k

lemma pow_three_centralBinom_eq_zero {p k n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk1 : (p + 1) / 2 ≤ k) (hk2 : k < p) (hn : n ≤ 3) (_hn0 : 0 < n) :
    ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3 = 0 := by
  have hdiv : p ∣ (2 * k).choose k := prime_dvd_centralBinom_of_large hp hodd hk1 hk2
  have hdiv3 : p ^ 3 ∣ ((2 * k).choose k) ^ 3 := pow_dvd_pow_of_dvd hdiv 3
  have hdivn : p ^ n ∣ ((2 * k).choose k) ^ 3 :=
    dvd_trans (pow_dvd_pow p hn) hdiv3
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact hdivn

/- The summands and the sum. -/

/-- The general summand in `ZMod (p^n)`. -/
def summand (p n k : ℕ) : ZMod (p ^ n) :=
  let num : ZMod (p ^ n) := (a (4 * k) : ZMod (p ^ n)) *
    ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3
  let den : ZMod (p ^ n) := ((-4096 : ℤ) : ZMod (p ^ n)) ^ k
  num * den⁻¹

/-- The truncated sum `S` appearing in the conjecture. -/
def Ssum (p n : ℕ) : ZMod (p ^ n) :=
  (range p).sum (fun k => summand p n k)

lemma summand_zero (p n : ℕ) : summand p n 0 = 0 := by
  simp [summand, a_zero]

lemma summand_eq_zero_of_large {p n k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk1 : (p + 1) / 2 ≤ k) (hk2 : k < p) (hn : n ≤ 3) (hn0 : 0 < n) :
    summand p n k = 0 := by
  simp only [summand]
  have : ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3 = 0 :=
    pow_three_centralBinom_eq_zero hp hodd hk1 hk2 hn hn0
  simp [this]

lemma Ssum_eq_sum_small {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hn : n ≤ 3) (hn0 : 0 < n) :
    Ssum p n = (range ((p + 1) / 2)).sum (fun k => summand p n k) := by
  simp only [Ssum]
  have hle : (p + 1) / 2 ≤ p := by
    have : 0 < p := hp.pos
    omega
  rw [← sum_range_add_sum_Ico _ hle]
  have : (Ico ((p + 1) / 2) p).sum (fun k => summand p n k) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [mem_Ico] at hk
    exact summand_eq_zero_of_large hp hodd hk.1 hk.2 hn hn0
  simp [this]

/- Recurrence for the subsequence `a(4n)`. -/

lemma a_add_two (m : ℕ) : a (m + 2) = 5 * a (m + 1) - 8 * a m :=
  a_succ_succ m

lemma a_add_four (m : ℕ) :
    a (m + 4) = 9 * a (m + 2) - 64 * a m := by
  have e1 : a (m + 2) = 5 * a (m + 1) - 8 * a m := a_add_two m
  have e2 : a (m + 3) = 5 * a (m + 2) - 8 * a (m + 1) := by
    simpa [show m + 3 = (m + 1) + 2 by omega] using a_add_two (m + 1)
  have e3 : a (m + 4) = 5 * a (m + 3) - 8 * a (m + 2) := by
    simpa [show m + 4 = (m + 2) + 2 by omega] using a_add_two (m + 2)
  rw [e3, e2, e1]
  ring

lemma a_add_eight (m : ℕ) :
    a (m + 8) = -47 * a (m + 4) - 4096 * a m := by
  have h1 : a (m + 4) = 9 * a (m + 2) - 64 * a m := a_add_four m
  have h2 : a (m + 6) = 9 * a (m + 4) - 64 * a (m + 2) := by
    simpa [show m + 6 = (m + 2) + 4 by omega] using a_add_four (m + 2)
  have h3 : a (m + 8) = 9 * a (m + 6) - 64 * a (m + 4) := by
    simpa [show m + 8 = (m + 4) + 4 by omega] using a_add_four (m + 4)
  have h576 : 576 * a (m + 2) = 64 * a (m + 4) + 4096 * a m := by
    have := congrArg (fun t => 64 * t) h1
    linarith
  linarith

lemma a_four_mul_add_two (n : ℕ) :
    a (4 * (n + 2)) = -47 * a (4 * (n + 1)) - 4096 * a (4 * n) := by
  have := a_add_eight (4 * n)
  have e1 : 4 * n + 8 = 4 * (n + 2) := by omega
  have e2 : 4 * n + 4 = 4 * (n + 1) := by omega
  simpa [e1, e2] using this

/- Quadratic residue symbol of `-7`. -/

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

lemma neg_one_pow_mul_three (m : ℕ) : (-1 : ℤ) ^ (m * 3) = (-1) ^ m := by
  rw [mul_comm, pow_mul]
  simp [pow_three]

lemma legendre_neg_seven_eq_legendre_self (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (_hp7 : p ≠ 7) :
    legendreSym p (-7) = legendreSym 7 p := by
  have h7 : (7 : ℕ) ≠ 2 := by decide
  have hsplit : legendreSym p (-7) = legendreSym p (-1) * legendreSym p 7 := by
    rw [show (-7 : ℤ) = (-1) * 7 by norm_num, legendreSym.mul]
  have hqr : legendreSym 7 p =
      (-1) ^ (p / 2 * (7 / 2)) * legendreSym p 7 :=
    legendreSym.quadratic_reciprocity' hp2 h7
  have hpow : (-1 : ℤ) ^ (p / 2 * (7 / 2)) = (-1) ^ (p / 2) := by
    have : 7 / 2 = 3 := by norm_num
    rw [this, neg_one_pow_mul_three]
  have hneg1 : legendreSym p (-1) = ZMod.χ₄ p := legendreSym.at_neg_one hp2
  have hchi : ZMod.χ₄ p = (-1) ^ (p / 2) := by
    have hodd : p % 2 = 1 := (Nat.odd_iff).mp (odd_of_prime_ne_two Fact.out hp2)
    exact ZMod.χ₄_eq_neg_one_pow hodd
  rw [hsplit, hneg1, hqr, hpow, hchi]

lemma Ssum_eq_conjecture_S (p n : ℕ) :
    Ssum p n = (range p).sum fun k =>
      let num : ZMod (p ^ n) := (a (4 * k) : ZMod (p ^ n)) *
        ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3
      let den : ZMod (p ^ n) := ((-4096 : ℤ) : ZMod (p ^ n)) ^ k
      num * den⁻¹ := rfl

/- Binet formula in `ℤ√(-7)`. -/

abbrev ZsqrtNeg7 := ℤ√(-7)

def twoAlpha : ZsqrtNeg7 := ⟨5, 1⟩
def twoBeta : ZsqrtNeg7 := ⟨5, -1⟩

lemma char_twoAlpha : twoAlpha ^ 2 = 10 * twoAlpha - 32 := by
  apply Zsqrtd.ext <;> simp [twoAlpha, sq]

lemma char_twoBeta : twoBeta ^ 2 = 10 * twoBeta - 32 := by
  apply Zsqrtd.ext <;> simp [twoBeta, sq]

lemma rec_twoAlpha (n : ℕ) :
    twoAlpha ^ (n + 2) = 10 * twoAlpha ^ (n + 1) - 32 * twoAlpha ^ n := by
  have h : twoAlpha ^ (n + 2) = twoAlpha ^ 2 * twoAlpha ^ n := by
    rw [← pow_add, Nat.add_comm]
  rw [h, char_twoAlpha, sub_mul, mul_assoc]
  rw [pow_succ]
  ring

lemma rec_twoBeta (n : ℕ) :
    twoBeta ^ (n + 2) = 10 * twoBeta ^ (n + 1) - 32 * twoBeta ^ n := by
  have h : twoBeta ^ (n + 2) = twoBeta ^ 2 * twoBeta ^ n := by
    rw [← pow_add, Nat.add_comm]
  rw [h, char_twoBeta, sub_mul, mul_assoc]
  rw [pow_succ]
  ring

/-- Binet: `(5+√-7)^n - (5-√-7)^n = 2^n √-7 · a(n)` in `ℤ√(-7)`. -/
lemma binet_two (n : ℕ) :
    twoAlpha ^ n - twoBeta ^ n = ⟨0, (2 : ℤ) ^ n * a n⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      simp [twoAlpha, twoBeta, Zsqrtd.ext_iff]
    | 1 =>
      simp [twoAlpha, twoBeta, a_one, Zsqrtd.ext_iff]
    | n + 2 =>
      have ih1 := ih (n + 1) (by omega)
      have ih0 := ih n (by omega)
      rw [rec_twoAlpha, rec_twoBeta]
      have : (10 * twoAlpha ^ (n + 1) - 32 * twoAlpha ^ n) -
          (10 * twoBeta ^ (n + 1) - 32 * twoBeta ^ n) =
          10 * (twoAlpha ^ (n + 1) - twoBeta ^ (n + 1)) -
          32 * (twoAlpha ^ n - twoBeta ^ n) := by ring
      rw [this, ih1, ih0]
      apply Zsqrtd.ext
      · simp
      · simp [pow_succ, a_succ_succ]; ring

lemma a_four : a 4 = 45 := by
  native_decide

lemma a_eight : a 8 = -2115 := by
  native_decide

lemma Ssum_three_two : Ssum 3 2 = 0 := by
  have h0 : summand 3 2 0 = 0 := summand_zero 3 2
  have h1 : summand 3 2 1 = 0 := by
    unfold summand
    rw [a_four]
    have ha : ((45 : ℤ) : ZMod (3 ^ 2)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      norm_num
    -- `45` in `ZMod` is the nat cast
    have ha' : (45 : ZMod (3 ^ 2)) = 0 := by
      rw [← Int.cast_ofNat (R := ZMod (3 ^ 2)) 45, ha]
    simp [ha']
  have h2 : summand 3 2 2 = 0 := by
    unfold summand
    have : ((choose 4 2 : ℕ) : ZMod (3 ^ 2)) ^ 3 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      decide
    simp [this]
  simp only [Ssum]
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
  simp [h0, h1, h2]

lemma conjecture_p_three :
    Ssum 3 2 = 0 ∧ (3 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 3 3 = 0) := by
  constructor
  · exact Ssum_three_two
  · intro h
    simp at h

/- Fast versions of the summand, definitionally equal after `a_eq_fast`. -/

def summandFast (p n k : ℕ) : ZMod (p ^ n) :=
  let num : ZMod (p ^ n) := (aFast (4 * k) : ZMod (p ^ n)) *
    ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3
  let den : ZMod (p ^ n) := ((-4096 : ℤ) : ZMod (p ^ n)) ^ k
  num * den⁻¹

lemma summand_eq_fast (p n k : ℕ) : summand p n k = summandFast p n k := by
  simp only [summand, summandFast, a_eq_fast]

lemma Ssum_eq_fast (p n : ℕ) :
    Ssum p n = (range p).sum (fun k => summandFast p n k) := by
  simp only [Ssum, summand_eq_fast]

lemma conjecture_p_five :
    Ssum 5 2 = 0 ∧ (5 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 5 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro h; simp at h

lemma conjecture_p_seven :
    Ssum 7 2 = 0 ∧ (7 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 7 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro h; simp at h

/- The half-index `n = (p-1)/2`. -/

lemma two_mul_half_odd {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    2 * ((p - 1) / 2) = p - 1 := by
  have : Odd p := odd_of_prime_ne_two hp hodd
  obtain ⟨m, hm⟩ := this
  have : p - 1 = 2 * m := by omega
  rw [this, Nat.mul_div_right _ (by omega)]

lemma half_lt_p {p : ℕ} (hp : p.Prime) : (p - 1) / 2 < p := by
  have : 0 < p := hp.pos
  omega

lemma prime_ge_three {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : 3 ≤ p := by
  have : 2 ≤ p := hp.two_le
  rcases Nat.eq_or_lt_of_le this with h | h
  · exact (hodd h.symm).elim
  · exact h

lemma prime_le_seven_of {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hle : p ≤ 7) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have h3 : 3 ≤ p := prime_ge_three hp hodd
  interval_cases p
  · exact Or.inl rfl
  · exact absurd hp (by decide : ¬Nat.Prime 4)
  · exact Or.inr (Or.inl rfl)
  · exact absurd hp (by decide : ¬Nat.Prime 6)
  · exact Or.inr (Or.inr rfl)

lemma prime_le_twentythree_of {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hle : p ≤ 23) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
  have h3 : 3 ≤ p := prime_ge_three hp hodd
  interval_cases p
  · exact Or.inl rfl
  · exact absurd hp (by decide : ¬Nat.Prime 4)
  · exact Or.inr (Or.inl rfl)
  · exact absurd hp (by decide : ¬Nat.Prime 6)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact absurd hp (by decide : ¬Nat.Prime 8)
  · exact absurd hp (by decide : ¬Nat.Prime 9)
  · exact absurd hp (by decide : ¬Nat.Prime 10)
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact absurd hp (by decide : ¬Nat.Prime 12)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact absurd hp (by decide : ¬Nat.Prime 14)
  · exact absurd hp (by decide : ¬Nat.Prime 15)
  · exact absurd hp (by decide : ¬Nat.Prime 16)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact absurd hp (by decide : ¬Nat.Prime 18)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact absurd hp (by decide : ¬Nat.Prime 20)
  · exact absurd hp (by decide : ¬Nat.Prime 21)
  · exact absurd hp (by decide : ¬Nat.Prime 22)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

lemma conjecture_p_eleven :
    Ssum 11 2 = 0 ∧ (11 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 11 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro; rw [Ssum_eq_fast]; native_decide

lemma conjecture_p_thirteen :
    Ssum 13 2 = 0 ∧ (13 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 13 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro h; simp at h

lemma conjecture_p_seventeen :
    Ssum 17 2 = 0 ∧ (17 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 17 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro h; simp at h

lemma conjecture_p_nineteen :
    Ssum 19 2 = 0 ∧ (19 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 19 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro h; simp at h

lemma conjecture_p_twentythree :
    Ssum 23 2 = 0 ∧ (23 % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum 23 3 = 0) := by
  constructor
  · rw [Ssum_eq_fast]; native_decide
  · intro; rw [Ssum_eq_fast]; native_decide

lemma factorial_eq_prod (k : ℕ) :
    (k.factorial : ℚ) = ∏ j ∈ range k, (j + 1 : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, factorial_succ, Nat.cast_mul, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma descFactorial_eq_prod (n k : ℕ) (hk : k ≤ n) :
    (n.descFactorial k : ℚ) = ∏ j ∈ range k, (n - j : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : k ≤ n := le_trans (Nat.le_succ k) hk
    rw [prod_range_succ, Nat.descFactorial_succ, Nat.cast_mul, ih hle]
    have : (n - k : ℕ) = n - (k : ℕ) := rfl
    simp [Nat.cast_sub (by omega : k ≤ n)]
    ring

/-- Product formula for binomial coefficients over `ℚ`. -/
lemma choose_eq_prod_rat (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℚ) = ∏ j ∈ range k, ((n - j : ℚ) / (j + 1)) := by
  have hmul : n.choose k * k.factorial = n.descFactorial k := by
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.div_mul_cancel]
    exact Nat.factorial_dvd_descFactorial n k
  have hQ : (n.choose k : ℚ) * (k.factorial : ℚ) = (n.descFactorial k : ℚ) := by
    exact_mod_cast hmul
  rw [factorial_eq_prod, descFactorial_eq_prod n k hk] at hQ
  have hne : (∏ j ∈ range k, (j + 1 : ℚ)) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    exact_mod_cast (Nat.succ_ne_zero j)
  rw [prod_div_distrib]
  exact (eq_div_iff hne).2 hQ

lemma n_sub_j_eq {p j : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (_hj : j ≤ (p - 1) / 2) :
    (((p - 1) / 2 : ℕ) : ℚ) - j = ((p : ℚ) - (2 * j + 1)) / 2 := by
  have hn2 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd hp hodd
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hleft : (2 : ℚ) * (((p - 1) / 2 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    have : ((2 * ((p - 1) / 2) : ℕ) : ℚ) = (p - 1 : ℕ) := by
      exact_mod_cast hn2
    simpa [Nat.cast_mul, Nat.cast_sub hp.one_le] using this
  field_simp [h2]
  linarith

lemma prod_one_sub_p_odd (p k : ℕ) :
    ∏ j ∈ range k, (1 - (p : ℚ) / (2 * j + 1)) =
      ∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (2 * j + 1) := by
  refine prod_congr rfl ?_
  intro j hj
  have hne : (2 * j + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * j)
  field_simp [hne]

lemma factorial_two_mul_succ (k : ℕ) :
    (2 * (k + 1))! = (2 * k + 2) * ((2 * k + 1) * (2 * k)!) := by
  have e1 : (2 * k + 2)! = (2 * k + 2) * (2 * k + 1)! := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, factorial_succ]
  have e2 : (2 * k + 1)! = (2 * k + 1) * (2 * k)! := by
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, factorial_succ]
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, e1, e2]

/-- `∏_{j < k} (2j+1) = (2k)! / (2^k k!)`. -/
lemma prod_odd_eq_fact_div (k : ℕ) :
    ∏ j ∈ range k, (2 * j + 1 : ℚ) =
      ((2 * k).factorial : ℚ) / ((2 : ℚ) ^ k * k.factorial) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih]
    have hfac : ((2 * (k + 1)).factorial : ℚ) =
        (2 * k + 2 : ℚ) * (2 * k + 1) * (2 * k).factorial := by
      rw [factorial_two_mul_succ]
      push_cast
      ring
    have hden : (2 : ℚ) ^ (k + 1) * ((k + 1).factorial : ℚ) =
        (2 : ℚ) * (k + 1) * ((2 : ℚ) ^ k * k.factorial) := by
      rw [pow_succ, factorial_succ]
      push_cast
      ring
    rw [hfac, hden]
    have hne1 : ((2 : ℚ) ^ k * k.factorial) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
      exact_mod_cast Nat.factorial_ne_zero k
    have hne2 : (2 * k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
    field_simp [hne1, hne2]

lemma choose_central_rat (k : ℕ) :
    ((2 * k).choose k : ℚ) =
      ((2 * k).factorial : ℚ) / (k.factorial * k.factorial : ℚ) := by
  have hk : k ≤ 2 * k := by omega
  have hdvd : k.factorial * (2 * k - k).factorial ∣ (2 * k).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial hk
  have hne : ((k.factorial * (2 * k - k).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (Nat.factorial_ne_zero k)
      (Nat.factorial_ne_zero (2 * k - k))
  rw [Nat.choose_eq_factorial_div_factorial hk, Nat.cast_div hdvd hne]
  simp [show 2 * k - k = k by omega]

lemma descFactorial_central_rat (k : ℕ) :
    ((2 * k).descFactorial k : ℚ) = ((2 * k).factorial : ℚ) / k.factorial := by
  have hmul : (2 * k).choose k * k.factorial = (2 * k).descFactorial k := by
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.div_mul_cancel]
    exact Nat.factorial_dvd_descFactorial _ _
  have hk0 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have := congrArg (fun m : ℕ => (m : ℚ)) hmul
  simp only [Nat.cast_mul] at this
  rw [choose_central_rat] at this
  field_simp [hk0] at this ⊢
  linarith

/-- `∏_{j < k} (2k - j) / (2j + 1) = 2^k`. -/
lemma prod_desc_over_odd (k : ℕ) :
    ∏ j ∈ range k, (2 * k - j : ℚ) / (2 * j + 1) = (2 : ℚ) ^ k := by
  have hnum : ∏ j ∈ range k, (2 * k - j : ℚ) = ((2 * k).descFactorial k : ℚ) := by
    simpa [Nat.cast_mul] using (descFactorial_eq_prod (2 * k) k (by omega)).symm
  have hden := prod_odd_eq_fact_div k
  have hne : ∏ j ∈ range k, (2 * j + 1 : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    exact_mod_cast Nat.succ_ne_zero (2 * j)
  rw [prod_div_distrib, hnum, hden, descFactorial_central_rat]
  have hk0 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2k : ((2 * k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp [hk0, h2k]

lemma prod_neg_half (k : ℕ) :
    ∏ _j ∈ range k, ((-1 : ℚ) / 2) = ((-1 : ℚ) / 2) ^ k := by
  rw [prod_const, card_range]

lemma div_neg_one_two_pow (k : ℕ) :
    ((-1 : ℚ) / 2) ^ k = (-1 : ℚ) ^ k / (2 : ℚ) ^ k :=
  div_pow (-1 : ℚ) 2 k

lemma prod_swap_desc_odd (k : ℕ) (p : ℕ) :
    (∏ j ∈ range k, (2 * k - j : ℚ) / (j + 1)) *
      (∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (2 * j + 1)) =
    (∏ j ∈ range k, (2 * k - j : ℚ) / (2 * j + 1)) *
      (∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (j + 1)) := by
  simp only [prod_div_distrib]
  have h1 : ∏ j ∈ range k, (2 * j + 1 : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    exact_mod_cast Nat.succ_ne_zero (2 * j)
  have h2 : ∏ j ∈ range k, (j + 1 : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    exact_mod_cast Nat.succ_ne_zero j
  field_simp [h1, h2]

/-- `C(n,k) = C(2k,k) (-1/4)^k ∏_{j<k}(1-p/(2j+1))` with `n=(p-1)/2`. -/
lemma choose_half_central_identity (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    (((p - 1) / 2).choose k : ℚ) =
      ((2 * k).choose k : ℚ) * ((-1 : ℚ) / 4) ^ k *
        ∏ j ∈ range k, (1 - (p : ℚ) / (2 * j + 1)) := by
  set n := (p - 1) / 2
  have hkn : k ≤ n := hk
  have hC := choose_eq_prod_rat n k hkn
  have hnj : ∀ j ∈ range k, (n : ℚ) - j = ((p : ℚ) - (2 * j + 1)) / 2 := by
    intro j hj
    have : j ≤ n := (mem_range.mp hj).le.trans hkn
    simpa [n] using n_sub_j_eq hp hodd this
  have hterm : ∀ j ∈ range k,
      ((n : ℚ) - j) / (j + 1) =
        ((-1 : ℚ) / 2) * (((2 * j + 1 : ℚ) - p) / (j + 1)) := by
    intro j hj
    rw [hnj j hj]
    ring
  have hLHS : (n.choose k : ℚ) =
      ((-1 : ℚ) ^ k / (2 : ℚ) ^ k) *
        ∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (j + 1) := by
    rw [hC]
    have hrew : ∏ j ∈ range k, ((n : ℚ) - j) / (j + 1) =
        ∏ j ∈ range k, ((-1 : ℚ) / 2) * (((2 * j + 1 : ℚ) - p) / (j + 1)) :=
      prod_congr rfl hterm
    rw [hrew, prod_mul_distrib, prod_neg_half, div_neg_one_two_pow]
  have hC2 := choose_eq_prod_rat (2 * k) k (by omega)
  have hPi := prod_one_sub_p_odd p k
  have hneg : ((-1 : ℚ) / 4) ^ k = (-1 : ℚ) ^ k / (4 : ℚ) ^ k := div_pow _ _ _
  have h4 : (4 : ℚ) ^ k = (2 : ℚ) ^ k * (2 : ℚ) ^ k := by
    rw [← mul_pow]; norm_num
  have hpow := prod_desc_over_odd k
  have hswap := prod_swap_desc_odd k p
  have hcast : ∀ j ∈ range k, ((2 * k : ℕ) : ℚ) - j = ((2 * k - j : ℕ) : ℚ) := by
    intro j hj
    have : j ≤ 2 * k := by
      have := mem_range.mp hj
      omega
    exact (Nat.cast_sub (R := ℚ) this).symm
  have hC2' : ((2 * k).choose k : ℚ) =
      ∏ j ∈ range k, ((2 * k - j : ℕ) : ℚ) / (j + 1) := by
    rw [hC2]
    refine prod_congr rfl ?_
    intro j hj
    rw [hcast j hj]
  have hRHS : ((2 * k).choose k : ℚ) * ((-1 : ℚ) / 4) ^ k *
      ∏ j ∈ range k, (1 - (p : ℚ) / (2 * j + 1)) =
      ((-1 : ℚ) ^ k / (2 : ℚ) ^ k) *
        ∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (j + 1) := by
    rw [hPi, hC2', hneg]
    have hcast_prod :
        ∏ j ∈ range k, ((2 * k - j : ℕ) : ℚ) / (j + 1) =
          ∏ j ∈ range k, ((2 * k : ℚ) - j) / (j + 1) := by
      refine prod_congr rfl ?_
      intro j hj
      rw [← hcast j hj, Nat.cast_mul, Nat.cast_ofNat]
    rw [hcast_prod]
    have hmul :
        (∏ j ∈ range k, (2 * k - j : ℚ) / (j + 1)) *
            ((-1 : ℚ) ^ k / (4 : ℚ) ^ k) *
          ∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (2 * j + 1) =
        ((-1 : ℚ) ^ k / (4 : ℚ) ^ k) *
          ((∏ j ∈ range k, (2 * k - j : ℚ) / (j + 1)) *
            ∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (2 * j + 1)) := by
      ring
    rw [hmul, hswap, hpow, h4]
    field_simp
  rw [hLHS, hRHS]

/- Modular form of the product `Π_k` and the odd harmonic sums. -/

lemma odd_lt_p_of_mem_range {p k j : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) (hj : j ∈ range k) : 2 * j + 1 < p := by
  have hjk : j < k := mem_range.mp hj
  have hn : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd hp hodd
  have : 2 * j + 1 ≤ 2 * k - 1 := by omega
  have : 2 * k ≤ p - 1 := by
    have : k ≤ (p - 1) / 2 := hk
    have : 2 * k ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 this
    omega
  omega

lemma isUnit_odd_zmod {p e k j : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he : 0 < e) (hk : k ≤ (p - 1) / 2) (hj : j ∈ range k) :
    IsUnit ((2 * j + 1 : ℕ) : ZMod (p ^ e)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hlt : 2 * j + 1 < p := odd_lt_p_of_mem_range hp hodd hk hj
  have hpos : 0 < 2 * j + 1 := Nat.succ_pos _
  have hcop : Nat.Coprime (2 * j + 1) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt hpos hlt
  rwa [Nat.coprime_pow_right_iff he]

lemma isUnit_two_zmod {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((2 : ℕ) : ZMod (p ^ e)) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff he]
  exact coprime_two_odd_prime hp hodd

lemma isUnit_four_zmod {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((4 : ℕ) : ZMod (p ^ e)) := by
  have h2 := isUnit_two_zmod hp hodd he
  have : ((4 : ℕ) : ZMod (p ^ e)) = (2 : ℕ) * (2 : ℕ) := by norm_num
  rw [this]
  exact h2.mul h2

lemma isUnit_sixtyfour_zmod {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((64 : ℕ) : ZMod (p ^ e)) := by
  have h2 := isUnit_two_zmod hp hodd he
  have : ((64 : ℕ) : ZMod (p ^ e)) = ((2 : ℕ) : ZMod (p ^ e)) ^ 6 := by norm_num
  rw [this]
  exact h2.pow 6

/-- `Π_k = ∏_{j<k} (1 - p/(2j+1))` in `ZMod (p^e)`. -/
def PiMod (p e k : ℕ) : ZMod (p ^ e) :=
  ∏ j ∈ range k, (1 - (p : ZMod (p ^ e)) * ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹)

/-- Odd harmonic sum `O_k = ∑_{j<k} 1/(2j+1)` in `ZMod (p^e)`. -/
def oddHarmonic (p e k : ℕ) : ZMod (p ^ e) :=
  ∑ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹

lemma PiMod_eq_one_sub_p_oddHarmonic {p e k : ℕ}
    (_hp : p.Prime) (_hodd : p ≠ 2) (_he : 0 < e) (_he3 : e ≤ 3)
    (_hk : k ≤ (p - 1) / 2) :
    PiMod p e k = ∏ j ∈ range k,
      (1 - (p : ZMod (p ^ e)) * ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹) :=
  rfl

lemma p_pow_eq_zero_of_le {p e : ℕ} (_hp : p.Prime) (_he : 0 < e) :
    ((p : ℕ) : ZMod (p ^ e)) ^ e = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma p_sq_eq_zero_mod_p_sq {p : ℕ} (hp : p.Prime) :
    ((p : ℕ) : ZMod (p ^ 2)) ^ 2 = 0 :=
  p_pow_eq_zero_of_le hp (by omega)

lemma p_mul_p_eq_zero_mod_p_sq {p : ℕ} (hp : p.Prime) :
    ((p : ℕ) : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
  simpa [pow_two] using p_sq_eq_zero_mod_p_sq hp

lemma p_sq_smul_eq_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 2)) :
    ((p : ZMod (p ^ 2)) ^ 2) * x = 0 := by
  rw [p_sq_eq_zero_mod_p_sq hp, zero_mul]

lemma p_mul_p_smul_eq_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * x = 0 := by
  rw [p_mul_p_eq_zero_mod_p_sq hp, zero_mul]

/-- In `ZMod p²`, `∏ (1 - p a_j) = 1 - p ∑ a_j`. -/
lemma prod_one_sub_p {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ZMod (p ^ 2)) :
    ∏ j ∈ s, (1 - (p : ZMod (p ^ 2)) * f j) =
      1 - (p : ZMod (p ^ 2)) * ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, ih]
    have hp2 := p_mul_p_eq_zero_mod_p_sq hp
    calc
      (1 - (p : ZMod (p ^ 2)) * f a) *
          (1 - (p : ZMod (p ^ 2)) * ∑ j ∈ s, f j)
        = 1 - (p : ZMod (p ^ 2)) * ∑ j ∈ s, f j - (p : ZMod (p ^ 2)) * f a +
            (p : ZMod (p ^ 2)) * f a * ((p : ZMod (p ^ 2)) * ∑ j ∈ s, f j) := by
          ring
      _ = 1 - (p : ZMod (p ^ 2)) * ∑ j ∈ s, f j - (p : ZMod (p ^ 2)) * f a := by
          have : (p : ZMod (p ^ 2)) * f a * ((p : ZMod (p ^ 2)) * ∑ j ∈ s, f j) = 0 := by
            calc
              _ = ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * (f a * ∑ j ∈ s, f j) := by ring
              _ = 0 := by rw [hp2, zero_mul]
          rw [this, add_zero]
      _ = 1 - (p : ZMod (p ^ 2)) * (f a + ∑ j ∈ s, f j) := by ring

/-- `Π_k ≡ 1 - p O_k (mod p²)` since higher powers of `p` vanish. -/
lemma PiMod_mod_p_sq {p k : ℕ} (hp : p.Prime) (_hodd : p ≠ 2)
    (_hk : k ≤ (p - 1) / 2) :
    PiMod p 2 k = 1 - (p : ZMod (p ^ 2)) * oddHarmonic p 2 k := by
  simp only [PiMod, oddHarmonic]
  exact prod_one_sub_p hp (range k) _

lemma sq_mul_of_mul_eq_zero {R : Type*} [CommRing R] {q x : R} (h : q * q = 0) :
    (q * x) ^ 2 = 0 := by
  calc (q * x) ^ 2 = q * q * (x * x) := by ring
    _ = 0 := by rw [h, zero_mul]

lemma cube_mul_of_mul_eq_zero {R : Type*} [CommRing R] {q x : R} (h : q * q = 0) :
    (q * x) ^ 3 = 0 := by
  rw [pow_succ, sq_mul_of_mul_eq_zero h, zero_mul]

lemma one_sub_pow_three_of_sq {R : Type*} [CommRing R] {q x : R} (h : q * q = 0) :
    (1 - q * x) ^ 3 = 1 - 3 * q * x := by
  have h2 := sq_mul_of_mul_eq_zero (q := q) (x := x) h
  have h3 := cube_mul_of_mul_eq_zero (q := q) (x := x) h
  calc
    (1 - q * x) ^ 3 = 1 - 3 * (q * x) + 3 * (q * x) ^ 2 - (q * x) ^ 3 := by ring
    _ = 1 - 3 * q * x := by rw [h2, h3]; ring

lemma PiMod_pow_three_mod_p_sq {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    PiMod p 2 k ^ 3 =
      1 - 3 * (p : ZMod (p ^ 2)) * oddHarmonic p 2 k := by
  rw [PiMod_mod_p_sq hp hodd hk]
  exact one_sub_pow_three_of_sq (p_mul_p_eq_zero_mod_p_sq hp)

lemma one_sub_mul_one_add_of_sq {R : Type*} [CommRing R] {q x : R} (h : q * q = 0) :
    (1 - q * x) * (1 + q * x) = 1 := by
  calc
    (1 - q * x) * (1 + q * x) = 1 - (q * x) ^ 2 := by ring
    _ = 1 := by rw [sq_mul_of_mul_eq_zero h, sub_zero]

/-- If `a * b = 1` then `a⁻¹ = b` in `ZMod n`. -/
lemma inv_eq_of_mul_eq_one_zmod {n : ℕ} {a b : ZMod n} (h : a * b = 1) :
    a⁻¹ = b :=
  ZMod.inv_eq_of_mul_eq_one n a b h

lemma PiMod_inv_pow_three_mod_p_sq {p k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    (PiMod p 2 k)⁻¹ ^ 3 =
      1 + 3 * (p : ZMod (p ^ 2)) * oddHarmonic p 2 k := by
  rw [PiMod_mod_p_sq hp hodd hk]
  have hinv : (1 - (p : ZMod (p ^ 2)) * oddHarmonic p 2 k)⁻¹ =
      1 + (p : ZMod (p ^ 2)) * oddHarmonic p 2 k :=
    inv_eq_of_mul_eq_one_zmod
      (one_sub_mul_one_add_of_sq (p_mul_p_eq_zero_mod_p_sq hp))
  rw [hinv]
  have hneg : (-p : ZMod (p ^ 2)) * (-p : ZMod (p ^ 2)) = 0 := by
    have := p_mul_p_eq_zero_mod_p_sq hp
    convert this using 1 <;> ring
  convert one_sub_pow_three_of_sq (q := (-p : ZMod (p ^ 2)))
      (x := oddHarmonic p 2 k) hneg using 1
  · ring
  · ring

/- The ring `ZMod m [√-7]` and the generating function `P`. -/

open QuadraticAlgebra

abbrev Quad (m : ℕ) := QuadraticAlgebra (ZMod m) (-7) 0

lemma omega_sq (m : ℕ) : (omega : Quad m) * omega = -7 := by
  ext <;> simp [omega_mul_omega_eq_mk]

/-- `z₁ = (-47 + 45 √-7) / 128`. -/
def z1 (m : ℕ) : Quad m :=
  ⟨(-47 : ZMod m) * (128 : ZMod m)⁻¹, (45 : ZMod m) * (128 : ZMod m)⁻¹⟩

/-- `z₂ = (-47 - 45 √-7) / 128`. -/
def z2 (m : ℕ) : Quad m :=
  ⟨(-47 : ZMod m) * (128 : ZMod m)⁻¹, (-45 : ZMod m) * (128 : ZMod m)⁻¹⟩

lemma isUnit_128 {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit (128 : ZMod (p ^ e)) := by
  have h2 := isUnit_two_zmod hp hodd he
  have : (128 : ZMod (p ^ e)) = ((2 : ℕ) : ZMod (p ^ e)) ^ 7 := by norm_num
  rw [this]
  exact h2.pow 7

/-- `P_n(z) = ∑_{k=0}^n C(n,k)³ z^k`. -/
def Pgen {R : Type*} [Semiring R] (n : ℕ) (z : R) : R :=
  ∑ k ∈ range (n + 1), (((n.choose k : ℕ) : R) ^ 3) * z ^ k

lemma Pgen_zero {R : Type*} [Semiring R] (z : R) : Pgen 0 z = 1 := by
  simp [Pgen]

lemma Pgen_functional_aux {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (z : R) :
    (((n.choose k : ℕ) : R) ^ 3) * z ^ (n - k) =
      (((n.choose (n - k) : ℕ) : R) ^ 3) * z ^ (n - k) := by
  rw [Nat.choose_symm hk]

lemma z1_re (m : ℕ) : (z1 m).re = (-47 : ZMod m) * (128 : ZMod m)⁻¹ := rfl

lemma z1_im (m : ℕ) : (z1 m).im = (45 : ZMod m) * (128 : ZMod m)⁻¹ := rfl

lemma z2_re (m : ℕ) : (z2 m).re = (-47 : ZMod m) * (128 : ZMod m)⁻¹ := rfl

lemma z2_im (m : ℕ) : (z2 m).im = (-45 : ZMod m) * (128 : ZMod m)⁻¹ := rfl

lemma Pgen_functional_of_inv {R : Type*} [CommRing R] (n : ℕ) (z w : R)
    (hzw : z * w = 1) :
    z ^ n * Pgen n w = Pgen n z := by
  simp only [Pgen]
  rw [mul_sum]
  -- RHS: ∑_j C(n,j)³ z^j
  -- LHS: ∑_k C(n,k)³ z^n w^k = ∑_k C(n,k)³ z^{n-k} (z w)^k = ∑_k C(n,k)³ z^{n-k}
  have hterm : ∀ k ∈ range (n + 1),
      z ^ n * ((((n.choose k : ℕ) : R) ^ 3) * w ^ k) =
        (((n.choose k : ℕ) : R) ^ 3) * z ^ (n - k) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have : z ^ n * w ^ k = z ^ (n - k) := by
      calc
        z ^ n * w ^ k = z ^ (n - k + k) * w ^ k := by rw [Nat.sub_add_cancel hk']
        _ = z ^ (n - k) * z ^ k * w ^ k := by rw [pow_add]
        _ = z ^ (n - k) * (z * w) ^ k := by rw [mul_assoc, ← mul_pow]
        _ = z ^ (n - k) * 1 ^ k := by rw [hzw]
        _ = z ^ (n - k) := by simp
    calc
      z ^ n * ((((n.choose k : ℕ) : R) ^ 3) * w ^ k)
        = ((((n.choose k : ℕ) : R) ^ 3) * (z ^ n * w ^ k)) := by ring
      _ = ((((n.choose k : ℕ) : R) ^ 3) * z ^ (n - k)) := by rw [this]
  rw [sum_congr rfl hterm]
  -- ∑_{k=0}^n C(n,k)³ z^{n-k} = ∑_{k=0}^n C(n, n-k)³ z^{n-k} = reflected sum
  have hsymm : ∀ k ∈ range (n + 1),
      (((n.choose k : ℕ) : R) ^ 3) * z ^ (n - k) =
        (((n.choose (n - k) : ℕ) : R) ^ 3) * z ^ (n - k) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [Nat.choose_symm hk']
  rw [sum_congr rfl hsymm]
  rw [← sum_range_reflect (fun j => (((n.choose j : ℕ) : R) ^ 3) * z ^ j) (n + 1)]
  refine sum_congr rfl ?_
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hnk : n + 1 - 1 - k = n - k := by omega
  simp [hnk]

lemma z1_mul_z2 (m : ℕ) (h128 : IsUnit (128 : ZMod m)) :
    z1 m * z2 m = 1 := by
  apply QuadraticAlgebra.ext
  · have hinv : (128 : ZMod m) * (128 : ZMod m)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ h128
    simp [z1, z2]
    ring_nf
    have h128sq : (16384 : ZMod m) = 128 * 128 := by norm_num
    have : (16384 : ZMod m) * (128 : ZMod m)⁻¹ * (128 : ZMod m)⁻¹ = 1 := by
      rw [h128sq]
      calc
        (128 * 128 : ZMod m) * (128 : ZMod m)⁻¹ * (128 : ZMod m)⁻¹
          = 128 * (128 * (128 : ZMod m)⁻¹) * (128 : ZMod m)⁻¹ := by ring
        _ = 128 * 1 * (128 : ZMod m)⁻¹ := by rw [hinv]
        _ = 128 * (128 : ZMod m)⁻¹ := by ring
        _ = 1 := hinv
    convert this using 1
    ring
  · simp [z1, z2]
    ring

/-! ### Companion Lucas sequence and Binet formulae in `Quad`. -/

/-- Lucas companion sequence `V_n(5, 8)`. -/
def V : ℕ → ℤ
| 0 => 2
| 1 => 5
| n + 2 => 5 * V (n + 1) - 8 * V n

@[simp] lemma V_zero : V 0 = 2 := rfl
@[simp] lemma V_one : V 1 = 5 := rfl

lemma V_succ_succ (n : ℕ) : V (n + 2) = 5 * V (n + 1) - 8 * V n := by
  cases n with
  | zero => simp [V]
  | succ n => simp [V]

/-- `2α = 5 + ω` in `Quad m`. -/
def twoAlphaQ (m : ℕ) : Quad m := ⟨5, 1⟩

/-- `2β = 5 - ω` in `Quad m`. -/
def twoBetaQ (m : ℕ) : Quad m := ⟨5, -1⟩

lemma norm_omega (m : ℕ) : QuadraticAlgebra.norm (omega : Quad m) = 7 := by
  simp [QuadraticAlgebra.norm_def]

lemma isUnit_seven {p e : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) (he : 0 < e) :
    IsUnit ((7 : ℕ) : ZMod (p ^ e)) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff he]
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_seven,
    Nat.prime_dvd_prime_iff_eq Nat.prime_seven hp]
  exact hp7.symm

lemma isUnit_omega {p e : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) (he : 0 < e) :
    IsUnit (omega : Quad (p ^ e)) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_omega]
  exact_mod_cast isUnit_seven hp hp7 he

lemma two_mul_inv_two {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_two_zmod hp hodd he)

lemma twoAlphaQ_sq (m : ℕ) : twoAlphaQ m ^ 2 = 10 * twoAlphaQ m - 32 := by
  apply QuadraticAlgebra.ext <;> simp [twoAlphaQ, pow_two] <;> ring

lemma twoBetaQ_sq (m : ℕ) : twoBetaQ m ^ 2 = 10 * twoBetaQ m - 32 := by
  apply QuadraticAlgebra.ext <;> simp [twoBetaQ, pow_two] <;> ring

lemma twoAlphaQ_pow_succ_succ (m n : ℕ) :
    twoAlphaQ m ^ (n + 2) = 10 * twoAlphaQ m ^ (n + 1) - 32 * twoAlphaQ m ^ n := by
  have h := twoAlphaQ_sq m
  calc
    twoAlphaQ m ^ (n + 2) = twoAlphaQ m ^ 2 * twoAlphaQ m ^ n := by
      rw [← pow_add, Nat.add_comm]
    _ = (10 * twoAlphaQ m - 32) * twoAlphaQ m ^ n := by rw [h]
    _ = 10 * twoAlphaQ m ^ (n + 1) - 32 * twoAlphaQ m ^ n := by
      rw [sub_mul, mul_assoc, pow_succ]; ring

lemma twoBetaQ_pow_succ_succ (m n : ℕ) :
    twoBetaQ m ^ (n + 2) = 10 * twoBetaQ m ^ (n + 1) - 32 * twoBetaQ m ^ n := by
  have h := twoBetaQ_sq m
  calc
    twoBetaQ m ^ (n + 2) = twoBetaQ m ^ 2 * twoBetaQ m ^ n := by
      rw [← pow_add, Nat.add_comm]
    _ = (10 * twoBetaQ m - 32) * twoBetaQ m ^ n := by rw [h]
    _ = 10 * twoBetaQ m ^ (n + 1) - 32 * twoBetaQ m ^ n := by
      rw [sub_mul, mul_assoc, pow_succ]; ring

/-- Binet in `Quad`: `(5+ω)ⁿ - (5-ω)ⁿ = 2ⁿ a(n) ω`. -/
lemma binet_twoAlphaQ (m n : ℕ) :
    twoAlphaQ m ^ n - twoBetaQ m ^ n =
      ⟨0, (2 : ZMod m) ^ n * (a n : ZMod m)⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      apply QuadraticAlgebra.ext <;> simp [twoAlphaQ, twoBetaQ]
    | 1 =>
      apply QuadraticAlgebra.ext
      · simp [twoAlphaQ, twoBetaQ, a_one]
      · simp [twoAlphaQ, twoBetaQ, a_one]; norm_num
    | n + 2 =>
      have ih1 := ih (n + 1) (by omega)
      have ih0 := ih n (by omega)
      rw [twoAlphaQ_pow_succ_succ, twoBetaQ_pow_succ_succ]
      have : (10 * twoAlphaQ m ^ (n + 1) - 32 * twoAlphaQ m ^ n) -
          (10 * twoBetaQ m ^ (n + 1) - 32 * twoBetaQ m ^ n) =
          10 * (twoAlphaQ m ^ (n + 1) - twoBetaQ m ^ (n + 1)) -
          32 * (twoAlphaQ m ^ n - twoBetaQ m ^ n) := by ring
      rw [this, ih1, ih0]
      apply QuadraticAlgebra.ext
      · simp
      · simp [pow_succ, a_succ_succ]; ring

lemma C_mul_omega (m : ℕ) (c : ZMod m) :
    (⟨c, 0⟩ : Quad m) * (omega : Quad m) = ⟨0, c⟩ := by
  apply QuadraticAlgebra.ext <;> simp

lemma C_pow (m n : ℕ) (c : ZMod m) :
    (⟨c, 0⟩ : Quad m) ^ n = ⟨c ^ n, 0⟩ := by
  induction n with
  | zero =>
    apply QuadraticAlgebra.ext
    · simp
    · simp
  | succ n ih =>
    rw [pow_succ, ih]
    apply QuadraticAlgebra.ext
    · simp [pow_succ]
    · simp

lemma binet_twoAlphaQ_omega (m n : ℕ) :
    twoAlphaQ m ^ n - twoBetaQ m ^ n =
      (⟨(2 : ZMod m) ^ n * (a n : ZMod m), 0⟩ : Quad m) * (omega : Quad m) := by
  rw [binet_twoAlphaQ, C_mul_omega]

lemma twoAlphaQ_pow_four (m : ℕ) : twoAlphaQ m ^ 4 = ⟨-376, 360⟩ := by
  have h2 : twoAlphaQ m ^ 2 = ⟨18, 10⟩ := by
    apply QuadraticAlgebra.ext <;> simp [twoAlphaQ, pow_two] <;> ring
  have : twoAlphaQ m ^ 4 = (twoAlphaQ m ^ 2) ^ 2 := by ring
  rw [this, h2]
  apply QuadraticAlgebra.ext <;> simp [pow_two] <;> ring

lemma twoBetaQ_pow_four (m : ℕ) : twoBetaQ m ^ 4 = ⟨-376, -360⟩ := by
  have h2 : twoBetaQ m ^ 2 = ⟨18, -10⟩ := by
    apply QuadraticAlgebra.ext <;> simp [twoBetaQ, pow_two] <;> ring
  have : twoBetaQ m ^ 4 = (twoBetaQ m ^ 2) ^ 2 := by ring
  rw [this, h2]
  apply QuadraticAlgebra.ext <;> simp [pow_two] <;> ring

lemma isUnit_1024 {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit (1024 : ZMod (p ^ e)) := by
  have h2 := isUnit_two_zmod hp hodd he
  have : (1024 : ZMod (p ^ e)) = ((2 : ℕ) : ZMod (p ^ e)) ^ 10 := by norm_num
  rw [this]
  exact h2.pow 10

lemma z1_eq_twoAlpha_pow_four {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (1024 : Quad (p ^ e)) * z1 (p ^ e) = twoAlphaQ (p ^ e) ^ 4 := by
  have h128 := isUnit_128 hp hodd he
  rw [twoAlphaQ_pow_four]
  apply QuadraticAlgebra.ext
  · simp [z1]
    apply h128.mul_right_cancel
    rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
    norm_num
  · simp [z1]
    apply h128.mul_right_cancel
    rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
    norm_num

lemma z2_eq_twoBeta_pow_four {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (1024 : Quad (p ^ e)) * z2 (p ^ e) = twoBetaQ (p ^ e) ^ 4 := by
  have h128 := isUnit_128 hp hodd he
  rw [twoBetaQ_pow_four]
  apply QuadraticAlgebra.ext
  · simp [z2]
    apply h128.mul_right_cancel
    rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
    norm_num
  · simp [z2]
    apply h128.mul_right_cancel
    rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
    norm_num

lemma isUnit_omega_of {p e : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) (he : 0 < e) :
    IsUnit (omega : Quad (p ^ e)) :=
  isUnit_omega hp hp7 he

lemma twoAlphaQ_pow_mul_four (m k : ℕ) :
    twoAlphaQ m ^ (4 * k) = (twoAlphaQ m ^ 4) ^ k := by
  rw [← pow_mul, Nat.mul_comm]

lemma twoBetaQ_pow_mul_four (m k : ℕ) :
    twoBetaQ m ^ (4 * k) = (twoBetaQ m ^ 4) ^ k := by
  rw [← pow_mul, Nat.mul_comm]

/-- `z₁ᵏ - z₂ᵏ = a(4k) ω / 64ᵏ` after clearing the unit `1024ᵏ`. -/
lemma z1_pow_sub_z2_pow {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (1024 : Quad (p ^ e)) ^ k * (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) =
      (⟨(2 : ZMod (p ^ e)) ^ (4 * k) * (a (4 * k) : ZMod (p ^ e)), 0⟩) *
        (omega : Quad (p ^ e)) := by
  have h1 := z1_eq_twoAlpha_pow_four hp hodd he
  have h2 := z2_eq_twoBeta_pow_four hp hodd he
  have : (1024 : Quad (p ^ e)) ^ k * z1 (p ^ e) ^ k = twoAlphaQ (p ^ e) ^ (4 * k) := by
    rw [← mul_pow, h1, twoAlphaQ_pow_mul_four]
  have : (1024 : Quad (p ^ e)) ^ k * z2 (p ^ e) ^ k = twoBetaQ (p ^ e) ^ (4 * k) := by
    rw [← mul_pow, h2, twoBetaQ_pow_mul_four]
  calc
    (1024 : Quad (p ^ e)) ^ k * (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k)
      = (1024 : Quad (p ^ e)) ^ k * z1 (p ^ e) ^ k -
          (1024 : Quad (p ^ e)) ^ k * z2 (p ^ e) ^ k := by ring
    _ = twoAlphaQ (p ^ e) ^ (4 * k) - twoBetaQ (p ^ e) ^ (4 * k) := by
        rw [← mul_pow, h1, ← mul_pow, h2, twoAlphaQ_pow_mul_four, twoBetaQ_pow_mul_four]
    _ = _ := by
        simpa using binet_twoAlphaQ_omega (p ^ e) (4 * k)

lemma omega_sq_eq (m : ℕ) : (omega : Quad m) ^ 2 = -7 := by
  apply QuadraticAlgebra.ext <;> simp [pow_two]

instance charP_quad (p : ℕ) [CharP (ZMod p) p] : CharP (Quad p) p where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      have : ((n : Quad p).re) = 0 := by
        simpa using congrArg QuadraticAlgebra.re h
      have : (n : ZMod p) = 0 := by simpa using this
      exact (CharP.cast_eq_zero_iff (ZMod p) p n).1 this
    · intro h
      have : (n : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p n).2 h
      apply QuadraticAlgebra.ext <;> simp [this]

lemma freshman_quad {p : ℕ} [Fact p.Prime] (x y : Quad p) :
    (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_char (R := Quad p) (p := p) x y

lemma odd_prime_eq_two_mul_add_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    p = 2 * (p / 2) + 1 := by
  have : Odd p := odd_of_prime_ne_two Fact.out hp2
  obtain ⟨m, hm⟩ := this
  have hp' : p = 2 * m + 1 := by omega
  rw [hp', Nat.mul_add_div (by norm_num : 0 < 2)]
  simp

lemma omega_pow_p_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (omega : Quad p) ^ p =
      (⟨(-7 : ZMod p) ^ (p / 2), 0⟩ : Quad p) * (omega : Quad p) := by
  have hpow : (omega : Quad p) ^ p = (omega : Quad p) ^ (2 * (p / 2) + 1) :=
    congrArg (fun n => (omega : Quad p) ^ n) (odd_prime_eq_two_mul_add_one hp2)
  rw [hpow, pow_succ, pow_mul, omega_sq_eq]
  have hneg7 : (-7 : Quad p) = ⟨-7, 0⟩ := by
    apply QuadraticAlgebra.ext <;> simp
  rw [hneg7, C_pow]

lemma neg_seven_ne_zero {p : ℕ} [Fact p.Prime] (hp7 : p ≠ 7) :
    (-7 : ZMod p) ≠ 0 := by
  intro h
  have h7 : (7 : ZMod p) = 0 := by
    have := congrArg Neg.neg h
    simpa using this
  have : p ∣ 7 := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact_mod_cast h7
  exact hp7 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_seven).mp this)

lemma euler_neg_seven {p : ℕ} [Fact p.Prime] (hp7 : p ≠ 7) :
    ((-7 : ZMod p) ^ (p / 2)) = (legendreSym p (-7) : ZMod p) := by
  convert (legendreSym.eq_pow (p := p) (-7)).symm using 1
  simp

lemma twoAlphaQ_pow_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    twoAlphaQ p ^ p =
      ⟨5, (legendreSym p (-7) : ZMod p)⟩ := by
  have hfresh : twoAlphaQ p ^ p = (⟨5, 0⟩ : Quad p) ^ p + (omega : Quad p) ^ p := by
    have : twoAlphaQ p = (⟨5, 0⟩ : Quad p) + omega := by
      apply QuadraticAlgebra.ext <;> simp [twoAlphaQ]
    rw [this]
    simpa using freshman_quad (⟨5, 0⟩ : Quad p) omega
  have h5 : (⟨5, 0⟩ : Quad p) ^ p = ⟨5, 0⟩ := by
    rw [C_pow]
    have hcard : (5 : ZMod p) ^ p = 5 := by
      have h := FiniteField.pow_card (5 : ZMod p)
      have hc : Fintype.card (ZMod p) = p := ZMod.card p
      rwa [hc] at h
    simp [hcard]
  rw [hfresh, h5, omega_pow_p_eq hp2, euler_neg_seven hp7]
  apply QuadraticAlgebra.ext <;> simp

lemma twoBetaQ_pow_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    twoBetaQ p ^ p =
      ⟨5, -((legendreSym p (-7) : ZMod p))⟩ := by
  have hfresh : twoBetaQ p ^ p = (⟨5, 0⟩ : Quad p) ^ p + (-omega : Quad p) ^ p := by
    have : twoBetaQ p = (⟨5, 0⟩ : Quad p) + (-omega) := by
      apply QuadraticAlgebra.ext <;> simp [twoBetaQ]
    rw [this]
    simpa using freshman_quad (⟨5, 0⟩ : Quad p) (-omega)
  have h5 : (⟨5, 0⟩ : Quad p) ^ p = ⟨5, 0⟩ := by
    rw [C_pow]
    have hcard : (5 : ZMod p) ^ p = 5 := by
      have h := FiniteField.pow_card (5 : ZMod p)
      have hc : Fintype.card (ZMod p) = p := ZMod.card p
      rwa [hc] at h
    simp [hcard]
  have hneg : (-omega : Quad p) ^ p = -((omega : Quad p) ^ p) := by
    rw [neg_pow, Odd.neg_one_pow (odd_of_prime_ne_two Fact.out hp2), neg_one_mul]
  rw [hfresh, h5, hneg, omega_pow_p_eq hp2, euler_neg_seven hp7]
  apply QuadraticAlgebra.ext <;> simp

lemma twoAlphaQ_mul_twoBetaQ (m : ℕ) :
    twoAlphaQ m * twoBetaQ m = 32 := by
  apply QuadraticAlgebra.ext <;> simp [twoAlphaQ, twoBetaQ] <;> ring

lemma isUnit_two_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (2 : ZMod p) := by
  have h : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_num
  rw [h, ZMod.isUnit_iff_coprime]
  exact coprime_two_odd_prime Fact.out hp2

lemma isUnit_32 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (32 : ZMod p) := by
  have : (32 : ZMod p) = (2 : ZMod p) ^ 5 := by norm_num
  rw [this]; exact (isUnit_two_mod_p hp2).pow 5

lemma isUnit_twoAlphaQ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (twoAlphaQ p) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
  have : QuadraticAlgebra.norm (twoAlphaQ p) = 32 := by
    simp [QuadraticAlgebra.norm_def, twoAlphaQ]; ring
  rw [this]; exact_mod_cast isUnit_32 hp2

lemma isUnit_twoBetaQ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (twoBetaQ p) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
  have : QuadraticAlgebra.norm (twoBetaQ p) = 32 := by
    simp [QuadraticAlgebra.norm_def, twoBetaQ]; ring
  rw [this]; exact_mod_cast isUnit_32 hp2

lemma twoAlphaQ_mul_comm (m : ℕ) : twoBetaQ m * twoAlphaQ m = 32 := by
  rw [mul_comm, twoAlphaQ_mul_twoBetaQ]

/-- In the split case `(-7/p)=1`, one has `a(p-1) ≡ 0 (mod p)`. -/
lemma a_p_sub_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    (a (p - 1) : ZMod p) = 0 := by
  have hA := twoAlphaQ_pow_p hp2 hp7
  have hB := twoBetaQ_pow_p hp2 hp7
  rw [hsplit] at hA hB
  have hA' : twoAlphaQ p ^ p = twoAlphaQ p := by
    rw [hA]; apply QuadraticAlgebra.ext <;> simp [twoAlphaQ]
  have hB' : twoBetaQ p ^ p = twoBetaQ p := by
    rw [hB]; apply QuadraticAlgebra.ext <;> simp [twoBetaQ]
  have hpos : 1 ≤ p := (Nat.Prime.one_lt Fact.out).le
  have hA1 : twoAlphaQ p ^ (p - 1) = 1 := by
    have hmul : twoAlphaQ p ^ (p - 1) * twoAlphaQ p = 1 * twoAlphaQ p := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hA', one_mul]
    exact (isUnit_twoAlphaQ hp2).mul_right_cancel hmul
  have hB1 : twoBetaQ p ^ (p - 1) = 1 := by
    have hmul : twoBetaQ p ^ (p - 1) * twoBetaQ p = 1 * twoBetaQ p := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hB', one_mul]
    exact (isUnit_twoBetaQ hp2).mul_right_cancel hmul
  have hbin := binet_twoAlphaQ p (p - 1)
  rw [hA1, hB1, sub_self] at hbin
  have him : (2 : ZMod p) ^ (p - 1) * (a (p - 1) : ZMod p) = 0 := by
    have := congrArg QuadraticAlgebra.im hbin.symm
    simpa using this
  have h2u : IsUnit ((2 : ZMod p) ^ (p - 1)) := (isUnit_two_mod_p hp2).pow _
  exact (IsUnit.mul_right_eq_zero h2u).mp him

/-- In the inert case `(-7/p)=-1`, one has `a(p+1) ≡ 0 (mod p)`. -/
lemma a_p_add_one_of_inert {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hinert : legendreSym p (-7) = -1) :
    (a (p + 1) : ZMod p) = 0 := by
  have hA := twoAlphaQ_pow_p hp2 hp7
  have hB := twoBetaQ_pow_p hp2 hp7
  rw [hinert] at hA hB
  have hA' : twoAlphaQ p ^ p = twoBetaQ p := by
    rw [hA]; apply QuadraticAlgebra.ext <;> simp [twoBetaQ]
  have hB' : twoBetaQ p ^ p = twoAlphaQ p := by
    rw [hB]; apply QuadraticAlgebra.ext <;> simp [twoAlphaQ]
  have hA1 : twoAlphaQ p ^ (p + 1) = 32 := by
    rw [pow_succ, hA', twoAlphaQ_mul_comm]
  have hB1 : twoBetaQ p ^ (p + 1) = 32 := by
    rw [pow_succ, hB', twoAlphaQ_mul_twoBetaQ]
  have hbin := binet_twoAlphaQ p (p + 1)
  rw [hA1, hB1, sub_self] at hbin
  have him : (2 : ZMod p) ^ (p + 1) * (a (p + 1) : ZMod p) = 0 := by
    have := congrArg QuadraticAlgebra.im hbin.symm
    simpa using this
  have h2u : IsUnit ((2 : ZMod p) ^ (p + 1)) := (isUnit_two_mod_p hp2).pow _
  exact (IsUnit.mul_right_eq_zero h2u).mp him

/-! ### Transfer of the half-index identity to `ZMod`. -/

lemma factorial_cast_prod (R : Type*) [CommRing R] (k : ℕ) :
    (k.factorial : R) = ∏ j ∈ range k, ((j + 1 : ℕ) : R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, factorial_succ, Nat.cast_mul, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma descFactorial_cast_prod (R : Type*) [CommRing R] (n k : ℕ) (hk : k ≤ n) :
    (n.descFactorial k : R) = ∏ j ∈ range k, ((n : R) - (j : R)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : k ≤ n := le_trans (Nat.le_succ k) hk
    rw [prod_range_succ, Nat.descFactorial_succ, Nat.cast_mul, ih hle]
    have : ((n - k : ℕ) : R) = (n : R) - (k : R) := Nat.cast_sub hle
    rw [this]
    ring

lemma isUnit_succ_of_lt_p {p e j : ℕ} (hp : p.Prime) (he : 0 < e) (hlt : j + 1 < p) :
    IsUnit (((j + 1 : ℕ) : ZMod (p ^ e))) := by
  rw [ZMod.isUnit_iff_coprime]
  have hpos : 0 < j + 1 := Nat.succ_pos _
  have hcop : Nat.Coprime (j + 1) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt hpos hlt
  rwa [Nat.coprime_pow_right_iff he]

lemma isUnit_factorial_of_lt_p {p e k : ℕ} (hp : p.Prime) (he : 0 < e) (hk : k < p) :
    IsUnit ((k.factorial : ℕ) : ZMod (p ^ e)) := by
  rw [factorial_cast_prod]
  refine IsUnit.prod_iff.mpr ?_
  intro j hj
  have : j + 1 < p := by
    have := mem_range.mp hj
    omega
  exact isUnit_succ_of_lt_p hp he this

lemma n_sub_j_zmod {p e j : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hj : j ≤ (p - 1) / 2) :
    ((((p - 1) / 2 : ℕ) : ZMod (p ^ e)) - (j : ZMod (p ^ e))) =
      ((p : ZMod (p ^ e)) - (2 * j + 1 : ℕ)) * (2 : ZMod (p ^ e))⁻¹ := by
  have h2u := isUnit_two_zmod hp hodd he
  have hn2 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd hp hodd
  have hinv : (2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h2u
  apply h2u.mul_left_cancel
  calc
    (2 : ZMod (p ^ e)) * ((((p - 1) / 2 : ℕ) : ZMod (p ^ e)) - (j : ZMod (p ^ e)))
        = (2 : ZMod (p ^ e)) * ((p - 1) / 2 : ℕ) -
            (2 : ZMod (p ^ e)) * (j : ZMod (p ^ e)) := by ring
    _ = ((2 * ((p - 1) / 2) : ℕ) : ZMod (p ^ e)) - ((2 * j : ℕ) : ZMod (p ^ e)) := by
          push_cast; rfl
    _ = ((p - 1 : ℕ) : ZMod (p ^ e)) - ((2 * j : ℕ) : ZMod (p ^ e)) := by
          rw [hn2]
    _ = ((p : ZMod (p ^ e)) - 1) - (2 * j : ℕ) := by
          rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    _ = (p : ZMod (p ^ e)) - (2 * j + 1 : ℕ) := by
          push_cast; ring
    _ = ((p : ZMod (p ^ e)) - (2 * j + 1 : ℕ)) *
          ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹) := by
          rw [hinv]; ring
    _ = (2 : ZMod (p ^ e)) * (((p : ZMod (p ^ e)) - (2 * j + 1 : ℕ)) *
          (2 : ZMod (p ^ e))⁻¹) := by
          ring

lemma choose_eq_prod_zmod {p e n k : ℕ} (hp : p.Prime) (he : 0 < e)
    (hk : k ≤ n) (hkp : k < p) :
    ((n.choose k : ℕ) : ZMod (p ^ e)) =
      ∏ j ∈ range k, (((n : ZMod (p ^ e)) - (j : ZMod (p ^ e))) *
        ((j + 1 : ℕ) : ZMod (p ^ e))⁻¹) := by
  have hunit : ∀ j ∈ range k, IsUnit (((j + 1 : ℕ) : ZMod (p ^ e))) := by
    intro j hj
    have : j + 1 < p := by
      have := mem_range.mp hj
      omega
    exact isUnit_succ_of_lt_p hp he this
  have hmul : n.choose k * k.factorial = n.descFactorial k := by
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.div_mul_cancel]
    exact Nat.factorial_dvd_descFactorial n k
  have hcast :
      ((n.choose k : ℕ) : ZMod (p ^ e)) * ((k.factorial : ℕ) : ZMod (p ^ e)) =
        ((n.descFactorial k : ℕ) : ZMod (p ^ e)) := by
    rw [← Nat.cast_mul, hmul]
  have hfu : IsUnit ((k.factorial : ℕ) : ZMod (p ^ e)) :=
    isUnit_factorial_of_lt_p hp he hkp
  apply hfu.mul_right_cancel
  rw [hcast, descFactorial_cast_prod (ZMod (p ^ e)) n k hk,
    factorial_cast_prod (ZMod (p ^ e)) k]
  have :
      (∏ j ∈ range k, (((n : ZMod (p ^ e)) - (j : ZMod (p ^ e))) *
          ((j + 1 : ℕ) : ZMod (p ^ e))⁻¹)) *
        (∏ j ∈ range k, ((j + 1 : ℕ) : ZMod (p ^ e))) =
      ∏ j ∈ range k, ((n : ZMod (p ^ e)) - (j : ZMod (p ^ e))) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl ?_
    intro j hj
    rw [mul_assoc, ZMod.inv_mul_of_unit _ (hunit j hj), mul_one]
  exact this.symm

/-- Integer form of the half-index identity, ready to cast. -/
lemma choose_half_integer (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    (((p - 1) / 2).choose k : ℚ) * (4 : ℚ) ^ k *
        ∏ j ∈ range k, (2 * j + 1 : ℚ) =
      ((2 * k).choose k : ℚ) * ((-1 : ℚ) ^ k) *
        ∏ j ∈ range k, ((2 * j + 1 : ℚ) - (p : ℚ)) := by
  have hQ := choose_half_central_identity p k hp hodd hk
  have hPi := prod_one_sub_p_odd p k
  have h4 : ((-1 : ℚ) / 4) ^ k = (-1 : ℚ) ^ k / (4 : ℚ) ^ k := div_pow _ _ _
  have hden : ∏ j ∈ range k, (2 * j + 1 : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    exact_mod_cast Nat.succ_ne_zero (2 * j)
  have h4ne : (4 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    (((p - 1) / 2).choose k : ℚ) * (4 : ℚ) ^ k * ∏ j ∈ range k, (2 * j + 1 : ℚ)
        = ((2 * k).choose k : ℚ) * ((-1 : ℚ) / 4) ^ k *
            (∏ j ∈ range k, (1 - (p : ℚ) / (2 * j + 1))) *
            (4 : ℚ) ^ k * ∏ j ∈ range k, (2 * j + 1 : ℚ) := by
          rw [hQ]
    _ = ((2 * k).choose k : ℚ) * ((-1 : ℚ) ^ k / (4 : ℚ) ^ k) *
            (∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) / (2 * j + 1)) *
            (4 : ℚ) ^ k * ∏ j ∈ range k, (2 * j + 1 : ℚ) := by
          rw [h4, hPi]
    _ = ((2 * k).choose k : ℚ) * ((-1 : ℚ) ^ k) *
            ∏ j ∈ range k, ((2 * j + 1 : ℚ) - p) := by
          rw [prod_div_distrib]
          field_simp [hden, h4ne]

lemma choose_half_int (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    (((p - 1) / 2).choose k : ℤ) * (4 : ℤ) ^ k *
        ∏ j ∈ range k, (2 * j + 1 : ℤ) =
      ((2 * k).choose k : ℤ) * ((-1 : ℤ) ^ k) *
        ∏ j ∈ range k, ((2 * j + 1 : ℤ) - (p : ℤ)) := by
  have hQ := choose_half_integer p k hp hodd hk
  have hL : (((p - 1) / 2).choose k : ℚ) * (4 : ℚ) ^ k *
      ∏ j ∈ range k, (2 * j + 1 : ℚ) =
      ((((p - 1) / 2).choose k : ℤ) * (4 : ℤ) ^ k *
        ∏ j ∈ range k, (2 * j + 1 : ℤ) : ℚ) := by
    simp
  have hR : ((2 * k).choose k : ℚ) * ((-1 : ℚ) ^ k) *
      ∏ j ∈ range k, ((2 * j + 1 : ℚ) - (p : ℚ)) =
      ((((2 * k).choose k : ℤ) * ((-1 : ℤ) ^ k) *
        ∏ j ∈ range k, ((2 * j + 1 : ℤ) - (p : ℤ)) : ℚ)) := by
    simp
  exact_mod_cast (hL.symm.trans (hQ.trans hR))

lemma choose_half_zmod {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hk : k ≤ (p - 1) / 2) :
    ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) =
      (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
        ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
          PiMod p e k := by
  have hZ := choose_half_int p k hp hodd hk
  have h4u := isUnit_four_zmod hp hodd he
  have h2u := isUnit_two_zmod hp hodd he
  have huodd : ∀ j ∈ range k, IsUnit (((2 * j + 1 : ℕ) : ZMod (p ^ e))) := by
    intro j hj; exact isUnit_odd_zmod hp hodd he hk hj
  -- Cast the integer identity.
  have hcast :
      ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) * (4 : ZMod (p ^ e)) ^ k *
          ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e)) =
        (((2 * k).choose k : ℕ) : ZMod (p ^ e)) * ((-1 : ZMod (p ^ e)) ^ k) *
          ∏ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e))) := by
    have := congrArg (fun z : ℤ => (z : ZMod (p ^ e))) hZ
    simpa [Int.cast_prod, Int.cast_pow, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_neg, Int.cast_one] using this
  -- Multiply both sides by the inverses `4^{-k}` and `∏ (2j+1)^{-1}`.
  have h4pow : IsUnit ((4 : ZMod (p ^ e)) ^ k) := h4u.pow k
  have hoddprod : IsUnit (∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))) :=
    IsUnit.prod_iff.mpr huodd
  have hPi : PiMod p e k =
      ∏ j ∈ range k,
        (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e))) *
          ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹ := by
    simp only [PiMod]
    refine prod_congr rfl ?_
    intro j hj
    have hu := huodd j hj
    apply hu.mul_right_cancel
    calc
      (1 - (p : ZMod (p ^ e)) * ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹) *
          ((2 * j + 1 : ℕ) : ZMod (p ^ e))
          = ((2 * j + 1 : ℕ) : ZMod (p ^ e)) -
              (p : ZMod (p ^ e)) * ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹ *
                ((2 * j + 1 : ℕ) : ZMod (p ^ e)) := by ring
      _ = ((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e)) := by
            rw [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
      _ = (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e))) *
            ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹ *
            ((2 * j + 1 : ℕ) : ZMod (p ^ e)) := by
            rw [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
  have hneg4 : ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k =
      (-1 : ZMod (p ^ e)) ^ k * ((4 : ZMod (p ^ e))⁻¹) ^ k := by
    rw [mul_pow]
  have hinv4k : ((4 : ZMod (p ^ e))⁻¹) ^ k * (4 : ZMod (p ^ e)) ^ k = 1 := by
    rw [← mul_pow]
    have : (4 : ZMod (p ^ e))⁻¹ * (4 : ZMod (p ^ e)) = 1 :=
      ZMod.inv_mul_of_unit _ h4u
    rw [this, one_pow]
  have hinvodd :
      (∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹) *
        (∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))) = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun j hj => ZMod.inv_mul_of_unit _ (huodd j hj)
  have hRHS :
      (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
          ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
          PiMod p e k *
          (4 : ZMod (p ^ e)) ^ k *
          ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e)) =
        (((2 * k).choose k : ℕ) : ZMod (p ^ e)) * ((-1 : ZMod (p ^ e)) ^ k) *
          ∏ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e))) := by
    rw [hPi, hneg4]
    simp only [prod_mul_distrib]
    calc
      (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
            ((-1 : ZMod (p ^ e)) ^ k * ((4 : ZMod (p ^ e))⁻¹) ^ k) *
            ((∏ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e)))) *
              ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹) *
            (4 : ZMod (p ^ e)) ^ k *
            ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))
          = (((2 * k).choose k : ℕ) : ZMod (p ^ e)) * ((-1 : ZMod (p ^ e)) ^ k) *
              (∏ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e)))) *
              (((4 : ZMod (p ^ e))⁻¹) ^ k * (4 : ZMod (p ^ e)) ^ k) *
              ((∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))⁻¹) *
                ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))) := by
            ring
      _ = (((2 * k).choose k : ℕ) : ZMod (p ^ e)) * ((-1 : ZMod (p ^ e)) ^ k) *
            ∏ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod (p ^ e)) - (p : ZMod (p ^ e))) := by
            rw [hinv4k, hinvodd]; ring
  -- We have `LHS * 4^k * odd = RHS * 4^k * odd`. Cancel the units.
  have hmul : ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) *
        (4 : ZMod (p ^ e)) ^ k *
        ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e)) =
      (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
        ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
        PiMod p e k *
        (4 : ZMod (p ^ e)) ^ k *
        ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e)) :=
    hcast.trans hRHS.symm
  -- Multiply both sides on the right by the two inverses.
  have := congrArg
    (fun z : ZMod (p ^ e) =>
      z * ((4 : ZMod (p ^ e)) ^ k)⁻¹ *
        (∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e)))⁻¹) hmul
  -- Simplify using `IsUnit` inverses.
  have h4inv : (4 : ZMod (p ^ e)) ^ k * ((4 : ZMod (p ^ e)) ^ k)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h4pow
  have hoddinv :
      (∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))) *
        (∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hoddprod
  -- Cancel the units `4^k` and `∏(2j+1)` from `hmul`.
  have hU : IsUnit ((4 : ZMod (p ^ e)) ^ k *
      ∏ j ∈ range k, ((2 * j + 1 : ℕ) : ZMod (p ^ e))) := h4pow.mul hoddprod
  apply hU.mul_right_cancel
  convert hmul using 1 <;> ring

/-! ### Rewritten summands and the first-order expansion. -/

lemma isUnit_neg64 {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((-64 : ZMod (p ^ e))) := by
  have h2 := isUnit_two_zmod hp hodd he
  have : (-64 : ZMod (p ^ e)) = -((2 : ZMod (p ^ e)) ^ 6) := by norm_num
  rw [this]
  exact (h2.pow 6).neg

lemma isUnit_neg4096_zmod {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((-4096 : ZMod (p ^ e))) := by
  have := isUnit_neg_4096 hp hodd he
  -- `(-4096 : ℤ)` vs `(-4096 : ZMod)`
  simpa using this

lemma geom_one_sub_p {p e : ℕ} (hp : p.Prime) (he : 0 < e) (x : ZMod (p ^ e)) :
    (1 - (p : ZMod (p ^ e)) * x) *
      ∑ i ∈ range e, ((p : ZMod (p ^ e)) * x) ^ i = 1 := by
  have hpe : ((p : ZMod (p ^ e)) ^ e) = 0 := p_pow_eq_zero_of_le hp he
  have hpow : ((p : ZMod (p ^ e)) * x) ^ e = 0 := by
    rw [mul_pow, hpe, zero_mul]
  have := geom_sum_mul_neg ((p : ZMod (p ^ e)) * x) e
  -- `geom_sum_mul_neg a n : (∑ a^i) * (1 - a) = 1 - a^n`
  rw [mul_comm]
  simpa [hpow] using this

lemma isUnit_one_sub_p {p e : ℕ} (hp : p.Prime) (he : 0 < e) (x : ZMod (p ^ e)) :
    IsUnit (1 - (p : ZMod (p ^ e)) * x) := by
  refine ⟨⟨1 - (p : ZMod (p ^ e)) * x,
    ∑ i ∈ range e, ((p : ZMod (p ^ e)) * x) ^ i,
    geom_one_sub_p hp he x, ?_⟩, rfl⟩
  rw [mul_comm]
  exact geom_one_sub_p hp he x

lemma isUnit_PiMod {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hk : k ≤ (p - 1) / 2) : IsUnit (PiMod p e k) := by
  refine IsUnit.prod_iff.mpr ?_
  intro j hj
  exact isUnit_one_sub_p hp he _

lemma geom_sum_mul_neg_comm {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    (1 - a) * ∑ i ∈ range n, a ^ i = 1 - a ^ n := by
  rw [mul_comm]
  exact geom_sum_mul_neg a n

/-- The linear combination `T` appearing in the first-order expansion. -/
def Tsum (p e : ℕ) : ZMod (p ^ e) :=
  ∑ k ∈ range (((p - 1) / 2) + 1),
    ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
      (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹

/-- The odd-harmonic weighted companion `U`. -/
def Usum (p e : ℕ) : ZMod (p ^ e) :=
  ∑ k ∈ range (((p - 1) / 2) + 1),
    ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
      oddHarmonic p e k *
      (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹

lemma half_succ_eq {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (p + 1) / 2 = (p - 1) / 2 + 1 := by
  have hodd' : Odd p := odd_of_prime_ne_two hp hodd
  obtain ⟨m, hm⟩ := hodd'
  have hp' : p = 2 * m + 1 := by omega
  have h1 : (p + 1) / 2 = m + 1 := by
    rw [hp']; omega
  have h2 : (p - 1) / 2 = m := by
    rw [hp']; omega
  omega

lemma isUnit_neg_four {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((-4 : ZMod (p ^ e))) := by
  have h4 := isUnit_four_zmod hp hodd he
  have : (-4 : ZMod (p ^ e)) = -((4 : ℕ) : ZMod (p ^ e)) := by norm_num
  rw [this]
  exact h4.neg

lemma neg4096_eq_neg64_mul_64 (R : Type*) [CommRing R] :
    (-4096 : R) = (-64 : R) * (64 : R) := by
  norm_num

lemma pow_neg4096_eq {R : Type*} [CommRing R] (k : ℕ) :
    (-4096 : R) ^ k = (-64 : R) ^ k * (64 : R) ^ k := by
  rw [neg4096_eq_neg64_mul_64, mul_pow]

lemma neg4_pow_three (R : Type*) [CommRing R] (k : ℕ) :
    (-4 : R) ^ (3 * k) = (-64 : R) ^ k := by
  have h : (-4 : R) ^ 3 = (-64 : R) := by norm_num
  rw [pow_mul, h]

/-- Central binomial rewritten via the half-index identity. -/
lemma choose_two_k_eq {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hk : k ≤ (p - 1) / 2) :
    (((2 * k).choose k : ℕ) : ZMod (p ^ e)) =
      ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) *
        ((-4 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹ := by
  have h := choose_half_zmod (p := p) (e := e) (k := k) hp hodd he hk
  have h4u := isUnit_four_zmod hp hodd he
  have hPi := isUnit_PiMod hp hodd he hk
  have hneg4 : ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
      ((-4 : ZMod (p ^ e)) ^ k) = 1 := by
    have hmul : (-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹ * (-4 : ZMod (p ^ e)) = 1 := by
      have : (-4 : ZMod (p ^ e)) = -((4 : ZMod (p ^ e))) := by norm_num
      rw [this]
      calc
        (-1) * (4 : ZMod (p ^ e))⁻¹ * -((4 : ZMod (p ^ e)))
          = (4 : ZMod (p ^ e))⁻¹ * (4 : ZMod (p ^ e)) := by ring
        _ = 1 := ZMod.inv_mul_of_unit _ h4u
    rw [← mul_pow, hmul, one_pow]
  have hPiInv : PiMod p e k * (PiMod p e k)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hPi
  -- Multiply the half-index identity by `(-4)^k * PiMod⁻¹`.
  have hmul :=
    congrArg (fun z : ZMod (p ^ e) =>
      z * ((-4 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹) h
  -- RHS simplifies to the central binomial.
  have hRHS :
      (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
          ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
          PiMod p e k *
          ((-4 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹ =
        (((2 * k).choose k : ℕ) : ZMod (p ^ e)) := by
    calc
      _ = (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
            (((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
              ((-4 : ZMod (p ^ e)) ^ k)) *
            (PiMod p e k * (PiMod p e k)⁻¹) := by ring
      _ = (((2 * k).choose k : ℕ) : ZMod (p ^ e)) := by
            rw [hneg4, hPiInv, mul_one, mul_one]
  have hLHS :
      ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) *
          ((-4 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹ =
        (((2 * k).choose k : ℕ) : ZMod (p ^ e)) *
          ((-1 : ZMod (p ^ e)) * (4 : ZMod (p ^ e))⁻¹) ^ k *
          PiMod p e k *
          ((-4 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹ := by
    simpa using hmul
  exact (hLHS.trans hRHS).symm

/-- Inverse of a product of units in `ZMod`. -/
lemma zmod_inv_mul {n : ℕ} {a b : ZMod n} (ha : IsUnit a) (hb : IsUnit b) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply inv_eq_of_mul_eq_one_zmod
  calc
    (a * b) * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one]

/-- The original summand equals `C(n,k)³ Π⁻³ a(4k) 64⁻ᵏ`. -/
lemma summand_eq_rewritten {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hk : k ≤ (p - 1) / 2) :
    summand p e k =
      ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
        (PiMod p e k)⁻¹ ^ 3 *
        (a (4 * k) : ZMod (p ^ e)) *
        ((64 : ZMod (p ^ e)) ^ k)⁻¹ := by
  simp only [summand]
  have hC := choose_two_k_eq hp hodd he hk
  have h64 := isUnit_sixtyfour_zmod hp hodd he
  have hneg64 := isUnit_neg64 hp hodd he
  have h64pow : IsUnit ((64 : ZMod (p ^ e)) ^ k) := h64.pow k
  have hneg64pow : IsUnit ((-64 : ZMod (p ^ e)) ^ k) := hneg64.pow k
  have hC3 :
      (((2 * k).choose k : ℕ) : ZMod (p ^ e)) ^ 3 =
        ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
          ((-64 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹ ^ 3 := by
    rw [hC, mul_pow, mul_pow, ← pow_mul, mul_comm k, neg4_pow_three]
    try ring
  have hden : ((-4096 : ℤ) : ZMod (p ^ e)) = (-4096 : ZMod (p ^ e)) := by simp
  rw [hC3, hden, pow_neg4096_eq, zmod_inv_mul hneg64pow h64pow]
  have hcancel : ((-64 : ZMod (p ^ e)) ^ k) * ((-64 : ZMod (p ^ e)) ^ k)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hneg64pow
  calc
    (a (4 * k) : ZMod (p ^ e)) *
        (((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
          ((-64 : ZMod (p ^ e)) ^ k) * (PiMod p e k)⁻¹ ^ 3) *
        (((-64 : ZMod (p ^ e)) ^ k)⁻¹ * ((64 : ZMod (p ^ e)) ^ k)⁻¹)
      = ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
          (PiMod p e k)⁻¹ ^ 3 *
          (a (4 * k) : ZMod (p ^ e)) *
          ((64 : ZMod (p ^ e)) ^ k)⁻¹ *
          (((-64 : ZMod (p ^ e)) ^ k) * ((-64 : ZMod (p ^ e)) ^ k)⁻¹) := by ring
    _ = ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
          (PiMod p e k)⁻¹ ^ 3 *
          (a (4 * k) : ZMod (p ^ e)) *
          ((64 : ZMod (p ^ e)) ^ k)⁻¹ := by
        rw [hcancel, mul_one]

lemma Ssum_eq_T_add_three_p_U {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    Ssum p 2 = Tsum p 2 + 3 * (p : ZMod (p ^ 2)) * Usum p 2 := by
  have hhalf := half_succ_eq hp hodd
  have hsmall := Ssum_eq_sum_small (p := p) (n := 2) hp hodd (by omega) (by omega)
  rw [hsmall, hhalf]
  simp only [Tsum, Usum]
  have hterm : ∀ k ∈ range (((p - 1) / 2) + 1),
      summand p 2 k =
        ((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ 2)) ^ 3 *
          (a (4 * k) : ZMod (p ^ 2)) * ((64 : ZMod (p ^ 2)) ^ k)⁻¹ +
        3 * (p : ZMod (p ^ 2)) *
          (((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ 2)) ^ 3 *
            oddHarmonic p 2 k *
            (a (4 * k) : ZMod (p ^ 2)) * ((64 : ZMod (p ^ 2)) ^ k)⁻¹) := by
    intro k hk
    have hk' : k ≤ (p - 1) / 2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hrew := summand_eq_rewritten (p := p) (e := 2) (k := k) hp hodd (by omega) hk'
    have hPi := PiMod_inv_pow_three_mod_p_sq hp hodd hk'
    rw [hrew, hPi]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib]
  simp [mul_sum]

/-! ### Relating `T` to the generating function `P` and first-order vanishing. -/

lemma isUnit_1024_mod {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    IsUnit ((1024 : ZMod (p ^ e))) :=
  isUnit_1024 hp hodd he

lemma two_pow_ten_eq_1024 (R : Type*) [CommRing R] : (2 : R) ^ 10 = 1024 := by
  norm_num

lemma two_pow_six_eq_64 (R : Type*) [CommRing R] : (2 : R) ^ 6 = 64 := by
  norm_num

lemma pow_1024_div_pow_64 {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    ((1024 : ZMod (p ^ e)) ^ k) * ((64 : ZMod (p ^ e)) ^ k)⁻¹ =
      (2 : ZMod (p ^ e)) ^ (4 * k) := by
  have h2 := isUnit_two_zmod hp hodd he
  have h1024eq : (1024 : ZMod (p ^ e)) = (2 : ZMod (p ^ e)) ^ 10 :=
    (two_pow_ten_eq_1024 _).symm
  have h64eq : (64 : ZMod (p ^ e)) = (2 : ZMod (p ^ e)) ^ 6 :=
    (two_pow_six_eq_64 _).symm
  rw [h1024eq, h64eq, ← pow_mul, ← pow_mul]
  have h2u : IsUnit ((2 : ZMod (p ^ e)) ^ (6 * k)) := h2.pow _
  apply h2u.mul_right_cancel
  rw [mul_assoc, ZMod.inv_mul_of_unit _ h2u, mul_one, ← pow_add]
  congr 1
  omega

lemma p_ne_seven_of_ge {p : ℕ} (hp : p.Prime) (hge : 29 ≤ p) : p ≠ 7 := by
  omega

lemma legendre_seven_of_mod (r : ℕ) (hr : r < 7) :
    legendreSym 7 (r : ℤ) = 1 ↔ r = 1 ∨ r = 2 ∨ r = 4 := by
  interval_cases r <;> decide

lemma split_iff_mod_seven {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    legendreSym p (-7) = 1 ↔ p % 7 ∈ ({1, 2, 4} : Set ℕ) := by
  have h := legendre_neg_seven_eq_legendre_self p hp2 hp7
  have hmod : legendreSym 7 (p : ℤ) = legendreSym 7 ((p % 7 : ℕ) : ℤ) := by
    apply legendreSym.mod
  have hr : p % 7 < 7 := Nat.mod_lt _ (by omega)
  constructor
  · intro hs
    have h1 : legendreSym 7 ((p % 7 : ℕ) : ℤ) = 1 := by
      rw [← hmod, ← h]; exact hs
    have := (legendre_seven_of_mod (p % 7) hr).mp h1
    simp [this]
  · intro hs
    simp at hs
    have : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
      rcases hs with h' | h' | h' <;> simp [h']
    have h1 : legendreSym 7 ((p % 7 : ℕ) : ℤ) = 1 :=
      (legendre_seven_of_mod (p % 7) hr).mpr this
    rw [h, hmod, h1]

lemma twoAlphaQ_pow_p_sub_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    twoAlphaQ p ^ (p - 1) = 1 := by
  have hA := twoAlphaQ_pow_p hp2 hp7
  rw [hsplit] at hA
  have hA' : twoAlphaQ p ^ p = twoAlphaQ p := by
    rw [hA]; apply QuadraticAlgebra.ext <;> simp [twoAlphaQ]
  have hpos : 1 ≤ p := (Nat.Prime.one_lt Fact.out).le
  have hmul : twoAlphaQ p ^ (p - 1) * twoAlphaQ p = 1 * twoAlphaQ p := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hA', one_mul]
  exact (isUnit_twoAlphaQ hp2).mul_right_cancel hmul

lemma twoBetaQ_pow_p_sub_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    twoBetaQ p ^ (p - 1) = 1 := by
  have hB := twoBetaQ_pow_p hp2 hp7
  rw [hsplit] at hB
  have hB' : twoBetaQ p ^ p = twoBetaQ p := by
    rw [hB]; apply QuadraticAlgebra.ext <;> simp [twoBetaQ]
  have hpos : 1 ≤ p := (Nat.Prime.one_lt Fact.out).le
  have hmul : twoBetaQ p ^ (p - 1) * twoBetaQ p = 1 * twoBetaQ p := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hB', one_mul]
  exact (isUnit_twoBetaQ hp2).mul_right_cancel hmul

lemma fermat_two_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1) = 1 := by
  have h2u := isUnit_two_mod_p hp2
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have := FiniteField.pow_card_sub_one_eq_one (2 : ZMod p) (by
    intro h
    have : (2 : ZMod p) = 0 := h
    have h2 : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_num
    rw [h2, ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this))
  rwa [hcard] at this

lemma z1_pow_n_eq_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    z1 p ^ ((p - 1) / 2) = 1 := by
  have hA := twoAlphaQ_pow_p_sub_one_of_split hp2 hp7 hsplit
  have h1024 := z1_eq_twoAlpha_pow_four (p := p) (e := 1) Fact.out hp2 (by omega)
  -- Work in `Quad p`. Note `p^1` vs `p` may have different casts; we stay with `Quad p`.
  -- `1024 * z1 = twoAlpha^4` in `Quad (p^1)`. Transfer via the ring iso if needed.
  -- Directly: `z1 = twoAlpha^4 / 1024` in `Quad p` by the same computation.
  have h128 : IsUnit (128 : ZMod p) := by
    have h2 := isUnit_two_mod_p hp2
    have : (128 : ZMod p) = (2 : ZMod p) ^ 7 := by norm_num
    rw [this]; exact h2.pow 7
  have hz : (1024 : Quad p) * z1 p = twoAlphaQ p ^ 4 := by
    have hfour := twoAlphaQ_pow_four p
    rw [hfour]
    apply QuadraticAlgebra.ext
    · simp [z1]
      apply h128.mul_right_cancel
      rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
      norm_num
    · simp [z1]
      apply h128.mul_right_cancel
      rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
      norm_num
  have n2 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd Fact.out hp2
  have h1024u : IsUnit (1024 : ZMod p) := by
    have h2 := isUnit_two_mod_p hp2
    have : (1024 : ZMod p) = (2 : ZMod p) ^ 10 := by norm_num
    rw [this]; exact h2.pow 10
  have hzpow : (1024 : Quad p) ^ ((p - 1) / 2) * z1 p ^ ((p - 1) / 2) =
      twoAlphaQ p ^ (2 * (p - 1)) := by
    rw [← mul_pow, hz, ← pow_mul]
    congr 1
    omega
  have hA2 : twoAlphaQ p ^ (2 * (p - 1)) = 1 := by
    rw [mul_comm, pow_mul, hA, one_pow]
  have h1024n : (1024 : Quad p) ^ ((p - 1) / 2) = 1 := by
    have : (1024 : Quad p) = ⟨1024, 0⟩ := by
      apply QuadraticAlgebra.ext <;> simp
    rw [this, _root_.C_pow]
    apply QuadraticAlgebra.ext
    · simp
      have : (1024 : ZMod p) = (2 : ZMod p) ^ 10 := by norm_num
      rw [this, ← pow_mul]
      have : 10 * ((p - 1) / 2) = 5 * (p - 1) := by omega
      rw [this, mul_comm 5, pow_mul, fermat_two_pow hp2, one_pow]
    · simp
  have h1024Q : IsUnit ((1024 : Quad p) ^ ((p - 1) / 2)) := by
    rw [h1024n]; exact isUnit_one
  apply h1024Q.mul_left_cancel
  rw [hzpow, hA2, h1024n, one_mul]

/-! ### Closed form for `T` in `Quad`. -/

lemma C_ofNat (m : ℕ) (c : ℕ) : (⟨(c : ZMod m), 0⟩ : Quad m) = (c : Quad m) := by
  apply QuadraticAlgebra.ext <;> simp

lemma C_int (m : ℕ) (c : ℤ) : (⟨(c : ZMod m), 0⟩ : Quad m) = (c : Quad m) := by
  apply QuadraticAlgebra.ext <;> simp

lemma embed_T_aux {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) (k : ℕ) :
    (⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) *
      (omega : Quad (p ^ e)) =
    z1 (p ^ e) ^ k - z2 (p ^ e) ^ k := by
  have hbin := z1_pow_sub_z2_pow (p := p) (e := e) (k := k) hp hodd he
  have h1024 : IsUnit ((1024 : ZMod (p ^ e)) ^ k) := (isUnit_1024 hp hodd he).pow k
  have hratio := pow_1024_div_pow_64 (p := p) (e := e) (k := k) hp hodd he
  have h1024Q : (1024 : Quad (p ^ e)) ^ k =
      (⟨(1024 : ZMod (p ^ e)) ^ k, 0⟩ : Quad (p ^ e)) := by
    have : (1024 : Quad (p ^ e)) = ⟨1024, 0⟩ := by
      apply QuadraticAlgebra.ext <;> simp
    rw [this, _root_.C_pow]
  have h1024uQ : IsUnit ((1024 : Quad (p ^ e)) ^ k) := by
    rw [h1024Q, QuadraticAlgebra.isUnit_iff_norm_isUnit]
    simpa [QuadraticAlgebra.norm_def] using h1024
  apply h1024uQ.mul_left_cancel
  rw [hbin, h1024Q]
  apply QuadraticAlgebra.ext
  · simp
  · simp
    rw [← hratio]
    ring

lemma omega_mul_inv {p e : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) (he : 0 < e) :
    (omega : Quad (p ^ e)) * (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) = 1 :=
  (isUnit_omega hp hp7 he).mul_val_inv

lemma inv_mul_omega {p e : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) (he : 0 < e) :
    (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) * (omega : Quad (p ^ e)) = 1 :=
  (isUnit_omega hp hp7 he).val_inv_mul

lemma z1_pow_sub_div_omega {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hp7 : p ≠ 7) :
    (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
        (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) =
      ⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ := by
  have h := embed_T_aux hp hodd he k
  have hω := isUnit_omega hp hp7 he
  apply hω.mul_right_cancel
  calc
    (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
        (↑hω.unit⁻¹ : Quad (p ^ e)) * omega
        = (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
            ((↑hω.unit⁻¹ : Quad (p ^ e)) * omega) := by ring
    _ = (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) * 1 := by rw [inv_mul_omega hp hp7 he]
    _ = z1 (p ^ e) ^ k - z2 (p ^ e) ^ k := by ring
    _ = ⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ * omega := h.symm

lemma z2_pow_n_eq_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    z2 p ^ ((p - 1) / 2) = 1 := by
  have hB := twoBetaQ_pow_p_sub_one_of_split hp2 hp7 hsplit
  have h128 : IsUnit (128 : ZMod p) := by
    have h2 := isUnit_two_mod_p hp2
    have : (128 : ZMod p) = (2 : ZMod p) ^ 7 := by norm_num
    rw [this]; exact h2.pow 7
  have n2 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd Fact.out hp2
  have hz : (1024 : Quad p) * z2 p = twoBetaQ p ^ 4 := by
    have hfour := twoBetaQ_pow_four p
    rw [hfour]
    apply QuadraticAlgebra.ext
    · simp [z2]
      apply h128.mul_right_cancel
      rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
      norm_num
    · simp [z2]
      apply h128.mul_right_cancel
      rw [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h128]
      norm_num
  have hzpow : (1024 : Quad p) ^ ((p - 1) / 2) * z2 p ^ ((p - 1) / 2) =
      twoBetaQ p ^ (2 * (p - 1)) := by
    rw [← mul_pow, hz, ← pow_mul]
    congr 1
    have : 4 * ((p - 1) / 2) = 2 * (p - 1) := by
      have := n2
      omega
    exact this
  have hB2 : twoBetaQ p ^ (2 * (p - 1)) = 1 := by
    rw [mul_comm, pow_mul, hB, one_pow]
  have h1024n : (1024 : Quad p) ^ ((p - 1) / 2) = 1 := by
    have : (1024 : Quad p) = ⟨1024, 0⟩ := by
      apply QuadraticAlgebra.ext <;> simp
    rw [this, _root_.C_pow]
    apply QuadraticAlgebra.ext
    · simp
      have : (1024 : ZMod p) = (2 : ZMod p) ^ 10 := by norm_num
      rw [this, ← pow_mul]
      have : 10 * ((p - 1) / 2) = 5 * (p - 1) := by
        have := n2; omega
      rw [this, mul_comm 5, pow_mul, fermat_two_pow hp2, one_pow]
    · simp
  have h1024Q : IsUnit ((1024 : Quad p) ^ ((p - 1) / 2)) := by
    rw [h1024n]; exact isUnit_one
  apply h1024Q.mul_left_cancel
  rw [hzpow, hB2, h1024n, one_mul]

/-- The generating function `P` evaluated in `Quad`. -/
lemma Pgen_z1_eq_z1_pow_mul_Pgen_z2 {m n : ℕ} (h128 : IsUnit (128 : ZMod m)) :
    Pgen n (z1 m) = z1 m ^ n * Pgen n (z2 m) := by
  have hzw : z1 m * z2 m = 1 := z1_mul_z2 m h128
  have := Pgen_functional_of_inv n (z1 m) (z2 m) hzw
  exact this.symm

lemma embed_real_sum (m : ℕ) (s : Finset ℕ) (f : ℕ → ZMod m) :
    (⟨∑ k ∈ s, f k, 0⟩ : Quad m) = ∑ k ∈ s, (⟨f k, 0⟩ : Quad m) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · apply QuadraticAlgebra.ext <;> simp
  · intro x s hx ih
    rw [sum_insert hx, sum_insert hx, ← ih]
    apply QuadraticAlgebra.ext <;> simp

lemma natCast_quad_pow (m c n : ℕ) :
    (((c : ℕ) : Quad m) ^ n) = ⟨((c : ZMod m) ^ n), 0⟩ := by
  have hc : ((c : ℕ) : Quad m) = ⟨(c : ZMod m), 0⟩ := (C_ofNat m c).symm
  rw [hc, _root_.C_pow]

lemma mul_real_quad (m : ℕ) (x y : ZMod m) :
    (⟨x, 0⟩ : Quad m) * ⟨y, 0⟩ = ⟨x * y, 0⟩ := by
  apply QuadraticAlgebra.ext <;> simp

lemma Tsum_term_embed {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hp7 : p ≠ 7) :
    (⟨((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
        (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) =
      ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
        (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
        (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) := by
  have hdiv := z1_pow_sub_div_omega (p := p) (e := e) (k := k) hp hodd he hp7
  have hC := natCast_quad_pow (p ^ e) (((p - 1) / 2).choose k) 3
  calc
    (⟨((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
        (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e))
        = ⟨((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3, 0⟩ *
            ⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ := by
          rw [mul_real_quad]; apply QuadraticAlgebra.ext <;> simp [mul_assoc]
    _ = ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
            ⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ := by
          rw [hC]
    _ = ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
            ((z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
              (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e))) := by
          rw [hdiv]
    _ = ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
            (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
            (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) := by
          rw [mul_assoc]

lemma Tsum_embed {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) (hp7 : p ≠ 7) :
    (⟨Tsum p e, 0⟩ : Quad (p ^ e)) =
      (Pgen ((p - 1) / 2) (z1 (p ^ e)) - Pgen ((p - 1) / 2) (z2 (p ^ e))) *
        (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) := by
  set n := (p - 1) / 2
  set ωinv : Quad (p ^ e) := ↑(isUnit_omega hp hp7 he).unit⁻¹
  have hleft : (⟨Tsum p e, 0⟩ : Quad (p ^ e)) =
      ∑ k ∈ range (n + 1),
        (⟨(((n.choose k : ℕ) : ZMod (p ^ e)) ^ 3) *
            (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) := by
    simp only [Tsum, n]
    exact embed_real_sum _ _ _
  have hterm : ∀ k ∈ range (n + 1),
      (⟨(((n.choose k : ℕ) : ZMod (p ^ e)) ^ 3) *
          (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) =
        (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) *
          (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) * ωinv := by
    intro k hk
    simpa [n, ωinv] using Tsum_term_embed (p := p) (e := e) (k := k) hp hodd he hp7
  rw [hleft, sum_congr rfl hterm]
  have hdistrib :
      ∑ k ∈ range (n + 1),
          (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) *
            (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) * ωinv =
        (∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) * z1 (p ^ e) ^ k -
          ∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) * z2 (p ^ e) ^ k) * ωinv := by
    simp only [mul_sub, sub_mul, sum_sub_distrib, sum_mul]
  rw [hdistrib]
  rfl

/-- When `(-7/p)=1`, one has `T ≡ 0` in `ZMod (p^1)`. -/
lemma Tsum_eq_zero_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    Tsum p 1 = 0 := by
  have he : (0 : ℕ) < 1 := by omega
  have hT := Tsum_embed (p := p) (e := 1) Fact.out hp2 he hp7
  have hz1 : z1 (p ^ 1) ^ ((p - 1) / 2) = 1 := by
    have hpow : p ^ 1 = p := pow_one p
    rw [hpow]
    exact z1_pow_n_eq_one_of_split hp2 hp7 hsplit
  have h128 : IsUnit (128 : ZMod (p ^ 1)) := isUnit_128 Fact.out hp2 he
  have hfun := Pgen_z1_eq_z1_pow_mul_Pgen_z2 (n := (p - 1) / 2) h128
  have hdiff :
      Pgen ((p - 1) / 2) (z1 (p ^ 1)) - Pgen ((p - 1) / 2) (z2 (p ^ 1)) = 0 := by
    rw [hfun, hz1, one_mul, sub_self]
  have hembed : (⟨Tsum p 1, 0⟩ : Quad (p ^ 1)) = 0 := by
    rw [hT, hdiff, zero_mul]
  have hre := congrArg QuadraticAlgebra.re hembed
  simpa using hre

/-! ### Reduction of `T` modulo `p` and first vanishing. -/

lemma zmod_castHom_inv {n m : ℕ} (h : m ∣ n) {u : ZMod n} (hu : IsUnit u) :
    (ZMod.castHom h (ZMod m)) u⁻¹ = ((ZMod.castHom h (ZMod m)) u)⁻¹ := by
  apply Eq.symm
  apply inv_eq_of_mul_eq_one_zmod
  rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]

lemma castHom_nat {n m : ℕ} (h : m ∣ n) (c : ℕ) :
    (ZMod.castHom h (ZMod m)) (c : ZMod n) = (c : ZMod m) := by
  simp [ZMod.castHom_apply]

lemma castHom_int {n m : ℕ} (h : m ∣ n) (c : ℤ) :
    (ZMod.castHom h (ZMod m)) (c : ZMod n) = (c : ZMod m) := by
  simp [ZMod.castHom_apply]

lemma Tsum_castHom {p e f : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he : 0 < e) (hf : e ≤ f) :
    (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (Tsum p f) = Tsum p e := by
  have h64f := isUnit_sixtyfour_zmod hp hodd (lt_of_lt_of_le he hf)
  simp only [Tsum]
  rw [map_sum]
  refine sum_congr rfl ?_
  intro k hk
  simp only [map_mul, map_pow, castHom_int, castHom_nat]
  have hinv :
      (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (((64 : ZMod (p ^ f)) ^ k)⁻¹) =
        ((64 : ZMod (p ^ e)) ^ k)⁻¹ := by
    rw [zmod_castHom_inv (u := (64 : ZMod (p ^ f)) ^ k) (pow_dvd_pow p hf) (h64f.pow k)]
    rw [map_pow]
    have h64 : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (64 : ZMod (p ^ f)) =
        (64 : ZMod (p ^ e)) :=
      map_natCast _ 64
    rw [h64]
  rw [hinv]

lemma Tsum_two_castHom_one {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) (Tsum p 2) =
      Tsum p 1 :=
  Tsum_castHom hp hodd (by omega) (by omega)

lemma Tsum_two_eq_zero_mod_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) (Tsum p 2) = 0 := by
  rw [Tsum_two_castHom_one Fact.out hp2, Tsum_eq_zero_of_split hp2 hp7 hsplit]

lemma Ssum_eq_Tsum_mod_p {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) (Ssum p 2) =
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) (Tsum p 2) := by
  rw [Ssum_eq_T_add_three_p_U hp hodd, map_add, map_mul, map_mul]
  have hp0 : (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
      (p : ZMod (p ^ 2)) = 0 := by
    rw [map_natCast]
    simp [ZMod.natCast_eq_zero_iff]
    try exact dvd_pow_self p (by omega)
  rw [hp0, mul_zero, zero_mul, add_zero]

lemma Ssum_eq_zero_mod_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) (Ssum p 2) = 0 := by
  rw [Ssum_eq_Tsum_mod_p Fact.out hp2, Tsum_two_eq_zero_mod_p_of_split hp2 hp7 hsplit]

lemma zmod_castHom_eq_zero_iff {p : ℕ} [hp : Fact p.Prime] (x : ZMod (p ^ 2)) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) x = 0 ↔
      ∃ y : ZMod (p ^ 2), x = (p : ZMod (p ^ 2)) * y := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero 1 (Nat.Prime.ne_zero hp.out)⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Nat.Prime.ne_zero hp.out)⟩
  constructor
  · intro hx
    have hxval : (x.val : ZMod (p ^ 1)) = 0 := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hx
      exact hx
    have hval : (p ^ 1) ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 1)).mp hxval
    have hval' : p ∣ x.val := by
      rw [pow_one] at hval; exact hval
    obtain ⟨y, hy⟩ := hval'
    refine ⟨(y : ZMod (p ^ 2)), ?_⟩
    have hx' : x = (x.val : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val x).symm
    rw [hx', hy, Nat.cast_mul]
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast]
    have hp0 : (p : ZMod (p ^ 1)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_one]
    rw [hp0, zero_mul]

lemma Tsum_div_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ T1 : ZMod (p ^ 2), Tsum p 2 = (p : ZMod (p ^ 2)) * T1 :=
  (zmod_castHom_eq_zero_iff (Tsum p 2)).mp
    (Tsum_two_eq_zero_mod_p_of_split hp2 hp7 hsplit)

lemma Ssum_eq_p_mul_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ T1 : ZMod (p ^ 2),
      Ssum p 2 = (p : ZMod (p ^ 2)) * (T1 + 3 * Usum p 2) := by
  obtain ⟨T1, hT⟩ := Tsum_div_p_of_split hp2 hp7 hsplit
  refine ⟨T1, ?_⟩
  rw [Ssum_eq_T_add_three_p_U Fact.out hp2, hT]
  ring

lemma Usum_term_embed {p e k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (hp7 : p ≠ 7) :
    (⟨((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
        oddHarmonic p e k *
        (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) =
      ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
        (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e)) *
        (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
        (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) := by
  have hdiv := z1_pow_sub_div_omega (p := p) (e := e) (k := k) hp hodd he hp7
  have hC := natCast_quad_pow (p ^ e) (((p - 1) / 2).choose k) 3
  calc
    (⟨((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3 *
        oddHarmonic p e k *
        (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e))
        = ⟨((((p - 1) / 2).choose k : ℕ) : ZMod (p ^ e)) ^ 3, 0⟩ *
            ⟨oddHarmonic p e k, 0⟩ *
            ⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ := by
          apply QuadraticAlgebra.ext <;> simp [mul_assoc]
    _ = ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
            ⟨oddHarmonic p e k, 0⟩ *
            ⟨(a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ := by
          rw [hC]
    _ = ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
            ⟨oddHarmonic p e k, 0⟩ *
            ((z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
              (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e))) := by
          rw [hdiv]
    _ = ((((p - 1) / 2).choose k : ℕ) : Quad (p ^ e)) ^ 3 *
            ⟨oddHarmonic p e k, 0⟩ *
            (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) *
            (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) := by
          ac_rfl

def Qgen {R : Type*} [Semiring R] (n : ℕ) (z : R) (O : ℕ → R) : R :=
  ∑ k ∈ range (n + 1), (((n.choose k : ℕ) : R) ^ 3) * O k * z ^ k

lemma Usum_embed {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) (hp7 : p ≠ 7) :
    (⟨Usum p e, 0⟩ : Quad (p ^ e)) =
      (Qgen ((p - 1) / 2) (z1 (p ^ e)) (fun k => (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e))) -
        Qgen ((p - 1) / 2) (z2 (p ^ e)) (fun k => (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e)))) *
        (↑(isUnit_omega hp hp7 he).unit⁻¹ : Quad (p ^ e)) := by
  set n := (p - 1) / 2
  set ωinv : Quad (p ^ e) := ↑(isUnit_omega hp hp7 he).unit⁻¹
  have hleft : (⟨Usum p e, 0⟩ : Quad (p ^ e)) =
      ∑ k ∈ range (n + 1),
        (⟨(((n.choose k : ℕ) : ZMod (p ^ e)) ^ 3) *
            oddHarmonic p e k *
            (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) := by
    simp only [Usum, n]
    exact embed_real_sum _ _ _
  have hterm : ∀ k ∈ range (n + 1),
      (⟨(((n.choose k : ℕ) : ZMod (p ^ e)) ^ 3) *
          oddHarmonic p e k *
          (a (4 * k) : ZMod (p ^ e)) * ((64 : ZMod (p ^ e)) ^ k)⁻¹, 0⟩ : Quad (p ^ e)) =
        (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) *
          (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e)) *
          (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) * ωinv := by
    intro k hk
    simpa [n, ωinv] using Usum_term_embed (p := p) (e := e) (k := k) hp hodd he hp7
  rw [hleft, sum_congr rfl hterm]
  have hdistrib :
      ∑ k ∈ range (n + 1),
          (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) *
            (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e)) *
            (z1 (p ^ e) ^ k - z2 (p ^ e) ^ k) * ωinv =
        (∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) *
              (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e)) * z1 (p ^ e) ^ k -
          ∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad (p ^ e)) ^ 3) *
              (⟨oddHarmonic p e k, 0⟩ : Quad (p ^ e)) * z2 (p ^ e) ^ k) * ωinv := by
    simp only [mul_sub, sub_mul, sum_sub_distrib, sum_mul, mul_assoc]
  rw [hdistrib]
  rfl

def quadCastHom {p e f : ℕ} (hf : e ≤ f) : Quad (p ^ f) →+* Quad (p ^ e) where
  toFun x := ⟨ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e)) x.re,
              ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e)) x.im⟩
  map_one' := by
    apply QuadraticAlgebra.ext
    · simp [map_one]
    · simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp [re_mul, map_mul, map_add, map_neg]
      have : (ZMod.cast (7 : ZMod (p ^ f)) : ZMod (p ^ e)) = (7 : ZMod (p ^ e)) :=
        ZMod.cast_natCast (pow_dvd_pow p hf) 7
      rw [this]
    · simp [im_mul, map_mul, map_add]
  map_zero' := by
    apply QuadraticAlgebra.ext <;> simp
  map_add' x y := by
    apply QuadraticAlgebra.ext
    · simp [map_add]
    · simp [map_add]

lemma quadCastHom_z1 {p e f : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he : 0 < e) (hf : e ≤ f) :
    quadCastHom hf (z1 (p ^ f)) = z1 (p ^ e) := by
  have h128u := isUnit_128 hp hodd (lt_of_lt_of_le he hf)
  have h128 : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (128 : ZMod (p ^ f)) =
      (128 : ZMod (p ^ e)) := map_natCast _ 128
  apply QuadraticAlgebra.ext
  · simp only [quadCastHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, z1]
    rw [map_mul, zmod_castHom_inv (pow_dvd_pow p hf) h128u, h128, map_neg]
    have : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (47 : ZMod (p ^ f)) =
        (47 : ZMod (p ^ e)) := map_natCast _ 47
    rw [this]
  · simp only [quadCastHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, z1]
    rw [map_mul, zmod_castHom_inv (pow_dvd_pow p hf) h128u, h128]
    have : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (45 : ZMod (p ^ f)) =
        (45 : ZMod (p ^ e)) := map_natCast _ 45
    rw [this]

lemma quadCastHom_z2 {p e f : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he : 0 < e) (hf : e ≤ f) :
    quadCastHom hf (z2 (p ^ f)) = z2 (p ^ e) := by
  have h128u := isUnit_128 hp hodd (lt_of_lt_of_le he hf)
  have h128 : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (128 : ZMod (p ^ f)) =
      (128 : ZMod (p ^ e)) := map_natCast _ 128
  apply QuadraticAlgebra.ext
  · simp only [quadCastHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, z2]
    rw [map_mul, zmod_castHom_inv (pow_dvd_pow p hf) h128u, h128, map_neg]
    have : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (47 : ZMod (p ^ f)) =
        (47 : ZMod (p ^ e)) := map_natCast _ 47
    rw [this]
  · simp only [quadCastHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, z2]
    rw [map_mul, map_neg, zmod_castHom_inv (pow_dvd_pow p hf) h128u, h128]
    have : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (45 : ZMod (p ^ f)) =
        (45 : ZMod (p ^ e)) := map_natCast _ 45
    rw [this]

lemma n_cast_eq_neg_inv_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (((p - 1) / 2 : ℕ) : ZMod p) = -((2 : ZMod p)⁻¹) := by
  have h2 := isUnit_two_mod_p hp2
  have hn : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd Fact.out hp2
  apply h2.mul_left_cancel
  have hL : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) = -1 := by
    rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_mul, hn]
    have hpos : 1 ≤ p := (Nat.Prime.one_le Fact.out)
    rw [Nat.cast_sub hpos, Nat.cast_one]
    simp
  have hR : (2 : ZMod p) * (-((2 : ZMod p)⁻¹)) = -1 := by
    rw [mul_neg, ZMod.mul_inv_of_unit _ h2]
  exact hL.trans hR.symm

lemma z1_pow_n_cast_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    quadCastHom (show 1 ≤ 2 by omega) (z1 (p ^ 2) ^ ((p - 1) / 2)) = 1 := by
  rw [map_pow, quadCastHom_z1 Fact.out hp2 (by omega) (by omega)]
  have hpow : p ^ 1 = p := pow_one p
  rw [hpow]
  exact z1_pow_n_eq_one_of_split hp2 hp7 hsplit

lemma exists_delta_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ δ : Quad (p ^ 2),
      z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ := by
  have hred := z1_pow_n_cast_of_split hp2 hp7 hsplit
  have hz : quadCastHom (show 1 ≤ 2 by omega)
      (z1 (p ^ 2) ^ ((p - 1) / 2) - 1) = 0 := by
    rw [map_sub, hred, map_one, sub_self]
  have hre0 :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
        (z1 (p ^ 2) ^ ((p - 1) / 2) - 1).re = 0 := by
    have := congrArg QuadraticAlgebra.re hz
    simpa [quadCastHom] using this
  have him0 :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
        (z1 (p ^ 2) ^ ((p - 1) / 2) - 1).im = 0 := by
    have := congrArg QuadraticAlgebra.im hz
    simpa [quadCastHom] using this
  obtain ⟨ar, hr⟩ := (zmod_castHom_eq_zero_iff _).mp hre0
  obtain ⟨ai, hi⟩ := (zmod_castHom_eq_zero_iff _).mp him0
  refine ⟨⟨ar, ai⟩, ?_⟩
  apply QuadraticAlgebra.ext
  · have hsub : (z1 (p ^ 2) ^ ((p - 1) / 2) - 1).re =
        (z1 (p ^ 2) ^ ((p - 1) / 2)).re - 1 := by
      simp
    rw [hsub] at hr
    have hmul : ((p : Quad (p ^ 2)) * ⟨ar, ai⟩).re = (p : ZMod (p ^ 2)) * ar := by
      simp [re_mul]
    rw [sub_eq_iff_eq_add, add_comm] at hr
    simp [hmul]
    exact hr
  · have hsub : (z1 (p ^ 2) ^ ((p - 1) / 2) - 1).im =
        (z1 (p ^ 2) ^ ((p - 1) / 2)).im := by
      simp
    rw [hsub] at hi
    have hmul : ((p : Quad (p ^ 2)) * ⟨ar, ai⟩).im = (p : ZMod (p ^ 2)) * ai := by
      simp [im_mul]
    simp [hmul]
    exact hi

lemma Tsum_eq_p_mul_delta {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ δ : Quad (p ^ 2),
      z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ ∧
      (⟨Tsum p 2, 0⟩ : Quad (p ^ 2)) =
        (p : Quad (p ^ 2)) * δ * Pgen ((p - 1) / 2) (z2 (p ^ 2)) *
          (↑(isUnit_omega Fact.out hp7 (by omega : 0 < 2)).unit⁻¹ : Quad (p ^ 2)) := by
  obtain ⟨δ, hδ⟩ := exists_delta_of_split hp2 hp7 hsplit
  refine ⟨δ, hδ, ?_⟩
  have he : (0 : ℕ) < 2 := by omega
  have hT := Tsum_embed (p := p) (e := 2) Fact.out hp2 he hp7
  have h128 : IsUnit (128 : ZMod (p ^ 2)) := isUnit_128 Fact.out hp2 he
  have hfun := Pgen_z1_eq_z1_pow_mul_Pgen_z2 (n := (p - 1) / 2) h128
  rw [hT, hfun, hδ]
  ring

/-! ### Harmonic numbers in `ZMod p` and the identity `H_n - H_{n-k} ≡ -2 O_k`. -/

/-- The harmonic sum `H_m = ∑_{i=1}^m 1/i` in `ZMod p`. -/
def harmonicMod (p m : ℕ) : ZMod p :=
  ∑ i ∈ range m, ((i + 1 : ℕ) : ZMod p)⁻¹

lemma harmonicMod_zero (p : ℕ) : harmonicMod p 0 = 0 := by
  simp [harmonicMod]

lemma harmonicMod_succ (p m : ℕ) :
    harmonicMod p (m + 1) = harmonicMod p m + (((m + 1 : ℕ) : ZMod p)⁻¹) := by
  simp [harmonicMod, sum_range_succ]

lemma isUnit_of_pos_lt_p {p j : ℕ} [Fact p.Prime] (hpos : 0 < j) (hlt : j < p) :
    IsUnit ((j : ℕ) : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact Nat.not_dvd_of_pos_of_lt hpos hlt

lemma isUnit_succ_lt_p {p j : ℕ} [Fact p.Prime] (hlt : j + 1 < p) :
    IsUnit (((j + 1 : ℕ) : ZMod p)) :=
  isUnit_of_pos_lt_p (Nat.succ_pos j) hlt

/-- For `j < n = (p-1)/2`, one has `n - j < p` and `n - j > 0`. -/
lemma n_sub_j_pos {p j : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hj : j < (p - 1) / 2) :
    0 < (p - 1) / 2 - j := by
  omega

lemma n_sub_j_lt_p {p j : ℕ} (hp : p.Prime) (hj : j ≤ (p - 1) / 2) :
    (p - 1) / 2 - j < p := by
  have : (p - 1) / 2 < p := half_lt_p hp
  omega

lemma isUnit_n_sub {p j : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hj : j < (p - 1) / 2) :
    IsUnit ((((p - 1) / 2 - j : ℕ) : ZMod p)) := by
  apply isUnit_of_pos_lt_p
  · exact n_sub_j_pos Fact.out hp2 hj
  · exact n_sub_j_lt_p Fact.out (Nat.le_of_lt hj)

/-- `↑(n - j) = ↑n - ↑j` in `ZMod p` (always true for natural subtraction when `j ≤ n`). -/
lemma n_sub_j_cast {p j : ℕ} (hj : j ≤ (p - 1) / 2) :
    (((p - 1) / 2 - j : ℕ) : ZMod p) =
      (((p - 1) / 2 : ℕ) : ZMod p) - (j : ZMod p) := by
  rw [Nat.cast_sub hj]

/-- `1/(n - m) = -2 / (2m + 1)` in `ZMod p`, for `m < n`. -/
lemma inv_n_sub_eq_neg_two_odd {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hm : m < (p - 1) / 2) :
    ((((p - 1) / 2 - m : ℕ) : ZMod p)⁻¹) =
      -((2 : ZMod p) * (((2 * m + 1 : ℕ) : ZMod p)⁻¹)) := by
  have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
  have hn := n_cast_eq_neg_inv_two (p := p) hp2
  have hunit : IsUnit ((((p - 1) / 2 - m : ℕ) : ZMod p)) := isUnit_n_sub hp2 hm
  have hodd : IsUnit (((2 * m + 1 : ℕ) : ZMod p)) := by
    have hlt : 2 * m + 1 < p := by
      have hn2 : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd Fact.out hp2
      omega
    exact isUnit_of_pos_lt_p (Nat.succ_pos _) hlt
  have hcast := n_sub_j_cast (p := p) (j := m) (Nat.le_of_lt hm)
  -- n - m = n - m = -1/2 - m = -(1 + 2m)/2
  have hval : (((p - 1) / 2 - m : ℕ) : ZMod p) =
      -((2 : ZMod p)⁻¹) * (((2 * m + 1 : ℕ) : ZMod p)) := by
    rw [hcast, hn]
    have : (2 * m + 1 : ℕ) = 2 * m + 1 := rfl
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2
    calc
      -((2 : ZMod p)⁻¹) - (m : ZMod p)
        = -((2 : ZMod p)⁻¹) - (2 : ZMod p) * (2 : ZMod p)⁻¹ * (m : ZMod p) := by
          rw [h2inv, one_mul]
      _ = -((2 : ZMod p)⁻¹) * (1 + (2 : ZMod p) * (m : ZMod p)) := by ring
      _ = -((2 : ZMod p)⁻¹) * ((2 : ZMod p) * (m : ZMod p) + 1) := by ring
  -- invert both sides
  have hrhs_unit : IsUnit (-((2 : ZMod p)⁻¹) * (((2 * m + 1 : ℕ) : ZMod p))) := by
    refine (h2.inv.neg).mul hodd
  apply_fun (fun x : ZMod p => x⁻¹) at hval
  -- x⁻¹ of a product
  have : ((((p - 1) / 2 - m : ℕ) : ZMod p)⁻¹) =
      (-((2 : ZMod p)⁻¹) * (((2 * m + 1 : ℕ) : ZMod p)))⁻¹ := by
    rw [hval]
  rw [this, zmod_inv_mul (h2.inv.neg) hodd]
  have hneg : (-((2 : ZMod p)⁻¹))⁻¹ = -((2 : ZMod p)) := by
    apply inv_eq_of_mul_eq_one_zmod
    rw [neg_mul_neg, ZMod.inv_mul_of_unit _ h2]
  rw [hneg]
  simp [neg_mul]

/-- `H_n - H_{n-k} = ∑_{m=0}^{k-1} 1/(n-m)`. -/
lemma harmonicMod_sub_range {p n : ℕ} :
    ∀ k, k ≤ n →
      harmonicMod p n - harmonicMod p (n - k) =
        ∑ m ∈ range k, (((n - m : ℕ) : ZMod p)⁻¹) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [harmonicMod]
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hpos : n - k = (n - (k + 1)) + 1 := by omega
    have hterm : harmonicMod p (n - k) - harmonicMod p (n - (k + 1)) =
        (((n - k : ℕ) : ZMod p)⁻¹) := by
      rw [hpos, harmonicMod_succ]
      simp
    have : harmonicMod p n - harmonicMod p (n - (k + 1)) =
        (harmonicMod p n - harmonicMod p (n - k)) +
          (harmonicMod p (n - k) - harmonicMod p (n - (k + 1))) := by
      abel
    rw [this, ih hk', hterm, sum_range_succ]

/-- Odd harmonic sum directly in `ZMod p`. -/
def oddHarmonicMod (p k : ℕ) : ZMod p :=
  ∑ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod p)⁻¹)

lemma oddHarmonicMod_eq_sum (p k : ℕ) :
    oddHarmonicMod p k = ∑ j ∈ range k, (((2 * j + 1 : ℕ) : ZMod p)⁻¹) :=
  rfl

/-- `H_n - H_{n-k} ≡ -2 O_k` in `ZMod p`. -/
lemma harmonicMod_sub_eq_neg_two_oddHarmonic {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    harmonicMod p ((p - 1) / 2) - harmonicMod p ((p - 1) / 2 - k) =
      -((2 : ZMod p) * oddHarmonicMod p k) := by
  have hsum := harmonicMod_sub_range (p := p) (n := (p - 1) / 2) k hk
  rw [hsum]
  have hterm : ∀ m ∈ range k,
      ((((p - 1) / 2 - m : ℕ) : ZMod p)⁻¹) =
        -((2 : ZMod p) * (((2 * m + 1 : ℕ) : ZMod p)⁻¹)) := by
    intro m hm
    have hm' : m < (p - 1) / 2 :=
      lt_of_lt_of_le (mem_range.mp hm) hk
    exact inv_n_sub_eq_neg_two_odd hp2 hm'
  rw [sum_congr rfl hterm]
  simp only [oddHarmonicMod, mul_sum, sum_neg_distrib]

/-- `O_k - O_{n-k} ≡ (H_{n-k} - H_k) / 2` in `ZMod p`. -/
lemma oddHarmonicMod_sub_of_split {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    oddHarmonicMod p k - oddHarmonicMod p ((p - 1) / 2 - k) =
      ((2 : ZMod p)⁻¹) *
        (harmonicMod p ((p - 1) / 2 - k) - harmonicMod p k) := by
  have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
  have hk1 := harmonicMod_sub_eq_neg_two_oddHarmonic (p := p) (k := k) hp2 hk
  have hnk : (p - 1) / 2 - k ≤ (p - 1) / 2 := Nat.sub_le _ _
  have hk2 := harmonicMod_sub_eq_neg_two_oddHarmonic (p := p)
    (k := (p - 1) / 2 - k) hp2 hnk
  have hsub : (p - 1) / 2 - ((p - 1) / 2 - k) = k := Nat.sub_sub_self hk
  rw [hsub] at hk2
  -- hk1: H_n - H_{n-k} = -2 O_k  ⇒  2 O_k = H_{n-k} - H_n
  -- hk2: H_n - H_k = -2 O_{n-k}  ⇒  2 O_{n-k} = H_k - H_n
  have hOk : (2 : ZMod p) * oddHarmonicMod p k =
      harmonicMod p ((p - 1) / 2 - k) - harmonicMod p ((p - 1) / 2) := by
    have hneg := congrArg Neg.neg hk1
    rw [neg_sub, neg_neg] at hneg
    exact hneg.symm
  have hOnk : (2 : ZMod p) * oddHarmonicMod p ((p - 1) / 2 - k) =
      harmonicMod p k - harmonicMod p ((p - 1) / 2) := by
    have hneg := congrArg Neg.neg hk2
    rw [neg_sub, neg_neg] at hneg
    exact hneg.symm
  apply h2.mul_left_cancel
  have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2
  calc
    (2 : ZMod p) * (oddHarmonicMod p k - oddHarmonicMod p ((p - 1) / 2 - k))
      = (2 : ZMod p) * oddHarmonicMod p k
          - (2 : ZMod p) * oddHarmonicMod p ((p - 1) / 2 - k) := by ring
    _ = (harmonicMod p ((p - 1) / 2 - k) - harmonicMod p ((p - 1) / 2))
          - (harmonicMod p k - harmonicMod p ((p - 1) / 2)) := by
        rw [hOk, hOnk]
    _ = harmonicMod p ((p - 1) / 2 - k) - harmonicMod p k := by ring
    _ = (2 : ZMod p) * ((2 : ZMod p)⁻¹ *
          (harmonicMod p ((p - 1) / 2 - k) - harmonicMod p k)) := by
        rw [← mul_assoc, h2inv, one_mul]

/-- Complex conjugation as a ring endomorphism of `Quad m`. -/
def quadConj {m : ℕ} : Quad m →+* Quad m where
  toFun x := ⟨x.re, -x.im⟩
  map_one' := by
    apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp [re_mul]
    · simp [im_mul]; ring
  map_zero' := by
    apply QuadraticAlgebra.ext <;> simp
  map_add' x y := by
    apply QuadraticAlgebra.ext
    · simp
    · simp; ring

lemma quadConj_z1 (m : ℕ) : quadConj (z1 m) = z2 m := by
  apply QuadraticAlgebra.ext <;> simp [quadConj, z1, z2]

lemma quadConj_z2 (m : ℕ) : quadConj (z2 m) = z1 m := by
  apply QuadraticAlgebra.ext <;> simp [quadConj, z1, z2]

lemma quadConj_nat {m : ℕ} (c : ℕ) : quadConj (c : Quad m) = (c : Quad m) := by
  apply QuadraticAlgebra.ext
  · simp [quadConj]
  · simp [quadConj]

lemma quadConj_C {m : ℕ} (c : ZMod m) : quadConj ⟨c, 0⟩ = ⟨c, 0⟩ := by
  simp [quadConj]

lemma Pgen_conj {m n : ℕ} (z : Quad m) :
    quadConj (Pgen n z) = Pgen n (quadConj z) := by
  simp only [Pgen, map_sum]
  refine sum_congr rfl ?_
  intro k hk
  rw [map_mul, map_pow, map_pow, quadConj_nat]

lemma isUnit_128_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (128 : ZMod p) := by
  have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
  have : (128 : ZMod p) = (2 : ZMod p) ^ 7 := by norm_num
  rw [this]
  exact h2.pow 7

/-- When split, `P(z1)` is real in `Quad p`. -/
lemma Pgen_z1_real_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    (Pgen ((p - 1) / 2) (z1 p)).im = 0 := by
  have h128 : IsUnit (128 : ZMod p) := isUnit_128_mod_p hp2
  have hz1 : z1 p ^ ((p - 1) / 2) = 1 :=
    z1_pow_n_eq_one_of_split hp2 hp7 hsplit
  have hfun := Pgen_z1_eq_z1_pow_mul_Pgen_z2 (n := (p - 1) / 2) (m := p) h128
  have hP : Pgen ((p - 1) / 2) (z1 p) = Pgen ((p - 1) / 2) (z2 p) := by
    rw [hfun, hz1, one_mul]
  have hconj : quadConj (Pgen ((p - 1) / 2) (z1 p)) =
      Pgen ((p - 1) / 2) (z2 p) := by
    rw [Pgen_conj, quadConj_z1]
  have heq : quadConj (Pgen ((p - 1) / 2) (z1 p)) =
      Pgen ((p - 1) / 2) (z1 p) := by
    rw [hconj, ← hP]
  have him : - (Pgen ((p - 1) / 2) (z1 p)).im =
      (Pgen ((p - 1) / 2) (z1 p)).im := by
    simpa [quadConj] using congrArg QuadraticAlgebra.im heq
  have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
  have h2im : (2 : ZMod p) * (Pgen ((p - 1) / 2) (z1 p)).im = 0 := by
    have := congrArg (fun z => z + (Pgen ((p - 1) / 2) (z1 p)).im) him
    simp only [neg_add_cancel] at this
    have hrewrite : (Pgen ((p - 1) / 2) (z1 p)).im +
        (Pgen ((p - 1) / 2) (z1 p)).im =
        (2 : ZMod p) * (Pgen ((p - 1) / 2) (z1 p)).im := by ring
    rw [hrewrite] at this
    exact this.symm
  exact (IsUnit.mul_right_eq_zero h2).mp h2im

/-- Cast of `oddHarmonic` along `p^f → p^e` when every odd denominator is a unit. -/
lemma oddHarmonic_castHom {p e f k : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he : 0 < e) (hf : e ≤ f) (hk : k ≤ (p - 1) / 2) :
    (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (oddHarmonic p f k) =
      oddHarmonic p e k := by
  simp only [oddHarmonic, map_sum]
  refine sum_congr rfl ?_
  intro j hj
  have hjk : j ∈ range k := hj
  have hu : IsUnit ((2 * j + 1 : ℕ) : ZMod (p ^ f)) :=
    isUnit_odd_zmod hp hodd (lt_of_lt_of_le he hf) hk hjk
  rw [zmod_castHom_inv (pow_dvd_pow p hf) hu, map_natCast]

/-- `H_n ≡ -2 O_n` in `ZMod p`. -/
lemma harmonicMod_n_eq_neg_two_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    harmonicMod p ((p - 1) / 2) = -((2 : ZMod p) * oddHarmonicMod p ((p - 1) / 2)) := by
  have h := harmonicMod_sub_eq_neg_two_oddHarmonic (p := p) (k := (p - 1) / 2) hp2 le_rfl
  have : (p - 1) / 2 - (p - 1) / 2 = 0 := Nat.sub_self _
  rw [this, harmonicMod_zero, sub_zero] at h
  exact h

/-- Generating function `R_n(z) = ∑ C(n,k)³ H_k z^k`. -/
def Rgen {R : Type*} [Semiring R] (n : ℕ) (z : R) (H : ℕ → R) : R :=
  ∑ k ∈ range (n + 1), (((n.choose k : ℕ) : R) ^ 3) * H k * z ^ k

lemma Usum_castHom {p e f : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he : 0 < e) (hf : e ≤ f) :
    (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (Usum p f) = Usum p e := by
  have h64f := isUnit_sixtyfour_zmod hp hodd (lt_of_lt_of_le he hf)
  simp only [Usum]
  rw [map_sum]
  refine sum_congr rfl ?_
  intro k hk
  have hk' : k ≤ (p - 1) / 2 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [map_mul, map_pow, castHom_int, castHom_nat]
  rw [oddHarmonic_castHom hp hodd he hf hk']
  have hinv :
      (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (((64 : ZMod (p ^ f)) ^ k)⁻¹) =
        ((64 : ZMod (p ^ e)) ^ k)⁻¹ := by
    rw [zmod_castHom_inv (u := (64 : ZMod (p ^ f)) ^ k) (pow_dvd_pow p hf) (h64f.pow k)]
    rw [map_pow]
    have h64 : (ZMod.castHom (pow_dvd_pow p hf) (ZMod (p ^ e))) (64 : ZMod (p ^ f)) =
        (64 : ZMod (p ^ e)) :=
      map_natCast _ 64
    rw [h64]
  rw [hinv]

/-! ### Binomial coefficients modulo a prime. -/

lemma choose_succ_add (n k : ℕ) :
    n.choose k + n.choose (k + 1) = (n + 1).choose (k + 1) :=
  (choose_succ_succ n k).symm

lemma choose_prime_eq_zero {p k : ℕ} [Fact p.Prime] (hk0 : k ≠ 0) (hkp : k < p) :
    ((p.choose k : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.Prime.dvd_choose_self Fact.out hk0 hkp

/-- `C(p-1, k) ≡ (-1)^k (mod p)` for `k < p`. -/
lemma choose_p_sub_one {p k : ℕ} [Fact p.Prime] (hk : k < p) :
    (((p - 1).choose k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hk' : k < p := Nat.lt_of_succ_lt hk
    have hpos : 1 ≤ p := Nat.Prime.one_le Fact.out
    have hadd :
        ((p - 1).choose k + (p - 1).choose (k + 1) : ℕ) = p.choose (k + 1) := by
      simpa [Nat.sub_add_cancel hpos] using choose_succ_add (p - 1) k
    have hsum :
        ((p - 1).choose k : ZMod p) + ((p - 1).choose (k + 1) : ZMod p) =
          (p.choose (k + 1) : ZMod p) := by
      rw [← Nat.cast_add, hadd]
    have hrhs : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 :=
      choose_prime_eq_zero (Nat.succ_ne_zero k) hk
    have hAB : ((p - 1).choose k : ZMod p) + ((p - 1).choose (k + 1) : ZMod p) = 0 :=
      hsum.trans hrhs
    have : (((p - 1).choose (k + 1) : ℕ) : ZMod p) =
        -(((p - 1).choose k : ℕ) : ZMod p) :=
      eq_neg_of_add_eq_zero_right hAB
    rw [this, ih hk', pow_succ]
    ring

/-- `k * C(p,k) = p * C(p-1, k-1)` for positive `k` and `p`. -/
lemma choose_prime_mul (p k : ℕ) (hk : 0 < k) (hp : 0 < p) :
    k * p.choose k = p * (p - 1).choose (k - 1) := by
  have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
  rw [Nat.sub_add_cancel hp, Nat.sub_add_cancel hk] at h
  linarith

lemma isUnit_of_pos_lt_p_pow {p e j : ℕ} [Fact p.Prime] (he : 0 < e)
    (hpos : 0 < j) (hlt : j < p) :
    IsUnit ((j : ℕ) : ZMod (p ^ e)) := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff he, Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact Nat.not_dvd_of_pos_of_lt hpos hlt

/-- `O_k = 2⁻¹ (H_{n-k} - H_n)` in `ZMod p`. -/
lemma oddHarmonicMod_eq_half_harmonic_sub {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    oddHarmonicMod p k =
      ((2 : ZMod p)⁻¹) *
        (harmonicMod p ((p - 1) / 2 - k) - harmonicMod p ((p - 1) / 2)) := by
  have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
  have h := harmonicMod_sub_eq_neg_two_oddHarmonic (p := p) (k := k) hp2 hk
  apply h2.mul_left_cancel
  have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2
  have hneg : (2 : ZMod p) * oddHarmonicMod p k =
      -(harmonicMod p ((p - 1) / 2) - harmonicMod p ((p - 1) / 2 - k)) := by
    have := congrArg Neg.neg h
    rw [neg_neg] at this
    exact this.symm
  rw [hneg, neg_sub, ← mul_assoc, h2inv, one_mul]

/-! ### Fermat quotient of `2` via integers. -/

lemma two_pow_p_sub_one_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ (p - 1) ≡ 1 [MOD p] :=
  Nat.ModEq.pow_card_sub_one_eq_one hp (coprime_two_odd_prime hp hp2)

lemma p_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ 2 ^ (p - 1) - 1 := by
  have hmod := two_pow_p_sub_one_mod hp hp2
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)

/-- Integer Fermat quotient `(2^{p-1} - 1)/p`. -/
def fermatQuotientTwoNat (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ℕ :=
  (2 ^ (p - 1) - 1) / p

lemma fermatQuotientTwoNat_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p * fermatQuotientTwoNat p hp hp2 = 2 ^ (p - 1) - 1 :=
  Nat.mul_div_cancel' (p_dvd_two_pow_sub_one hp hp2)

lemma two_pow_p_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ p - 2 = 2 * (2 ^ (p - 1) - 1) := by
  have hpos : 1 ≤ p := Nat.Prime.one_le hp
  have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by
    calc
      2 ^ p = 2 ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hpos]
      _ = 2 * 2 ^ (p - 1) := pow_succ' _ _
  omega

/-- Alternating harmonic sum `∑_{k=1}^{p-1} (-1)^{k-1}/k` in `ZMod p`. -/
def altHarmonic (p : ℕ) : ZMod p :=
  ∑ k ∈ Icc 1 (p - 1), ((-1 : ZMod p) ^ (k - 1)) * ((k : ℕ) : ZMod p)⁻¹

lemma Icc_odd_union_even {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ((range ((p - 1) / 2)).image (fun j => 2 * j + 1)) ∪
      ((Icc 1 ((p - 1) / 2)).image (fun j => 2 * j)) =
      Icc 1 (p - 1) := by
  set n := (p - 1) / 2
  have hn2 : 2 * n = p - 1 := two_mul_half_odd hp hp2
  apply subset_antisymm
  · intro a ha
    rw [mem_union, mem_image, mem_image] at ha
    rw [mem_Icc]
    rcases ha with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · have : j < n := mem_range.mp hj; omega
    · have : 1 ≤ j ∧ j ≤ n := mem_Icc.mp hj; omega
  · intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    have ha2 : a ≤ p - 1 := (mem_Icc.mp ha).2
    rw [mem_union]
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨j, hj⟩ := he
      have haeq : a = 2 * j := by
        rw [two_mul]; exact hj
      refine Or.inr (mem_image.mpr ⟨j, ?_, haeq.symm⟩)
      rw [mem_Icc]; omega
    · obtain ⟨j, hj⟩ := ho
      refine Or.inl (mem_image.mpr ⟨j, ?_, hj.symm⟩)
      rw [mem_range]; omega

lemma disjoint_odd_even_image (n : ℕ) :
    Disjoint ((range n).image (fun j => 2 * j + 1))
      ((Icc 1 n).image (fun j => 2 * j)) := by
  refine disjoint_left.mpr ?_
  intro a ha1 ha2
  rcases mem_image.mp ha1 with ⟨j, _, rfl⟩
  rcases mem_image.mp ha2 with ⟨i, _, hi⟩
  omega

lemma image_two_mul_add_one_inj (n : ℕ) {x y : ℕ}
    (_hx : x ∈ range n) (_hy : y ∈ range n)
    (h : 2 * x + 1 = 2 * y + 1) : x = y := by omega

lemma image_two_mul_inj (n : ℕ) {x y : ℕ}
    (_hx : x ∈ Icc 1 n) (_hy : y ∈ Icc 1 n)
    (h : 2 * x = 2 * y) : x = y := by omega

lemma altHarmonic_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    altHarmonic p =
      oddHarmonicMod p ((p - 1) / 2) -
        ((2 : ZMod p)⁻¹) * harmonicMod p ((p - 1) / 2) := by
  set n := (p - 1) / 2
  have hunion := Icc_odd_union_even Fact.out hp2
  have hdisj := disjoint_odd_even_image n
  have hodd_pow : ∀ j, ((-1 : ZMod p) ^ (2 * j + 1 - 1)) = 1 := by
    intro j
    have : 2 * j + 1 - 1 = 2 * j := by omega
    rw [this, pow_mul, neg_one_sq, one_pow]
  have heven_pow : ∀ j, 0 < j → ((-1 : ZMod p) ^ (2 * j - 1)) = -1 := by
    intro j hj
    have : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
    rw [this, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  simp only [altHarmonic]
  rw [← hunion, sum_union hdisj]
  have hodd :
      ∑ x ∈ (range n).image (fun j => 2 * j + 1),
          ((-1 : ZMod p) ^ (x - 1)) * ((x : ℕ) : ZMod p)⁻¹ =
        oddHarmonicMod p n := by
    have hinj : Set.InjOn (fun j : ℕ => 2 * j + 1) (range n) := by
      intro x _ y _ h
      have : 2 * x + 1 = 2 * y + 1 := h
      omega
    rw [sum_image hinj]
    simp only [oddHarmonicMod]
    refine sum_congr rfl ?_
    intro j _
    rw [hodd_pow, one_mul]
  have heven :
      ∑ x ∈ (Icc 1 n).image (fun j => 2 * j),
          ((-1 : ZMod p) ^ (x - 1)) * ((x : ℕ) : ZMod p)⁻¹ =
        -((2 : ZMod p)⁻¹ * harmonicMod p n) := by
    have hinj : Set.InjOn (fun j : ℕ => 2 * j) (Icc 1 n) := by
      intro x _ y _ h
      have : 2 * x = 2 * y := h
      omega
    rw [sum_image hinj]
    have hIcc : Icc 1 n = (range n).image (fun j => j + 1) := by
      ext a
      simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro h
        exact ⟨a - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        omega
    have hinj2 : Set.InjOn (fun j : ℕ => j + 1) (range n) := by
      intro x _ y _ h
      have : x + 1 = y + 1 := h
      omega
    rw [hIcc, sum_image hinj2]
    have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
    have hterm : ∀ j ∈ range n,
        ((-1 : ZMod p) ^ (2 * (j + 1) - 1)) * (((2 * (j + 1) : ℕ) : ZMod p)⁻¹) =
          -((2 : ZMod p)⁻¹ * (((j + 1 : ℕ) : ZMod p)⁻¹)) := by
      intro j hj
      have hjpos : 0 < j + 1 := Nat.succ_pos _
      have hlt : j + 1 < p := by
        have := mem_range.mp hj
        have : n < p := half_lt_p Fact.out
        omega
      have hju : IsUnit (((j + 1 : ℕ) : ZMod p)) := isUnit_of_pos_lt_p hjpos hlt
      have hpow : ((-1 : ZMod p) ^ (2 * (j + 1) - 1)) = -1 :=
        heven_pow (j + 1) hjpos
      have h2j : ((2 * (j + 1) : ℕ) : ZMod p) =
          (2 : ZMod p) * ((j + 1 : ℕ) : ZMod p) := by
        push_cast; rfl
      rw [hpow, h2j, zmod_inv_mul h2 hju, neg_one_mul]
    rw [sum_congr rfl hterm, sum_neg_distrib, ← mul_sum]
    rfl
  rw [hodd, heven]
  ring

lemma altHarmonic_eq_neg_harmonic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    altHarmonic p = - harmonicMod p ((p - 1) / 2) := by
  rw [altHarmonic_split hp2]
  have hO := harmonicMod_n_eq_neg_two_odd (p := p) hp2
  have h2 : IsUnit (2 : ZMod p) := isUnit_two_mod_p hp2
  have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2
  have hO' : oddHarmonicMod p ((p - 1) / 2) =
      -((2 : ZMod p)⁻¹ * harmonicMod p ((p - 1) / 2)) := by
    apply h2.mul_left_cancel
    have h2O : (2 : ZMod p) * oddHarmonicMod p ((p - 1) / 2) =
        - harmonicMod p ((p - 1) / 2) := by
      have := congrArg Neg.neg hO
      simpa [neg_mul, neg_neg] using this.symm
    rw [h2O, mul_neg, ← mul_assoc, h2inv, one_mul]
  rw [hO']
  -- ⊢ -(2⁻¹ * H) - 2⁻¹ * H = -H
  have hH2 : (2 : ZMod p) * ((2 : ZMod p)⁻¹ * harmonicMod p ((p - 1) / 2)) =
      harmonicMod p ((p - 1) / 2) := by
    rw [← mul_assoc, h2inv, one_mul]
  have hrewrite :
      -((2 : ZMod p)⁻¹ * harmonicMod p ((p - 1) / 2)) -
        (2 : ZMod p)⁻¹ * harmonicMod p ((p - 1) / 2) =
      -((2 : ZMod p) * ((2 : ZMod p)⁻¹ * harmonicMod p ((p - 1) / 2))) := by
    simp only [two_mul, neg_add, sub_eq_add_neg]
  rw [hrewrite, hH2]

/-! ### Fermat quotient of 2 equals the alternating harmonic number. -/

lemma range_p_succ_split {p : ℕ} (hp : 2 ≤ p) :
    range (p + 1) = ({0} : Finset ℕ) ∪ Icc 1 (p - 1) ∪ {p} := by
  ext x
  simp only [mem_range, mem_union, mem_singleton, mem_Icc]
  constructor <;> intro <;> omega

lemma sum_choose_prime_interior {p : ℕ} (hp : p.Prime) :
    ∑ k ∈ Icc 1 (p - 1), p.choose k = 2 ^ p - 2 := by
  have h2 : 2 ≤ p := Nat.Prime.two_le hp
  have hsum := Nat.sum_range_choose p
  have hsplit := range_p_succ_split h2
  have hdisj1 : Disjoint ({0} : Finset ℕ) (Icc 1 (p - 1)) := by
    refine disjoint_left.mpr ?_
    intro x hx hx'
    simp only [mem_singleton] at hx
    simp only [mem_Icc] at hx'
    omega
  have hdisj2 : Disjoint (({0} : Finset ℕ) ∪ Icc 1 (p - 1)) ({p} : Finset ℕ) := by
    refine disjoint_left.mpr ?_
    intro x hx hx'
    simp only [mem_union, mem_singleton, mem_Icc] at hx hx'
    omega
  rw [hsplit, sum_union hdisj2, sum_union hdisj1, sum_singleton, sum_singleton] at hsum
  have h0 : p.choose 0 = 1 := choose_zero_right p
  have hpe : p.choose p = 1 := choose_self p
  rw [h0, hpe] at hsum
  have hge : 2 ≤ 2 ^ p := Nat.le_self_pow (by omega) 2
  omega

/-- Modular inverse of `k` lifted to `{0, …, p-1}`. -/
def invLift (p k : ℕ) : ℕ := ((k : ZMod p)⁻¹).val

lemma invLift_mul {p k : ℕ} [Fact p.Prime] (hpos : 0 < k) (hlt : k < p) :
    (k : ZMod p) * (invLift p k : ZMod p) = 1 := by
  have hu := isUnit_of_pos_lt_p hpos hlt
  simp only [invLift]
  rw [ZMod.natCast_zmod_val, ZMod.mul_inv_of_unit _ hu]

lemma invLift_pos {p k : ℕ} [Fact p.Prime] (hpos : 0 < k) (hlt : k < p) :
    0 < invLift p k := by
  have hmul := invLift_mul (p := p) hpos hlt
  have : invLift p k ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, mul_zero] at hmul
    exact zero_ne_one hmul
  exact Nat.pos_of_ne_zero this

lemma invLift_mul_nat {p k : ℕ} [Fact p.Prime] (hpos : 0 < k) (hlt : k < p) :
    ∃ t : ℕ, k * invLift p k = 1 + p * t := by
  have hmul := invLift_mul (p := p) hpos hlt
  have hge : 1 ≤ k * invLift p k := by
    have := invLift_pos (p := p) hpos hlt
    nlinarith
  have hcast : ((k * invLift p k : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, hmul]
  have hmod : (k * invLift p k) % p = 1 := by
    have heq : ((k * invLift p k : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa using hcast
    have hmeq : k * invLift p k ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ p).mp heq
    rw [hmeq, Nat.mod_eq_of_lt (Nat.Prime.one_lt Fact.out)]
  have hsub : (k * invLift p k - 1) % p = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (by rw [hmod, Nat.mod_eq_of_lt (Nat.Prime.one_lt Fact.out)])
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hsub
  refine ⟨t, ?_⟩
  rw [add_comm]
  exact (Nat.sub_eq_iff_eq_add hge).mp ht

lemma two_mul_fermat_eq_pow_sub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (p * fermatQuotientTwoNat p hp hp2) = 2 ^ p - 2 := by
  rw [fermatQuotientTwoNat_mul hp hp2, two_pow_p_eq hp hp2]

/-- `(2^p - 2)/p ≡ ∑_{k=1}^{p-1} (-1)^{k-1}/k (mod p)`. -/
lemma fermat_two_eq_altHarmonic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) * (fermatQuotientTwoNat p Fact.out hp2 : ZMod p) =
      altHarmonic p := by
  have hp : p.Prime := Fact.out
  let q := fermatQuotientTwoNat p hp hp2
  have hinterior := sum_choose_prime_interior hp
  -- For each k, write k * invLift k = 1 + p * t k.
  let t : ℕ → ℕ := fun k =>
    if h : 0 < k ∧ k < p then Classical.choose (invLift_mul_nat (p := p) h.1 h.2) else 0
  have ht : ∀ k, 0 < k → k < p → k * invLift p k = 1 + p * t k := by
    intro k hpos hlt
    have h := Classical.choose_spec (invLift_mul_nat (p := p) hpos hlt)
    simp only [t, dif_pos (And.intro hpos hlt)]
    exact h
  -- p * ∑ C(p-1, k-1) * invLift k = ∑ C(p,k) + p * ∑ C(p,k) * t k
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      p * ((p - 1).choose (k - 1) * invLift p k) =
        p.choose k + p * (p.choose k * t k) := by
    intro k hk
    have hpos : 0 < k := (mem_Icc.mp hk).1
    have hlt : k < p := lt_of_le_of_lt (mem_Icc.mp hk).2 (Nat.sub_lt hp.pos (by omega))
    have hch := choose_prime_mul p k hpos hp.pos
    have hkt := ht k hpos hlt
    -- k * C(p,k) * invLift = p * C(p-1,k-1) * invLift
    have := congrArg (fun n => n * invLift p k) hch.symm
    -- this: p * C(p-1,k-1) * invLift = k * C(p,k) * invLift
    calc
      p * ((p - 1).choose (k - 1) * invLift p k)
          = (p * (p - 1).choose (k - 1)) * invLift p k := by ring
      _ = (k * p.choose k) * invLift p k := by rw [hch]
      _ = p.choose k * (k * invLift p k) := by ring
      _ = p.choose k * (1 + p * t k) := by rw [hkt]
      _ = p.choose k + p * (p.choose k * t k) := by ring
  have hsum :
      p * ∑ k ∈ Icc 1 (p - 1), (p - 1).choose (k - 1) * invLift p k =
        ∑ k ∈ Icc 1 (p - 1), p.choose k +
          p * ∑ k ∈ Icc 1 (p - 1), p.choose k * t k := by
    rw [mul_sum, sum_congr rfl hterm, sum_add_distrib, mul_sum]
  rw [hinterior] at hsum
  have h2pq : 2 ^ p - 2 = 2 * (p * q) := (two_mul_fermat_eq_pow_sub hp hp2).symm
  rw [h2pq] at hsum
  -- cancel a factor of p
  have hppos : 0 < p := hp.pos
  have hcancel :
      ∑ k ∈ Icc 1 (p - 1), (p - 1).choose (k - 1) * invLift p k =
        2 * q + ∑ k ∈ Icc 1 (p - 1), p.choose k * t k := by
    have := hsum
    -- p * LHS = 2 * p * q + p * extra
    have : p * ∑ k ∈ Icc 1 (p - 1), (p - 1).choose (k - 1) * invLift p k =
        p * (2 * q + ∑ k ∈ Icc 1 (p - 1), p.choose k * t k) := by
      rw [hsum]
      ring
    exact Nat.eq_of_mul_eq_mul_left hppos this
  -- reduce mod p
  have hmod :
      (((∑ k ∈ Icc 1 (p - 1), (p - 1).choose (k - 1) * invLift p k : ℕ) : ZMod p)) =
        (2 : ZMod p) * (q : ZMod p) := by
    rw [hcancel, Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    have hextra :
        ((∑ k ∈ Icc 1 (p - 1), p.choose k * t k : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sum]
      apply sum_eq_zero
      intro k hk
      have hpos : 0 < k := (mem_Icc.mp hk).1
      have hlt : k < p := lt_of_le_of_lt (mem_Icc.mp hk).2 (Nat.sub_lt hp.pos (by omega))
      rw [Nat.cast_mul, choose_prime_eq_zero (Nat.pos_iff_ne_zero.mp hpos) hlt, zero_mul]
    rw [hextra, add_zero]
  -- identify the left-hand side with altHarmonic
  have hident :
      ((∑ k ∈ Icc 1 (p - 1), (p - 1).choose (k - 1) * invLift p k : ℕ) : ZMod p) =
        altHarmonic p := by
    rw [Nat.cast_sum]
    simp only [altHarmonic]
    refine sum_congr rfl ?_
    intro k hk
    have hpos : 0 < k := (mem_Icc.mp hk).1
    have hlt : k < p := lt_of_le_of_lt (mem_Icc.mp hk).2 (Nat.sub_lt hp.pos (by omega))
    have hk1 : k - 1 < p := lt_of_le_of_lt (Nat.sub_le k 1) hlt
    rw [Nat.cast_mul]
    have hch : (((p - 1).choose (k - 1) : ℕ) : ZMod p) = (-1 : ZMod p) ^ (k - 1) :=
      choose_p_sub_one hk1
    have hinv : (invLift p k : ZMod p) = ((k : ℕ) : ZMod p)⁻¹ := by
      simp only [invLift]
      exact ZMod.natCast_zmod_val _
    rw [hch, hinv]
  rw [← hident, hmod]

/-- `H_n ≡ -2 q_p(2) (mod p)`. -/
lemma harmonic_eq_neg_two_fermat {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    harmonicMod p ((p - 1) / 2) =
      -((2 : ZMod p) * (fermatQuotientTwoNat p Fact.out hp2 : ZMod p)) := by
  have h := altHarmonic_eq_neg_harmonic (p := p) hp2
  rw [← fermat_two_eq_altHarmonic hp2] at h
  exact (neg_eq_iff_eq_neg.mp h.symm)

lemma isUnit_two_quad {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (2 : Quad p) :=
  (isUnit_two_mod_p hp2).map (algebraMap (ZMod p) (Quad p))

lemma two_quad_mul_embed_inv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : Quad p) * ⟨(2 : ZMod p)⁻¹, 0⟩ = 1 := by
  have h2 := isUnit_two_mod_p hp2
  apply QuadraticAlgebra.ext
  · simp [re_mul]
    exact ZMod.mul_inv_of_unit _ h2
  · simp [im_mul]

lemma embed_oddHarmonic_eq {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    (⟨oddHarmonicMod p k, 0⟩ : Quad p) =
      ⟨(2 : ZMod p)⁻¹, 0⟩ *
        (⟨harmonicMod p ((p - 1) / 2 - k), 0⟩ -
          ⟨harmonicMod p ((p - 1) / 2), 0⟩) := by
  have h := oddHarmonicMod_eq_half_harmonic_sub (p := p) (k := k) hp2 hk
  apply QuadraticAlgebra.ext
  · simp [re_mul, h, sub_eq_add_neg]
  · simp [im_mul]

lemma pow_sub_mul_inv {R : Type*} [CommRing R] (z : R) (hz : IsUnit z)
    (n k : ℕ) (hk : k ≤ n) :
    z ^ (n - k) = z ^ n * ((↑hz.unit⁻¹ : R) ^ k) := by
  have hinv : z * (↑hz.unit⁻¹ : R) = 1 := hz.mul_val_inv
  have : z ^ n * (↑hz.unit⁻¹ : R) ^ k = z ^ (n - k + k) * (↑hz.unit⁻¹ : R) ^ k := by
    rw [Nat.sub_add_cancel hk]
  rw [this, pow_add, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]

lemma Qgen_via_R {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (z : Quad p)
    (hz : IsUnit z) :
    Qgen ((p - 1) / 2) z (fun k => (⟨oddHarmonicMod p k, 0⟩ : Quad p)) =
      ⟨(2 : ZMod p)⁻¹, 0⟩ *
        (z ^ ((p - 1) / 2) *
          Rgen ((p - 1) / 2) (↑hz.unit⁻¹ : Quad p)
            (fun k => (⟨harmonicMod p k, 0⟩ : Quad p)) -
          (⟨harmonicMod p ((p - 1) / 2), 0⟩ : Quad p) *
            Pgen ((p - 1) / 2) z) := by
  set n := (p - 1) / 2
  have hterm : ∀ k ∈ range (n + 1),
      (((n.choose k : ℕ) : Quad p) ^ 3) *
        (⟨oddHarmonicMod p k, 0⟩ : Quad p) * z ^ k =
      ⟨(2 : ZMod p)⁻¹, 0⟩ *
        ((((n.choose k : ℕ) : Quad p) ^ 3) *
          (⟨harmonicMod p (n - k), 0⟩ : Quad p) * z ^ k -
        (⟨harmonicMod p n, 0⟩ : Quad p) *
          (((n.choose k : ℕ) : Quad p) ^ 3) * z ^ k) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hO := embed_oddHarmonic_eq (p := p) (k := k) hp2 (by simpa [n] using hk')
    rw [hO]
    ring
  simp only [Qgen, Rgen, Pgen]
  -- unfold `n` in the goal sums
  change
      ∑ k ∈ range (n + 1),
          (((n.choose k : ℕ) : Quad p) ^ 3) *
            (⟨oddHarmonicMod p k, 0⟩ : Quad p) * z ^ k =
        ⟨(2 : ZMod p)⁻¹, 0⟩ *
          (z ^ n *
            ∑ k ∈ range (n + 1),
              (((n.choose k : ℕ) : Quad p) ^ 3) *
                (⟨harmonicMod p k, 0⟩ : Quad p) * (↑hz.unit⁻¹ : Quad p) ^ k -
            (⟨harmonicMod p n, 0⟩ : Quad p) *
              ∑ k ∈ range (n + 1),
                (((n.choose k : ℕ) : Quad p) ^ 3) * z ^ k)
  rw [sum_congr rfl hterm, ← mul_sum]
  have hsplit :
      ∑ k ∈ range (n + 1),
          ((((n.choose k : ℕ) : Quad p) ^ 3) *
            (⟨harmonicMod p (n - k), 0⟩ : Quad p) * z ^ k -
          (⟨harmonicMod p n, 0⟩ : Quad p) *
            (((n.choose k : ℕ) : Quad p) ^ 3) * z ^ k) =
        ∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad p) ^ 3) *
              (⟨harmonicMod p (n - k), 0⟩ : Quad p) * z ^ k -
        (⟨harmonicMod p n, 0⟩ : Quad p) *
          ∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad p) ^ 3) * z ^ k := by
    rw [sum_sub_distrib]
    congr 1
    refine Eq.trans ?_ (mul_sum _ _ _).symm
    refine sum_congr rfl ?_
    intro k _; ring
  rw [hsplit]
  have hreflect :
      ∑ k ∈ range (n + 1),
          (((n.choose k : ℕ) : Quad p) ^ 3) *
            (⟨harmonicMod p (n - k), 0⟩ : Quad p) * z ^ k =
        z ^ n *
          ∑ k ∈ range (n + 1),
            (((n.choose k : ℕ) : Quad p) ^ 3) *
              (⟨harmonicMod p k, 0⟩ : Quad p) * (↑hz.unit⁻¹ : Quad p) ^ k := by
    have hre := (sum_range_reflect
      (fun k => (((n.choose k : ℕ) : Quad p) ^ 3) *
        (⟨harmonicMod p (n - k), 0⟩ : Quad p) * z ^ k) (n + 1)).symm
    rw [hre]
    refine (sum_congr rfl ?_).trans (mul_sum _ _ _).symm
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hnk : n + 1 - 1 - k = n - k := by omega
    simp only [hnk]
    rw [Nat.choose_symm hk', Nat.sub_sub_self hk']
    have hpw : z ^ (n - k) = z ^ n * (↑hz.unit⁻¹ : Quad p) ^ k :=
      pow_sub_mul_inv z hz n k hk'
    rw [hpw]
    ring
  rw [hreflect]

lemma isUnit_z1_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (z1 p) :=
  let h128 := isUnit_128_mod_p hp2
  ⟨⟨z1 p, z2 p, z1_mul_z2 p h128, by rw [mul_comm]; exact z1_mul_z2 p h128⟩, rfl⟩

lemma isUnit_z2_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (z2 p) :=
  let h128 := isUnit_128_mod_p hp2
  ⟨⟨z2 p, z1 p, by rw [mul_comm]; exact z1_mul_z2 p h128, z1_mul_z2 p h128⟩, rfl⟩

lemma z2_eq_z1_unit_inv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    z2 p = (↑(isUnit_z1_mod_p hp2).unit⁻¹ : Quad p) := by
  have hz1 := isUnit_z1_mod_p hp2
  have hprod : z1 p * z2 p = 1 := z1_mul_z2 p (isUnit_128_mod_p hp2)
  apply hz1.mul_left_cancel
  rw [hz1.mul_val_inv, hprod]

lemma z1_eq_z2_unit_inv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    z1 p = (↑(isUnit_z2_mod_p hp2).unit⁻¹ : Quad p) := by
  have hz2 := isUnit_z2_mod_p hp2
  have hprod : z2 p * z1 p = 1 := by
    rw [mul_comm]
    exact z1_mul_z2 p (isUnit_128_mod_p hp2)
  apply hz2.mul_left_cancel
  rw [hz2.mul_val_inv, hprod]

lemma z2_pow_n_eq_one_mod_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp7 : p ≠ 7) (hsplit : legendreSym p (-7) = 1) :
    z2 p ^ ((p - 1) / 2) = 1 := by
  have hz1 := z1_pow_n_eq_one_of_split hp2 hp7 hsplit
  have h128 := isUnit_128_mod_p hp2
  have hprod := z1_mul_z2 p h128
  have : (z1 p * z2 p) ^ ((p - 1) / 2) = 1 := by
    rw [hprod, one_pow]
  rw [mul_pow, hz1, one_mul] at this
  exact this

lemma Pgen_z1_eq_Pgen_z2_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp7 : p ≠ 7) (hsplit : legendreSym p (-7) = 1) :
    Pgen ((p - 1) / 2) (z1 p) = Pgen ((p - 1) / 2) (z2 p) := by
  have h128 := isUnit_128_mod_p hp2
  have hfun := Pgen_z1_eq_z1_pow_mul_Pgen_z2 (n := (p - 1) / 2) h128
  have hz1 := z1_pow_n_eq_one_of_split hp2 hp7 hsplit
  rw [hfun, hz1, one_mul]

/-- When split, `Q(z₁) - Q(z₂) = 2⁻¹ (R(z₂) - R(z₁))`. -/
lemma Q_diff_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    let n := (p - 1) / 2
    let O : ℕ → Quad p := fun k => ⟨oddHarmonicMod p k, 0⟩
    let H : ℕ → Quad p := fun k => ⟨harmonicMod p k, 0⟩
    Qgen n (z1 p) O - Qgen n (z2 p) O =
      ⟨(2 : ZMod p)⁻¹, 0⟩ * (Rgen n (z2 p) H - Rgen n (z1 p) H) := by
  intro n O H
  have hz1 := isUnit_z1_mod_p hp2
  have hz2 := isUnit_z2_mod_p hp2
  have hQ1 := Qgen_via_R (p := p) hp2 (z1 p) hz1
  have hQ2 := Qgen_via_R (p := p) hp2 (z2 p) hz2
  have hinv1 : (↑hz1.unit⁻¹ : Quad p) = z2 p := (z2_eq_z1_unit_inv hp2).symm
  have hinv2 : (↑hz2.unit⁻¹ : Quad p) = z1 p := (z1_eq_z2_unit_inv hp2).symm
  have hpow1 : z1 p ^ n = 1 := by
    simpa [n] using z1_pow_n_eq_one_of_split hp2 hp7 hsplit
  have hpow2 : z2 p ^ n = 1 := by
    simpa [n] using z2_pow_n_eq_one_mod_p_of_split hp2 hp7 hsplit
  have hP : Pgen n (z1 p) = Pgen n (z2 p) := by
    simpa [n] using Pgen_z1_eq_Pgen_z2_of_split hp2 hp7 hsplit
  simp only [n, O, H] at hQ1 hQ2 ⊢
  rw [hQ1, hQ2, hinv1, hinv2, hpow1, hpow2, one_mul, one_mul, hP]
  ring

lemma two_pow_fermat_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod (p ^ 2)) ^ (p - 1) =
      1 + (p : ZMod (p ^ 2)) * (fermatQuotientTwoNat p hp hp2 : ZMod (p ^ 2)) := by
  have hmul := fermatQuotientTwoNat_mul hp hp2
  have hge : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by norm_num)
  have heq : 2 ^ (p - 1) = 1 + p * fermatQuotientTwoNat p hp hp2 := by omega
  have := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) heq
  simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using this

lemma twoAlphaQ_pow_p_sub_one_cast_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp7 : p ≠ 7) (hsplit : legendreSym p (-7) = 1) :
    quadCastHom (show 1 ≤ 2 by omega) (twoAlphaQ (p ^ 2) ^ (p - 1)) = 1 := by
  rw [map_pow]
  have hz : quadCastHom (show 1 ≤ 2 by omega) (twoAlphaQ (p ^ 2)) = twoAlphaQ (p ^ 1) := by
    apply QuadraticAlgebra.ext
    · simp [quadCastHom, twoAlphaQ]
      change ZMod.cast ((5 : ℕ) : ZMod (p ^ 2)) = ((5 : ℕ) : ZMod (p ^ 1))
      exact ZMod.cast_natCast (pow_dvd_pow p (show 1 ≤ 2 by omega)) 5
    · simp [quadCastHom, twoAlphaQ]
  rw [hz]
  have hpow : p ^ 1 = p := pow_one p
  rw [hpow]
  exact twoAlphaQ_pow_p_sub_one_of_split hp2 hp7 hsplit

lemma exists_epsAlpha_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ ε : Quad (p ^ 2),
      twoAlphaQ (p ^ 2) ^ (p - 1) = 1 + (p : Quad (p ^ 2)) * ε := by
  have hred := twoAlphaQ_pow_p_sub_one_cast_of_split hp2 hp7 hsplit
  have hz : quadCastHom (show 1 ≤ 2 by omega)
      (twoAlphaQ (p ^ 2) ^ (p - 1) - 1) = 0 := by
    rw [map_sub, hred, map_one, sub_self]
  have hre0 :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
        (twoAlphaQ (p ^ 2) ^ (p - 1) - 1).re = 0 := by
    have := congrArg QuadraticAlgebra.re hz
    simpa [quadCastHom] using this
  have him0 :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
        (twoAlphaQ (p ^ 2) ^ (p - 1) - 1).im = 0 := by
    have := congrArg QuadraticAlgebra.im hz
    simpa [quadCastHom] using this
  obtain ⟨ar, hr⟩ := (zmod_castHom_eq_zero_iff _).mp hre0
  obtain ⟨ai, hi⟩ := (zmod_castHom_eq_zero_iff _).mp him0
  refine ⟨⟨ar, ai⟩, ?_⟩
  apply QuadraticAlgebra.ext
  · have hsub : (twoAlphaQ (p ^ 2) ^ (p - 1) - 1).re =
        (twoAlphaQ (p ^ 2) ^ (p - 1)).re - 1 := by simp
    rw [hsub] at hr
    have hmul : ((p : Quad (p ^ 2)) * ⟨ar, ai⟩).re = (p : ZMod (p ^ 2)) * ar := by
      simp [re_mul]
    rw [sub_eq_iff_eq_add, add_comm] at hr
    simp [hmul]
    exact hr
  · have hsub : (twoAlphaQ (p ^ 2) ^ (p - 1) - 1).im =
        (twoAlphaQ (p ^ 2) ^ (p - 1)).im := by simp
    rw [hsub] at hi
    have hmul : ((p : Quad (p ^ 2)) * ⟨ar, ai⟩).im = (p : ZMod (p ^ 2)) * ai := by
      simp [im_mul]
    simp [hmul]
    exact hi

/-! ### The unit `μ = (1 + ω)/2` and the closed form of `z₁`. -/

/-- `μ = (1 + √-7)/2` in `Quad m`. -/
def muQ (m : ℕ) : Quad m := ⟨(2 : ZMod m)⁻¹, (2 : ZMod m)⁻¹⟩

/-- The conjugate `μ̄ = (1 - √-7)/2`. -/
def muQbar (m : ℕ) : Quad m := ⟨(2 : ZMod m)⁻¹, -((2 : ZMod m)⁻¹)⟩

lemma inv_two_right {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    ((2 : ZMod (p ^ e))⁻¹) * (2 : ZMod (p ^ e)) = 1 :=
  ZMod.inv_mul_of_unit _ (isUnit_two_zmod hp hodd he)

lemma inv_two_left {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (2 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹) = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_two_zmod hp hodd he)

lemma inv_two_sq_mul_four {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 1 := by
  have h := inv_two_right hp hodd he
  calc
    ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e)))
      = ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))) *
          ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))) := by ring
    _ = 1 := by rw [h, mul_one]

lemma cancel_four {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    {x y : ZMod (p ^ e)}
    (h : x * ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
      y * ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e)))) : x = y :=
  (isUnit_two_zmod hp hodd he |>.mul (isUnit_two_zmod hp hodd he)).mul_right_cancel h

lemma eight_mul_inv_two_sq_eq_two {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (8 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) = 2 := by
  apply cancel_four hp hodd he
  have hsq := inv_two_sq_mul_four hp hodd he
  have : (8 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
      (8 : ZMod (p ^ e)) * (((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e)))) := by ring
  rw [this, hsq, mul_one]
  norm_num

lemma six_mul_inv_two_sq_eq_three_inv_two {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (6 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) =
      3 * ((2 : ZMod (p ^ e))⁻¹) := by
  apply cancel_four hp hodd he
  have hsq := inv_two_sq_mul_four hp hodd he
  have hr := inv_two_right hp hodd he
  have hL : (6 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 6 := by
    have : (6 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
        6 * (((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
          ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e)))) := by ring
    rw [this, hsq, mul_one]
  have hR : (3 * ((2 : ZMod (p ^ e))⁻¹)) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 6 := by
    have : (3 * ((2 : ZMod (p ^ e))⁻¹)) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
        3 * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))) * 2 := by ring
    rw [this, hr, mul_one]; norm_num
  exact hL.trans hR.symm

lemma two_mul_inv_two_sq_eq_inv_two {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (2 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) =
      (2 : ZMod (p ^ e))⁻¹ := by
  apply cancel_four hp hodd he
  have hsq := inv_two_sq_mul_four hp hodd he
  have hr := inv_two_right hp hodd he
  have hL : (2 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 2 := by
    have : (2 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
        2 * (((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
          ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e)))) := by ring
    rw [this, hsq, mul_one]
  have hR : ((2 : ZMod (p ^ e))⁻¹) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 2 := by
    have : ((2 : ZMod (p ^ e))⁻¹) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
        ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))) * 2 := by ring
    rw [this, hr, one_mul]
  exact hL.trans hR.symm

lemma ten_mul_inv_two_sq_eq_five_inv_two {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (10 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) =
      5 * ((2 : ZMod (p ^ e))⁻¹) := by
  apply cancel_four hp hodd he
  have hsq := inv_two_sq_mul_four hp hodd he
  have hr := inv_two_right hp hodd he
  have hL : (10 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 10 := by
    have : (10 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
        10 * (((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) *
          ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e)))) := by ring
    rw [this, hsq, mul_one]
  have hR : (5 * ((2 : ZMod (p ^ e))⁻¹)) *
      ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) = 10 := by
    have : (5 * ((2 : ZMod (p ^ e))⁻¹)) *
        ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))) =
        5 * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))) * 2 := by ring
    rw [this, hr, mul_one]; norm_num
  exact hL.trans hR.symm

lemma muQ_mul_muQbar {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    muQ (p ^ e) * muQbar (p ^ e) = 2 := by
  apply QuadraticAlgebra.ext
  · simp [muQ, muQbar]
    have : (2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹ +
        (7 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹ =
        (8 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹) := by ring
    rw [this, eight_mul_inv_two_sq_eq_two hp hodd he]
  · simp [muQ, muQbar]

lemma muQ_sq {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    muQ (p ^ e) ^ 2 =
      ⟨-3 * ((2 : ZMod (p ^ e))⁻¹), (2 : ZMod (p ^ e))⁻¹⟩ := by
  apply QuadraticAlgebra.ext
  · simp [muQ, pow_two]
    trans -((6 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹))
    · ring
    · rw [six_mul_inv_two_sq_eq_three_inv_two hp hodd he]
  · simp [muQ, pow_two]
    trans (2 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹)
    · ring
    · exact two_mul_inv_two_sq_eq_inv_two hp hodd he

lemma muQ_pow_three {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    muQ (p ^ e) ^ 3 =
      ⟨-5 * ((2 : ZMod (p ^ e))⁻¹), -((2 : ZMod (p ^ e))⁻¹)⟩ := by
  rw [pow_succ, muQ_sq hp hodd he]
  apply QuadraticAlgebra.ext
  · simp [muQ]
    trans -((10 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹))
    · ring
    · rw [ten_mul_inv_two_sq_eq_five_inv_two hp hodd he]
  · simp [muQ]
    trans -((2 : ZMod (p ^ e)) * ((2 : ZMod (p ^ e))⁻¹ * (2 : ZMod (p ^ e))⁻¹))
    · ring
    · rw [two_mul_inv_two_sq_eq_inv_two hp hodd he]

lemma twoAlphaQ_eq_neg_two_mu_cubed {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    twoAlphaQ (p ^ e) = -2 * muQ (p ^ e) ^ 3 := by
  have hl := inv_two_left hp hodd he
  rw [muQ_pow_three hp hodd he]
  apply QuadraticAlgebra.ext
  · simp [twoAlphaQ]
    have : (2 : ZMod (p ^ e)) * (5 * (2 : ZMod (p ^ e))⁻¹) =
        5 * ((2 : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹) := by ring
    rw [this, hl, mul_one]
  · simp [twoAlphaQ]
    exact hl.symm

lemma twoAlphaQ_pow_four_eq_sixteen_mu_pow_twelve
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    twoAlphaQ (p ^ e) ^ 4 = 16 * muQ (p ^ e) ^ 12 := by
  have h := twoAlphaQ_eq_neg_two_mu_cubed hp hodd he
  have h4 : twoAlphaQ (p ^ e) ^ 4 = (-2 * muQ (p ^ e) ^ 3) ^ 4 := by
    rw [h]
  rw [h4]
  have : (-2 * muQ (p ^ e) ^ 3) ^ 4 = (16 : Quad (p ^ e)) * muQ (p ^ e) ^ 12 := by
    have hneg : (-2 : Quad (p ^ e)) ^ 4 = 16 := by
      have : (-2 : Quad (p ^ e)) = ⟨-2, 0⟩ := by
        apply QuadraticAlgebra.ext <;> simp
      rw [this, C_pow]
      apply QuadraticAlgebra.ext
      · simp; norm_num
      · simp
    rw [mul_pow, hneg, ← pow_mul]
  exact this

lemma z1_eq_mu_pow_twelve_div_sixtyfour
    {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e) :
    (64 : Quad (p ^ e)) * z1 (p ^ e) = muQ (p ^ e) ^ 12 := by
  have h1024 := z1_eq_twoAlpha_pow_four hp hodd he
  have hα := twoAlphaQ_pow_four_eq_sixteen_mu_pow_twelve hp hodd he
  -- `1024 * z1 = twoAlpha^4 = 16 * μ^12`, so `64 * z1 = μ^12`
  have h16 : (1024 : Quad (p ^ e)) = 16 * 64 := by
    apply QuadraticAlgebra.ext <;> simp; norm_num
  have h1024z : (1024 : Quad (p ^ e)) * z1 (p ^ e) = 16 * muQ (p ^ e) ^ 12 := by
    rw [h1024, hα]
  have h16u : IsUnit (16 : ZMod (p ^ e)) := by
    have h2 := isUnit_two_zmod hp hodd he
    have : (16 : ZMod (p ^ e)) = (2 : ZMod (p ^ e)) ^ 4 := by norm_num
    rw [this]; exact h2.pow 4
  -- cancel the real unit 16
  have h16Q : (16 : Quad (p ^ e)) = ⟨16, 0⟩ := by
    apply QuadraticAlgebra.ext <;> simp
  have h16Qu : IsUnit (16 : Quad (p ^ e)) := by
    rw [h16Q, QuadraticAlgebra.isUnit_iff_norm_isUnit]
    simpa [QuadraticAlgebra.norm_def] using h16u
  apply h16Qu.mul_left_cancel
  calc
    (16 : Quad (p ^ e)) * ((64 : Quad (p ^ e)) * z1 (p ^ e))
      = ((16 : Quad (p ^ e)) * 64) * z1 (p ^ e) := by ring
    _ = (1024 : Quad (p ^ e)) * z1 (p ^ e) := by
          have : (16 : Quad (p ^ e)) * 64 = 1024 := by
            apply QuadraticAlgebra.ext <;> simp; norm_num
          rw [this]
    _ = 16 * muQ (p ^ e) ^ 12 := h1024z

lemma sixtyfour_pow_n_fermat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (64 : ZMod (p ^ 2)) ^ ((p - 1) / 2) =
      1 + (p : ZMod (p ^ 2)) *
        (3 * (fermatQuotientTwoNat p hp hp2 : ZMod (p ^ 2))) := by
  have h2 := two_pow_fermat_zmod hp hp2
  have h64 : (64 : ZMod (p ^ 2)) = (2 : ZMod (p ^ 2)) ^ 6 := by norm_num
  have hn : 6 * ((p - 1) / 2) = 3 * (p - 1) := by
    have : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd hp hp2
    omega
  rw [h64, ← pow_mul, hn]
  have : (2 : ZMod (p ^ 2)) ^ (3 * (p - 1)) = ((2 : ZMod (p ^ 2)) ^ (p - 1)) ^ 3 := by
    rw [mul_comm, pow_mul]
  rw [this, h2]
  have hp2z : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
    p_mul_p_eq_zero_mod_p_sq hp
  set q : ZMod (p ^ 2) := (fermatQuotientTwoNat p hp hp2 : ZMod (p ^ 2))
  set pp : ZMod (p ^ 2) := (p : ZMod (p ^ 2))
  have : (1 + pp * q) ^ 3 = 1 + pp * (3 * q) := by
    have hexp : (1 + pp * q) ^ 3 =
        1 + 3 * (pp * q) + 3 * (pp * q) ^ 2 + (pp * q) ^ 3 := by ring
    have hsq : (pp * q) ^ 2 = 0 := by
      calc
        (pp * q) ^ 2 = (pp * q) * (pp * q) := pow_two _
        _ = (pp * pp) * (q * q) := by ring
        _ = 0 * (q * q) := by rw [hp2z]
        _ = 0 := zero_mul _
    have hcu : (pp * q) ^ 3 = 0 := by
      calc
        (pp * q) ^ 3 = (pp * q) ^ 2 * (pp * q) := pow_succ _ _
        _ = 0 * (pp * q) := by rw [hsq]
        _ = 0 := zero_mul _
    rw [hexp, hsq, hcu]
    ring
  exact this

lemma one_zero_two_four_pow_n_fermat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (1024 : ZMod (p ^ 2)) ^ ((p - 1) / 2) =
      1 + (p : ZMod (p ^ 2)) *
        (5 * (fermatQuotientTwoNat p hp hp2 : ZMod (p ^ 2))) := by
  have h2 := two_pow_fermat_zmod hp hp2
  have h1024 : (1024 : ZMod (p ^ 2)) = (2 : ZMod (p ^ 2)) ^ 10 := by norm_num
  have hn : 10 * ((p - 1) / 2) = 5 * (p - 1) := by
    have : 2 * ((p - 1) / 2) = p - 1 := two_mul_half_odd hp hp2
    omega
  rw [h1024, ← pow_mul, hn]
  have : (2 : ZMod (p ^ 2)) ^ (5 * (p - 1)) = ((2 : ZMod (p ^ 2)) ^ (p - 1)) ^ 5 := by
    rw [mul_comm, pow_mul]
  rw [this, h2]
  have hp2z : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 :=
    p_mul_p_eq_zero_mod_p_sq hp
  set q : ZMod (p ^ 2) := (fermatQuotientTwoNat p hp hp2 : ZMod (p ^ 2))
  set pp : ZMod (p ^ 2) := (p : ZMod (p ^ 2))
  have hsq : (pp * q) ^ 2 = 0 := by
    calc
      (pp * q) ^ 2 = (pp * q) * (pp * q) := pow_two _
      _ = (pp * pp) * (q * q) := by ring
      _ = 0 * (q * q) := by rw [hp2z]
      _ = 0 := zero_mul _
  have : (1 + pp * q) ^ 5 = 1 + pp * (5 * q) := by
    have hexp : (1 + pp * q) ^ 5 =
        1 + 5 * (pp * q) + 10 * (pp * q) ^ 2 + 10 * (pp * q) ^ 3 +
          5 * (pp * q) ^ 4 + (pp * q) ^ 5 := by ring
    have hcu : (pp * q) ^ 3 = 0 := by
      calc
        (pp * q) ^ 3 = (pp * q) ^ 2 * (pp * q) := pow_succ _ _
        _ = 0 * (pp * q) := by rw [hsq]
        _ = 0 := zero_mul _
    have hp4 : (pp * q) ^ 4 = 0 := by
      calc
        (pp * q) ^ 4 = (pp * q) ^ 3 * (pp * q) := pow_succ _ _
        _ = 0 * (pp * q) := by rw [hcu]
        _ = 0 := zero_mul _
    have hp5 : (pp * q) ^ 5 = 0 := by
      calc
        (pp * q) ^ 5 = (pp * q) ^ 4 * (pp * q) := pow_succ _ _
        _ = 0 * (pp * q) := by rw [hp4]
        _ = 0 := zero_mul _
    rw [hexp, hsq, hcu, hp4, hp5]
    ring
  exact this

lemma C_pow_nat (m n : ℕ) (c : ℕ) :
    ((c : Quad m) ^ n) = ⟨((c : ZMod m) ^ n), 0⟩ := by
  have : (c : Quad m) = ⟨(c : ZMod m), 0⟩ := by
    apply QuadraticAlgebra.ext <;> simp
  rw [this, C_pow]

/-- In `ZMod p`, `C((p-1)/2, k) ≡ C(2k,k) (-4)^{-k}`. -/
lemma choose_half_mod_p {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : k ≤ (p - 1) / 2) :
    ((((p - 1) / 2).choose k : ℕ) : ZMod p) =
      (((2 * k).choose k : ℕ) : ZMod p) *
        ((-4 : ZMod p)⁻¹) ^ k := by
  have hp : p.Prime := Fact.out
  have he : (0 : ℕ) < 1 := by omega
  have h := choose_half_zmod (p := p) (e := 1) (k := k) hp hp2 he hk
  have hPi : PiMod p 1 k = 1 := by
    simp only [PiMod]
    refine prod_eq_one ?_
    intro j _hj
    have : (p : ZMod (p ^ 1)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_one]
    rw [this, zero_mul, sub_zero]
  rw [hPi, mul_one] at h
  have h4 : IsUnit (4 : ZMod (p ^ 1)) := isUnit_four_zmod hp hp2 he
  have hneg4 : ((-1 : ZMod (p ^ 1)) * (4 : ZMod (p ^ 1))⁻¹) = (-4 : ZMod (p ^ 1))⁻¹ := by
    have h4' : IsUnit (-4 : ZMod (p ^ 1)) := h4.neg
    apply h4'.mul_left_cancel
    have h4inv : (4 : ZMod (p ^ 1)) * (4 : ZMod (p ^ 1))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ h4
    calc
      (-4 : ZMod (p ^ 1)) * ((-1 : ZMod (p ^ 1)) * (4 : ZMod (p ^ 1))⁻¹)
        = (4 : ZMod (p ^ 1)) * (4 : ZMod (p ^ 1))⁻¹ := by ring
      _ = 1 := h4inv
      _ = (-4 : ZMod (p ^ 1)) * (-4 : ZMod (p ^ 1))⁻¹ :=
            (ZMod.mul_inv_of_unit _ h4').symm
  rw [hneg4] at h
  have hpow : p ^ 1 = p := pow_one p
  rw [hpow] at h
  exact h

lemma legendre_neg_seven_eq_neg_one_of_not_split {p : ℕ} [Fact p.Prime]
    (_hp2 : p ≠ 2) (hp7 : p ≠ 7) (hns : ¬ legendreSym p (-7) = 1) :
    legendreSym p (-7) = -1 := by
  have ha0 : ((-7 : ℤ) : ZMod p) ≠ 0 := by
    simpa using neg_seven_ne_zero hp7
  rcases legendreSym.eq_one_or_neg_one (p := p) (a := (-7 : ℤ)) ha0 with h1 | h1
  · exact (hns h1).elim
  · exact h1

/-- Reduction of `Usum` from `p^2` to `p`. -/
lemma Usum_two_castHom_one {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) (Usum p 2) =
      Usum p 1 :=
  Usum_castHom hp hodd (by omega) (by omega)

/-- Multiplication by `p` on `ZMod (p^2)` vanishes iff the argument reduces to `0` mod `p`. -/
lemma p_lt_p_sq {p : ℕ} (hp : p.Prime) : p < p ^ 2 := by
  have : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
  simpa [pow_two] using this

lemma p_mul_eq_zero_iff {p : ℕ} [Fact p.Prime] (y : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * y = 0 ↔
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) y = 0 := by
  constructor
  · intro hy
    haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Nat.Prime.ne_zero Fact.out)⟩
    have hval0 : ZMod.val ((p : ZMod (p ^ 2)) * y) = 0 := by
      rw [hy, ZMod.val_zero]
    have hp_lt : p < p ^ 2 := p_lt_p_sq Fact.out
    have hvmul : ZMod.val ((p : ZMod (p ^ 2)) * y) = (p * y.val) % (p ^ 2) := by
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hp_lt]
    rw [hvmul] at hval0
    have hdivp2 : p ^ 2 ∣ p * y.val := Nat.dvd_of_mod_eq_zero hval0
    have hppos : 0 < p := Nat.Prime.pos Fact.out
    have hdiv : p ∣ y.val := by
      have hpp : p * p ∣ p * y.val := by
        convert hdivp2 using 1
        exact (pow_two p).symm
      exact Nat.dvd_of_mul_dvd_mul_left hppos hpp
    have hxval : (y.val : ZMod (p ^ 1)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_one]
      exact hdiv
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact hxval
  · intro hy
    obtain ⟨z, rfl⟩ := (zmod_castHom_eq_zero_iff y).mp hy
    rw [← mul_assoc, p_mul_p_eq_zero_mod_p_sq Fact.out, zero_mul]

lemma Ssum_two_eq_zero_of_T1_red {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {T1 : ZMod (p ^ 2)} (hT : Tsum p 2 = (p : ZMod (p ^ 2)) * T1)
    (hred : (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
      (T1 + 3 * Usum p 2) = 0) :
    Ssum p 2 = 0 := by
  have hS : Ssum p 2 = (p : ZMod (p ^ 2)) * (T1 + 3 * Usum p 2) := by
    rw [Ssum_eq_T_add_three_p_U Fact.out hp2, hT]; ring
  rw [hS, (p_mul_eq_zero_iff _).mpr hred]

lemma delta_eq_two_eps_sub_five_q2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ (δ ε : Quad (p ^ 2)),
      z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ ∧
      twoAlphaQ (p ^ 2) ^ (p - 1) = 1 + (p : Quad (p ^ 2)) * ε ∧
      (1024 : Quad (p ^ 2)) ^ ((p - 1) / 2) *
        (1 + (p : Quad (p ^ 2)) * δ) =
      (1 + (p : Quad (p ^ 2)) * ε) ^ 2 := by
  obtain ⟨δ, hδ⟩ := exists_delta_of_split hp2 hp7 hsplit
  obtain ⟨ε, hε⟩ := exists_epsAlpha_of_split hp2 hp7 hsplit
  refine ⟨δ, ε, hδ, hε, ?_⟩
  have he : (0 : ℕ) < 2 := by omega
  have hrel := z1_eq_twoAlpha_pow_four (p := p) (e := 2) Fact.out hp2 he
  -- `1024 * z1 = twoAlpha^4`, raise to n
  have hn : 4 * ((p - 1) / 2) = 2 * (p - 1) := by
    have := two_mul_half_odd Fact.out hp2
    omega
  have hzpow :
      (1024 : Quad (p ^ 2)) ^ ((p - 1) / 2) * z1 (p ^ 2) ^ ((p - 1) / 2) =
        twoAlphaQ (p ^ 2) ^ (2 * (p - 1)) := by
    rw [← mul_pow, hrel, ← pow_mul, hn]
  rw [hδ] at hzpow
  have hε2 : twoAlphaQ (p ^ 2) ^ (2 * (p - 1)) =
      (1 + (p : Quad (p ^ 2)) * ε) ^ 2 := by
    rw [mul_comm, pow_mul, hε]
  rw [hε2] at hzpow
  exact hzpow

lemma omega_pow_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    (omega : Quad p) ^ p = omega := by
  rw [omega_pow_p_eq hp2, euler_neg_seven hp7, hsplit]
  have : ((1 : ℤ) : ZMod p) = 1 := by simp
  rw [this]
  apply QuadraticAlgebra.ext <;> simp

lemma muQ_eq_half_one_add_omega {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    muQ p = ⟨(2 : ZMod p)⁻¹, 0⟩ * (1 + (omega : Quad p)) := by
  apply QuadraticAlgebra.ext
  · simp [muQ]
  · simp [muQ]

lemma two_mul_inv_two_quad {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : Quad p) * ⟨(2 : ZMod p)⁻¹, 0⟩ = 1 := by
  apply QuadraticAlgebra.ext
  · simp
    exact ZMod.mul_inv_of_unit _ (isUnit_two_mod_p hp2)
  · simp

lemma isUnit_muQ_mod_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (muQ p) := by
  have hmul : muQ p * muQbar p = 2 := by
    have he : (0 : ℕ) < 1 := by omega
    have h := muQ_mul_muQbar (p := p) (e := 1) Fact.out hp2 he
    rwa [pow_one] at h
  refine ⟨⟨muQ p, muQbar p * ⟨(2 : ZMod p)⁻¹, 0⟩, ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, hmul, two_mul_inv_two_quad hp2]
  · have hcomm : muQbar p * muQ p = 2 := by rw [mul_comm, hmul]
    calc
      muQbar p * ⟨(2 : ZMod p)⁻¹, 0⟩ * muQ p
        = muQbar p * (⟨(2 : ZMod p)⁻¹, 0⟩ * muQ p) := by rw [mul_assoc]
      _ = muQbar p * (muQ p * ⟨(2 : ZMod p)⁻¹, 0⟩) := by
            rw [mul_comm (⟨(2 : ZMod p)⁻¹, 0⟩ : Quad p)]
      _ = (muQbar p * muQ p) * ⟨(2 : ZMod p)⁻¹, 0⟩ := by rw [mul_assoc]
      _ = (2 : Quad p) * ⟨(2 : ZMod p)⁻¹, 0⟩ := by rw [hcomm]
      _ = 1 := two_mul_inv_two_quad hp2

lemma one_add_omega_pow_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    (1 + (omega : Quad p)) ^ p = 1 + (omega : Quad p) := by
  rw [freshman_quad, one_pow, omega_pow_p_of_split hp2 hp7 hsplit]

lemma inv_two_pow_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((2 : ZMod p)⁻¹) ^ p = (2 : ZMod p)⁻¹ := by
  have h2 := isUnit_two_mod_p hp2
  have hcard : ∀ x : ZMod p, x ^ p = x := by
    intro x
    have h := FiniteField.pow_card x
    have hc : Fintype.card (ZMod p) = p := ZMod.card p
    rwa [hc] at h
  exact hcard _

lemma C_inv_two_pow_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (⟨(2 : ZMod p)⁻¹, 0⟩ : Quad p) ^ p = ⟨(2 : ZMod p)⁻¹, 0⟩ := by
  rw [C_pow, inv_two_pow_p hp2]

lemma muQ_pow_p_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    muQ p ^ p = muQ p := by
  rw [muQ_eq_half_one_add_omega hp2, mul_pow, C_inv_two_pow_p hp2,
    one_add_omega_pow_p_of_split hp2 hp7 hsplit]

lemma muQ_pow_p_sub_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    muQ p ^ (p - 1) = 1 := by
  have hμ := isUnit_muQ_mod_p hp2
  have hp : muQ p ^ p = muQ p := muQ_pow_p_of_split hp2 hp7 hsplit
  have hpeq : muQ p ^ p = muQ p ^ (p - 1) * muQ p := by
    have hpos : 1 ≤ p := Nat.Prime.one_le Fact.out
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  rw [hpeq] at hp
  apply hμ.mul_right_cancel
  rw [hp, one_mul]

lemma castHom_inv_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
      ((2 : ZMod (p ^ 2))⁻¹) = (2 : ZMod (p ^ 1))⁻¹ := by
  have h2u : IsUnit ((2 : ℕ) : ZMod (p ^ 2)) :=
    isUnit_two_zmod Fact.out hp2 (by omega : (0 : ℕ) < 2)
  apply Eq.symm
  apply inv_eq_of_mul_eq_one_zmod
  have h2L : (2 : ZMod (p ^ 2)) = ((2 : ℕ) : ZMod (p ^ 2)) := by norm_num
  have h2R : (2 : ZMod (p ^ 1)) = ((2 : ℕ) : ZMod (p ^ 1)) := by norm_num
  have h2cast : (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
      ((2 : ℕ) : ZMod (p ^ 2)) = ((2 : ℕ) : ZMod (p ^ 1)) := map_natCast _ 2
  have hinv2 : (2 : ZMod (p ^ 2))⁻¹ = ((2 : ℕ) : ZMod (p ^ 2))⁻¹ := by rw [h2L]
  calc
    (2 : ZMod (p ^ 1)) *
        (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
          ((2 : ZMod (p ^ 2))⁻¹)
      = ((2 : ℕ) : ZMod (p ^ 1)) *
        (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
          (((2 : ℕ) : ZMod (p ^ 2))⁻¹) := by rw [h2R, hinv2]
    _ = (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
          ((2 : ℕ) : ZMod (p ^ 2)) *
        (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
          (((2 : ℕ) : ZMod (p ^ 2))⁻¹) := by rw [h2cast]
    _ = (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
          (((2 : ℕ) : ZMod (p ^ 2)) * ((2 : ℕ) : ZMod (p ^ 2))⁻¹) := by
            rw [map_mul]
    _ = (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) 1 := by
          rw [ZMod.mul_inv_of_unit _ h2u]
    _ = 1 := map_one _

lemma quadCastHom_muQ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    quadCastHom (show 1 ≤ 2 by omega) (muQ (p ^ 2)) = muQ (p ^ 1) := by
  apply QuadraticAlgebra.ext
  · simp only [quadCastHom, muQ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    exact castHom_inv_two hp2
  · simp only [quadCastHom, muQ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    exact castHom_inv_two hp2

lemma muQ_pow_p_sub_one_cast_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp7 : p ≠ 7) (hsplit : legendreSym p (-7) = 1) :
    quadCastHom (show 1 ≤ 2 by omega) (muQ (p ^ 2) ^ (p - 1)) = 1 := by
  rw [map_pow, quadCastHom_muQ hp2]
  have hpow : p ^ 1 = p := pow_one p
  rw [hpow]
  exact muQ_pow_p_sub_one_of_split hp2 hp7 hsplit

lemma exists_qmu_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ qμ : Quad (p ^ 2),
      muQ (p ^ 2) ^ (p - 1) = 1 + (p : Quad (p ^ 2)) * qμ := by
  have hred := muQ_pow_p_sub_one_cast_of_split hp2 hp7 hsplit
  have hz : quadCastHom (show 1 ≤ 2 by omega)
      (muQ (p ^ 2) ^ (p - 1) - 1) = 0 := by
    rw [map_sub, hred, map_one, sub_self]
  have hre0 :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
        (muQ (p ^ 2) ^ (p - 1) - 1).re = 0 := by
    have := congrArg QuadraticAlgebra.re hz
    simpa [quadCastHom] using this
  have him0 :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1)))
        (muQ (p ^ 2) ^ (p - 1) - 1).im = 0 := by
    have := congrArg QuadraticAlgebra.im hz
    simpa [quadCastHom] using this
  obtain ⟨ar, hr⟩ := (zmod_castHom_eq_zero_iff _).mp hre0
  obtain ⟨ai, hi⟩ := (zmod_castHom_eq_zero_iff _).mp him0
  refine ⟨⟨ar, ai⟩, ?_⟩
  apply QuadraticAlgebra.ext
  · have hsub : (muQ (p ^ 2) ^ (p - 1) - 1).re =
        (muQ (p ^ 2) ^ (p - 1)).re - 1 := by simp
    rw [hsub] at hr
    have hmul : ((p : Quad (p ^ 2)) * ⟨ar, ai⟩).re = (p : ZMod (p ^ 2)) * ar := by
      simp [re_mul]
    rw [sub_eq_iff_eq_add, add_comm] at hr
    simp [hmul]
    exact hr
  · have hsub : (muQ (p ^ 2) ^ (p - 1) - 1).im =
        (muQ (p ^ 2) ^ (p - 1)).im := by simp
    rw [hsub] at hi
    have hmul : ((p : Quad (p ^ 2)) * ⟨ar, ai⟩).im = (p : ZMod (p ^ 2)) * ai := by
      simp [im_mul]
    simp [hmul]
    exact hi

lemma p_mul_p_eq_zero_quad {p : ℕ} (hp : p.Prime) :
    (p : Quad (p ^ 2)) * (p : Quad (p ^ 2)) = 0 := by
  apply QuadraticAlgebra.ext
  · simp
    exact p_mul_p_eq_zero_mod_p_sq hp
  · simp

lemma one_add_p_pow_six {p : ℕ} (hp : p.Prime) (q : Quad (p ^ 2)) :
    (1 + (p : Quad (p ^ 2)) * q) ^ 6 =
      1 + (p : Quad (p ^ 2)) * (6 * q) := by
  set pp : Quad (p ^ 2) := (p : Quad (p ^ 2))
  have hp2z : pp * pp = 0 := p_mul_p_eq_zero_quad hp
  have hsq : (pp * q) ^ 2 = 0 := by
    calc
      (pp * q) ^ 2 = (pp * q) * (pp * q) := pow_two _
      _ = (pp * pp) * (q * q) := by ring
      _ = 0 * (q * q) := by rw [hp2z]
      _ = 0 := zero_mul _
  have hexp : (1 + pp * q) ^ 6 =
      1 + 6 * (pp * q) + 15 * (pp * q) ^ 2 + 20 * (pp * q) ^ 3 +
        15 * (pp * q) ^ 4 + 6 * (pp * q) ^ 5 + (pp * q) ^ 6 := by ring
  have hcu : (pp * q) ^ 3 = 0 := by
    calc
      (pp * q) ^ 3 = (pp * q) ^ 2 * (pp * q) := pow_succ _ _
      _ = 0 * (pp * q) := by rw [hsq]
      _ = 0 := zero_mul _
  have hp4 : (pp * q) ^ 4 = 0 := by
    calc
      (pp * q) ^ 4 = (pp * q) ^ 3 * (pp * q) := pow_succ _ _
      _ = 0 * (pp * q) := by rw [hcu]
      _ = 0 := zero_mul _
  have hp5 : (pp * q) ^ 5 = 0 := by
    calc
      (pp * q) ^ 5 = (pp * q) ^ 4 * (pp * q) := pow_succ _ _
      _ = 0 * (pp * q) := by rw [hp4]
      _ = 0 := zero_mul _
  have hp6 : (pp * q) ^ 6 = 0 := by
    calc
      (pp * q) ^ 6 = (pp * q) ^ 5 * (pp * q) := pow_succ _ _
      _ = 0 * (pp * q) := by rw [hp5]
      _ = 0 := zero_mul _
  rw [hexp, hsq, hcu, hp4, hp5, hp6]
  ring

lemma sixtyfour_pow_n_fermat_quad {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (64 : Quad (p ^ 2)) ^ ((p - 1) / 2) =
      1 + (p : Quad (p ^ 2)) *
        ⟨3 * (fermatQuotientTwoNat p hp hp2 : ZMod (p ^ 2)), 0⟩ := by
  have h := sixtyfour_pow_n_fermat hp hp2
  have h64 : (64 : Quad (p ^ 2)) = ⟨(64 : ZMod (p ^ 2)), 0⟩ := by
    apply QuadraticAlgebra.ext <;> simp
  rw [h64, C_pow]
  apply QuadraticAlgebra.ext
  · simp
    exact h
  · simp

lemma z1_pow_n_mul_sixtyfour_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (64 : Quad (p ^ 2)) ^ ((p - 1) / 2) * z1 (p ^ 2) ^ ((p - 1) / 2) =
      muQ (p ^ 2) ^ (6 * (p - 1)) := by
  have he : (0 : ℕ) < 2 := by omega
  have hrel := z1_eq_mu_pow_twelve_div_sixtyfour (p := p) (e := 2) Fact.out hp2 he
  have hn : 12 * ((p - 1) / 2) = 6 * (p - 1) := by
    have := two_mul_half_odd Fact.out hp2
    omega
  have : (64 : Quad (p ^ 2)) ^ ((p - 1) / 2) * z1 (p ^ 2) ^ ((p - 1) / 2) =
      (muQ (p ^ 2) ^ 12) ^ ((p - 1) / 2) := by
    rw [← mul_pow, hrel]
  rw [this, ← pow_mul, hn]

lemma muQ_pow_six_p_sub_one_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp7 : p ≠ 7) (hsplit : legendreSym p (-7) = 1) :
    ∃ qμ : Quad (p ^ 2),
      muQ (p ^ 2) ^ (6 * (p - 1)) =
        1 + (p : Quad (p ^ 2)) * (6 * qμ) := by
  obtain ⟨qμ, hq⟩ := exists_qmu_of_split hp2 hp7 hsplit
  refine ⟨qμ, ?_⟩
  have : muQ (p ^ 2) ^ (6 * (p - 1)) = (muQ (p ^ 2) ^ (p - 1)) ^ 6 := by
    rw [mul_comm, pow_mul]
  rw [this, hq, one_add_p_pow_six Fact.out]

/-- Reducing `δ` modulo `p` yields `6 q_μ - 3 q_2` in `Quad p`. -/
lemma delta_reduce_eq_fermat {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ (δ qμ : Quad (p ^ 2)),
      z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ ∧
      muQ (p ^ 2) ^ (p - 1) = 1 + (p : Quad (p ^ 2)) * qμ ∧
      (p : Quad (p ^ 2)) *
        (δ + ⟨3 * (fermatQuotientTwoNat p Fact.out hp2 : ZMod (p ^ 2)), 0⟩ - 6 * qμ) = 0 := by
  obtain ⟨δ, hδ⟩ := exists_delta_of_split hp2 hp7 hsplit
  obtain ⟨qμ, hqμ⟩ := exists_qmu_of_split hp2 hp7 hsplit
  refine ⟨δ, qμ, hδ, hqμ, ?_⟩
  have h64 := sixtyfour_pow_n_fermat_quad Fact.out hp2
  have hprod := z1_pow_n_mul_sixtyfour_pow (p := p) hp2
  have hmu : muQ (p ^ 2) ^ (6 * (p - 1)) =
      1 + (p : Quad (p ^ 2)) * (6 * qμ) := by
    have : muQ (p ^ 2) ^ (6 * (p - 1)) = (muQ (p ^ 2) ^ (p - 1)) ^ 6 := by
      rw [mul_comm, pow_mul]
    rw [this, hqμ, one_add_p_pow_six Fact.out]
  rw [hδ, h64] at hprod
  rw [hmu] at hprod
  -- (1 + p * 3q2) * (1 + p δ) = 1 + p * 6 qμ
  have hp2z := p_mul_p_eq_zero_quad (p := p) Fact.out
  set pp : Quad (p ^ 2) := (p : Quad (p ^ 2))
  set q2c : Quad (p ^ 2) :=
    ⟨3 * (fermatQuotientTwoNat p Fact.out hp2 : ZMod (p ^ 2)), 0⟩
  have hexp : (1 + pp * q2c) * (1 + pp * δ) = 1 + pp * (q2c + δ) := by
    have : pp * q2c * (pp * δ) = 0 := by
      calc
        pp * q2c * (pp * δ) = (pp * pp) * (q2c * δ) := by ring
        _ = 0 * (q2c * δ) := by rw [hp2z]
        _ = 0 := zero_mul _
    linear_combination this
  rw [hexp] at hprod
  -- 1 + p (q2c + δ) = 1 + p (6 qμ)
  have heq : pp * (q2c + δ) = pp * (6 * qμ) := by
    have := congrArg (fun z : Quad (p ^ 2) => z - 1) hprod
    simpa [add_sub_cancel_left] using this
  have hgoal : pp * (δ + q2c - 6 * qμ) = 0 := by
    calc
      pp * (δ + q2c - 6 * qμ)
        = pp * (q2c + δ) - pp * (6 * qμ) := by ring
      _ = pp * (6 * qμ) - pp * (6 * qμ) := by rw [heq]
      _ = 0 := sub_self _
  exact hgoal

lemma Pgen_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (n : ℕ) (z : R) :
    f (Pgen n z) = Pgen n (f z) := by
  simp only [Pgen, map_sum, map_mul, map_pow, map_natCast]

lemma Qgen_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (n : ℕ) (z : R) (O : ℕ → R) (O' : ℕ → S) (hO : ∀ k, k ≤ n → f (O k) = O' k) :
    f (Qgen n z O) = Qgen n (f z) O' := by
  simp only [Qgen, map_sum, map_mul, map_pow, map_natCast]
  refine sum_congr rfl ?_
  intro k hk
  rw [hO k (Nat.lt_succ_iff.mp (mem_range.mp hk))]

lemma quadCastHom_oddHarmonic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ)
    (hk : k ≤ (p - 1) / 2) :
    quadCastHom (show 1 ≤ 2 by omega)
        (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2)) =
      (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1)) := by
  apply QuadraticAlgebra.ext
  · simp only [quadCastHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    exact oddHarmonic_castHom (p := p) (e := 1) (f := 2) (k := k)
      Fact.out hp2 (by omega) (by omega) hk
  · simp [quadCastHom]

lemma not_split_of_not_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hmod : p % 7 ∈ ({1, 2, 4} : Set ℕ)) :
    legendreSym p (-7) = 1 :=
  (split_iff_mod_seven hp2 hp7).mpr hmod

/-- The combination appearing in `S = T + 3p U` after embedding, when split. -/
lemma Ssum_embed_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1) :
    ∃ δ : Quad (p ^ 2),
      z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ ∧
      (⟨Ssum p 2, 0⟩ : Quad (p ^ 2)) =
        (p : Quad (p ^ 2)) *
          (δ * Pgen ((p - 1) / 2) (z2 (p ^ 2)) +
            3 * (Qgen ((p - 1) / 2) (z1 (p ^ 2))
                  (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))) -
              Qgen ((p - 1) / 2) (z2 (p ^ 2))
                  (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))))) *
          (↑(isUnit_omega Fact.out hp7 (by omega : 0 < 2)).unit⁻¹ : Quad (p ^ 2)) := by
  obtain ⟨δ, hδ, hT⟩ := Tsum_eq_p_mul_delta hp2 hp7 hsplit
  refine ⟨δ, hδ, ?_⟩
  have he : (0 : ℕ) < 2 := by omega
  have hU := Usum_embed (p := p) (e := 2) Fact.out hp2 he hp7
  have hS := Ssum_eq_T_add_three_p_U Fact.out hp2
  have hSemb : (⟨Ssum p 2, 0⟩ : Quad (p ^ 2)) =
      (⟨Tsum p 2, 0⟩ : Quad (p ^ 2)) +
        3 * (p : Quad (p ^ 2)) * (⟨Usum p 2, 0⟩ : Quad (p ^ 2)) := by
    rw [hS]
    apply QuadraticAlgebra.ext <;> simp [mul_assoc]
  rw [hSemb, hT, hU]
  ring

lemma re_embed_eq_zero {m : ℕ} {x : ZMod m}
    (h : (⟨x, 0⟩ : Quad m) = 0) : x = 0 := by
  simpa using congrArg QuadraticAlgebra.re h

lemma quad_p_mul_eq_zero_of_red {p : ℕ} [Fact p.Prime] (z : Quad (p ^ 2))
    (h : quadCastHom (show 1 ≤ 2 by omega) z = 0) :
    (p : Quad (p ^ 2)) * z = 0 := by
  have hre :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) z.re = 0 := by
    have := congrArg QuadraticAlgebra.re h
    simpa [quadCastHom] using this
  have him :
      (ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by omega)) (ZMod (p ^ 1))) z.im = 0 := by
    have := congrArg QuadraticAlgebra.im h
    simpa [quadCastHom] using this
  obtain ⟨ar, hr⟩ := (zmod_castHom_eq_zero_iff z.re).mp hre
  obtain ⟨ai, hi⟩ := (zmod_castHom_eq_zero_iff z.im).mp him
  apply QuadraticAlgebra.ext
  · simp
    rw [hr, ← mul_assoc, p_mul_p_eq_zero_mod_p_sq Fact.out, zero_mul]
  · simp
    rw [hi, ← mul_assoc, p_mul_p_eq_zero_mod_p_sq Fact.out, zero_mul]

lemma Ssum_two_eq_zero_of_combo_red {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1)
    {δ : Quad (p ^ 2)}
    (hδ : z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ)
    (hS : (⟨Ssum p 2, 0⟩ : Quad (p ^ 2)) =
        (p : Quad (p ^ 2)) *
          (δ * Pgen ((p - 1) / 2) (z2 (p ^ 2)) +
            3 * (Qgen ((p - 1) / 2) (z1 (p ^ 2))
                  (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))) -
              Qgen ((p - 1) / 2) (z2 (p ^ 2))
                  (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))))) *
          (↑(isUnit_omega Fact.out hp7 (by omega : 0 < 2)).unit⁻¹ : Quad (p ^ 2)))
    (hred : quadCastHom (show 1 ≤ 2 by omega)
        (δ * Pgen ((p - 1) / 2) (z2 (p ^ 2)) +
          3 * (Qgen ((p - 1) / 2) (z1 (p ^ 2))
                (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))) -
            Qgen ((p - 1) / 2) (z2 (p ^ 2))
                (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))))) = 0) :
    Ssum p 2 = 0 := by
  set ωinv : Quad (p ^ 2) :=
    ↑(isUnit_omega Fact.out hp7 (by omega : (0 : ℕ) < 2)).unit⁻¹
  set X : Quad (p ^ 2) :=
    δ * Pgen ((p - 1) / 2) (z2 (p ^ 2)) +
      3 * (Qgen ((p - 1) / 2) (z1 (p ^ 2))
            (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))) -
        Qgen ((p - 1) / 2) (z2 (p ^ 2))
            (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))))
  have hX0 : (p : Quad (p ^ 2)) * X = 0 :=
    quad_p_mul_eq_zero_of_red X (by simpa [X] using hred)
  have hS0 : (⟨Ssum p 2, 0⟩ : Quad (p ^ 2)) = 0 := by
    simpa [X, ωinv, hX0] using hS
  exact re_embed_eq_zero hS0

lemma quadCastHom_Qgen_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (z : Quad (p ^ 2)) :
    quadCastHom (show 1 ≤ 2 by omega)
        (Qgen ((p - 1) / 2) z (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2)))) =
      Qgen ((p - 1) / 2) (quadCastHom (show 1 ≤ 2 by omega) z)
        (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1))) := by
  refine Qgen_map (quadCastHom (show 1 ≤ 2 by omega)) ((p - 1) / 2) z _ _ ?_
  intro k hk
  exact quadCastHom_oddHarmonic (p := p) hp2 k hk

lemma quadCastHom_Qgen_z1 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    quadCastHom (show 1 ≤ 2 by omega)
        (Qgen ((p - 1) / 2) (z1 (p ^ 2))
          (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2)))) =
      Qgen ((p - 1) / 2) (z1 (p ^ 1))
        (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1))) := by
  rw [quadCastHom_Qgen_odd hp2, quadCastHom_z1 Fact.out hp2 (by omega) (by omega)]

lemma quadCastHom_Qgen_z2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    quadCastHom (show 1 ≤ 2 by omega)
        (Qgen ((p - 1) / 2) (z2 (p ^ 2))
          (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2)))) =
      Qgen ((p - 1) / 2) (z2 (p ^ 1))
        (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1))) := by
  rw [quadCastHom_Qgen_odd hp2, quadCastHom_z2 Fact.out hp2 (by omega) (by omega)]

lemma quadCastHom_Pgen_z2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    quadCastHom (show 1 ≤ 2 by omega) (Pgen ((p - 1) / 2) (z2 (p ^ 2))) =
      Pgen ((p - 1) / 2) (z2 (p ^ 1)) := by
  rw [Pgen_map, quadCastHom_z2 Fact.out hp2 (by omega) (by omega)]

/-- The reduced combination equals the same combination formed in `Quad (p^1)`. -/
lemma combo_castHom {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (δ : Quad (p ^ 2)) :
    quadCastHom (show 1 ≤ 2 by omega)
        (δ * Pgen ((p - 1) / 2) (z2 (p ^ 2)) +
          3 * (Qgen ((p - 1) / 2) (z1 (p ^ 2))
                (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))) -
            Qgen ((p - 1) / 2) (z2 (p ^ 2))
                (fun k => (⟨oddHarmonic p 2 k, 0⟩ : Quad (p ^ 2))))) =
      quadCastHom (show 1 ≤ 2 by omega) δ * Pgen ((p - 1) / 2) (z2 (p ^ 1)) +
        3 * (Qgen ((p - 1) / 2) (z1 (p ^ 1))
              (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1))) -
          Qgen ((p - 1) / 2) (z2 (p ^ 1))
              (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1)))) := by
  simp only [map_add, map_mul, map_sub, map_ofNat]
  rw [quadCastHom_Pgen_z2 hp2, quadCastHom_Qgen_z1 hp2, quadCastHom_Qgen_z2 hp2]

lemma Ssum_two_eq_zero_of_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hsplit : legendreSym p (-7) = 1)
    (hcombo : ∀ δ : Quad (p ^ 2),
      z1 (p ^ 2) ^ ((p - 1) / 2) = 1 + (p : Quad (p ^ 2)) * δ →
      quadCastHom (show 1 ≤ 2 by omega) δ * Pgen ((p - 1) / 2) (z2 (p ^ 1)) +
        3 * (Qgen ((p - 1) / 2) (z1 (p ^ 1))
              (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1))) -
          Qgen ((p - 1) / 2) (z2 (p ^ 1))
              (fun k => (⟨oddHarmonic p 1 k, 0⟩ : Quad (p ^ 1)))) = 0) :
    Ssum p 2 = 0 := by
  obtain ⟨δ, hδ, hS⟩ := Ssum_embed_split hp2 hp7 hsplit
  apply Ssum_two_eq_zero_of_combo_red hp2 hp7 hsplit hδ hS
  rw [combo_castHom hp2]
  exact hcombo δ hδ

lemma Ssum_three_of_not_split {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (hns : ¬ legendreSym p (-7) = 1) :
    p % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum p 3 = 0 := by
  intro hmod
  exact (hns (not_split_of_not_mod hp2 hp7 hmod)).elim

/--
Conjecture of Zhi-Wei Sun on the sum $S(p)$ for the sequence A190969.
Let $S(p) := \sum_{k=0}^{p-1} \frac{a(4k) \binom{2k}{k}^3}{(-4096)^k}$.
Sun conjectured that $S(p) \equiv 0 \pmod{p^2}$ for every odd prime $p$,
and also $S(p) \equiv 0 \pmod{p^3}$ for any odd prime $p \equiv 1,2,4 \pmod{7}$.

The sum is formalized here by interpreting the division as multiplication by the modular inverse
in the ring $\mathbb{Z}/p^n\mathbb{Z}$. Since $p$ is an odd prime, $4096$ is invertible modulo $p^n$.
-/
theorem oeis_a190969_conjecture_0 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    let K (n : ℕ) := ZMod (p ^ n)
    let S (n : ℕ) : K n :=
        (range p).sum fun k =>
            let num : K n := (a (4 * k) : K n) * ((choose (2 * k) k : ℕ) : K n) ^ 3
            let den : K n := ((-4096 : ℤ) : K n) ^ k
            -- The inverse den⁻¹ exists because p is an odd prime and thus coprime to 4096.
            num * den⁻¹
    S 2 = 0 ∧ (p % 7 ∈ ({1, 2, 4} : Set ℕ) → S 3 = 0) := by
  change Ssum p 2 = 0 ∧ (p % 7 ∈ ({1, 2, 4} : Set ℕ) → Ssum p 3 = 0)
  rcases le_or_gt p 23 with hle | hgt
  · rcases prime_le_twentythree_of hp hp_odd hle with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact conjecture_p_three
    · exact conjecture_p_five
    · exact conjecture_p_seven
    · exact conjecture_p_eleven
    · exact conjecture_p_thirteen
    · exact conjecture_p_seventeen
    · exact conjecture_p_nineteen
    · exact conjecture_p_twentythree
  · -- General odd prime `p ≥ 29`.
    have hp29 : 29 ≤ p := by
      by_contra h
      have hle : p ≤ 28 := Nat.lt_succ_iff.mp (lt_of_not_ge h)
      have hge : 24 ≤ p := Nat.succ_le_of_lt hgt
      interval_cases p <;> exact (by decide : ¬ Nat.Prime _) hp
    have hp7 : p ≠ 7 := p_ne_seven_of_ge hp hp29
    haveI : Fact p.Prime := ⟨hp⟩
    -- Split: `S 2 = 0` and `S 3 = 0`. Inert: `S 2 = 0`; the `S 3` claim is vacuous.
    sorry
