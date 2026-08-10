import FormalConjectures.Util.ProblemImports

open Finset

/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k

def Good (b d : ℕ) : Prop := d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

def signedVal (b : ℕ) : List Int → Int
  | [] => 0
  | c :: cs => c + (b : Int) * signedVal b cs

lemma quot_nonneg_of_digit {B digit q V : Int}
    (hV : 0 ≤ V) (hEq : V = digit + B * q)
    (hB : 0 < B) (hdB : digit < B) : 0 ≤ q := by
  by_contra hq
  have hqle : q ≤ -1 := by omega
  have hmul : B * q ≤ B * (-1 : Int) :=
    mul_le_mul_of_nonneg_left hqle (le_of_lt hB)
  have hlt : V < 0 := by
    calc
      V = digit + B * q := hEq
      _ ≤ digit + B * (-1 : Int) := by omega
      _ < B + B * (-1 : Int) := by omega
      _ = 0 := by ring
  omega

lemma natAbs_eq_digit_add {b digit : ℕ} {q V : Int}
    (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hEq : V = (digit : Int) + (b : Int) * q) :
    V.natAbs = digit + b * q.natAbs := by
  apply Int.ofNat.inj
  change (V.natAbs : Int) = ((digit + b * q.natAbs : ℕ) : Int)
  rw [Int.natAbs_of_nonneg hV]
  rw [show ((digit + b * q.natAbs : ℕ) : Int) = (digit : Int) + (b : Int) * q by
    rw [Nat.cast_add, Nat.cast_mul, Int.natAbs_of_nonneg hq]]
  exact hEq

lemma digits_carry_good {b : ℕ} (hb : 5 ≤ b) :
    ∀ (l : List Int) (carry : Int),
      (carry = 0 ∨ carry = -1) →
      (∀ c ∈ l, c = 1 ∨ c = -1) →
      0 ≤ carry + signedVal b l →
      ∀ d ∈ b.digits (carry + signedVal b l).natAbs, Good b d := by
  intro l
  induction l with
  | nil =>
      intro carry hcarry hcoeff hnon d hd
      rcases hcarry with rfl | rfl
      · simp [signedVal] at hd
      · simp [signedVal] at hnon
  | cons c cs ih =>
      intro carry hcarry hcoeff hnon d hd
      have hc : c = 1 ∨ c = -1 := hcoeff c (by simp)
      have hcoeff_cs : ∀ x ∈ cs, x = 1 ∨ x = -1 := by
        intro x hx; exact hcoeff x (by simp [hx])
      have hb1 : 1 < b := by omega
      have hbpos : 0 < b := by omega
      have hbposI : (0 : Int) < (b : Int) := by exact_mod_cast hbpos
      have hbI : (5 : Int) ≤ (b : Int) := by exact_mod_cast hb
      have cast_b_sub_one : ((b - 1 : ℕ) : Int) = (b : Int) - 1 := by omega
      have cast_b_sub_two : ((b - 2 : ℕ) : Int) = (b : Int) - 2 := by omega
      rcases hcarry with rfl | rfl <;> rcases hc with rfl | rfl
      · -- carry 0, c=1
        let q : Int := signedVal b cs
        let digit : ℕ := 1
        have hdigit_lt : digit < b := by omega
        have hEq : (0 : Int) + signedVal b (1 :: cs) = (digit : Int) + (b : Int) * q := by simp [signedVal, q, digit]
        have hq : 0 ≤ q := quot_nonneg_of_digit hnon hEq hbposI (by exact_mod_cast hdigit_lt)
        have hmEq := natAbs_eq_digit_add (b:=b) (digit:=digit) hnon hq hEq
        by_cases hm0 : (0 + signedVal b (1 :: cs)).natAbs = 0
        · have hnil : b.digits ((0 : Int) + signedVal b (1 :: cs)).natAbs = [] := by rw [hm0, Nat.digits_zero]
          rw [hnil] at hd; cases hd
        · rw [Nat.digits_eq_cons_digits_div hb1 hm0] at hd
          have hmod : (0 + signedVal b (1 :: cs)).natAbs % b = digit := by
            rw [hmEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit_lt]
          have hdiv : (0 + signedVal b (1 :: cs)).natAbs / b = q.natAbs := by
            rw [hmEq, Nat.add_mul_div_left, Nat.div_eq_of_lt hdigit_lt, Nat.zero_add]
            exact hbpos
          simp only [hmod, hdiv, List.mem_cons] at hd
          rcases hd with rfl | hd
          · simp [Good, digit]
          · exact ih 0 (Or.inl rfl) hcoeff_cs (by simpa [q] using hq) d (by simpa [q] using hd)
      · -- carry 0, c=-1
        let q : Int := -1 + signedVal b cs
        let digit : ℕ := b - 1
        have hdigit_lt : digit < b := by omega
        have hEq : (0 : Int) + signedVal b ((-1) :: cs) = (digit : Int) + (b : Int) * q := by
          simp [signedVal, q, digit, cast_b_sub_one]
          ring
        have hq : 0 ≤ q := quot_nonneg_of_digit hnon hEq hbposI (by exact_mod_cast hdigit_lt)
        have hmEq := natAbs_eq_digit_add (b:=b) (digit:=digit) hnon hq hEq
        by_cases hm0 : (0 + signedVal b ((-1) :: cs)).natAbs = 0
        · have hnil : b.digits ((0 : Int) + signedVal b ((-1) :: cs)).natAbs = [] := by rw [hm0, Nat.digits_zero]
          rw [hnil] at hd; cases hd
        · rw [Nat.digits_eq_cons_digits_div hb1 hm0] at hd
          have hmod : (0 + signedVal b ((-1) :: cs)).natAbs % b = digit := by
            rw [hmEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit_lt]
          have hdiv : (0 + signedVal b ((-1) :: cs)).natAbs / b = q.natAbs := by
            rw [hmEq, Nat.add_mul_div_left, Nat.div_eq_of_lt hdigit_lt, Nat.zero_add]
            exact hbpos
          simp only [hmod, hdiv, List.mem_cons] at hd
          rcases hd with rfl | hd
          · simp [Good, digit]
          · exact ih (-1) (Or.inr rfl) hcoeff_cs (by simpa [q] using hq) d (by simpa [q] using hd)
      · -- carry -1, c=1
        let q : Int := signedVal b cs
        let digit : ℕ := 0
        have hdigit_lt : digit < b := by omega
        have hEq : (-1 : Int) + signedVal b (1 :: cs) = (digit : Int) + (b : Int) * q := by simp [signedVal, q, digit]
        have hq : 0 ≤ q := quot_nonneg_of_digit hnon hEq hbposI (by exact_mod_cast hdigit_lt)
        have hmEq := natAbs_eq_digit_add (b:=b) (digit:=digit) hnon hq hEq
        by_cases hm0 : ((-1 : Int) + signedVal b (1 :: cs)).natAbs = 0
        · have hnil : b.digits (((-1 : Int) + signedVal b (1 :: cs)).natAbs) = [] := by rw [hm0, Nat.digits_zero]
          rw [hnil] at hd; cases hd
        · rw [Nat.digits_eq_cons_digits_div hb1 hm0] at hd
          have hmod : ((-1 : Int) + signedVal b (1 :: cs)).natAbs % b = digit := by
            rw [hmEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit_lt]
          have hdiv : ((-1 : Int) + signedVal b (1 :: cs)).natAbs / b = q.natAbs := by
            rw [hmEq, Nat.add_mul_div_left, Nat.div_eq_of_lt hdigit_lt, Nat.zero_add]
            exact hbpos
          simp only [hmod, hdiv, List.mem_cons] at hd
          rcases hd with rfl | hd
          · simp [Good, digit]
          · exact ih 0 (Or.inl rfl) hcoeff_cs (by simpa [q] using hq) d (by simpa [q] using hd)
      · -- carry -1, c=-1
        let q : Int := -1 + signedVal b cs
        let digit : ℕ := b - 2
        have hdigit_lt : digit < b := by omega
        have hEq : (-1 : Int) + signedVal b ((-1) :: cs) = (digit : Int) + (b : Int) * q := by
          simp [signedVal, q, digit, cast_b_sub_two]
          ring
        have hq : 0 ≤ q := quot_nonneg_of_digit hnon hEq hbposI (by exact_mod_cast hdigit_lt)
        have hmEq := natAbs_eq_digit_add (b:=b) (digit:=digit) hnon hq hEq
        by_cases hm0 : ((-1 : Int) + signedVal b ((-1) :: cs)).natAbs = 0
        · have hnil : b.digits (((-1 : Int) + signedVal b ((-1) :: cs)).natAbs) = [] := by rw [hm0, Nat.digits_zero]
          rw [hnil] at hd; cases hd
        · rw [Nat.digits_eq_cons_digits_div hb1 hm0] at hd
          have hmod : ((-1 : Int) + signedVal b ((-1) :: cs)).natAbs % b = digit := by
            rw [hmEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit_lt]
          have hdiv : ((-1 : Int) + signedVal b ((-1) :: cs)).natAbs / b = q.natAbs := by
            rw [hmEq, Nat.add_mul_div_left, Nat.div_eq_of_lt hdigit_lt, Nat.zero_add]
            exact hbpos
          simp only [hmod, hdiv, List.mem_cons] at hd
          rcases hd with rfl | hd
          · simp [Good, digit]
          · exact ih (-1) (Or.inr rfl) hcoeff_cs (by simpa [q] using hq) d (by simpa [q] using hd)

lemma signedVal_append_single (b : ℕ) : ∀ (l : List Int) (c : Int),
    signedVal b (l ++ [c]) = signedVal b l + c * (b : Int) ^ l.length
  | [], c => by simp [signedVal]
  | a :: l, c => by
      simp [signedVal, signedVal_append_single b l c, pow_succ]
      ring

lemma signedVal_map_neg (b : ℕ) : ∀ (l : List Int),
    signedVal b (l.map fun z => -z) = - signedVal b l
  | [] => by simp [signedVal]
  | a :: l => by
      simp [signedVal, signedVal_map_neg b l]
      ring

def coeffs (σ : ℕ → Int) (n : ℕ) : List Int :=
  (List.range n).map fun i => σ (i + 1)

lemma coeffs_succ (σ : ℕ → Int) (n : ℕ) :
    coeffs σ (n + 1) = coeffs σ n ++ [σ (n + 1)] := by
  simp [coeffs, List.range_succ, List.map_append]

lemma length_coeffs (σ : ℕ → Int) (n : ℕ) : (coeffs σ n).length = n := by
  simp [coeffs]

lemma signedVal_coeffs_eq_sum (b : ℕ) (σ : ℕ → Int) : ∀ n : ℕ,
    (b : Int) * signedVal b (coeffs σ n) =
      (Finset.Icc 1 n).sum fun k : ℕ => σ k * (b : Int) ^ k
  | 0 => by simp [coeffs, signedVal]
  | n + 1 => by
      rw [coeffs_succ, signedVal_append_single, length_coeffs]
      rw [mul_add]
      rw [signedVal_coeffs_eq_sum b σ n]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [pow_succ']
      ring

lemma coeffs_good {σ : ℕ → Int} {n : ℕ}
    (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1) :
    ∀ c ∈ coeffs σ n, c = 1 ∨ c = -1 := by
  intro c hc
  rw [coeffs, List.mem_map] at hc
  rcases hc with ⟨i, hi, rfl⟩
  rw [List.mem_range] at hi
  exact hσ (i + 1) (by simp [Finset.mem_Icc]; omega)

lemma digits_signedVal_good {b : ℕ} (hb : 5 ≤ b) (l : List Int)
    (hl : ∀ c ∈ l, c = 1 ∨ c = -1) :
    ∀ d ∈ b.digits (signedVal b l).natAbs, Good b d := by
  by_cases hnon : 0 ≤ signedVal b l
  · simpa using digits_carry_good (b:=b) hb l 0 (Or.inl rfl) hl (by simpa using hnon)
  · have hneg_non : 0 ≤ signedVal b (l.map fun z => -z) := by
      rw [signedVal_map_neg]
      omega
    have hmap : ∀ c ∈ l.map (fun z => -z), c = 1 ∨ c = -1 := by
      intro c hc
      rw [List.mem_map] at hc
      rcases hc with ⟨x, hx, rfl⟩
      rcases hl x hx with hx1 | hxm1
      · right; omega
      · left; omega
    intro d hd
    have := digits_carry_good (b:=b) hb (l.map fun z => -z) 0 (Or.inl rfl) hmap (by simpa using hneg_non) d
    rw [signedVal_map_neg] at this
    exact this (by simpa [Int.natAbs_neg] using hd)

lemma digits_original_good {b n : ℕ} (hb : 5 ≤ b) (σ : ℕ → Int)
    (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1) :
    ∀ d ∈ b.digits ((Icc 1 n).sum (fun k : ℕ => σ k * (b : Int) ^ k)).natAbs,
      Good b d := by
  intro d hd
  let V : Int := signedVal b (coeffs σ n)
  have hxEq : (Icc 1 n).sum (fun k : ℕ => σ k * (b : Int) ^ k) = (b : Int) * V := by
    dsimp [V]
    exact (signedVal_coeffs_eq_sum b σ n).symm
  have hnat : ((Icc 1 n).sum (fun k : ℕ => σ k * (b : Int) ^ k)).natAbs = b * V.natAbs := by
    rw [hxEq, Int.natAbs_mul, Int.natAbs_natCast]
  have hb1 : 1 < b := by omega
  by_cases hV0 : V.natAbs = 0
  · rw [hnat, hV0, mul_zero, Nat.digits_zero] at hd
    cases hd
  · rw [hnat, Nat.digits_base_mul hb1 (Nat.pos_of_ne_zero hV0)] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp [Good]
    · exact digits_signedVal_good (b:=b) hb (coeffs σ n) (coeffs_good hσ) d hd


/--
Conjecture: For any natural number $n$ and base $b > 4$, the absolute value of any sum of the form
$\sum_{k=1}^n \sigma_k b^k$ where $\sigma_k \in \{-1, 1\}$ only contains digits
belonging to $\{0, 1, b-2, b-1\}$ when expressed in base $b$.
This is the formalization of the conjecture for general base $b$.
-/
theorem oeis_243106_conjecture_0 (b n : ℕ) (hb : b ≥ 5) :
  ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
    let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
    ∀ d ∈ (b.digits x.natAbs),
      d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 :=
by
  intro σ hσ
  dsimp
  intro d hd
  simpa [Good] using digits_original_good (b:=b) (n:=n) hb σ hσ d hd
