import FormalConjectures.Util.ProblemImports

/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

-- Helper definition for the set of indices coprime to 30.
def coprime_indices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisor_product (n r : ℕ) : ℤ :=
  (coprime_indices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))

/-! ### Auxiliary lemmas for the proof.

The key input is Landau's integrality criterion together with a divisibility boost.
For a prime power `t = p^i`, Legendre's formula reduces the divisibility to a
statement about floors, which in turn reduces (via `s = n % t`, `j = 30*s/t < 30`)
to elementary finite checks. -/

/-- Floor identity: `15*s/t = (30*s/t)/2`. -/
private theorem f15 (s t : ℕ) : 15*s/t = 30*s/t/2 := by
  rw [Nat.div_div_eq_div_mul, show t*2 = 2*t from mul_comm _ _,
      show 30*s = 2*(15*s) from by ring, Nat.mul_div_mul_left _ _ (by norm_num)]

/-- Floor identity: `10*s/t = (30*s/t)/3`. -/
private theorem f10 (s t : ℕ) : 10*s/t = 30*s/t/3 := by
  rw [Nat.div_div_eq_div_mul, show t*3 = 3*t from mul_comm _ _,
      show 30*s = 3*(10*s) from by ring, Nat.mul_div_mul_left _ _ (by norm_num)]

/-- Floor identity: `6*s/t = (30*s/t)/5`. -/
private theorem f6 (s t : ℕ) : 6*s/t = 30*s/t/5 := by
  rw [Nat.div_div_eq_div_mul, show t*5 = 5*t from mul_comm _ _,
      show 30*s = 5*(6*s) from by ring, Nat.mul_div_mul_left _ _ (by norm_num)]

/-- If `s < t` then `30*s/t < 30`. -/
private theorem jlt (s t : ℕ) (hs : s < t) : 30*s/t < 30 := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]; omega

/-- Landau's integrality inequality (the `s < t` case). -/
private theorem R0 (s t : ℕ) (hs : s < t) : 15*s/t + 10*s/t + 6*s/t ≤ 30*s/t := by
  rw [f15, f10, f6]
  have := jlt s t hs
  omega

/-- The divisibility boost (the `s < t` case): if `30*s ≡ 1 [MOD t]` we gain a `+1`. -/
private theorem R1 (s t : ℕ) (hs : s < t) (hmod : 30*s % t = 1) :
    15*s/t + 10*s/t + 6*s/t + 1 ≤ 30*s/t := by
  rw [f15, f10, f6]
  set j := 30*s/t with hj
  have hjlt : j < 30 := jlt s t hs
  have hkey : 30*s = t*j + 1 := by
    have h := Nat.div_add_mod (30*s) t
    rw [hmod] at h
    rw [hj]; omega
  have hodd : j % 2 = 1 := by
    have he : Even (30*s) := ⟨15*s, by ring⟩
    rw [hkey] at he
    rw [Nat.even_add_one] at he
    have hh : Odd (t*j) := Nat.not_even_iff_odd.mp he
    exact Nat.odd_iff.mp (Nat.odd_mul.mp hh).2
  have h3 : j % 3 ≠ 0 := by
    intro hc
    have : (3:ℕ) ∣ t * j := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hc) t
    have h3s : (3:ℕ) ∣ 30*s := ⟨10*s, by ring⟩
    omega
  have h5 : j % 5 ≠ 0 := by
    intro hc
    have : (5:ℕ) ∣ t * j := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hc) t
    have h5s : (5:ℕ) ∣ 30*s := ⟨6*s, by ring⟩
    omega
  omega

/-- Decomposition of a floor term along `n = t*(n/t) + n%t`. -/
private theorem decomp (c n t : ℕ) (ht : 0 < t) : c*n/t = c*(n%t)/t + c*(n/t) := by
  have hdm : n = t*(n/t)+n%t := (Nat.div_add_mod n t).symm
  have key : c*n = c*(n%t) + t*(c*(n/t)) := by
    calc c*n = c*(t*(n/t)+n%t) := by rw [← hdm]
      _ = c*(n%t) + t*(c*(n/t)) := by ring
  rw [key, Nat.add_mul_div_left _ _ ht]

/-- The per-prime-power inequality, in terms of the residue condition `30*n % t = 1`. -/
private theorem lemD (n t : ℕ) (ht : 2 ≤ t) :
    15*n/t + 10*n/t + 6*n/t + (if 30*n%t = 1 then 1 else 0) ≤ 30*n/t + n/t := by
  have htpos : 0 < t := by omega
  have hs : n % t < t := Nat.mod_lt n htpos
  have e30 := decomp 30 n t htpos
  have e15 := decomp 15 n t htpos
  have e10 := decomp 10 n t htpos
  have e6 := decomp 6 n t htpos
  have emod : 30*n % t = 30*(n%t) % t := by
    have hdm : n = t*(n/t)+n%t := (Nat.div_add_mod n t).symm
    have key : 30*n = 30*(n%t) + t*(30*(n/t)) := by
      calc 30*n = 30*(t*(n/t)+n%t) := by rw [← hdm]
        _ = 30*(n%t) + t*(30*(n/t)) := by ring
    rw [key, Nat.add_mul_mod_self_left]
  by_cases hc : 30*n % t = 1
  · simp only [hc, if_true]
    have hR := R1 (n%t) t hs (by rw [← emod]; exact hc)
    omega
  · simp only [hc, if_false]
    have hR := R0 (n%t) t hs
    omega

/-- The per-prime-power inequality, in terms of the divisibility condition `t ∣ 30*n-1`. -/
private theorem lemD' (n t : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n) :
    15*n/t + 10*n/t + 6*n/t + (if t ∣ 30*n-1 then 1 else 0) ≤ 30*n/t + n/t := by
  have hiff : (t ∣ 30*n - 1) ↔ (30*n % t = 1) := by
    rw [← Nat.modEq_iff_dvd' (show 1 ≤ 30*n by omega), Nat.ModEq,
        Nat.mod_eq_of_lt (show (1:ℕ) < t by omega)]
    omega
  simp only [hiff]
  exact lemD n t ht

/-- The core divisibility, in `ℕ`:
`(30n-1) · (15n)!(10n)!(6n)!` divides `(30n)! · n!`. -/
private theorem main_dvd (n : ℕ) (hn : 1 ≤ n) :
    (30*n - 1) * ((15*n)! * (10*n)! * (6*n)!) ∣ (30*n)! * n ! := by
  have hd_ne : (30*n - 1) ≠ 0 := by omega
  have hden_ne : ((15*n)! * (10*n)! * (6*n)!) ≠ 0 := by positivity
  have hnum_ne : ((30*n)! * n !) ≠ 0 := by positivity
  apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero hd_ne hden_ne) hnum_ne).mp
  intro p hp
  have hpge : 2 ≤ p := hp.two_le
  have hbound : ∀ m:ℕ, m ≤ 30*n → Nat.log p m < 30*n+1 := fun m hm =>
    lt_of_le_of_lt (Nat.log_le_self p m) (by omega)
  have F30 : ((30*n)!).factorization p = ∑ i ∈ Finset.Ico 1 (30*n+1), 30*n/p^i :=
    Nat.factorization_factorial hp (hbound _ (le_refl _))
  have F1 : (n !).factorization p = ∑ i ∈ Finset.Ico 1 (30*n+1), n/p^i :=
    Nat.factorization_factorial hp (hbound _ (by omega))
  have F15 : ((15*n)!).factorization p = ∑ i ∈ Finset.Ico 1 (30*n+1), 15*n/p^i :=
    Nat.factorization_factorial hp (hbound _ (by omega))
  have F10 : ((10*n)!).factorization p = ∑ i ∈ Finset.Ico 1 (30*n+1), 10*n/p^i :=
    Nat.factorization_factorial hp (hbound _ (by omega))
  have F6 : ((6*n)!).factorization p = ∑ i ∈ Finset.Ico 1 (30*n+1), 6*n/p^i :=
    Nat.factorization_factorial hp (hbound _ (by omega))
  have hnum : ((30*n)! * n !).factorization p
      = ∑ i ∈ Finset.Ico 1 (30*n+1), (30*n/p^i + n/p^i) := by
    rw [Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _), Finsupp.add_apply,
        F30, F1, ← Finset.sum_add_distrib]
  have hden : ((15*n)! * (10*n)! * (6*n)!).factorization p
      = ∑ i ∈ Finset.Ico 1 (30*n+1), (15*n/p^i + 10*n/p^i + 6*n/p^i) := by
    rw [Nat.factorization_mul (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _))
          (factorial_ne_zero _), Finsupp.add_apply,
        Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _), Finsupp.add_apply,
        F15, F10, F6, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have he : (30*n-1).factorization p
      = ∑ i ∈ Finset.Ico 1 (30*n+1), (if p^i ∣ 30*n-1 then 1 else 0) := by
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega)
        (lt_trans (show 30*n-1 < 30*n+1 by omega) (Nat.lt_pow_self hpge)), Finset.card_filter]
  rw [Nat.factorization_mul hd_ne hden_ne, Finsupp.add_apply, he, hden, hnum,
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hile : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hti : 2 ≤ p^i := by
    calc 2 ≤ p := hpge
      _ = p^1 := (pow_one p).symm
      _ ≤ p^i := Nat.pow_le_pow_right (by omega) hile
  have hL := lemD' n (p^i) hti hn
  omega

/--
It appears that a(n)/(30*n - 1) is integral for all n (checked up to n = 1000).
This is the specific case of the general conjecture for r=1 with D(1)=1.
-/
theorem oeis_a211417_conjecture_specific (n : ℕ) :
  (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [a]
    norm_num
  -- n ≥ 1
  set num := (30*n)! * n ! with hnum_def
  set den := (15*n)! * (10*n)! * (6*n)! with hden_def
  have hmd := main_dvd n hn
  rw [← hnum_def, ← hden_def] at hmd
  have hdvd : den ∣ num := dvd_trans (Dvd.intro_left _ rfl) hmd
  have han : a n = num / den := by rw [hden_def, hnum_def]; rfl
  have heq : a n * den = num := by rw [han]; exact Nat.div_mul_cancel hdvd
  have hnat : (30*n - 1) ∣ a n := by
    have hh : (30*n - 1) * den ∣ (a n) * den := by rw [heq]; exact hmd
    exact (mul_dvd_mul_iff_right (by rw [hden_def]; positivity : den ≠ 0)).mp hh
  have hcast : ((30*n - 1 : ℕ) : ℤ) = 30 * (n:ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [← hcast]
  exact_mod_cast hnat
