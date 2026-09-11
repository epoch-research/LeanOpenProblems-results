import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

namespace A363347Proof

/-- Quadratic reciprocity for the two residue classes in the conjecture. -/
lemma square_five (p : ℕ) (hp : p.Prime)
    (hres : p % 10 = 1 ∨ p % 10 = 9) : IsSquare (5 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp2 : p ≠ 2 := by omega
  have h5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
  have hs : IsSquare (p : ZMod 5) := by
    rw [← ZMod.natCast_mod p 5]
    rcases h5 with h | h
    · rw [h]; exact ⟨1, by norm_num⟩
    · rw [h]; exact ⟨2, by norm_num⟩
  exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
    (by decide) hp2).mp hs

/-- Choose an even square root of five, then subtract one to get an odd index. -/
lemma index_exists (p : ℕ) (hp : p.Prime)
    (hres : p % 10 = 1 ∨ p % 10 = 9) :
    ∃ n : ℕ, 3 ≤ n ∧ n + 2 ≤ p ∧ Odd n ∧
      (p : ℤ) ∣ (n : ℤ)^2 + 2 * n - 4 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp11 : 11 ≤ p := by
    have := hp.two_le
    rcases hres with h | h
    · omega
    · by_contra! hh
      have : p = 9 := by omega
      subst p
      norm_num at hp
  have hpodd : p % 2 = 1 := by omega
  obtain ⟨x, hx⟩ := square_five p hp hres
  have hxe : ∃ r : ℕ, r < p ∧ r % 2 = 0 ∧ (r : ZMod p)^2 = 5 := by
    by_cases he : x.val % 2 = 0
    · exact ⟨x.val, x.val_lt, he, by simpa [pow_two] using hx.symm⟩
    · have hx0 : x ≠ 0 := by
        intro h
        subst x
        have hzero : (5 : ZMod p) = 0 := by simpa using hx
        have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp hzero
        have := Nat.le_of_dvd (by decide : 0 < 5) hd
        omega
      have hv0 : 0 < x.val := by
        by_contra! h
        have : x = 0 := by
          have hh : x.val = 0 := by omega
          simpa using congrArg (fun a : ℕ => (a : ZMod p)) hh
        contradiction
      refine ⟨p - x.val, by omega, by omega, ?_⟩
      rw [Nat.cast_sub (le_of_lt x.val_lt), ZMod.natCast_self, ZMod.natCast_zmod_val,
        zero_sub, neg_sq]
      simpa [pow_two] using hx.symm
  obtain ⟨r, hrp, hre, hrsq⟩ := hxe
  have hr4 : 4 ≤ r := by
    by_contra! hh
    have hr : r = 0 ∨ r = 2 := by omega
    rcases hr with rfl | rfl
    · have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp (by simpa using hrsq.symm)
      have := Nat.le_of_dvd (by decide : 0 < 5) hd
      omega
    · have hbad : (1 : ZMod p) = 0 := by linear_combination -hrsq
      exact one_ne_zero hbad
  refine ⟨r - 1, by omega, by omega, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (by omega)
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    linear_combination hrsq


/-- The denominator continuants, with the indices shifted by one. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => (k + 3 : ℤ) * (b (k + 1) - b k)

/-- The determinant of consecutive continuants is a factorial. -/
lemma b_det (k : ℕ) :
    2 * ((k + 1 : ℤ) * b (k + 1) - (k + 2 : ℤ) * b k) = (k + 2).factorial := by
  induction k with
  | zero => norm_num [b]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.factorial_succ]
    simp only [b, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat] at *
    linear_combination (k + 3) * ih

/-- A strict lower bound ensures that none of the recursive divisions is by zero. -/
lemma cf_pos (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    0 < continued_fraction_denominator n k ∧
      (k : ℚ) * (k - 2) < (k - 1) * continued_fraction_denominator n k := by
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hnq : (3 : ℚ) ≤ n := by exact_mod_cast hn
  rw [continued_fraction_denominator]
  simp only [show ¬ n ≤ 2 by omega, hk, hkn, and_self, ↓reduceIte]
  by_cases he : k = n - 1
  · simp only [he, ↓reduceIte]
    have hcast : (2 : ℚ) ≤ (n - 1 : ℕ) := by exact_mod_cast (show 2 ≤ n - 1 by omega)
    constructor
    · positivity
    · nlinarith
  · simp only [he, ↓reduceIte]
    have ih := cf_pos n (k + 1) hn (by omega) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at ih
    set t := continued_fraction_denominator n (k + 1)
    have ht : t ≠ 0 := ne_of_gt ih.1
    have heq : (((k - 1 : ℚ) * (k - (k + 1) / t) - k * (k - 2)) * t) =
        k * t - (k - 1) * (k + 1) := by
      field_simp
      ring
    have hmain : (k : ℚ) * (k - 2) < (k - 1) * (k - (k + 1) / t) := by
      have hrhs : 0 < (k : ℚ) * t - (k - 1) * (k + 1) := by nlinarith [ih.2]
      have hh : 0 < ((k - 1 : ℚ) * (k - (k + 1) / t) - k * (k - 2)) * t := by
        rw [heq]; exact hrhs
      have := (mul_pos_iff_of_pos_right ih.1).mp hh
      linarith
    exact ⟨by nlinarith [mul_nonneg (by positivity : (0 : ℚ) ≤ k) (by linarith : (0 : ℚ) ≤ k - 2)], hmain⟩
termination_by n - k


/-- Express the fraction using a tail and its prefix continuants. -/
lemma cf_prefix (n m : ℕ) (hn : 4 ≤ n) (hm : m + 3 ≤ n - 1) :
    continued_fraction_denominator n 2 *
      ((b (m + 1) : ℚ) * continued_fraction_denominator n (m + 3) -
        (m + 3 : ℚ) * b m) =
      (m + 2 : ℚ) * continued_fraction_denominator n (m + 3) -
        (m + 3 : ℚ) * (m + 1) := by
  induction m with
  | zero =>
    have ht := (cf_pos n 3 (by omega) (by omega) (by omega)).1.ne'
    rw [continued_fraction_denominator.eq_1 n 2]
    simp only [show ¬ n ≤ 2 by omega, show 2 ≤ 2 ∧ 2 ≤ n - 1 by omega,
      show ¬ 2 = n - 1 by omega, ↓reduceIte]
    norm_num [b]
    field_simp
  | succ m ih =>
    have ih := ih (by omega)
    have ht := (cf_pos n (m + 4) (by omega) (by omega) (by omega)).1.ne'
    rw [continued_fraction_denominator.eq_1 n (m + 3)] at ih
    rw [if_neg (by omega : ¬ n ≤ 2),
      if_pos (by omega : 2 ≤ m + 3 ∧ m + 3 ≤ n - 1),
      if_neg (by omega : ¬ m + 3 = n - 1)] at ih
    dsimp only at ih
    simp only [Nat.cast_add, Nat.cast_ofNat] at ih
    have hidx : m + 3 + 1 = m + 4 := by omega
    rw [hidx] at ih
    field_simp at ih
    simp only [show m + 1 + 3 = m + 4 by omega, b,
      Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    linear_combination ih

/-- Unreduced denominator at index `m + 3`. -/
def D (m : ℕ) : ℤ := 4 * b (m + 1) + (m + 3 : ℤ) * b m

/-- Unreduced numerator at index `m + 3`. -/
def F (m : ℕ) : ℤ := (m + 3 : ℤ)^2 + 2 * (m + 3) - 4

lemma cf_final (m : ℕ) :
    continued_fraction_denominator (m + 3) 2 * (D m : ℚ) = F m := by
  cases m with
  | zero => rw [continued_fraction_denominator.eq_1]; norm_num [D, F, b]
  | succ m =>
    have hi := cf_prefix (m + 4) m (by omega) (by omega)
    rw [continued_fraction_denominator.eq_1 (m + 4) (m + 3)] at hi
    rw [if_neg (by omega : ¬ m + 4 ≤ 2),
      if_pos (by omega : 2 ≤ m + 3 ∧ m + 3 ≤ m + 4 - 1),
      if_pos (by omega : m + 3 = m + 4 - 1)] at hi
    simp only [Nat.cast_add, Nat.cast_ofNat] at hi
    simp only [show m + 1 + 3 = m + 4 by omega,
      D, F, b, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_ofNat, Nat.cast_add, Nat.cast_one]
    linear_combination 4 * hi

lemma D_det (m : ℕ) :
    2 * (m + 2 : ℤ) * D m - 2 * b (m + 1) * F m = -((m + 3).factorial : ℤ) := by
  have hi := b_det m
  rw [show m + 3 = (m + 2) + 1 by omega, Nat.factorial_succ]
  simp only [D, F, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  linear_combination -(m + 3) * hi


/-- At an odd index below `p`, the cofactor divides the factorial and cancels,
while the prime `p` cannot cancel. -/
lemma realizes_prime (p m : ℕ) (hp : p.Prime) (hmp : m + 5 ≤ p)
    (hodd : Odd (m + 3)) (hdiv : (p : ℤ) ∣ F m) :
    A363347 (m + 3) = p := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hmz : (0 : ℤ) ≤ m := by positivity
  have hmpz : (m : ℤ) + 5 ≤ p := by exact_mod_cast hmp
  have hFpos : 0 < F m := by dsimp [F]; nlinarith
  obtain ⟨c, hc⟩ := hdiv
  have hcpos : 0 < c := by nlinarith [hc]
  have hcbound : c < (m : ℤ) + 3 := by
    have : F m < (p : ℤ) * (m + 3) := by dsimp [F]; nlinarith
    nlinarith [hc]
  lift c to ℕ using hcpos.le
  have hcn : 0 < c := by exact_mod_cast hcpos
  have hcle : c ≤ m + 3 := by exact_mod_cast hcbound.le
  have hcfact : (c : ℤ) ∣ (m + 3).factorial := by
    exact_mod_cast Nat.dvd_factorial hcn hcle
  obtain ⟨t, ht⟩ := hodd
  have htz : (m : ℤ) + 3 = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
  have hcop : IsCoprime (c : ℤ) (2 * (m + 2 : ℤ)) := by
    refine ⟨-(p : ℤ), (t : ℤ) + 2, ?_⟩
    have : F m = (p : ℤ) * c := hc
    dsimp [F] at this
    nlinarith
  have hcF : (c : ℤ) ∣ F m := ⟨p, by rw [hc]; ring⟩
  have hcD : (c : ℤ) ∣ D m := by
    apply hcop.dvd_of_dvd_mul_left
    have heq : 2 * (m + 2 : ℤ) * D m =
        2 * b (m + 1) * F m - (m + 3).factorial := by linarith [D_det m]
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right hcF _) hcfact
  obtain ⟨d, hd⟩ := hcD
  have hDpos : 0 < D m := by
    have hFq : (0 : ℚ) < F m := by exact_mod_cast hFpos
    have hRpos := (cf_pos (m + 3) 2 (by omega) (by omega) (by omega)).1
    have heq := cf_final m
    have : (0 : ℚ) < D m := by nlinarith
    exact_mod_cast this
  have hdpos : 0 < d := by nlinarith [hd]
  have hpd : Nat.Coprime p d.natAbs := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hh
    have hpd : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hh
    have hpD : (p : ℤ) ∣ D m := by rw [hd]; exact dvd_mul_of_dvd_right hpd _
    have hpF : (p : ℤ) ∣ F m := ⟨c, hc⟩
    have hpfact : (p : ℤ) ∣ -((m + 3).factorial : ℤ) := by
      rw [← D_det m]
      exact dvd_sub (dvd_mul_of_dvd_right hpD _) (dvd_mul_of_dvd_right hpF _)
    have hpfact' : p ∣ (m + 3).factorial := by exact_mod_cast (dvd_neg.mp hpfact)
    have := hp.dvd_factorial.mp hpfact'
    omega
  have hR : continued_fraction_denominator (m + 3) 2 = (p : ℚ) / (d : ℚ) := by
    apply (eq_div_iff (by exact_mod_cast hdpos.ne' : (d : ℚ) ≠ 0)).mpr
    have heq := cf_final m
    rw [hd, hc] at heq
    push_cast at heq
    apply mul_right_cancel₀ (by exact_mod_cast hcn.ne' : (c : ℚ) ≠ 0)
    linear_combination heq
  simp only [A363347, show ¬ m + 3 ≤ 2 by omega, ↓reduceIte]
  rw [hR]
  have hnum := Rat.num_div_eq_of_coprime (a := (p : ℤ)) hdpos (by simpa using hpd)
  simpa using congrArg Int.natAbs hnum

end A363347Proof

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  by
    intro p ⟨hp, hres⟩
    have hres' : p % 10 = 1 ∨ p % 10 = 9 := by simpa [Nat.ModEq] using hres
    obtain ⟨n, hn, hnp, hodd, hdvd⟩ := A363347Proof.index_exists p hp hres'
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact ⟨m + 3, A363347Proof.realizes_prime p m hp (by omega) hodd (by
      simpa [A363347Proof.F] using hdvd)⟩

theorem oeis_363347_conjecture_2.disproof : ¬ (type_of% @oeis_363347_conjecture_2) := sorry
