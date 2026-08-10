import FormalConjectures.Util.ProblemImports

open Nat

/--
Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

open Polynomial
open Finset

/--
The polynomial associated with the $n$-th Apéry number:
$$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$$
-/
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

/-- Key structural lemma (verified): the central binomial coefficient `(2k choose k)`
is even for `k ≥ 1`, since `(2k).choose k = (2m+1).choose m + (2m+1).choose (m+1)`
(Pascal) and the two summands are equal (symmetry). -/
theorem two_dvd_central (k : ℕ) (hk : 1 ≤ k) : 2 ∣ (2 * k).choose k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hpascal : (2 * (m + 1)).choose (m + 1)
      = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := by
    have h : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h, Nat.choose_succ_succ (2 * m + 1) m]
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := Nat.choose_symm_half m
  rw [hpascal, hsymm]; omega

/-- The trinomial-revision identity `C(n,k)·C(n+k,k) = C(n+k,2k)·C(2k,k)`. -/
theorem apery_choose_id (n k : ℕ) (hkn : k ≤ n) :
    (n.choose k) * ((n + k).choose k) = ((n + k).choose (2 * k)) * ((2 * k).choose k) := by
  have h := Nat.choose_mul (n := n + k) (k := 2 * k) (s := k) (by omega)
  have e1 : (n + k) - k = n := by omega
  have e2 : 2 * k - k = k := by omega
  rw [e1, e2] at h
  rw [h]; ring

/-- Structural fact behind the conjecture: every coefficient `C(n,k)^2 · C(n+k,k)` of
`a_n(x)` with `1 ≤ k ≤ n` is even, i.e. `a_n(x) ≡ 1 (mod 2)`.  This yields irreducibility
for `n` a power of two (Eisenstein at `2` on the reverse) and, together with `p = n+1`,
for `n+1` prime. -/
theorem apery_coeff_even (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    2 ∣ (n.choose k) ^ 2 * ((n + k).choose k) := by
  have key : 2 ∣ (n.choose k) * ((n + k).choose k) := by
    rw [apery_choose_id n k hkn]
    exact Dvd.dvd.mul_left (two_dvd_central k hk) _
  have e : (n.choose k) ^ 2 * ((n + k).choose k)
      = (n.choose k) * ((n.choose k) * ((n + k).choose k)) := by ring
  rw [e]; exact Dvd.dvd.mul_left key _

/-- When `n+1` is prime, `n+1` divides every coefficient `C(n,k)^2·C(n+k,k)` of `a_n`
with `1 ≤ k ≤ n`.  (For `1 ≤ k ≤ n`, `n+1 ≤ n+k` and `(n+k)-k = n < n+1`, so by Kummer
`n+1 ∣ C(n+k,k)`.)  This is the Eisenstein divisibility for the reverse polynomial. -/
theorem apery_coeff_dvd_succ (n k : ℕ) (hp : (n + 1).Prime) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + 1) ∣ (n.choose k) ^ 2 * ((n + k).choose k) := by
  have hdvd : (n + 1) ∣ (n + k).choose k :=
    Nat.Prime.dvd_choose hp (a := k) (b := n + k) (by omega) (by omega) (by omega)
  exact Dvd.dvd.mul_left hdvd _

/-- The leading coefficient `C(2n,n)` of `a_n` is divisible by `n+1` to the first power only
(`2n < (n+1)^2`), giving the `mod (n+1)^2` Eisenstein condition for the reverse polynomial. -/
theorem apery_central_factorization_le_one (n : ℕ) :
    ((2 * n).choose n).factorization (n + 1) ≤ 1 := by
  apply Nat.factorization_choose_le_one
  have : 2 * n < (n + 1) ^ 2 := by nlinarith [sq_nonneg n]
  simpa using this

/-! ### An integer model of the Apéry polynomial and a mirror–Eisenstein criterion

We introduce the integer polynomial `aperyZ n ∈ ℤ[X]` with the same coefficients as
`apery_poly n`, and prove a general **mirror–Eisenstein irreducibility criterion**:
if some prime `q` divides every middle coefficient `C(n,j)^2 C(n+j,j)` (`1 ≤ j ≤ n`) and
`q^2` does not divide the leading coefficient `C(2n,n)`, then `apery_poly n` is irreducible
over `ℚ`.  Applying this with `q = 2` (for `n` a power of two) and `q = n+1` (for `n+1`
prime) settles two infinite families of the conjecture. -/

noncomputable def aperyZ (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ)) * X ^ k

lemma aperyZ_coeff (n i : ℕ) :
    (aperyZ n).coeff i =
      if i ≤ n then ((((n.choose i) ^ 2 * ((n + i).choose i) : ℕ) : ℤ)) else 0 := by
  rw [aperyZ, finset_sum_coeff]
  simp_rw [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n+1)) i
    (fun k => (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ))]
  simp [Finset.mem_range]

lemma aperyZ_coeff_zero (n : ℕ) : (aperyZ n).coeff 0 = 1 := by
  rw [aperyZ_coeff]; simp

lemma aperyZ_coeff_n (n : ℕ) : (aperyZ n).coeff n = (((2*n).choose n : ℕ) : ℤ) := by
  rw [aperyZ_coeff]; simp [two_mul]

lemma aperyZ_natDegree (n : ℕ) : (aperyZ n).natDegree = n := by
  have hle : (aperyZ n).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [aperyZ_coeff, if_neg (by omega)]
  have hge : n ≤ (aperyZ n).natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    rw [aperyZ_coeff_n]
    exact_mod_cast (Nat.choose_pos (show n ≤ 2*n by omega)).ne'
  omega

lemma aperyZ_natTrailingDegree (n : ℕ) : (aperyZ n).natTrailingDegree = 0 := by
  apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
  rw [Polynomial.constantCoeff_apply, aperyZ_coeff_zero]
  exact one_ne_zero

lemma aperyZ_primitive (n : ℕ) : (aperyZ n).IsPrimitive := by
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have := hr 0
  rw [aperyZ_coeff_zero] at this
  exact isUnit_of_dvd_one this

lemma aperyZ_isUnit_mirror_of {q : ℤ[X]} (hq : IsUnit q) : IsUnit q.mirror := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hq
  refine isUnit_iff_exists_inv.mpr ⟨v.mirror, ?_⟩
  rw [← mirror_mul_of_domain, hv, show (1 : ℤ[X]) = C 1 by simp, mirror_C]

lemma aperyZ_isUnit_mirror {p : ℤ[X]} : IsUnit p.mirror ↔ IsUnit p := by
  constructor
  · intro h; rw [← p.mirror_mirror]; exact aperyZ_isUnit_mirror_of h
  · exact aperyZ_isUnit_mirror_of

lemma aperyZ_irreducible_of_mirror {p : ℤ[X]} (h : Irreducible p.mirror) : Irreducible p := by
  constructor
  · intro hu; exact h.not_isUnit (aperyZ_isUnit_mirror_of hu)
  · intro x y hxy
    have : p.mirror = x.mirror * y.mirror := by rw [hxy, mirror_mul_of_domain]
    rcases h.isUnit_or_isUnit this with hx | hy
    · left; exact aperyZ_isUnit_mirror.mp hx
    · right; exact aperyZ_isUnit_mirror.mp hy

/-- **Mirror–Eisenstein criterion.** If `q` is a prime dividing every middle coefficient
`C(n,j)^2 C(n+j,j)` (`1 ≤ j ≤ n`) of the Apéry polynomial, and `q^2` does not divide the
leading coefficient `C(2n,n)`, then `aperyZ n` is irreducible over `ℤ` (the mirror polynomial
is Eisenstein at `q`). -/
lemma aperyZ_irreducible_of (n : ℕ) (hn : 1 ≤ n) (q : ℕ) (hq : q.Prime)
    (hdvd : ∀ j, 1 ≤ j → j ≤ n → (q:ℤ) ∣ ((((n.choose j)^2 * ((n+j).choose j)):ℕ):ℤ))
    (hsq : ((2*n).choose n).factorization q ≤ 1) :
    Irreducible (aperyZ n) := by
  apply aperyZ_irreducible_of_mirror
  set P := aperyZ n with hP
  set 𝓟 : Ideal ℤ := Ideal.span {(q:ℤ)} with h𝓟
  have hqZ : Prime (q:ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqne : (q:ℤ) ≠ 0 := hqZ.ne_zero
  have hPrime : 𝓟.IsPrime := (Ideal.span_singleton_prime hqne).mpr hqZ
  have hmnd : P.mirror.natDegree = n := by rw [mirror_natDegree, hP, aperyZ_natDegree]
  have hmcoeff : ∀ k, k ≤ n → P.mirror.coeff k = P.coeff (n - k) := by
    intro k hk
    rw [coeff_mirror, hP, aperyZ_natDegree, aperyZ_natTrailingDegree, Nat.add_zero, revAt_le hk]
  have heis : P.mirror.IsEisensteinAt 𝓟 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mirror_leadingCoeff, hP, Polynomial.trailingCoeff, aperyZ_natTrailingDegree,
          aperyZ_coeff_zero, h𝓟, Ideal.mem_span_singleton]
      intro h
      exact hqZ.not_unit (isUnit_of_dvd_one h)
    · intro m hm
      rw [hmnd] at hm
      rw [hmcoeff m (le_of_lt hm), hP, aperyZ_coeff, if_pos (by omega), h𝓟,
          Ideal.mem_span_singleton]
      exact hdvd (n - m) (by omega) (by omega)
    · rw [hmcoeff 0 (by omega), Nat.sub_zero, hP, aperyZ_coeff_n, h𝓟,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hcZ : (((q:ℤ))^2) = (((q^2 : ℕ)):ℤ) := by push_cast; ring
      rw [hcZ, Int.natCast_dvd_natCast] at h
      have hpos : (2*n).choose n ≠ 0 := (Nat.choose_pos (show n ≤ 2*n by omega)).ne'
      rw [Nat.Prime.pow_dvd_iff_le_factorization hq hpos] at h
      omega
  have hprim : P.mirror.IsPrimitive := by
    intro r hr
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
    have hh := hr n
    rw [hmcoeff n (le_refl n), Nat.sub_self, hP, aperyZ_coeff_zero] at hh
    exact isUnit_of_dvd_one hh
  exact heis.irreducible hPrime hprim (by rw [hmnd]; omega)

lemma aperyZ_map (n : ℕ) : (aperyZ n).map (Int.castRingHom ℚ) = apery_poly n := by
  rw [aperyZ, apery_poly, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  norm_num

lemma apery_poly_irr_of_aperyZ (n : ℕ) (h : Irreducible (aperyZ n)) :
    Irreducible (apery_poly n) := by
  rw [← aperyZ_map]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (aperyZ_primitive n)).mp h

/-- The Apéry polynomial is irreducible whenever `n + 1` is prime
(Eisenstein at `n+1` on the mirror polynomial). -/
lemma apery_poly_irreducible_of_succ_prime (n : ℕ) (hn : 1 ≤ n) (hp : (n+1).Prime) :
    Irreducible (apery_poly n) := by
  apply apery_poly_irr_of_aperyZ
  apply aperyZ_irreducible_of n hn (n+1) hp
  · intro j hj1 hjn
    exact_mod_cast apery_coeff_dvd_succ n j hp hj1 hjn
  · exact apery_central_factorization_le_one n

/-- The Apéry polynomial is irreducible whenever `n` is a power of two
(Eisenstein at `2` on the mirror polynomial, using `v_2(C(2n,n)) = 1`). -/
lemma apery_poly_irreducible_of_pow_two (j : ℕ) : Irreducible (apery_poly (2^j)) := by
  set n := 2^j with hn
  have hnpos : 1 ≤ n := Nat.one_le_two_pow
  apply apery_poly_irr_of_aperyZ
  apply aperyZ_irreducible_of n hnpos 2 Nat.prime_two
  · intro k hk1 hkn
    exact_mod_cast apery_coeff_even n k hk1 hkn
  · have h2n : 2 * n = 2^(j+1) := by rw [hn]; ring
    rw [h2n]
    have hk : n ≤ 2^(j+1) := by
      rw [hn]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk0 : n ≠ 0 := by omega
    rw [Nat.factorization_choose_prime_pow (p:=2) (n:=j+1) (k:=n) Nat.prime_two hk hk0]
    have hf : n.factorization 2 = j := by
      rw [hn, Nat.Prime.factorization_pow Nat.prime_two]; simp
    omega

/--
Conjecture: For each n=1,2,3,... the polynomial a_n(x) = Sum_{k=0..n} C(n,k)^2*C(n+k,k)*x^k is irreducible over the field of rational numbers. - _Zhi-Wei Sun_, Mar 21 2013
-/
theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  by_cases hpow : ∃ j, n = 2^j
  · obtain ⟨j, rfl⟩ := hpow; exact apery_poly_irreducible_of_pow_two j
  · by_cases hsucc : (n+1).Prime
    · exact apery_poly_irreducible_of_succ_prime n hn hsucc
    · sorry
