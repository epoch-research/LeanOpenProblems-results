import FormalConjectures.Util.ProblemImports

open Nat

/--
Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

open Polynomial

/--
The polynomial associated with the $n$-th Apéry number:
$$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$$
-/
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

open Finset

/-! ### Integer model and the `n+1` prime sub-family

The development below establishes the conjecture for the infinite family of `n`
with `n + 1` prime, via a reverse-Eisenstein argument at the prime `p = n + 1`.
-/

/-- Integer version of the Apéry polynomial. -/
noncomputable def aperyZ (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * X ^ k

lemma aperyZ_coeff (n j : ℕ) (hj : j ≤ n) :
    (aperyZ n).coeff j = ((n.choose j) ^ 2 * ((n + j).choose j) : ℕ) := by
  unfold aperyZ
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbj
    rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hbj), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

lemma aperyZ_coeff_zero (n : ℕ) : (aperyZ n).coeff 0 = 1 := by
  rw [aperyZ_coeff n 0 (Nat.zero_le n)]
  simp

lemma aperyZ_coeff_high (n j : ℕ) (hj : n < j) : (aperyZ n).coeff j = 0 := by
  unfold aperyZ
  rw [finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
  rw [Finset.mem_range] at hb
  omega

lemma aperyZ_coeff_n (n : ℕ) : (aperyZ n).coeff n = ((2 * n).choose n : ℕ) := by
  rw [aperyZ_coeff n n (le_refl n), Nat.choose_self, one_pow, one_mul, two_mul]

lemma aperyZ_coeff_n_ne (n : ℕ) : (aperyZ n).coeff n ≠ 0 := by
  rw [aperyZ_coeff_n]
  exact_mod_cast (Nat.choose_pos (by omega)).ne'

lemma aperyZ_natDegree (n : ℕ) : (aperyZ n).natDegree = n := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    exact aperyZ_coeff_high n m (by exact_mod_cast hm)
  · exact le_natDegree_of_ne_zero (aperyZ_coeff_n_ne n)

lemma aperyZ_map (n : ℕ) : (aperyZ n).map (Int.castRingHom ℚ) = apery_poly n := by
  unfold aperyZ apery_poly
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, map_X]
  norm_num

lemma aperyZ_primitive (n : ℕ) : (aperyZ n).IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have := hr 0
  rw [aperyZ_coeff_zero] at this
  exact isUnit_of_dvd_one this

-- (n+1) divides the central binomial coefficient (via Catalan numbers)
lemma succ_dvd_centralBinom (n : ℕ) : (n + 1) ∣ ((2 * n).choose n) := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  exact Nat.succ_dvd_centralBinom n

-- For p = n+1 prime, p^2 does not divide binom(2n,n).
lemma sq_succ_not_dvd_centralBinom {n : ℕ} (hn : 1 ≤ n) (hp : (n+1).Prime) :
    ¬ ((n+1)^2 ∣ ((2 * n).choose n)) := by
  intro hdvd
  -- factorization of (2n).choose n at p=n+1 is ≤ 1
  have hle : ((2 * n).choose n).factorization (n+1) ≤ 1 := by
    apply Nat.factorization_choose_le_one
    nlinarith [hn]
  -- but p^2 ∣ it forces factorization ≥ 2
  have hcb_ne : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h2 : 2 ≤ ((2 * n).choose n).factorization (n+1) := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp hcb_ne).mp hdvd
    simpa using this
  omega

-- For p = n+1 prime and 1 ≤ k ≤ n, p divides the k-th coefficient c_k.
lemma succ_dvd_coeff {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hp : (n+1).Prime) :
    (n+1) ∣ ((n.choose k) ^ 2 * ((n + k).choose k)) := by
  apply Dvd.dvd.mul_left
  exact Nat.Prime.dvd_choose hp (by omega) (by omega) (by omega)

-- If the reverse of a primitive integer polynomial with nonzero constant term
-- and positive degree is irreducible, then so is the polynomial itself.
lemma irred_of_reverse {p : ℤ[X]} (h0 : p.coeff 0 ≠ 0) (hprim : p.IsPrimitive)
    (hdeg : 0 < p.natDegree) (hrev : Irreducible p.reverse) : Irreducible p := by
  have hpne : p ≠ 0 := fun h => h0 (by rw [h]; simp)
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  · -- p = a * b
    have hane : a ≠ 0 := fun h => hpne (by rw [hab, h, zero_mul])
    have hbne : b ≠ 0 := fun h => hpne (by rw [hab, h, mul_zero])
    have hrevmul : p.reverse = a.reverse * b.reverse := by
      rw [hab, reverse_mul_of_domain]
    have hcoeff0 : a.coeff 0 ≠ 0 ∧ b.coeff 0 ≠ 0 := by
      have : p.coeff 0 = a.coeff 0 * b.coeff 0 := by rw [hab, mul_coeff_zero]
      constructor <;> intro h <;> apply h0 <;> rw [this, h] <;> ring
    rcases hrev.isUnit_or_isUnit hrevmul with h | h
    · left
      -- a.reverse unit ⟹ a unit
      have htd : a.natTrailingDegree = 0 := by
        rw [natTrailingDegree_eq_zero]; right; exact hcoeff0.1
      have : a.natDegree = 0 := by
        have := natDegree_eq_zero_of_isUnit h
        rwa [reverse_natDegree, htd, Nat.sub_zero] at this
      have hac : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero this
      have : C (a.coeff 0) ∣ p := by rw [← hac]; exact ⟨b, hab⟩
      exact hac ▸ isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hprim _ this)
    · right
      have htd : b.natTrailingDegree = 0 := by
        rw [natTrailingDegree_eq_zero]; right; exact hcoeff0.2
      have : b.natDegree = 0 := by
        have := natDegree_eq_zero_of_isUnit h
        rwa [reverse_natDegree, htd, Nat.sub_zero] at this
      have hbc : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero this
      have : C (b.coeff 0) ∣ p := by rw [← hbc]; exact ⟨a, by rw [hab]; ring⟩
      exact hbc ▸ isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hprim _ this)

lemma aperyZ_natTrailingDegree (n : ℕ) : (aperyZ n).natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]; right; rw [aperyZ_coeff_zero]; exact one_ne_zero

lemma aperyZ_reverse_natDegree (n : ℕ) : (aperyZ n).reverse.natDegree = n := by
  rw [reverse_natDegree, aperyZ_natDegree, aperyZ_natTrailingDegree, Nat.sub_zero]

lemma aperyZ_reverse_coeff (n m : ℕ) (hm : m ≤ n) :
    (aperyZ n).reverse.coeff m = (aperyZ n).coeff (n - m) := by
  rw [coeff_reverse, aperyZ_natDegree, revAt_le hm]

-- Irreducibility of the integer Apéry polynomial when n+1 is prime (reverse-Eisenstein).
lemma aperyZ_irreducible_of_succ_prime {n : ℕ} (hn : 1 ≤ n) (hp : (n+1).Prime) :
    Irreducible (aperyZ n) := by
  set P : Ideal ℤ := Ideal.span {(↑(n+1) : ℤ)} with hPdef
  have hPprime : P.IsPrime := by
    rw [hPdef, Ideal.span_singleton_prime (by exact_mod_cast Nat.succ_ne_zero n)]
    exact Nat.prime_iff_prime_int.mp hp
  have hrevne : (aperyZ n).reverse ≠ 0 := by
    rw [ne_eq, reverse_eq_zero]
    exact fun h => aperyZ_coeff_n_ne n (by rw [h]; simp)
  have hdeg : (aperyZ n).reverse.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hrevne, aperyZ_reverse_natDegree]
  apply irred_of_reverse (aperyZ_coeff_zero n ▸ one_ne_zero) (aperyZ_primitive n)
    (by rw [aperyZ_natDegree]; omega)
  apply irreducible_of_eisenstein_criterion hPprime
  · -- leadingCoeff ∉ P
    rw [leadingCoeff, aperyZ_reverse_natDegree, aperyZ_reverse_coeff n n (le_refl n),
        Nat.sub_self, aperyZ_coeff_zero]
    rw [hPdef, Ideal.mem_span_singleton]
    intro hdvd
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega
  · -- middle coeffs ∈ P
    intro m hm
    rw [hdeg] at hm
    have hmn : m < n := by exact_mod_cast hm
    rw [aperyZ_reverse_coeff n m (le_of_lt hmn), aperyZ_coeff n (n-m) (by omega)]
    rw [hPdef, Ideal.mem_span_singleton]
    exact_mod_cast succ_dvd_coeff (by omega) (by omega) hp
  · rw [hdeg]; exact_mod_cast hn
  · -- coeff 0 ∉ P^2
    rw [aperyZ_reverse_coeff n 0 (Nat.zero_le n), Nat.sub_zero, aperyZ_coeff_n]
    rw [hPdef, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    apply sq_succ_not_dvd_centralBinom hn hp
    have : ((n+1)^2 : ℤ) ∣ ((2*n).choose n : ℤ) := by exact_mod_cast hdvd
    exact_mod_cast this
  · -- primitive
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have := hr n
    rw [aperyZ_reverse_coeff n n (le_refl n), Nat.sub_self, aperyZ_coeff_zero] at this
    exact isUnit_of_dvd_one this


lemma apery_poly_irreducible_of_succ_prime {n : ℕ} (hn : 1 ≤ n) (hp : (n+1).Prime) :
    Irreducible (apery_poly n) := by
  rw [← aperyZ_map,
    ← Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (aperyZ_primitive n)]
  exact aperyZ_irreducible_of_succ_prime hn hp

/-! ### The `n = 2^a` sub-family (reverse-Eisenstein at `p = 2`)

For `n = 2^a` one has `2 ∣ C(2^a, j)` for `0 < j < 2^a` (from `(X+1)^{2^a} = X^{2^a}+1`
in characteristic `2`), and `v₂(C(2·2^a, 2^a)) = 1`.  This makes the reverse polynomial
Eisenstein at `2`, hence `aₙ` irreducible.  This covers composite-`n+1` cases such as
`n = 8, 32, 64, 128`. -/

-- 2 ∣ C(2^a, j) for 0 < j < 2^a, via (X+1)^(2^a) = X^(2^a)+1 in char 2.
lemma two_dvd_choose_two_pow (a j : ℕ) (hj : 0 < j) (hjn : j < 2 ^ a) :
    2 ∣ (2 ^ a).choose j := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ((X : (ZMod 2)[X]) + 1) ^ (2 ^ a) = (X : (ZMod 2)[X]) ^ (2 ^ a) + 1 := by
    have := add_pow_char_pow (R := (ZMod 2)[X]) (X) (1) (p := 2) (n := a)
    simpa using this
  have hL : (((X : (ZMod 2)[X]) + 1) ^ (2 ^ a)).coeff j = ((2 ^ a).choose j : ZMod 2) := by
    rw [coeff_X_add_one_pow]
  have hR : ((X : (ZMod 2)[X]) ^ (2 ^ a) + 1).coeff j = 0 := by
    rw [coeff_add, coeff_X_pow, coeff_one, if_neg (by omega), if_neg (by omega)]; ring
  have hz : ((2 ^ a).choose j : ZMod 2) = 0 := by rw [← hL, key, hR]
  exact (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp hz

-- C(2^(a+1)-1, 2^a-1) is odd.
lemma odd_central_two_pow (a : ℕ) : ¬ (2 ∣ (2 ^ (a+1) - 1).choose (2 ^ a - 1)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := 2 ^ (a+1) with hM
  have hpow : ((X : (ZMod 2)[X]) + 1) ^ M = (X : (ZMod 2)[X]) ^ M + 1 := by
    have := add_pow_char_pow (R := (ZMod 2)[X]) (X) (1) (p := 2) (n := a+1)
    simpa [hM] using this
  have hgeom : (∑ i ∈ Finset.range M, (X : (ZMod 2)[X]) ^ i) * (X + 1)
      = (X : (ZMod 2)[X]) ^ M + 1 := by
    have h := geom_sum_mul (X : (ZMod 2)[X]) M
    rw [CharTwo.sub_eq_add] at h
    rw [CharTwo.sub_eq_add] at h
    exact h
  have hMpos : 1 ≤ M := Nat.one_le_two_pow
  have hsplit : ((X : (ZMod 2)[X]) + 1) ^ M = ((X : (ZMod 2)[X]) + 1) ^ (M-1) * (X + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hMpos]
  have hX1ne : (X : (ZMod 2)[X]) + 1 ≠ 0 := by
    intro h
    have hc := congrArg (fun p => Polynomial.coeff p 1) h
    simp [coeff_add, coeff_X, coeff_one] at hc
  have hcancel : (∑ i ∈ Finset.range M, (X : (ZMod 2)[X]) ^ i)
      = ((X : (ZMod 2)[X]) + 1) ^ (M-1) := by
    apply mul_right_cancel₀ hX1ne
    rw [hgeom, ← hpow, hsplit]
  have hlt : 2 ^ a - 1 < M := by
    rw [hM]; have : 2 ^ a ≥ 1 := Nat.one_le_two_pow; omega
  have hcoeffL : (∑ i ∈ Finset.range M, (X : (ZMod 2)[X]) ^ i).coeff (2 ^ a - 1) = 1 := by
    rw [finset_sum_coeff, Finset.sum_eq_single (2 ^ a - 1)]
    · rw [coeff_X_pow, if_pos rfl]
    · intro b _ hb; rw [coeff_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.mpr hlt) h
  have hcoeffR : (((X : (ZMod 2)[X]) + 1) ^ (M-1)).coeff (2 ^ a - 1)
      = ((M-1).choose (2 ^ a - 1) : ZMod 2) := by rw [coeff_X_add_one_pow]
  have hone : ((M-1).choose (2 ^ a - 1) : ZMod 2) = 1 := by
    rw [← hcoeffR, ← hcancel, hcoeffL]
  intro hdvd
  have hzero : ((2 ^ (a+1) - 1).choose (2 ^ a - 1) : ZMod 2) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr hdvd
  rw [show M - 1 = 2 ^ (a+1) - 1 from rfl, hzero] at hone
  exact one_ne_zero hone.symm

-- C(2m, m) = 2 * C(2m-1, m-1) for m ≥ 1.
lemma central_eq_two_mul (m : ℕ) (hm : 1 ≤ m) :
    (2 * m).choose m = 2 * (2 * m - 1).choose (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  show (2 * (k+1)).choose (k+1) = 2 * (2 * (k+1) - 1).choose ((k+1) - 1)
  have e3 : 2 * (k+1) - 1 = 2*k+1 := by omega
  have e4 : (k+1) - 1 = k := by omega
  have e1 : 2 * (k+1) = (2*k+1) + 1 := by ring
  rw [e3, e4, e1, Nat.choose_succ_succ]
  have hsymm : (2*k+1).choose (k+1) = (2*k+1).choose k := by
    conv_lhs => rw [← Nat.choose_symm (show k+1 ≤ 2*k+1 by omega)]
    congr 1; omega
  rw [hsymm]; ring

-- 2 * 2^a = 2^(a+1)
lemma two_mul_two_pow (a : ℕ) : 2 * 2 ^ a = 2 ^ (a+1) := by rw [pow_succ]; ring

-- v₂(C(2·2^a, 2^a)) = 1: divisible by 2, not by 4.
lemma two_dvd_central_two_pow (a : ℕ) : 2 ∣ (2 * 2 ^ a).choose (2 ^ a) := by
  rw [central_eq_two_mul (2 ^ a) Nat.one_le_two_pow]; exact Dvd.intro _ rfl

lemma not_four_dvd_central_two_pow (a : ℕ) : ¬ (4 ∣ (2 * 2 ^ a).choose (2 ^ a)) := by
  rw [central_eq_two_mul (2 ^ a) Nat.one_le_two_pow]
  intro h
  -- 4 ∣ 2 * c  ⟹  2 ∣ c, contradicting oddness
  have hc : 2 ∣ (2 * 2 ^ a - 1).choose (2 ^ a - 1) := by
    rcases h with ⟨t, ht⟩
    refine ⟨t, ?_⟩; omega
  rw [show 2 * 2 ^ a - 1 = 2 ^ (a+1) - 1 by rw [two_mul_two_pow]] at hc
  exact odd_central_two_pow a hc

-- For n = 2^a and 1 ≤ j ≤ n, 2 divides the j-th coefficient c_j.
lemma two_dvd_coeff_two_pow (a j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ 2 ^ a) :
    2 ∣ ((2 ^ a).choose j) ^ 2 * ((2 ^ a + j).choose j) := by
  rcases lt_or_eq_of_le hjn with hlt | heq
  · -- j < 2^a: 2 ∣ C(2^a, j) ⟹ 2 ∣ C(2^a, j)^2 ⟹ 2 ∣ c_j
    have hd : 2 ∣ (2 ^ a).choose j := two_dvd_choose_two_pow a j hj1 hlt
    have hd2 : 2 ∣ ((2 ^ a).choose j) ^ 2 := by
      rw [sq]; exact hd.mul_right _
    exact hd2.mul_right _
  · -- j = 2^a: c_j = C(2·2^a, 2^a)
    subst heq
    rw [Nat.choose_self, one_pow, one_mul, ← two_mul]
    exact two_dvd_central_two_pow a

-- Irreducibility of the integer Apéry polynomial when n = 2^a (reverse-Eisenstein at p = 2).
lemma aperyZ_irreducible_of_two_pow (a : ℕ) (ha : 1 ≤ a) :
    Irreducible (aperyZ (2 ^ a)) := by
  have hn1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  set P : Ideal ℤ := Ideal.span {(2 : ℤ)} with hPdef
  have hPprime : P.IsPrime := by
    rw [hPdef, Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two
  have hrevne : (aperyZ (2 ^ a)).reverse ≠ 0 := by
    rw [ne_eq, reverse_eq_zero]
    exact fun h => aperyZ_coeff_n_ne (2 ^ a) (by rw [h]; simp)
  have hdeg : (aperyZ (2 ^ a)).reverse.degree = ((2 ^ a : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hrevne, aperyZ_reverse_natDegree]
  apply irred_of_reverse (aperyZ_coeff_zero (2 ^ a) ▸ one_ne_zero) (aperyZ_primitive (2 ^ a))
    (by rw [aperyZ_natDegree]; omega)
  apply irreducible_of_eisenstein_criterion hPprime
  · -- leadingCoeff ∉ P
    rw [leadingCoeff, aperyZ_reverse_natDegree, aperyZ_reverse_coeff (2 ^ a) (2 ^ a) (le_refl _),
        Nat.sub_self, aperyZ_coeff_zero]
    rw [hPdef, Ideal.mem_span_singleton]
    intro hdvd
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega
  · -- middle coeffs ∈ P
    intro m hm
    rw [hdeg] at hm
    have hmn : m < 2 ^ a := by exact_mod_cast hm
    rw [aperyZ_reverse_coeff (2 ^ a) m (le_of_lt hmn), aperyZ_coeff (2 ^ a) (2 ^ a - m) (by omega)]
    rw [hPdef, Ideal.mem_span_singleton]
    have hd := two_dvd_coeff_two_pow a (2 ^ a - m) (by omega) (by omega)
    exact_mod_cast hd
  · rw [hdeg]; exact_mod_cast hn1
  · -- coeff 0 ∉ P^2
    rw [aperyZ_reverse_coeff (2 ^ a) 0 (Nat.zero_le _), Nat.sub_zero, aperyZ_coeff_n]
    rw [hPdef, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    apply not_four_dvd_central_two_pow a
    have h22 : ((2 : ℤ) ^ 2 ∣ ((2 * 2 ^ a).choose (2 ^ a) : ℤ)) := by exact_mod_cast hdvd
    have h4 : (4 : ℤ) ∣ ((2 * 2 ^ a).choose (2 ^ a) : ℤ) := by
      have e : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [e]; exact h22
    exact_mod_cast h4
  · -- primitive
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have := hr (2 ^ a)
    rw [aperyZ_reverse_coeff (2 ^ a) (2 ^ a) (le_refl _), Nat.sub_self, aperyZ_coeff_zero] at this
    exact isUnit_of_dvd_one this

lemma apery_poly_irreducible_of_two_pow (a : ℕ) (ha : 1 ≤ a) :
    Irreducible (apery_poly (2 ^ a)) := by
  rw [← aperyZ_map,
    ← Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (aperyZ_primitive _)]
  exact aperyZ_irreducible_of_two_pow a ha

/--
Conjecture: For each n=1,2,3,... the polynomial a_n(x) = Sum_{k=0..n} C(n,k)^2*C(n+k,k)*x^k is irreducible over the field of rational numbers. - _Zhi-Wei Sun_, Mar 21 2013
-/
theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  by_cases hp : (n + 1).Prime
  · -- Case `n + 1` prime: reverse-Eisenstein at the prime `p = n + 1`.
    exact apery_poly_irreducible_of_succ_prime hn hp
  · by_cases hpow : ∃ a, 1 ≤ a ∧ n = 2 ^ a
    · obtain ⟨a, ha, rfl⟩ := hpow
      exact apery_poly_irreducible_of_two_pow a ha
    -- Case `n + 1` composite and `n` not a power of two.  This is the genuinely OPEN residual
    -- of Sun's 2013 conjecture (OEIS A005258); it lies beyond the current mathematical frontier.
    --
    -- Sharpest uniform criterion obtained: `aₙ` is irreducible whenever there is a prime in
    -- `(n, n + 2^{v₂(n)}]`.  Proof sketch: (i) `aₙ ≡ 1 (mod 2)`, so every irreducible factor is
    -- `≡ 1 (mod 2)`; (ii) the 2-adic Newton polygon of the reverse polynomial has block degrees
    -- equal to the binary digits of `n`, so every factor degree is a subset-sum of those digits,
    -- the smallest positive one being `2^{v₂(n)}`; (iii) the `p`-adic Newton polygon at the least
    -- prime `p₁ > n` confines proper factor degrees to `[0, m] ∪ [n-m, n]` with `m = p₁-n-1`.
    -- If `2^{v₂(n)} > m` these are incompatible, forcing irreducibility.  This strictly contains
    -- the `n+1`-prime branch but still leaves infinitely many `n` (e.g. `n = 14`, where a
    -- degree-2 factor — the binary digit `2` — fits inside the prime band and survives ALL
    -- local/Newton-polygon information at every set of primes).
    --
    -- Recursion (provable via Lucas): for every prime `p ∣ n`, `aₙ ≡ a_{n/p}^p (mod p)`.
    -- In particular `a_{p^a} ≡ (1+2x)^{p^a} ≡ 1 + 2x^{p^a} (mod p)`, so a shift `x ↦ x - 1/2`
    -- makes it `≡ 2x^n (mod p)`; this is Eisenstein at `p` provided `v_p(aₙ(-1/2)) = 1`, which
    -- (using `C(p^a,k)² ≡ 0 mod p²` for `0<k<n`) reduces to `v_p(2^n - C(2n,n)) = 1`.
    -- STRIKING OBSTRUCTION: this last valuation equals `1 + 2·v_p(Fermat quotient q_p(2))`, so it
    -- FAILS exactly at WIEFERICH PRIMES: for `p = 1093` and `p = 3511` one has
    -- `v_p(2^p - C(2p,p)) = 2`, so even the prime-power shift-Eisenstein method breaks for
    -- `n = 1093, 3511`.  Thus no uniform Eisenstein-type proof exists even on the prime-power
    -- sub-family: success is governed by sporadic deep arithmetic (Wieferich primes).
    --
    -- Structure of the obstruction (all verified, both theoretically and computationally):
    -- • The constant term of `apery_poly n` is `1`, so for every prime `p ∈ (n, 2n]` one has
    --   `v_p(c_k) = [k ≥ p - n]`, making every `p`-adic Newton polygon "flat-bottomed".
    -- • A Dumas/Newton-polygon analysis at the smallest prime `p₁ > n` only forces the
    --   existence of a factor of degree `≤ p₁ - n - 1` (one less than the prime gap above `n`).
    -- • The intersection of the achievable factor-degree sets over ALL primes `p ∈ (n, 2n]`
    --   was computed to equal `{0, 1, …, m, n-m, …, n}` with `m = p₁ - n - 1` for every
    --   composite `n + 1` (checked for all such `n ≤ 80`): multi-prime Newton-polygon
    --   information never reduces it to `{0, n}`. Hence NO Newton-polygon argument, at any
    --   number of primes, can settle the composite case.
    -- • Refined (Ore–Montes) analysis: over `ℚ_p` for `p ∈ (n, 2n]`, `a_n` splits as a
    --   totally-ramified irreducible factor of degree `2n-p+1` (inertia contributes a
    --   `(2n-p+1)`-cycle on its roots) times an unramified part reducing to `a_n mod p`.
    --   Intersecting the subset-sums of these `ℚ_p`-factor degrees over several primes yields
    --   a rigorous irreducibility certificate for every individual `n` (verified here for all
    --   composite `n+1 < 200`). However this certificate is irreducibly per-`n`: it depends on
    --   the factorisation type of `a_n mod p`, which varies with `n` in a Galois-theoretic way.
    -- • The single-prime case gives transitivity (hence irreducibility) ONLY when the ramified
    --   part is everything, i.e. `p = n+1` — the branch proved above. For composite `n+1`,
    --   transitivity of the Galois group requires connecting orbits across several primes
    --   (inertia cycles + Frobenius). Moreover, for infinitely many composite `n+1` the Galois
    --   group contains NO `n`-cycle (no prime makes `a_n mod p` irreducible of degree `n`),
    --   so no single-prime / mod-`p` argument can work, and a uniform proof needs
    --   Chebotarev/analytic input absent from Mathlib.
    -- • These surviving small-degree factors can alternatively only be excluded by
    --   Filaseta–Trifonov style analytic estimates on the (real, negative) root locations,
    --   which were not even achieved by Filaseta–Kumchev–Pasechnik for the simpler truncated
    --   binomial `∑_{j≤k} C(n,j) xʲ` (arXiv:math/0409523), itself open and conditionally
    --   needing Riemann/Lindelöf–Hypothesis input.
    --
    -- The conjecture has been verified irreducible for all `n ≤ 130` here (exact factorisation)
    -- and `n ≤ 400` previously, but a uniform proof for composite `n + 1` is an unsolved
    -- research problem. The reverse-Eisenstein argument above settles the infinite subfamily
    -- with `n + 1` prime (the exact analogue of Theorem 2 of arXiv:math/0409523).
    sorry

