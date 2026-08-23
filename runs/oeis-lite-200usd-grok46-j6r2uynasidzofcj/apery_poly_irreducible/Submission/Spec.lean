import FormalConjectures.Util.ProblemImports

open Nat Polynomial

/-!
Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

/-
The polynomial associated with the $n$-th Apéry number:
$$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$$
-/
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

/- Integer-coefficient version of `apery_poly`. -/
noncomputable def aperyPolyZ (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * X ^ k

lemma aperyPolyZ_coeff (n k : ℕ) :
    (aperyPolyZ n).coeff k = (n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) := by
  unfold aperyPolyZ
  rw [finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _hj hne
    exact if_neg (Ne.symm hne)
  · intro hk
    have : n < k := by
      contrapose! hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    simp [choose_eq_zero_of_lt this]

lemma apery_poly_eq_map (n : ℕ) :
    apery_poly n = (aperyPolyZ n).map (Int.castRingHom ℚ) := by
  unfold apery_poly aperyPolyZ
  simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_X]

lemma aperyPolyZ_natDegree (n : ℕ) : (aperyPolyZ n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [aperyPolyZ_coeff]
    have : n < N := hN
    simp [choose_eq_zero_of_lt this]
  · rw [aperyPolyZ_coeff]
    have hpos : 0 < (n + n).choose n := choose_pos (Nat.le_add_left n n)
    have h1 : (n.choose n : ℤ) ≠ 0 := by simp
    have h2 : ((n + n).choose n : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact mul_ne_zero (pow_ne_zero 2 h1) h2

lemma int_cast_injective_rat : Function.Injective (Int.castRingHom ℚ) :=
  Int.cast_injective

lemma apery_poly_natDegree (n : ℕ) : (apery_poly n).natDegree = n := by
  rw [apery_poly_eq_map, natDegree_map_eq_of_injective int_cast_injective_rat,
    aperyPolyZ_natDegree]

lemma aperyPolyZ_coeff_zero (n : ℕ) : (aperyPolyZ n).coeff 0 = 1 := by
  simp [aperyPolyZ_coeff]

lemma aperyPolyZ_leadingCoeff (n : ℕ) :
    (aperyPolyZ n).leadingCoeff = ((n + n).choose n : ℤ) := by
  rw [leadingCoeff, aperyPolyZ_natDegree, aperyPolyZ_coeff]
  simp

lemma aperyPolyZ_isPrimitive (n : ℕ) : (aperyPolyZ n).IsPrimitive := by
  intro r hr
  have : r ∣ (aperyPolyZ n).coeff 0 := (C_dvd_iff_dvd_coeff r _).mp hr 0
  rw [aperyPolyZ_coeff_zero] at this
  exact isUnit_of_dvd_one this

lemma apery_poly_irreducible_iff (n : ℕ) :
    Irreducible (apery_poly n) ↔ Irreducible (aperyPolyZ n) := by
  rw [apery_poly_eq_map]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (aperyPolyZ_isPrimitive n)).symm

lemma apery_poly_ne_zero (n : ℕ) : apery_poly n ≠ 0 := by
  intro h
  have hc : (apery_poly n).coeff 0 = 0 := by simp [h]
  have : (apery_poly n).coeff 0 = 1 := by
    rw [apery_poly_eq_map, coeff_map, aperyPolyZ_coeff_zero]
    simp
  simp [this] at hc

lemma apery_poly_irreducible_one : Irreducible (apery_poly 1) := by
  refine irreducible_of_degree_eq_one ?_
  rw [degree_eq_natDegree (apery_poly_ne_zero 1), apery_poly_natDegree]
  simp

/- 2-adic valuations of binomial coefficients -/

lemma two_prime_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Sum of binary digits. -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma padicValNat_factorial_two (n : ℕ) :
    padicValNat 2 n.factorial = n - s2 n := by
  haveI := two_prime_fact
  simpa [s2] using sub_one_mul_padicValNat_factorial (p := 2) n

lemma padicValNat_le_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b := by
  by_cases ha : a = 0
  · subst ha
    exact (hb (eq_zero_of_zero_dvd h)).elim
  · have : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
    have : p ^ padicValNat p a ∣ b := dvd_trans this h
    exact (padicValNat_dvd_iff_le hb).mp this

lemma s2_add_s2_sub_le (n k : ℕ) (h : k ≤ n) : s2 n ≤ s2 k + s2 (n - k) := by
  haveI := two_prime_fact
  have hdiv : k.factorial * (n - k).factorial ∣ n.factorial :=
    Nat.factorial_mul_factorial_dvd_factorial h
  have hk0 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hnk0 : (n - k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hne : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hle : padicValNat 2 (k.factorial * (n - k).factorial) ≤
      padicValNat 2 n.factorial :=
    padicValNat_le_of_dvd hne hdiv
  rw [padicValNat.mul hk0 hnk0] at hle
  rw [padicValNat_factorial_two, padicValNat_factorial_two,
    padicValNat_factorial_two] at hle
  have hsk : s2 k ≤ k := Nat.digit_sum_le 2 k
  have hsnk : s2 (n - k) ≤ n - k := Nat.digit_sum_le 2 (n - k)
  have hsn : s2 n ≤ n := Nat.digit_sum_le 2 n
  omega

lemma padicValNat_choose_two {n k : ℕ} (h : k ≤ n) :
    padicValNat 2 (n.choose k) = s2 k + s2 (n - k) - s2 n := by
  haveI := two_prime_fact
  have hform := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) h
  simpa [s2] using hform

lemma padicValNat_choose_add_two (n k : ℕ) :
    padicValNat 2 ((n + k).choose k) = s2 k + s2 n - s2 (n + k) := by
  have h : k ≤ n + k := Nat.le_add_left _ _
  have h' := padicValNat_choose_two h
  simpa [Nat.add_sub_cancel] using h'

lemma apery_coeff_padicVal_two {n k : ℕ} (hk : k ≤ n) :
    padicValNat 2 (n.choose k ^ 2 * (n + k).choose k) =
      2 * padicValNat 2 (n.choose k) + padicValNat 2 ((n + k).choose k) := by
  have h1 : n.choose k ≠ 0 := (choose_pos hk).ne'
  have h2 : (n + k).choose k ≠ 0 := (choose_pos (Nat.le_add_left k n)).ne'
  have hsq : n.choose k ^ 2 ≠ 0 := pow_ne_zero 2 h1
  rw [padicValNat.mul hsq h2, padicValNat.pow 2 h1]

lemma s2_zero : s2 0 = 0 := by simp [s2, Nat.digits_zero]

lemma s2_one : s2 1 = 1 := by
  simp [s2]

lemma s2_double {n : ℕ} (hn : n ≠ 0) : s2 (2 * n) = s2 n := by
  have hpos : 0 < 2 * n := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hn)
  unfold s2
  rw [Nat.digits_def' (by decide : 1 < 2) hpos]
  simp [Nat.mul_mod_right, Nat.mul_div_right n (by decide : 0 < 2)]

lemma s2_two_pow (m : ℕ) : s2 (2 ^ m) = 1 := by
  induction m with
  | zero => simp [s2_one]
  | succ m ih =>
    rw [pow_succ, mul_comm, s2_double (pow_ne_zero _ (by decide)), ih]

lemma s2_le_self (n : ℕ) : s2 n ≤ n := Nat.digit_sum_le 2 n

lemma padicValNat_central_two (n : ℕ) :
    padicValNat 2 ((n + n).choose n) = s2 n := by
  have hle : n ≤ n + n := Nat.le_add_left _ _
  rw [padicValNat_choose_two hle]
  have hsub : n + n - n = n := Nat.add_sub_cancel _ _
  rw [hsub]
  have : s2 n + s2 n - s2 (n + n) = s2 n := by
    have h2n : n + n = 2 * n := by ring
    by_cases hn : n = 0
    · simp [hn, s2_zero]
    · rw [h2n, s2_double hn]
      omega
  exact this

/- Lucas modulo 2 -/

lemma choose_modEq_two (n k : ℕ) :
    n.choose k ≡ (n % 2).choose (k % 2) * (n / 2).choose (k / 2) [MOD 2] := by
  haveI := two_prime_fact
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)

lemma choose_even_of_even_odd {n k : ℕ} (hn : Even n) (hk : Odd k) :
    Even (n.choose k) := by
  have h := choose_modEq_two n k
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hn
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
  rw [hn2, hk2, choose_zero_succ] at h
  have : n.choose k % 2 = 0 := by
    simpa using h
  exact Nat.even_iff.mpr this

lemma choose_add_even_of_odd_odd {n k : ℕ} (hn : Odd n) (hk : Odd k) :
    Even ((n + k).choose k) := by
  have hnk : Even (n + k) := hn.add_odd hk
  exact choose_even_of_even_odd hnk hk

lemma even_iff_even_of_modEq_two {a b : ℕ} (h : a ≡ b [MOD 2]) : Even a ↔ Even b := by
  rw [Nat.even_iff, Nat.even_iff, h]

/-- For `k ≥ 1`, either `choose n k` or `choose (n+k) k` is even. -/
lemma choose_or_choose_add_even {n k : ℕ} (hk : 1 ≤ k) :
    Even (n.choose k) ∨ Even ((n + k).choose k) := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rcases Nat.even_or_odd k with hk_even | hk_odd
    · have hkpos : 0 < k := hk
      have hk2 : 1 ≤ k / 2 := by
        have hkge : 2 ≤ k := by
          have : 2 ∣ k := hk_even.two_dvd
          obtain ⟨m, hm⟩ := this
          have hmpos : 0 < m := by
            apply Nat.pos_of_ne_zero
            rintro rfl
            simp [hm] at hkpos
          omega
        exact Nat.le_div_iff_mul_le (by decide) |>.mpr (by omega)
      have hlt : k / 2 < k := Nat.div_lt_self hkpos (by decide)
      have ih' := ih (k / 2) hlt (n := n / 2) hk2
      have h1 := choose_modEq_two n k
      have h2 := choose_modEq_two (n + k) k
      have hk2e : k % 2 = 0 := Nat.even_iff.mp hk_even
      have hdiv : (n + k) / 2 = n / 2 + k / 2 := by
        have hkmul : k = (k / 2) * 2 := by
          rw [Nat.mul_comm]
          exact (Nat.mul_div_cancel' hk_even.two_dvd).symm
        calc
          (n + k) / 2 = (n + k / 2 * 2) / 2 := congrArg (fun t => (n + t) / 2) hkmul
          _ = n / 2 + k / 2 := Nat.add_mul_div_right n (k / 2) (by decide)
      have red1 : n.choose k ≡ (n / 2).choose (k / 2) [MOD 2] := by
        have : (n % 2).choose (k % 2) = 1 := by
          rw [hk2e, Nat.choose_zero_right]
        simpa [this] using h1
      have red2 : (n + k).choose k ≡ (n / 2 + k / 2).choose (k / 2) [MOD 2] := by
        have : ((n + k) % 2).choose (k % 2) = 1 := by
          rw [hk2e, Nat.choose_zero_right]
        simpa [this, hdiv] using h2
      have e1 : Even (n.choose k) ↔ Even ((n / 2).choose (k / 2)) :=
        even_iff_even_of_modEq_two red1
      have e2 : Even ((n + k).choose k) ↔ Even ((n / 2 + k / 2).choose (k / 2)) :=
        even_iff_even_of_modEq_two red2
      simpa [e1, e2] using ih'
    · rcases Nat.even_or_odd n with hn | hn
      · exact Or.inl (choose_even_of_even_odd hn hk_odd)
      · exact Or.inr (choose_add_even_of_odd_odd hn hk_odd)

lemma apery_coeff_even_of_pos {n k : ℕ} (hk : 1 ≤ k) :
    Even (n.choose k ^ 2 * (n + k).choose k) := by
  rcases choose_or_choose_add_even (n := n) hk with h | h
  · exact Even.mul_right (Even.pow_of_ne_zero h (by decide)) _
  · exact Even.mul_left h _

lemma apery_coeffZ_even_of_pos {n k : ℕ} (hk : 1 ≤ k) :
    Even ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) := by
  have h : Even (n.choose k ^ 2 * (n + k).choose k) := apery_coeff_even_of_pos hk
  exact (Int.even_coe_nat _).mpr h

lemma aperyPolyZ_coeff_even {n k : ℕ} (hk : 1 ≤ k) :
    (2 : ℤ) ∣ (aperyPolyZ n).coeff k := by
  rw [aperyPolyZ_coeff]
  have h : Even (n.choose k ^ 2 * (n + k).choose k) := apery_coeff_even_of_pos hk
  exact even_iff_two_dvd.mp ((Int.even_coe_nat _).mpr h)

/- Auxiliary integer used in the rational-root analysis. -/
def aperyT (n : ℕ) (v : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * v ^ (n - k)

lemma even_sum_of_even {ι : Type*} {s : Finset ι} {f : ι → ℤ}
    (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Even.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma aperyT_odd_of_odd {n : ℕ} {v : ℤ} (hv : Odd v) :
    Odd (aperyT n v) := by
  have h0mem : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  unfold aperyT
  rw [← Finset.sum_erase_add _ _ h0mem]
  simp only [choose_zero_right, Nat.cast_one, one_pow, mul_one, pow_zero, one_mul,
    Nat.sub_zero]
  refine Even.add_odd ?_ (Odd.pow hv)
  refine even_sum_of_even ?_
  intro k hk
  have hkne : k ≠ 0 := Finset.ne_of_mem_erase hk
  have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hkne
  have he : Even ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) :=
    apery_coeffZ_even_of_pos hkpos
  exact Even.mul_right (Even.mul_right he _) _

lemma aperyT_ne_zero_of_odd {n : ℕ} {v : ℤ} (hv : Odd v) : aperyT n v ≠ 0 := by
  intro h
  have := aperyT_odd_of_odd (n := n) hv
  rw [h] at this
  exact Int.not_odd_zero this

lemma apery_poly_eval_eq_aeval (n : ℕ) (r : ℚ) :
    (apery_poly n).eval r = aeval r (aperyPolyZ n) := by
  rw [apery_poly_eq_map, eval_map, aeval_def]
  rfl

lemma aperyPolyZ_aeval (n : ℕ) (r : ℚ) :
    aeval r (aperyPolyZ n) =
      ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) : ℚ) * r ^ k := by
  rw [aeval_def, eval₂_eq_sum_range, aperyPolyZ_natDegree]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  simp [aperyPolyZ_coeff]

lemma apery_poly_eval_pos {n : ℕ} {r : ℚ} (hr : 0 ≤ r) :
    0 < (apery_poly n).eval r := by
  rw [apery_poly_eval_eq_aeval, aperyPolyZ_aeval]
  have h0mem : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
  rw [← Finset.sum_erase_add _ _ h0mem]
  have hterm0 :
      ((n.choose 0 : ℤ) ^ 2 * ((n + 0).choose 0 : ℤ) : ℚ) * r ^ 0 = 1 := by simp
  have hrest :
      0 ≤ ∑ k ∈ (Finset.range (n + 1)).erase 0,
        ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) : ℚ) * r ^ k := by
    refine Finset.sum_nonneg ?_
    intro k _hk
    exact mul_nonneg
      (by exact_mod_cast (mul_nonneg (sq_nonneg (n.choose k : ℤ)) (Int.natCast_nonneg _)))
      (pow_nonneg hr _)
  linarith

lemma aperyT_eq_mul_eval {n : ℕ} {v : ℤ} (hv : v ≠ 0) :
    (aperyT n v : ℚ) =
      (v : ℚ) ^ n * aeval ((-1 : ℚ) / (v : ℚ)) (aperyPolyZ n) := by
  rw [aperyPolyZ_aeval, Finset.mul_sum, aperyT]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hvne : (v : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hv
  have hpow : ((-1 : ℚ) / (v : ℚ)) ^ k = (-1 : ℚ) ^ k / (v : ℚ) ^ k := by
    rw [div_pow]
  rw [hpow]
  field_simp [hvne]
  have hpow' : (v : ℚ) ^ (n - k) * (v : ℚ) ^ k = (v : ℚ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  simp [mul_assoc, hpow']

/- Reverse polynomial -/

lemma reverse_aperyPolyZ_coeff (n j : ℕ) (hj : j ≤ n) :
    (aperyPolyZ n).reverse.coeff j = (aperyPolyZ n).coeff (n - j) := by
  rw [coeff_reverse, aperyPolyZ_natDegree, revAt_le hj]

lemma aperyPolyZ_reverse_leading (n : ℕ) :
    (aperyPolyZ n).reverse.leadingCoeff = 1 := by
  have htr : (aperyPolyZ n).natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero_of_constantCoeff_ne_zero]
    simp [constantCoeff, aperyPolyZ_coeff_zero]
  rw [reverse_leadingCoeff, trailingCoeff, htr, aperyPolyZ_coeff_zero]

lemma aperyPolyZ_reverse_natDegree (n : ℕ) :
    (aperyPolyZ n).reverse.natDegree = n := by
  have htr : (aperyPolyZ n).natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero_of_constantCoeff_ne_zero]
    simp [constantCoeff, aperyPolyZ_coeff_zero]
  rw [reverse_natDegree, aperyPolyZ_natDegree, htr, tsub_zero]

lemma aperyPolyZ_reverse_isPrimitive (n : ℕ) :
    (aperyPolyZ n).reverse.IsPrimitive := by
  intro r hr
  have : r ∣ (aperyPolyZ n).reverse.leadingCoeff :=
    (C_dvd_iff_dvd_coeff r _).mp hr ((aperyPolyZ n).reverse.natDegree)
  rw [aperyPolyZ_reverse_leading] at this
  exact isUnit_of_dvd_one this

lemma two_not_dvd_one : ¬ (2 : ℤ) ∣ 1 := by
  intro h
  have : (2 : ℤ) ≤ 1 := Int.le_of_dvd (by decide) h
  omega

lemma padicValNat_centralBinom_two_pow (m : ℕ) :
    padicValNat 2 ((2 ^ m + 2 ^ m).choose (2 ^ m)) = 1 := by
  have hle : 2 ^ m ≤ 2 ^ m + 2 ^ m := Nat.le_add_left _ _
  rw [padicValNat_choose_two hle]
  have hsub : 2 ^ m + 2 ^ m - 2 ^ m = 2 ^ m := Nat.add_sub_cancel _ _
  rw [hsub, s2_two_pow]
  have : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by
    rw [← two_mul, pow_succ']
  rw [this, s2_two_pow]

lemma aperyPolyZ_reverse_eisenstein_two_pow {m : ℕ} :
    (aperyPolyZ (2 ^ m)).reverse.IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  refine ⟨?leading, ?mem, ?notMem⟩
  · rw [aperyPolyZ_reverse_leading]
    intro h
    exact two_not_dvd_one (Ideal.mem_span_singleton.mp h)
  · intro j hj
    rw [aperyPolyZ_reverse_natDegree] at hj
    have hj' : j ≤ 2 ^ m := le_of_lt hj
    rw [reverse_aperyPolyZ_coeff _ _ hj']
    have hpos : 1 ≤ 2 ^ m - j := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hj)
    exact Ideal.mem_span_singleton.mpr (aperyPolyZ_coeff_even hpos)
  · rw [coeff_zero_reverse, aperyPolyZ_leadingCoeff]
    intro h
    have hdiv : (2 : ℤ) ^ 2 ∣ ((2 ^ m + 2 ^ m).choose (2 ^ m) : ℤ) := by
      have hmem : ((2 ^ m + 2 ^ m).choose (2 ^ m) : ℤ) ∈ Ideal.span {(2 : ℤ)} ^ 2 := h
      rw [Ideal.span_singleton_pow] at hmem
      simpa [pow_two] using (Ideal.mem_span_singleton.mp hmem)
    have hne : (2 ^ m + 2 ^ m).choose (2 ^ m) ≠ 0 :=
      (choose_pos (Nat.le_add_left (2 ^ m) (2 ^ m))).ne'
    haveI := two_prime_fact
    have hle : 2 ≤ padicValNat 2 ((2 ^ m + 2 ^ m).choose (2 ^ m)) := by
      have : (2 : ℕ) ^ 2 ∣ (2 ^ m + 2 ^ m).choose (2 ^ m) := by
        exact_mod_cast hdiv
      exact (padicValNat_dvd_iff_le hne).mp this
    have : padicValNat 2 ((2 ^ m + 2 ^ m).choose (2 ^ m)) = 1 :=
      padicValNat_centralBinom_two_pow m
    omega

lemma isUnit_of_reverse_isUnit {f : ℤ[X]} (h0 : f.coeff 0 ≠ 0)
    (hu : IsUnit f.reverse) : IsUnit f := by
  obtain ⟨u, huu, hf⟩ := Polynomial.isUnit_iff.mp hu
  have hfdeg : f.natDegree = 0 := by
    have htr : f.natTrailingDegree = 0 := by
      rw [natTrailingDegree_eq_zero_of_constantCoeff_ne_zero]
      simpa [constantCoeff] using h0
    have : f.reverse.natDegree = 0 := by
      rw [← hf, natDegree_C]
    have := reverse_natDegree f
    omega
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hfdeg
  have hfC : f = C c := hc.symm
  have hcu : c = u := by
    have : C c = C u := by
      rw [← reverse_C c, ← hfC, hf]
    exact C_injective this
  rw [hfC, hcu]
  exact Polynomial.isUnit_iff.mpr ⟨u, huu, rfl⟩

lemma reverse_irreducible_of_irreducible {f : ℤ[X]}
    (h0 : f.coeff 0 ≠ 0) (hir : Irreducible f.reverse) : Irreducible f := by
  refine ⟨fun hu => hir.not_isUnit ?_, ?_⟩
  · obtain ⟨u, huu, hf⟩ := Polynomial.isUnit_iff.mp hu
    rw [← hf, reverse_C]
    exact Polynomial.isUnit_iff.mpr ⟨u, huu, rfl⟩
  · intro a b hab
    have ha0 : a.coeff 0 ≠ 0 := by
      intro ha
      apply h0
      rw [hab, coeff_mul]
      apply Finset.sum_eq_zero
      intro ij hij
      have hij0 : ij.1 + ij.2 = 0 := Finset.mem_antidiagonal.mp hij
      have hi : ij.1 = 0 := by omega
      simp [hi, ha]
    have hb0 : b.coeff 0 ≠ 0 := by
      intro hb
      apply h0
      rw [hab, coeff_mul]
      apply Finset.sum_eq_zero
      intro ij hij
      have hij0 : ij.1 + ij.2 = 0 := Finset.mem_antidiagonal.mp hij
      have hj : ij.2 = 0 := by omega
      simp [hj, hb]
    have hmul : f.reverse = a.reverse * b.reverse := by
      rw [hab, reverse_mul_of_domain]
    rcases hir.isUnit_or_isUnit hmul with hu | hu
    · exact Or.inl (isUnit_of_reverse_isUnit ha0 hu)
    · exact Or.inr (isUnit_of_reverse_isUnit hb0 hu)

lemma prime_span_two : (Ideal.span {(2 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by decide : (2 : ℤ) ≠ 0)).mpr Int.prime_two

lemma apery_poly_irreducible_two_pow (m : ℕ) :
    Irreducible (apery_poly (2 ^ m)) := by
  rw [apery_poly_irreducible_iff]
  refine reverse_irreducible_of_irreducible (by simp [aperyPolyZ_coeff_zero]) ?_
  refine IsEisensteinAt.irreducible aperyPolyZ_reverse_eisenstein_two_pow
    prime_span_two (aperyPolyZ_reverse_isPrimitive _) ?_
  rw [aperyPolyZ_reverse_natDegree]
  exact pow_pos (by decide) m

lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  simpa [Nat.add_sub_cancel, add_comm] using
    s2_add_s2_sub_le (a + b) b (Nat.le_add_left b a)

lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · simp [hn, s2_zero]
  · exact s2_double hn

/-- If `n+1` is prime, the reverse of `aperyPolyZ n` is Eisenstein at `n+1`. -/
lemma aperyPolyZ_reverse_eisenstein_succ_prime {n : ℕ} (hn : 1 ≤ n)
    (hp : Nat.Prime (n + 1)) :
    (aperyPolyZ n).reverse.IsEisensteinAt (Ideal.span {(n + 1 : ℤ)}) := by
  haveI : Fact (Nat.Prime (n + 1)) := ⟨hp⟩
  refine ⟨?leading, ?mem, ?notMem⟩
  · rw [aperyPolyZ_reverse_leading]
    intro h
    have hdvd : (n + 1 : ℤ) ∣ 1 := Ideal.mem_span_singleton.mp h
    have hle : (n + 1 : ℤ) ≤ 1 := Int.le_of_dvd (by decide) hdvd
    have : (2 : ℤ) ≤ n + 1 := by exact_mod_cast (Nat.Prime.two_le hp)
    omega
  · intro j hj
    rw [aperyPolyZ_reverse_natDegree] at hj
    have hjle : j ≤ n := le_of_lt hj
    rw [reverse_aperyPolyZ_coeff _ _ hjle, aperyPolyZ_coeff]
    have hpos : 1 ≤ n - j := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hj)
    have hbig : n + 1 ≤ n + (n - j) := by omega
    have hdvd : (n + 1 : ℕ) ∣ (n + (n - j)).choose (n - j) :=
      hp.dvd_choose (by omega) (by omega) hbig
    have : (n + 1 : ℤ) ∣ ((n + (n - j)).choose (n - j) : ℤ) := by
      exact_mod_cast hdvd
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right this _)
  · rw [coeff_zero_reverse, aperyPolyZ_leadingCoeff]
    intro h
    have hdiv : (n + 1 : ℤ) ^ 2 ∣ ((n + n).choose n : ℤ) := by
      have hmem : ((n + n).choose n : ℤ) ∈ Ideal.span {(n + 1 : ℤ)} ^ 2 := h
      rw [Ideal.span_singleton_pow] at hmem
      simpa [pow_two] using (Ideal.mem_span_singleton.mp hmem)
    have hne : (n + n).choose n ≠ 0 := (choose_pos (Nat.le_add_left n n)).ne'
    have hle : 2 ≤ padicValNat (n + 1) ((n + n).choose n) := by
      have : (n + 1) ^ 2 ∣ (n + n).choose n := by exact_mod_cast hdiv
      exact (padicValNat_dvd_iff_le hne).mp this
    have heq : padicValNat (n + 1) ((n + n).choose n) = 1 := by
      have hdiv' : n.factorial * n.factorial ∣ (n + n).factorial := by
        simpa [Nat.add_sub_cancel] using
          Nat.factorial_mul_factorial_dvd_factorial (Nat.le_add_left n n)
      have hform : (n + n).choose n =
          (n + n).factorial / (n.factorial * n.factorial) := by
        simpa [Nat.add_sub_cancel] using
          Nat.choose_eq_factorial_div_factorial (Nat.le_add_left n n)
      rw [hform, padicValNat.div_of_dvd hdiv',
        padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
      have h2n : padicValNat (n + 1) (n + n).factorial = 1 := by
        have hbound : Nat.log (n + 1) (n + n) < 2 := by
          rw [Nat.log_lt_iff_lt_pow (Nat.Prime.one_lt hp) (by omega)]
          have : n + n < (n + 1) ^ 2 := by
            nlinarith [Nat.Prime.one_lt hp]
          exact this
        rw [padicValNat_factorial (p := n + 1) (n := n + n) hbound]
        have hIco : Finset.Ico 1 2 = {1} := by
          ext x; simp
        rw [hIco, Finset.sum_singleton]
        have : (n + n) / (n + 1) = 1 := by
          have hle : n + 1 ≤ n + n := by omega
          have hlt : n + n < 2 * (n + 1) := by omega
          rw [Nat.le_antisymm_iff]
          constructor
          · rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
            omega
          · rw [Nat.le_div_iff_mul_le (by omega)]
            omega
        simpa using this
      have hnfac : padicValNat (n + 1) n.factorial = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hd
        have : n + 1 ≤ n := (hp.dvd_factorial).mp hd
        omega
      rw [h2n, hnfac]
    omega

lemma apery_poly_irreducible_succ_prime {n : ℕ} (hn : 1 ≤ n)
    (hp : Nat.Prime (n + 1)) : Irreducible (apery_poly n) := by
  rw [apery_poly_irreducible_iff]
  refine reverse_irreducible_of_irreducible (by simp [aperyPolyZ_coeff_zero]) ?_
  have hP : (Ideal.span {(n + 1 : ℤ)}).IsPrime := by
    refine (Ideal.span_singleton_prime ?_).mpr ?_
    · exact_mod_cast (Nat.succ_ne_zero n)
    · exact Nat.prime_iff_prime_int.mp hp
  refine IsEisensteinAt.irreducible
    (aperyPolyZ_reverse_eisenstein_succ_prime hn hp) hP
    (aperyPolyZ_reverse_isPrimitive n) ?_
  rw [aperyPolyZ_reverse_natDegree]
  omega

lemma padicValNat_factorial_eq_zero_of_lt {p n : ℕ} (hp : Nat.Prime p) (h : n < p) :
    padicValNat p n.factorial = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  exact (not_le_of_gt h) ((hp.dvd_factorial).mp hd)

lemma padicValNat_choose_eq_zero_of_lt {p n k : ℕ} (hp : Nat.Prime p)
    (hn : n < p) (hk : k ≤ n) :
    padicValNat p (n.choose k) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hform := Nat.choose_eq_factorial_div_factorial hk
  have hdiv := Nat.factorial_mul_factorial_dvd_factorial hk
  rw [hform, padicValNat.div_of_dvd hdiv,
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat_factorial_eq_zero_of_lt hp hn,
    padicValNat_factorial_eq_zero_of_lt hp (lt_of_le_of_lt hk hn),
    padicValNat_factorial_eq_zero_of_lt hp (lt_of_le_of_lt (Nat.sub_le n k) hn)]

lemma padicValNat_factorial_one_of_mem_Ico {p m : ℕ} (hp : Nat.Prime p)
    (hlo : p ≤ m) (hhi : m < 2 * p) :
    padicValNat p m.factorial = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmpos : m ≠ 0 := by omega
  have hbound : Nat.log p m < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt hmpos]
    have : m < p ^ 2 := by
      have : m < p + p := by omega
      nlinarith [hp.two_le]
    exact this
  rw [padicValNat_factorial (p := p) (n := m) hbound]
  have hIco : Finset.Ico 1 2 = {1} := by ext x; simp
  rw [hIco, Finset.sum_singleton]
  have : m / p = 1 := by
    rw [Nat.le_antisymm_iff]
    constructor
    · rw [Nat.div_le_iff_le_mul_add_pred hp.pos]; omega
    · rw [Nat.le_div_iff_mul_le hp.pos]; omega
  simpa using this

lemma apery_coeff_val_of_prime {n k p : ℕ} (hp : Nat.Prime p) (hnp : n < p)
    (hk : k ≤ n) :
    padicValNat p (n.choose k ^ 2 * (n + k).choose k) =
      if p ≤ n + k then 1 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hC0 : padicValNat p (n.choose k) = 0 :=
    padicValNat_choose_eq_zero_of_lt hp hnp hk
  have hsq0 : padicValNat p (n.choose k ^ 2) = 0 := by
    rw [padicValNat.pow 2 (choose_pos hk).ne', hC0]
  have hprod :
      padicValNat p (n.choose k ^ 2 * (n + k).choose k) =
        padicValNat p ((n + k).choose k) := by
    rw [padicValNat.mul (pow_ne_zero 2 (choose_pos hk).ne')
      (choose_pos (Nat.le_add_left k n)).ne', hsq0, zero_add]
  rw [hprod]
  by_cases hpk : p ≤ n + k
  · rw [if_pos hpk]
    have hform := Nat.choose_eq_factorial_div_factorial (Nat.le_add_left k n)
    have hdiv := Nat.factorial_mul_factorial_dvd_factorial (Nat.le_add_left k n)
    rw [hform, padicValNat.div_of_dvd hdiv,
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    have hr : n + k - k = n := Nat.add_sub_cancel _ _
    rw [hr, padicValNat_factorial_eq_zero_of_lt hp hnp,
      padicValNat_factorial_eq_zero_of_lt hp (lt_of_le_of_lt hk hnp), add_zero]
    exact padicValNat_factorial_one_of_mem_Ico hp hpk (by omega)
  · rw [if_neg hpk]
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hlt : n + k < p := Nat.not_le.mp hpk
    have hf : ¬ p ∣ (n + k).factorial := by
      intro h
      exact (not_le_of_gt hlt) ((hp.dvd_factorial).mp h)
    have heq : (n + k).choose k * (k.factorial * n.factorial) = (n + k).factorial := by
      simpa [Nat.add_sub_cancel, mul_assoc] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k n)
    apply hf
    rw [← heq]
    exact dvd_mul_of_dvd_left hd _

/- Binary digit-sum recurrences -/

lemma s2_odd (m : ℕ) : s2 (2 * m + 1) = s2 m + 1 := by
  have hpos : 0 < 2 * m + 1 := Nat.succ_pos _
  unfold s2
  rw [Nat.digits_def' (by decide : 1 < 2) hpos]
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hmod, hdiv]
  simp [add_comm]

lemma s2_succ (m : ℕ) :
    s2 (m + 1) + padicValNat 2 (m + 1) = s2 m + 1 := by
  haveI := two_prime_fact
  have h1 : padicValNat 2 (m + 1).factorial =
      padicValNat 2 m.factorial + padicValNat 2 (m + 1) := by
    have hm1 : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
    have hfac : m.factorial ≠ 0 := Nat.factorial_ne_zero m
    rw [Nat.factorial_succ, mul_comm, padicValNat.mul hfac hm1]
  have hs : s2 m ≤ m := s2_le_self m
  have hs1 : s2 (m + 1) ≤ m + 1 := s2_le_self (m + 1)
  have hform := padicValNat_factorial_two (m + 1)
  have hform' := padicValNat_factorial_two m
  -- (m+1) - s2(m+1) = (m - s2 m) + v₂(m+1)
  have : (m + 1 - s2 (m + 1) : ℤ) =
      (m - s2 m : ℤ) + padicValNat 2 (m + 1) := by
    have h1' : (padicValNat 2 (m + 1).factorial : ℤ) =
        padicValNat 2 m.factorial + padicValNat 2 (m + 1) := by
      exact_mod_cast h1
    simpa [hform, hform', Int.ofNat_sub hs1, Int.ofNat_sub hs] using h1'
  have hZ : (s2 (m + 1) + padicValNat 2 (m + 1) : ℤ) = s2 m + 1 := by linarith
  exact_mod_cast hZ

lemma s2_succ_le (m : ℕ) : s2 (m + 1) ≤ s2 m + 1 := by
  have := s2_succ m
  omega

lemma s2_div2 (m : ℕ) : s2 (m / 2) = s2 m - m % 2 := by
  rcases Nat.even_or_odd m with h | h
  · obtain ⟨k, hk⟩ := h
    have hmod : m % 2 = 0 := Nat.even_iff.mp ⟨k, hk⟩
    have hdiv : m / 2 = k := by
      rw [hk, ← two_mul, Nat.mul_div_right _ (by decide)]
    rw [hdiv, show s2 m = s2 (2 * k) by rw [hk, ← two_mul], s2_two_mul, hmod]
    simp
  · obtain ⟨k, hk⟩ := h
    have hmod : m % 2 = 1 := Nat.odd_iff.mp ⟨k, hk⟩
    have hdiv : m / 2 = k := by
      rw [hk, Nat.add_comm, Nat.add_mul_div_left 1 k (by decide : 0 < 2)]
      simp
    rw [hdiv, show s2 m = s2 (2 * k + 1) by rw [hk], s2_odd, hmod]
    simp

lemma apery_coeff_val_rev {n j : ℕ} (hj : j ≤ n) :
    padicValNat 2 (n.choose (n - j) ^ 2 * (n + (n - j)).choose (n - j)) +
      s2 n + s2 (2 * n - j) = 3 * s2 (n - j) + 2 * s2 j := by
  have hk : n - j ≤ n := Nat.sub_le _ _
  have hval := apery_coeff_padicVal_two hk
  rw [hval, padicValNat_choose_two hk, padicValNat_choose_add_two]
  have hnj : n - (n - j) = j := Nat.sub_sub_self hj
  rw [hnj]
  have hsum : n + (n - j) = 2 * n - j := by omega
  rw [hsum]
  have hch : s2 (n - j) + s2 j ≥ s2 n := by
    simpa [hnj, add_comm] using s2_add_s2_sub_le n (n - j) hk
  have hch2 : s2 (n - j) + s2 n ≥ s2 (2 * n - j) := by
    have hjle : n - j ≤ 2 * n - j := by omega
    have hle := s2_add_s2_sub_le (2 * n - j) (n - j) hjle
    have hdiff : 2 * n - j - (n - j) = n := by omega
    simpa [hdiff] using hle
  have hsj : s2 j ≤ j := s2_le_self _
  have hsk : s2 (n - j) ≤ n - j := s2_le_self _
  have hsn : s2 n ≤ n := s2_le_self _
  have hs2 : s2 (2 * n - j) ≤ 2 * n - j := s2_le_self _
  -- lift to ℤ to avoid ℕ-subtraction issues
  have hz :
      ((s2 (n - j) + s2 j - s2 n : ℕ) : ℤ) = s2 (n - j) + s2 j - s2 n :=
    Int.ofNat_sub hch
  have hz2 :
      ((s2 (n - j) + s2 n - s2 (2 * n - j) : ℕ) : ℤ) =
        s2 (n - j) + s2 n - s2 (2 * n - j) :=
    Int.ofNat_sub hch2
  zify
  rw [hz, hz2]
  ring

/-- Key digit-sum inequality for the reverse 2-adic bound. -/
lemma s2_two_mul_sub_le {n j : ℕ} (hj : j ≤ n) :
    2 * s2 n + s2 (2 * n - j) ≤ 3 * s2 j + 3 * s2 (n - j) := by
  induction n using Nat.strong_induction_on generalizing j with
  | h n ih =>
    rcases n with _ | n
    · have : j = 0 := by omega
      simp [this, s2_zero]
    · rcases j with _ | j
      · have h2 : 2 * (n + 1) - 0 = 2 * (n + 1) := by omega
        rw [h2, s2_two_mul]
        simp [s2_zero]
        omega
      · rcases Nat.even_or_odd (n + 1) with hen | hon
        · obtain ⟨n2, hn2⟩ := hen
          have hn2e : n + 1 = 2 * n2 := by rw [two_mul]; exact hn2
          have hn2lt : n2 < n + 1 := by omega
          rcases Nat.even_or_odd (j + 1) with hej | hoj
          · obtain ⟨j2, hj2⟩ := hej
            have hj2e : j + 1 = 2 * j2 := by rw [two_mul]; exact hj2
            have hj2le : j2 ≤ n2 := by omega
            have ih2 := ih n2 hn2lt hj2le
            rw [hn2e, hj2e]
            have hsub : 2 * (2 * n2) - 2 * j2 = 2 * (2 * n2 - j2) := by omega
            have hnj : 2 * n2 - 2 * j2 = 2 * (n2 - j2) := by omega
            rw [hsub, hnj]
            simp [s2_two_mul]
            exact ih2
          · obtain ⟨j2, hj2⟩ := hoj
            have hj2e : j + 1 = 2 * j2 + 1 := hj2
            have hj2le : j2 + 1 ≤ n2 := by omega
            have ih2 := ih n2 hn2lt hj2le
            rw [hn2e, hj2e]
            have h2n : 2 * (2 * n2) - (2 * j2 + 1) = 2 * (2 * n2 - j2 - 1) + 1 := by omega
            have hnj : 2 * n2 - (2 * j2 + 1) = 2 * (n2 - j2 - 1) + 1 := by omega
            rw [s2_two_mul, s2_odd, h2n, s2_odd, hnj, s2_odd]
            have hA : 2 * n2 - (j2 + 1) = 2 * n2 - j2 - 1 := by omega
            have hB : n2 - (j2 + 1) = n2 - j2 - 1 := by omega
            rw [hA, hB] at ih2
            have hsj : s2 (j2 + 1) ≤ s2 j2 + 1 := s2_succ_le j2
            omega
        · obtain ⟨n2, hn2⟩ := hon
          have hn2o : n + 1 = 2 * n2 + 1 := hn2
          have hn2lt : n2 < n + 1 := by omega
          rcases Nat.even_or_odd (j + 1) with hej | hoj
          · obtain ⟨j2, hj2⟩ := hej
            have hj2e : j + 1 = 2 * j2 := by rw [two_mul]; exact hj2
            have hj2le : j2 ≤ n2 := by omega
            have ih2 := ih n2 hn2lt hj2le
            rw [hn2o, hj2e]
            have hsub : 2 * (2 * n2 + 1) - 2 * j2 = 2 * (2 * n2 + 1 - j2) := by omega
            have hnj : 2 * n2 + 1 - 2 * j2 = 2 * (n2 - j2) + 1 := by omega
            rw [s2_odd, s2_two_mul, hsub, s2_two_mul, hnj, s2_odd]
            have hcmp : s2 (2 * n2 + 1 - j2) ≤ s2 (2 * n2 - j2) + 1 := by
              cases j2 with
              | zero =>
                simpa [s2_odd] using (s2_two_mul n2).symm.le
              | succ j2 =>
                have heq1 : 2 * n2 + 1 - (j2 + 1) = 2 * n2 - j2 := by omega
                have heq2 : (2 * n2 - j2 - 1) + 1 = 2 * n2 - j2 := by omega
                rw [heq1, ← heq2]
                exact s2_succ_le (2 * n2 - j2 - 1)
            omega
          · obtain ⟨j2, hj2⟩ := hoj
            have hj2e : j + 1 = 2 * j2 + 1 := hj2
            have hj2le : j2 ≤ n2 := by omega
            have ih2 := ih n2 hn2lt hj2le
            rw [hn2o, hj2e]
            have hsub : 2 * (2 * n2 + 1) - (2 * j2 + 1) = 2 * (2 * n2 - j2) + 1 := by omega
            have hnj : 2 * n2 + 1 - (2 * j2 + 1) = 2 * (n2 - j2) := by omega
            rw [s2_odd, s2_odd, hsub, s2_odd, hnj, s2_two_mul]
            omega

lemma apery_coeff_val_rev_ge {n j : ℕ} (hj : j ≤ n) :
    s2 n ≤ padicValNat 2 (n.choose (n - j) ^ 2 * (n + (n - j)).choose (n - j)) + s2 j := by
  have h := apery_coeff_val_rev hj
  have hineq := s2_two_mul_sub_le hj
  omega

lemma s2_lt_self_of_two_le {j : ℕ} (hj : 2 ≤ j) : s2 j < j := by
  have hrec : s2 j ≤ j / 2 + j % 2 := by
    have := s2_div2 j
    have hle : s2 (j / 2) ≤ j / 2 := s2_le_self (j / 2)
    have hmod : j % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt j (by decide : 0 < 2))
    omega
  have : j / 2 + j % 2 < j := by
    have h2 : 0 < 2 := by decide
    have : j / 2 < j := Nat.div_lt_self (by omega) (by decide)
    omega
  omega

lemma s2_eq_self_iff {j : ℕ} : s2 j = j ↔ j ≤ 1 := by
  constructor
  · intro h
    by_contra hne
    have : 2 ≤ j := by omega
    have := s2_lt_self_of_two_le this
    omega
  · intro h
    interval_cases j <;> simp [s2_zero, s2_one]

lemma apery_coeff_central (n : ℕ) :
    n.choose n ^ 2 * (n + n).choose n = (n + n).choose n := by simp

lemma apery_coeff_pred (n : ℕ) (hn : 1 ≤ n) :
    n.choose (n - 1) ^ 2 * (n + (n - 1)).choose (n - 1) =
      n ^ 2 * (2 * n - 1).choose (n - 1) := by
  have hch : n.choose (n - 1) = n := by
    convert Nat.choose_succ_self_right (n - 1) using 2 <;> omega
  have hsum : n + (n - 1) = 2 * n - 1 := by omega
  rw [hch, hsum]

lemma s2_eq_zero_iff {n : ℕ} : s2 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    unfold s2 at h
    have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
    have hlast := Nat.getLast_digit_ne_zero (b := 2) hn
    have hmem := List.getLast_mem hne
    have hsum : (Nat.digits 2 n).sum = 0 := h
    have : ∀ x ∈ Nat.digits 2 n, x = 0 := by
      simpa [List.sum_eq_zero_iff] using hsum
    exact hlast (this _ hmem)
  · rintro rfl; exact s2_zero

lemma s2_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < s2 n := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  exact hn.ne' (s2_eq_zero_iff.mp h)

lemma choose_two_mul_eq_two_mul_pred (n : ℕ) (hn : 1 ≤ n) :
    (n + n).choose n = 2 * (2 * n - 1).choose (n - 1) := by
  have h := Nat.succ_mul_choose_eq (2 * n - 1) (n - 1)
  have hk : (2 * n - 1).succ = 2 * n := by omega
  have hr : (n - 1).succ = n := by omega
  rw [hk, hr] at h
  -- h : 2n * choose(2n-1, n-1) = choose(2n, n) * n
  have hnn : n + n = 2 * n := by ring
  have : (n + n).choose n * n = 2 * (2 * n - 1).choose (n - 1) * n := by
    rw [hnn]
    linarith [h]
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

lemma padicValNat_two_two : padicValNat 2 2 = 1 := by
  haveI := two_prime_fact
  exact padicValNat_self

lemma padicValNat_choose_two_pred (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 ((2 * n - 1).choose (n - 1)) = s2 n - 1 := by
  haveI := two_prime_fact
  have hrel := choose_two_mul_eq_two_mul_pred n hn
  have hne : (2 * n - 1).choose (n - 1) ≠ 0 :=
    (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
  have hs : 1 ≤ s2 n := Nat.succ_le_of_lt (s2_pos_of_pos (by omega))
  have : padicValNat 2 ((n + n).choose n) =
      padicValNat 2 2 + padicValNat 2 ((2 * n - 1).choose (n - 1)) := by
    rw [hrel, padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hne]
  rw [padicValNat_central_two, padicValNat_two_two] at this
  omega

lemma padicValNat_apery_pred {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 2 (n.choose (n - 1) ^ 2 * (n + (n - 1)).choose (n - 1)) =
      2 * padicValNat 2 n + s2 n - 1 := by
  haveI := two_prime_fact
  rw [apery_coeff_pred n hn]
  have hn0 : n ≠ 0 := by omega
  have hch0 : (2 * n - 1).choose (n - 1) ≠ 0 :=
    (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
  have hsq : n ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  rw [padicValNat.mul hsq hch0, padicValNat.pow 2 hn0, padicValNat_choose_two_pred n hn]
  have hs : 1 ≤ s2 n := Nat.succ_le_of_lt (s2_pos_of_pos (by omega))
  omega

/-- 2-adic size of the `k`-th term of `aperyT n w`, for `v = v₂(w)`. -/
def aperyTau (n k v : ℕ) : ℕ :=
  padicValNat 2 (n.choose k ^ 2 * (n + k).choose k) + (n - k) * v

lemma aperyTau_n (n v : ℕ) : aperyTau n n v = s2 n := by
  unfold aperyTau
  simp [padicValNat_central_two]

lemma aperyTau_sub_ge {n j v : ℕ} (hj : j ≤ n) :
    aperyTau n (n - j) v + s2 j ≥ aperyTau n n v + j * v := by
  have hnj : n - (n - j) = j := Nat.sub_sub_self hj
  have h1 : aperyTau n (n - j) v =
      padicValNat 2 (n.choose (n - j) ^ 2 * (n + (n - j)).choose (n - j)) + j * v := by
    unfold aperyTau; rw [hnj]
  have h2 : aperyTau n n v = s2 n := aperyTau_n n v
  rw [h1, h2]
  have := apery_coeff_val_rev_ge hj
  omega

lemma aperyTau_unique_min_of_two_le_val {n j v : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (hv : 2 ≤ v) : aperyTau n n v < aperyTau n (n - j) v := by
  have h := aperyTau_sub_ge (v := v) hjn
  have hs : s2 j ≤ j := s2_le_self j
  have : (aperyTau n n v : ℤ) + j * v ≤ aperyTau n (n - j) v + s2 j := by exact_mod_cast h
  have : (aperyTau n n v : ℤ) < aperyTau n (n - j) v := by nlinarith
  exact_mod_cast this

lemma aperyTau_unique_min_of_val_one {n j : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n) :
    aperyTau n n 1 < aperyTau n (n - j) 1 := by
  have h := aperyTau_sub_ge (v := 1) hjn
  have hs : s2 j < j := s2_lt_self_of_two_le hj
  omega

lemma aperyTau_pred_val_one {n : ℕ} (hn : 1 ≤ n) :
    aperyTau n (n - 1) 1 = aperyTau n n 1 + 2 * padicValNat 2 n := by
  have hnj : n - (n - 1) = 1 := by omega
  have h1 : aperyTau n (n - 1) 1 =
      padicValNat 2 (n.choose (n - 1) ^ 2 * (n + (n - 1)).choose (n - 1)) + 1 := by
    unfold aperyTau; rw [hnj]
  rw [h1, aperyTau_n, padicValNat_apery_pred hn]
  have hs : 1 ≤ s2 n := Nat.succ_le_of_lt (s2_pos_of_pos (by omega))
  omega

lemma aperyTau_unique_min_even {n j : ℕ} (hn : 1 ≤ n) (he : Even n)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    aperyTau n n 1 < aperyTau n (n - j) 1 := by
  rcases hj.eq_or_lt with rfl | hjt
  · have h := aperyTau_pred_val_one hn
    have : 1 ≤ padicValNat 2 n := by
      haveI := two_prime_fact
      have hn0 : n ≠ 0 := by omega
      have : 2 ∣ n := he.two_dvd
      exact (padicValNat_dvd_iff_le hn0).mp this
    omega
  · exact aperyTau_unique_min_of_val_one hjt hjn

/- Valuation of a finite sum with a unique minimal term. -/

lemma padicValInt_pow {p : ℕ} [hp : Fact p.Prime] {z : ℤ} (hz : z ≠ 0) (k : ℕ) :
    padicValInt p (z ^ k) = k * padicValInt p z := by
  simp [padicValInt, Int.natAbs_pow, padicValNat.pow k (Int.natAbs_ne_zero.mpr hz)]

lemma padicValInt_neg_one_pow (k : ℕ) : padicValInt 2 ((-1 : ℤ) ^ k) = 0 := by
  have h : ((-1 : ℤ) ^ k) = 1 ∨ ((-1 : ℤ) ^ k) = -1 := by
    rcases Nat.even_or_odd k with h | h
    · exact Or.inl (Even.neg_one_pow h)
    · exact Or.inr (Odd.neg_one_pow h)
  rcases h with h | h <;> simp [h]

lemma padicValInt_two_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt 2 (a * b) = padicValInt 2 a + padicValInt 2 b := by
  haveI := two_prime_fact
  exact padicValInt.mul ha hb

lemma padicValInt_sum_of_unique_min {p : ℕ} [hp : Fact p.Prime]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) {i0 : ι}
    (hi0 : i0 ∈ s) (hfi0 : f i0 ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ i0 → padicValInt p (f i0) < padicValInt p (f i) ∨ f i = 0) :
    padicValInt p (∑ i ∈ s, f i) = padicValInt p (f i0) := by
  let m := padicValInt p (f i0)
  have hdiv0 : (p : ℤ) ^ m ∣ f i0 := padicValInt_dvd _
  have hrest : ∀ i ∈ s.erase i0, (p : ℤ) ^ (m + 1) ∣ f i := by
    intro i hi
    have hi' : i ∈ s := Finset.mem_of_mem_erase hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    rcases hmin i hi' hne with hlt | hz
    · have hfi : f i ≠ 0 := by
        intro h
        simp [h] at hlt
      have hle' : m + 1 ≤ padicValInt p (f i) := Nat.succ_le_iff.mpr hlt
      exact dvd_trans (pow_dvd_pow (p : ℤ) hle') (padicValInt_dvd _)
    · simp [hz]
  have hsumrest : (p : ℤ) ^ (m + 1) ∣ ∑ i ∈ s.erase i0, f i :=
    Finset.dvd_sum hrest
  have hsum : ∑ i ∈ s, f i = f i0 + ∑ i ∈ s.erase i0, f i := by
    rw [add_comm, Finset.sum_erase_add _ _ hi0]
  have hdiv : (p : ℤ) ^ m ∣ ∑ i ∈ s, f i := by
    rw [hsum]
    exact dvd_add hdiv0 (dvd_trans (pow_dvd_pow _ (Nat.le_succ m)) hsumrest)
  have hndiv : ¬ (p : ℤ) ^ (m + 1) ∣ ∑ i ∈ s, f i := by
    intro h
    have h' : (p : ℤ) ^ (m + 1) ∣ f i0 + ∑ i ∈ s.erase i0, f i := by
      rwa [hsum] at h
    have : (p : ℤ) ^ (m + 1) ∣ f i0 := (dvd_add_left hsumrest).mp h'
    have hle' : m + 1 ≤ padicValInt p (f i0) :=
      ((padicValInt_dvd_iff (p := p) (n := m + 1) (a := f i0)).mp this).resolve_left hfi0
    omega
  have hsum0 : ∑ i ∈ s, f i ≠ 0 := by
    intro h
    apply hndiv
    simp [h]
  have hle : m ≤ padicValInt p (∑ i ∈ s, f i) := by
    have := (padicValInt_dvd_iff (p := p) (n := m) (a := ∑ i ∈ s, f i)).mp hdiv
    exact this.resolve_left hsum0
  have hnle : ¬ m + 1 ≤ padicValInt p (∑ i ∈ s, f i) := by
    intro h
    have : (p : ℤ) ^ (m + 1) ∣ ∑ i ∈ s, f i :=
      dvd_trans (pow_dvd_pow _ h) (padicValInt_dvd _)
    exact hndiv this
  omega

lemma apery_coeff_ne_zero {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) ≠ 0 := by
  have h1 : (n.choose k : ℤ) ≠ 0 := by exact_mod_cast (choose_pos hk).ne'
  have h2 : ((n + k).choose k : ℤ) ≠ 0 := by
    exact_mod_cast (choose_pos (Nat.le_add_left k n)).ne'
  exact mul_ne_zero (pow_ne_zero 2 h1) h2

lemma aperyT_term_val {n : ℕ} {w : ℤ} (hw : w ≠ 0) (k : ℕ) (hk : k ≤ n) :
    padicValInt 2
      (((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)) =
      aperyTau n k (padicValInt 2 w) := by
  haveI := two_prime_fact
  have hc : (n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) ≠ 0 := apery_coeff_ne_zero hk
  have hneg : (-1 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  have hwpow : w ^ (n - k) ≠ 0 := pow_ne_zero _ hw
  rw [mul_assoc, padicValInt.mul (p := 2) hc (mul_ne_zero hneg hwpow),
    padicValInt.mul (p := 2) hneg hwpow, padicValInt_neg_one_pow, zero_add,
    padicValInt_pow hw]
  unfold aperyTau
  simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]

lemma aperyT_ne_zero_of_unique_min {n : ℕ} {w : ℤ} (hw : w ≠ 0)
    (hmin : ∀ k ∈ Finset.range (n + 1), k ≠ n →
      aperyTau n n (padicValInt 2 w) < aperyTau n k (padicValInt 2 w)) :
    aperyT n w ≠ 0 := by
  haveI := two_prime_fact
  let f : ℕ → ℤ := fun k =>
    ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)
  have hnmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hterm0 : f n ≠ 0 := by
    have hc := apery_coeff_ne_zero (le_rfl : n ≤ n)
    exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by decide))) (pow_ne_zero _ hw)
  have hvales : ∀ k ∈ Finset.range (n + 1), k ≠ n →
      padicValInt 2 (f n) < padicValInt 2 (f k) ∨ f k = 0 := by
    intro k hk hne
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    refine Or.inl ?_
    rw [show padicValInt 2 (f n) = aperyTau n n (padicValInt 2 w) from
          aperyT_term_val hw n le_rfl,
        show padicValInt 2 (f k) = aperyTau n k (padicValInt 2 w) from
          aperyT_term_val hw k hk']
    exact hmin k hk hne
  have hval := padicValInt_sum_of_unique_min (p := 2) (s := Finset.range (n + 1))
    f hnmem hterm0 hvales
  intro h
  have hT : aperyT n w = ∑ k ∈ Finset.range (n + 1), f k := rfl
  have hval' : padicValInt 2 (aperyT n w) = padicValInt 2 (f n) := by
    simpa [hT] using hval
  rw [h] at hval'
  have hrhs := aperyT_term_val (n := n) hw n le_rfl
  have : padicValInt 2 (0 : ℤ) = aperyTau n n (padicValInt 2 w) := by
    simpa [f] using hval'.trans hrhs
  have hs : s2 n = 0 := by
    simpa [padicValInt.zero, aperyTau_n] using this.symm
  have hn0 : n = 0 := s2_eq_zero_iff.mp hs
  subst hn0
  simp [aperyT] at h

lemma aperyT_ne_zero_of_val_ge_two {n : ℕ} {w : ℤ} (hw : w ≠ 0)
    (hv : 2 ≤ padicValInt 2 w) : aperyT n w ≠ 0 := by
  apply aperyT_ne_zero_of_unique_min hw
  intro k hk hne
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hj : 1 ≤ n - k := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (lt_of_le_of_ne hk' hne))
  have hjn : n - k ≤ n := Nat.sub_le _ _
  have hmin' := aperyTau_unique_min_of_two_le_val (n := n) (j := n - k)
    (v := padicValInt 2 w) hj hjn hv
  have hrew : n - (n - k) = k := Nat.sub_sub_self hk'
  rwa [hrew] at hmin'

lemma aperyT_ne_zero_of_val_one_even {n : ℕ} {w : ℤ} (hn : 1 ≤ n) (he : Even n)
    (hw : w ≠ 0) (hv : padicValInt 2 w = 1) : aperyT n w ≠ 0 := by
  apply aperyT_ne_zero_of_unique_min hw
  intro k hk hne
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hj : 1 ≤ n - k := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (lt_of_le_of_ne hk' hne))
  have hmin' := aperyTau_unique_min_even (n := n) (j := n - k) hn he hj (Nat.sub_le _ _)
  have hrew : n - (n - k) = k := Nat.sub_sub_self hk'
  rw [hrew] at hmin'
  rwa [hv]

lemma aperyT_ne_zero_of_even_or_odd {n : ℕ} {w : ℤ} (hw : w ≠ 0)
    (h : Odd w ∨ 2 ≤ padicValInt 2 w ∨ (1 ≤ n ∧ Even n ∧ padicValInt 2 w = 1)) :
    aperyT n w ≠ 0 := by
  rcases h with h | h | h
  · exact aperyT_ne_zero_of_odd h
  · exact aperyT_ne_zero_of_val_ge_two hw h
  · exact aperyT_ne_zero_of_val_one_even h.1 h.2.1 hw h.2.2

lemma int_dvd_one {a : ℤ} (h : a ∣ 1) : a = 1 ∨ a = -1 :=
  Int.isUnit_iff.mp (isUnit_of_dvd_one h)

/- Rational roots of `apery_poly`. -/

lemma apery_poly_aeval_eq_eval (n : ℕ) (r : ℚ) :
    aeval r (aperyPolyZ n) = (apery_poly n).eval r :=
  (apery_poly_eval_eq_aeval n r).symm

lemma apery_poly_eq_zero_of_root {n : ℕ} {r : ℚ} (hr : (apery_poly n).eval r = 0) :
    aeval r (aperyPolyZ n) = 0 := by
  rwa [apery_poly_aeval_eq_eval]

lemma apery_poly_rational_root_form {n : ℕ} {r : ℚ}
    (hr : (apery_poly n).eval r = 0) :
    ∃ w : ℤ, 0 < w ∧ w ∣ ((n + n).choose n : ℤ) ∧ r = -1 / (w : ℚ) := by
  have h0 : aeval r (aperyPolyZ n) = 0 := apery_poly_eq_zero_of_root hr
  have hnum := num_dvd_of_is_root (A := ℤ) (K := ℚ) h0
  have hden := den_dvd_of_is_root (A := ℤ) (K := ℚ) h0
  rw [aperyPolyZ_coeff_zero] at hnum
  rw [aperyPolyZ_leadingCoeff] at hden
  have hrneg : r < 0 := by
    have : ¬ 0 ≤ r := by
      intro hge
      have := apery_poly_eval_pos (n := n) hge
      linarith
    exact lt_of_not_ge this
  set a := IsFractionRing.num ℤ r
  set b := (IsFractionRing.den ℤ r : ℤ)
  have hrepr : r = (a : ℚ) / (b : ℚ) := by
    simpa [a, b] using (IsFractionRing.mk'_num_den' (A := ℤ) (K := ℚ) r).symm
  have hab : a = 1 ∨ a = -1 := int_dvd_one hnum
  rcases hab with ha | ha
  · -- r = 1 / b < 0 ⇒ b < 0; take w = -b
    have hbneg : b < 0 := by
      have heq : r = (1 : ℚ) / (b : ℚ) := by
        rw [hrepr, ha]; simp
      have hr' : (1 : ℚ) / (b : ℚ) < 0 := heq ▸ hrneg
      rcases (div_neg_iff.mp hr') with h | h
      · exact_mod_cast h.2
      · exact absurd h.1 (by norm_num)
    refine ⟨-b, neg_pos.mpr hbneg, ?_, ?_⟩
    · simpa [b, dvd_neg] using hden
    · rw [hrepr, ha, Int.cast_neg]
      field_simp
      ring
  · -- r = -1 / b < 0 ⇒ b > 0; take w = b
    have hbpos : 0 < b := by
      have heq : r = (-1 : ℚ) / (b : ℚ) := by
        rw [hrepr, ha]; simp
      have hr' : (-1 : ℚ) / (b : ℚ) < 0 := heq ▸ hrneg
      rcases (div_neg_iff.mp hr') with h | h
      · exact absurd h.1 (by norm_num)
      · exact_mod_cast h.2
    refine ⟨b, hbpos, ?_, ?_⟩
    · simpa [b] using hden
    · rw [hrepr, ha]
      simp

lemma aperyT_eq_zero_of_root {n : ℕ} {w : ℤ} (hw : w ≠ 0)
    (hr : (apery_poly n).eval ((-1 : ℚ) / (w : ℚ)) = 0) :
    aperyT n w = 0 := by
  have h := aperyT_eq_mul_eval (n := n) hw
  have : aeval ((-1 : ℚ) / (w : ℚ)) (aperyPolyZ n) = 0 :=
    apery_poly_eq_zero_of_root hr
  have : (aperyT n w : ℚ) = 0 := by
    simpa [this] using h
  exact_mod_cast this

/- No rational roots for `n ≥ 2`. -/

lemma padicValInt_pos_of_two_dvd {w : ℤ} (hw : w ≠ 0) (hd : (2 : ℤ) ∣ w) :
    1 ≤ padicValInt 2 w := by
  have hne : padicValInt 2 w ≠ 0 := by
    intro h
    rcases padicValInt.eq_zero_iff.mp h with h | h | h
    · cases h
    · exact hw h
    · exact h hd
  omega

lemma aperyT_two_term {n : ℕ} {w : ℤ} (hn : 1 ≤ n) :
    ((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
      ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
        (-1 : ℤ) ^ (n - 1) * w =
      ((-1 : ℤ) ^ n) * ((2 * n - 1).choose (n - 1) : ℤ) * (2 - n ^ 2 * w) := by
  have hch : (n.choose (n - 1) : ℤ) = (n : ℤ) := by
    have : n.choose (n - 1) = n := by
      have h := Nat.choose_succ_self_right (n - 1)
      have : (n - 1 + 1) = n := by omega
      rwa [this] at h
    exact_mod_cast this
  have hsum : n + (n - 1) = 2 * n - 1 := by omega
  have hcn : ((n + n).choose n : ℤ) = 2 * ((2 * n - 1).choose (n - 1) : ℤ) := by
    exact_mod_cast choose_two_mul_eq_two_mul_pred n hn
  have hpow : (-1 : ℤ) ^ (n - 1) = - ((-1 : ℤ) ^ n) := by
    have : n = (n - 1) + 1 := by omega
    nth_rw 2 [this]
    rw [pow_succ]
    ring
  rw [hch, hsum, hcn, hpow]
  ring

lemma padicValNat_factorial_two_ge_two {j : ℕ} (hj : 4 ≤ j) :
    2 ≤ padicValNat 2 j.factorial := by
  haveI := two_prime_fact
  have hdiv : (4 : ℕ) ∣ j.factorial :=
    Nat.dvd_factorial (by decide : 0 < 4) hj
  have hne : j.factorial ≠ 0 := Nat.factorial_ne_zero _
  have : (2 : ℕ) ^ 2 ∣ j.factorial := by
    simpa using hdiv
  exact (padicValNat_dvd_iff_le hne).mp this

lemma padicValNat_factorial_two_ge_three {j : ℕ} (hj : 4 ≤ j) :
    3 ≤ padicValNat 2 j.factorial := by
  haveI := two_prime_fact
  have h8 : (8 : ℕ) ∣ (4 : ℕ).factorial := by decide
  have h4j : (4 : ℕ).factorial ∣ j.factorial :=
    Nat.factorial_dvd_factorial hj
  have hdiv : (8 : ℕ) ∣ j.factorial := dvd_trans h8 h4j
  have hne : j.factorial ≠ 0 := Nat.factorial_ne_zero _
  have : (2 : ℕ) ^ 3 ∣ j.factorial := by simpa using hdiv
  exact (padicValNat_dvd_iff_le hne).mp this

lemma aperyTau_of_ge_four {n j : ℕ} (hj : 4 ≤ j) (hjn : j ≤ n) :
    aperyTau n n 1 + 2 ≤ aperyTau n (n - j) 1 := by
  have h := aperyTau_sub_ge (v := 1) hjn
  have hfac : padicValNat 2 j.factorial = j - s2 j := padicValNat_factorial_two j
  have hge : 2 ≤ j - s2 j := by
    have := padicValNat_factorial_two_ge_two hj
    omega
  have hs : s2 j ≤ j := s2_le_self j
  have hnval : aperyTau n n 1 = s2 n := aperyTau_n n 1
  omega

lemma aperyTau_of_ge_four_three {n j : ℕ} (hj : 4 ≤ j) (hjn : j ≤ n) :
    aperyTau n n 1 + 3 ≤ aperyTau n (n - j) 1 := by
  have h := aperyTau_sub_ge (v := 1) hjn
  have hge : 3 ≤ j - s2 j := by
    have := padicValNat_factorial_two_ge_three hj
    have hfac : padicValNat 2 j.factorial = j - s2 j := padicValNat_factorial_two j
    omega
  have hs : s2 j ≤ j := s2_le_self j
  have hnval : aperyTau n n 1 = s2 n := aperyTau_n n 1
  omega

lemma s2_div2_odd {m : ℕ} : s2 (2 * m + 1) = s2 m + 1 := s2_odd m

lemma exists_of_odd (n : ℕ) (hn : Odd n) : ∃ m, n = 2 * m + 1 := hn

lemma aperyTau_sub_two_ge {n : ℕ} (hn : Odd n) (h2 : 2 ≤ n) :
    aperyTau n n 1 + 2 ≤ aperyTau n (n - 2) 1 := by
  obtain ⟨m, hm⟩ := exists_of_odd n hn
  have hmpos : 1 ≤ m := by omega
  have hjn : 2 ≤ n := h2
  have hrev := apery_coeff_val_rev (n := n) (j := 2) (by omega)
  have htau2 : aperyTau n (n - 2) 1 =
      padicValNat 2 (n.choose (n - 2) ^ 2 * (n + (n - 2)).choose (n - 2)) + 2 := by
    have : n - (n - 2) = 2 := by omega
    unfold aperyTau
    rw [this]
  have hs2 : s2 2 = 1 := by
    have : 2 = 2 ^ 1 := by decide
    rw [this, s2_two_pow]
  have h2n : 2 * n - 2 = 2 * (n - 1) := by omega
  have hn1 : n - 1 = 2 * m := by omega
  have hn2 : n - 2 = 2 * m - 1 := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_odd]
  have hs2n1 : s2 (n - 1) = s2 m := by
    rw [hn1, s2_two_mul]
  have hs2n2 : s2 (n - 2) = s2 (m - 1) + 1 := by
    have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [hn2, this, s2_odd]
  have h2n2 : s2 (2 * n - 2) = s2 (n - 1) := by
    rw [h2n, s2_two_mul]
  have hdiff :
      aperyTau n (n - 2) 1 = aperyTau n n 1 + 3 * padicValNat 2 m + 2 := by
    have hsucc := s2_succ (m - 1)
    have hm1 : (m - 1) + 1 = m := by omega
    rw [hm1] at hsucc
    -- s2 m + v₂(m) = s2 (m-1) + 1
    rw [htau2, aperyTau_n]
    have hz := hrev
    -- padic + s2 n + s2(2n-2) = 3 s2(n-2) + 2 s2 2
    rw [hs2, h2n2, hs2n1, hs2n, hs2n2] at hz
    -- padic + (s2 m + 1) + s2 m = 3 (s2 (m-1) + 1) + 2
    have : padicValNat 2 (n.choose (n - 2) ^ 2 * (n + (n - 2)).choose (n - 2)) +
        (s2 m + 1) + s2 m = 3 * (s2 (m - 1) + 1) + 2 := by
      simpa using hz
    have hv : s2 m + padicValNat 2 m = s2 (m - 1) + 1 := hsucc
    have hsle : s2 (m - 1) ≤ m - 1 := s2_le_self _
    have hsm : s2 m ≤ m := s2_le_self _
    omega
  have : 0 ≤ padicValNat 2 m := Nat.zero_le _
  omega

lemma aperyTau_sub_two_of_mod_four_one {n : ℕ} (hn : Odd n) (h2 : 2 ≤ n)
    (hmod : n % 4 = 1) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - 2) 1 := by
  obtain ⟨m, hm⟩ := exists_of_odd n hn
  have hmpos : 1 ≤ m := by omega
  have hge := aperyTau_sub_two_ge hn h2
  -- `n = 4t+1` ⇒ `m = 2t` is even, so `v₂(m) ≥ 1` and the exact
  -- increment `3 v₂(m) + 2` is at least 5.
  have hmeven : Even m := by
    have : n = 4 * (n / 4) + 1 := by
      have := Nat.div_add_mod n 4
      omega
    have : m = 2 * (n / 4) := by omega
    exact ⟨n / 4, by omega⟩
  haveI := two_prime_fact
  have hv : 1 ≤ padicValNat 2 m := by
    have hdiv : 2 ∣ m := even_iff_two_dvd.mp hmeven
    have hm0 : m ≠ 0 := by omega
    exact (padicValNat_dvd_iff_le hm0).mp hdiv
  -- Reuse the exact identity from the previous proof via `apery_coeff_val_rev`.
  have hrev := apery_coeff_val_rev (n := n) (j := 2) (by omega)
  have htau2 : aperyTau n (n - 2) 1 =
      padicValNat 2 (n.choose (n - 2) ^ 2 * (n + (n - 2)).choose (n - 2)) + 2 := by
    have : n - (n - 2) = 2 := by omega
    unfold aperyTau
    rw [this]
  have hs2 : s2 2 = 1 := by
    have : 2 = 2 ^ 1 := by decide
    rw [this, s2_two_pow]
  have h2n : 2 * n - 2 = 2 * (n - 1) := by omega
  have hn1 : n - 1 = 2 * m := by omega
  have hn2 : n - 2 = 2 * m - 1 := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_odd]
  have hs2n1 : s2 (n - 1) = s2 m := by rw [hn1, s2_two_mul]
  have hs2n2 : s2 (n - 2) = s2 (m - 1) + 1 := by
    have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [hn2, this, s2_odd]
  have h2n2 : s2 (2 * n - 2) = s2 (n - 1) := by rw [h2n, s2_two_mul]
  have hsucc := s2_succ (m - 1)
  have hm1 : (m - 1) + 1 = m := by omega
  rw [hm1] at hsucc
  rw [htau2, aperyTau_n]
  rw [hs2, h2n2, hs2n1, hs2n, hs2n2] at hrev
  have hsle : s2 (m - 1) ≤ m - 1 := s2_le_self _
  have hsm : s2 m ≤ m := s2_le_self _
  omega

lemma aperyTau_sub_three {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    aperyTau n (n - 3) 1 = aperyTau n n 1 + 1 + 2 * padicValNat 2 ((n - 1) / 2) := by
  obtain ⟨m, hm⟩ := exists_of_odd n hn
  have hmpos : 1 ≤ m := by omega
  have htau3 : aperyTau n (n - 3) 1 =
      padicValNat 2 (n.choose (n - 3) ^ 2 * (n + (n - 3)).choose (n - 3)) + 3 := by
    have : n - (n - 3) = 3 := by omega
    unfold aperyTau
    rw [this]
  have hrev := apery_coeff_val_rev (n := n) (j := 3) (by omega)
  have hs3 : s2 3 = 2 := by
    have : 3 = 2 * 1 + 1 := rfl
    rw [this, s2_odd, s2_one]
  have hn1 : n - 1 = 2 * m := by omega
  have hn3 : n - 3 = 2 * (m - 1) := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_odd]
  have hs2n3 : s2 (n - 3) = s2 (m - 1) := by
    rw [hn3, s2_two_mul]
  have h2n3 : 2 * n - 3 = 2 * (2 * m - 1) + 1 := by omega
  have hs2n2 : s2 (2 * n - 3) = s2 (m - 1) + 2 := by
    have hA : 2 * n - 3 = 2 * (2 * m - 1) + 1 := by omega
    have hB : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [hA, s2_odd, hB, s2_odd]
  have hmd : (n - 1) / 2 = m := by
    rw [hn1, Nat.mul_div_right _ (by decide : 0 < 2)]
  rw [htau3, aperyTau_n, hmd]
  have hz := hrev
  rw [hs3, hs2n, hs2n3, hs2n2] at hz
  -- padic + (s2 m + 1) + (s2 (m-1) + 2) = 3 s2 (m-1) + 2*2
  have hsucc := s2_succ (m - 1)
  have hm1 : (m - 1) + 1 = m := by omega
  rw [hm1] at hsucc
  have hsle : s2 (m - 1) ≤ m - 1 := s2_le_self _
  have hsm : s2 m ≤ m := s2_le_self _
  omega

lemma padicValNat_div2_of_mod_four {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    padicValNat 2 ((n - 1) / 2) = 0 ↔ n % 4 = 3 := by
  obtain ⟨m, hm⟩ := exists_of_odd n hn
  have hmd : (n - 1) / 2 = m := by
    have : n - 1 = 2 * m := by omega
    rw [this, Nat.mul_div_right _ (by decide)]
  rw [hmd]
  haveI := two_prime_fact
  constructor
  · intro h
    have hodd : Odd m := by
      rw [Nat.odd_iff]
      have : ¬ 2 ∣ m := by
        intro hd
        have : 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le (by omega)).mp hd
        omega
      exact Nat.not_even_iff.mp (mt even_iff_two_dvd.mp this)
    -- n = 2m+1 with m odd ⇒ n ≡ 3 mod 4
    obtain ⟨k, hk⟩ := hodd
    have : n = 4 * k + 3 := by omega
    rw [this, Nat.add_mod, Nat.mul_mod]
    simp
  · intro h
    have : n = 4 * (n / 4) + 3 := by
      have := Nat.div_add_mod n 4
      omega
    have : m = 2 * (n / 4) + 1 := by omega
    have hodd : Odd m := ⟨n / 4, this⟩
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hd)

lemma aperyTau_sub_three_of_mod_four {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hmod : n % 4 = 3) :
    aperyTau n (n - 3) 1 = aperyTau n n 1 + 1 := by
  rw [aperyTau_sub_three hn h3]
  have : padicValNat 2 ((n - 1) / 2) = 0 := (padicValNat_div2_of_mod_four hn h3).2 hmod
  simp [this]

lemma aperyTau_sub_three_of_mod_four_one {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hmod : n % 4 = 1) :
    aperyTau n n 1 + 3 ≤ aperyTau n (n - 3) 1 := by
  rw [aperyTau_sub_three hn h3]
  have hne : padicValNat 2 ((n - 1) / 2) ≠ 0 := by
    intro h
    have := (padicValNat_div2_of_mod_four hn h3).1 h
    omega
  have : 1 ≤ padicValNat 2 ((n - 1) / 2) := Nat.pos_of_ne_zero hne
  omega

lemma exists_odd_mul_two_of_val_one {w : ℤ} (hw : w ≠ 0)
    (hv : padicValInt 2 w = 1) : ∃ u : ℤ, Odd u ∧ w = 2 * u := by
  haveI := two_prime_fact
  have hdiv : (2 : ℤ) ∣ w := by
    have : (2 : ℤ) ^ 1 ∣ w :=
      (padicValInt_dvd_iff (p := 2) (n := 1) (a := w)).mpr (Or.inr (by omega))
    simpa using this
  obtain ⟨u, hu⟩ := hdiv
  refine ⟨u, ?_, hu⟩
  have hu0 : u ≠ 0 := by
    intro h; apply hw; simp [hu, h]
  have hsum : padicValInt 2 w = padicValInt 2 (2 : ℤ) + padicValInt 2 u := by
    rw [hu]
    exact padicValInt.mul (by decide : (2 : ℤ) ≠ 0) hu0
  have h2 : padicValInt 2 (2 : ℤ) = 1 := by
    simp [padicValInt]
  have huval : padicValInt 2 u = 0 := by omega
  have : ¬ (2 : ℤ) ∣ u := by
    intro hd
    have hne : padicValInt 2 u ≠ 0 := by
      intro hz
      rcases padicValInt.eq_zero_iff.mp hz with h | h | h
      · cases h
      · exact hu0 h
      · exact h hd
    omega
  exact Int.not_even_iff_odd.mp (mt even_iff_two_dvd.mp this)

lemma two_sub_sq_val {n : ℕ} {u : ℤ} (hn2 : 2 ≤ n) (hn : Odd n) (hu : Odd u) :
    1 ≤ padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2 * u) := by
  have hnZ : (3 : ℤ) ≤ n := by
    have : 3 ≤ n := by
      have hodd : n % 2 = 1 := Nat.odd_iff.mp hn
      omega
    exact_mod_cast this
  have hoddn : Odd (n : ℤ) := (Int.odd_coe_nat _).mpr hn
  have hsq : Odd ((n : ℤ) ^ 2) := hoddn.pow
  have hprod : Odd ((n : ℤ) ^ 2 * u) := hsq.mul hu
  have h1 : Odd (1 : ℤ) := by decide
  have heven : Even ((1 : ℤ) - (n : ℤ) ^ 2 * u) := by
    have hneg : Odd (-((n : ℤ) ^ 2 * u)) := hprod.neg
    simpa [sub_eq_add_neg] using h1.add_odd hneg
  have hne : (1 : ℤ) - (n : ℤ) ^ 2 * u ≠ 0 := by
    intro h
    have heq : (n : ℤ) ^ 2 * u = 1 := by
      linarith
    have habs : |(n : ℤ) ^ 2 * u| = 1 := by simp [heq]
    have : 9 ≤ |(n : ℤ) ^ 2 * u| := by
      have huabs : 1 ≤ |u| := by
        have : u ≠ 0 := by
          intro hu0
          have : Even u := by simp [hu0]
          exact Int.not_even_iff_odd.mpr hu this
        exact Int.one_le_abs this
      have : (9 : ℤ) ≤ (n : ℤ) ^ 2 := by nlinarith
      have : (9 : ℤ) ≤ (n : ℤ) ^ 2 * |u| := by nlinarith
      simpa [abs_mul, abs_pow] using this
    omega
  haveI := two_prime_fact
  have : (2 : ℤ) ∣ (1 - (n : ℤ) ^ 2 * u) := even_iff_two_dvd.mp heven
  exact padicValInt_pos_of_two_dvd hne this

lemma apery_two_term_eq {n : ℕ} {w : ℤ} (hn : 1 ≤ n) :
    ((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
      ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
        (-1 : ℤ) ^ (n - 1) * w =
      ((-1 : ℤ) ^ n) * ((2 * n - 1).choose (n - 1) : ℤ) * (2 - (n : ℤ) ^ 2 * w) :=
  aperyT_two_term hn

lemma apery_two_term_val {n : ℕ} {w : ℤ} (hn : 2 ≤ n) (hw : w ≠ 0)
    (hwpos : 0 < w) :
    padicValInt 2
      (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
        ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
          (-1 : ℤ) ^ (n - 1) * w) =
      padicValInt 2 ((2 * n - 1).choose (n - 1) : ℤ) +
        padicValInt 2 (2 - (n : ℤ) ^ 2 * w) := by
  haveI := two_prime_fact
  rw [apery_two_term_eq (by omega : 1 ≤ n)]
  have hch : ((2 * n - 1).choose (n - 1) : ℤ) ≠ 0 := by
    exact_mod_cast (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
  have hneg : (-1 : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by decide)
  have hz : (2 - (n : ℤ) ^ 2 * w) ≠ 0 := by
    intro h
    have : (n : ℤ) ^ 2 * w = 2 := by linarith
    have hge : (4 : ℤ) ≤ (n : ℤ) ^ 2 * w := by
      have hn4 : (4 : ℤ) ≤ (n : ℤ) ^ 2 := by
        have : 2 ≤ n := hn
        nlinarith
      have hw1 : (1 : ℤ) ≤ w := by
        have : (0 : ℤ) < w := hwpos
        omega
      nlinarith
    omega
  have hassoc :
      ((-1 : ℤ) ^ n) * ((2 * n - 1).choose (n - 1) : ℤ) * (2 - (n : ℤ) ^ 2 * w) =
        ((-1 : ℤ) ^ n) * (((2 * n - 1).choose (n - 1) : ℤ) * (2 - (n : ℤ) ^ 2 * w)) := by
    ring
  rw [hassoc, padicValInt.mul (p := 2) hneg (mul_ne_zero hch hz),
    padicValInt.mul (p := 2) hch hz, padicValInt_neg_one_pow, zero_add]

lemma padicValInt_choose_two_pred_int {n : ℕ} (hn : 1 ≤ n) :
    padicValInt 2 ((2 * n - 1).choose (n - 1) : ℤ) = s2 n - 1 := by
  have h := padicValNat_choose_two_pred n hn
  have hs : 1 ≤ s2 n := Nat.succ_le_of_lt (s2_pos_of_pos (by omega))
  simp [padicValInt, h]

lemma aperyT_sum_split_two {n : ℕ} {w : ℤ} (hn : 2 ≤ n) :
    aperyT n w =
      (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
        ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
          (-1 : ℤ) ^ (n - 1) * w) +
      ∑ k ∈ Finset.range (n - 1),
        ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k) := by
  unfold aperyT
  have hset : Finset.range (n + 1) =
      insert n (insert (n - 1) (Finset.range (n - 1))) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  have hn1 : n - 1 ∉ Finset.range (n - 1) := by
    simp
  have hn0 : n ∉ insert (n - 1) (Finset.range (n - 1)) := by
    simp
    omega
  rw [hset, Finset.sum_insert hn0, Finset.sum_insert hn1]
  have hpow : n - (n - 1) = 1 := by omega
  simp [Nat.choose_self, Nat.sub_self, pow_zero, hpow, pow_one]
  ring

lemma aperyT_three (w : ℤ) :
    aperyT 3 w = w ^ 3 - 36 * w ^ 2 + 90 * w - 20 := by
  unfold aperyT
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_succ_succ]
  ring

lemma aperyT_three_ne_zero_of_val_one {w : ℤ} (hw : w ≠ 0)
    (hv : padicValInt 2 w = 1) : aperyT 3 w ≠ 0 := by
  obtain ⟨u, huodd, hw2⟩ := exists_odd_mul_two_of_val_one hw hv
  rw [aperyT_three, hw2]
  intro h
  have hform : (2 * u) ^ 3 - 36 * (2 * u) ^ 2 + 90 * (2 * u) - 20 =
      (4 : ℤ) * (2 * u ^ 3 - 36 * u ^ 2 + 45 * u - 5) := by ring
  have h4 : (4 : ℤ) * (2 * u ^ 3 - 36 * u ^ 2 + 45 * u - 5) = 0 := by
    rwa [← hform]
  have h' : 2 * u ^ 3 - 36 * u ^ 2 + 45 * u - 5 = 0 :=
    (mul_eq_zero.mp h4).resolve_left (by decide)
  have hdvd : u ∣ (5 : ℤ) := by
    have eq : 2 * u ^ 3 - 36 * u ^ 2 + 45 * u = 5 := by linarith
    have hu3 : u ∣ u ^ 3 := ⟨u ^ 2, by ring⟩
    have hu2 : u ∣ u ^ 2 := ⟨u, by ring⟩
    have : u ∣ 2 * u ^ 3 - 36 * u ^ 2 + 45 * u :=
      dvd_add (dvd_sub (dvd_mul_of_dvd_right hu3 (2 : ℤ))
        (dvd_mul_of_dvd_right hu2 (36 : ℤ)))
        (dvd_mul_of_dvd_right (dvd_refl u) (45 : ℤ))
    rwa [eq] at this
  have habs : u.natAbs ∣ 5 := Int.natAbs_dvd_natAbs.mpr hdvd
  have hcases : u.natAbs = 1 ∨ u.natAbs = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  have : u = 1 ∨ u = -1 ∨ u = 5 ∨ u = -5 := by
    rcases hcases with h | h
    · rcases Int.natAbs_eq_iff.mp h with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (Or.inl (by exact_mod_cast h))
    · rcases Int.natAbs_eq_iff.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
      · exact Or.inr (Or.inr (Or.inr (by exact_mod_cast h)))
  rcases this with rfl | rfl | rfl | rfl <;> norm_num at h'

lemma two_sub_n2w_ne_zero {n : ℕ} {w : ℤ} (hn : 2 ≤ n) (hw : w ≠ 0) :
    (2 : ℤ) - (n : ℤ) ^ 2 * w ≠ 0 := by
  intro h
  have heq : (n : ℤ) ^ 2 * w = 2 := by linarith
  have hn2 : (4 : ℤ) ≤ (n : ℤ) ^ 2 := by
    nlinarith [show (2 : ℤ) ≤ n by exact_mod_cast hn]
  have : (4 : ℤ) ≤ |(n : ℤ) ^ 2 * w| := by
    rw [abs_mul, abs_pow]
    have : (1 : ℤ) ≤ |w| := Int.one_le_abs hw
    nlinarith [sq_abs (n : ℤ), abs_nonneg (n : ℤ)]
  have : |(n : ℤ) ^ 2 * w| = 2 := by simp [heq]
  omega

lemma apery_two_term_val' {n : ℕ} {w : ℤ} (hn : 2 ≤ n) (hw : w ≠ 0) :
    padicValInt 2
      (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
        ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
          (-1 : ℤ) ^ (n - 1) * w) =
      padicValInt 2 ((2 * n - 1).choose (n - 1) : ℤ) +
        padicValInt 2 (2 - (n : ℤ) ^ 2 * w) := by
  haveI := two_prime_fact
  rw [apery_two_term_eq (by omega : 1 ≤ n)]
  have hch : ((2 * n - 1).choose (n - 1) : ℤ) ≠ 0 := by
    exact_mod_cast (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
  have hneg : (-1 : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by decide)
  have hz := two_sub_n2w_ne_zero hn hw
  have hassoc :
      ((-1 : ℤ) ^ n) * ((2 * n - 1).choose (n - 1) : ℤ) * (2 - (n : ℤ) ^ 2 * w) =
        ((-1 : ℤ) ^ n) * (((2 * n - 1).choose (n - 1) : ℤ) * (2 - (n : ℤ) ^ 2 * w)) := by
    ring
  rw [hassoc, padicValInt.mul (p := 2) hneg (mul_ne_zero hch hz),
    padicValInt.mul (p := 2) hch hz, padicValInt_neg_one_pow, zero_add]

lemma two_sub_n2_two_mul {n : ℕ} {u : ℤ} :
    (2 : ℤ) - (n : ℤ) ^ 2 * (2 * u) = 2 * (1 - (n : ℤ) ^ 2 * u) := by
  ring

lemma apery_two_term_val_of_val_one {n : ℕ} {w u : ℤ}
    (hn : 2 ≤ n) (hw : w ≠ 0) (hu : w = 2 * u) :
    padicValInt 2
      (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
        ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
          (-1 : ℤ) ^ (n - 1) * w) =
      (s2 n - 1) + padicValInt 2 (2 - (n : ℤ) ^ 2 * w) := by
  haveI := two_prime_fact
  rw [apery_two_term_val' hn hw, padicValInt_choose_two_pred_int (by omega : 1 ≤ n)]

lemma padicValInt_two_mul_of_ne {z : ℤ} (hz : z ≠ 0) :
    padicValInt 2 (2 * z) = 1 + padicValInt 2 z := by
  haveI := two_prime_fact
  have h2 : (2 : ℤ) ≠ 0 := by decide
  rw [padicValInt.mul h2 hz]
  have : padicValInt 2 (2 : ℤ) = 1 := by simp [padicValInt]
  omega

lemma apery_two_term_val_cancel {n : ℕ} {w u : ℤ}
    (hn : 2 ≤ n) (hodd : Odd n) (hw : w ≠ 0) (huodd : Odd u) (hwu : w = 2 * u) :
    padicValInt 2
      (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
        ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
          (-1 : ℤ) ^ (n - 1) * w) =
      s2 n + padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2 * u) := by
  haveI := two_prime_fact
  have hval := apery_two_term_val_of_val_one hn hw hwu
  have hne : (1 : ℤ) - (n : ℤ) ^ 2 * u ≠ 0 := by
    have := two_sub_sq_val hn hodd huodd
    intro h
    have : (2 : ℤ) - (n : ℤ) ^ 2 * w = 0 := by
      rw [hwu, two_sub_n2_two_mul, h, mul_zero]
    exact two_sub_n2w_ne_zero hn hw this
  have hv2 : padicValInt 2 (2 - (n : ℤ) ^ 2 * w) =
      1 + padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2 * u) := by
    rw [hwu, two_sub_n2_two_mul, padicValInt_two_mul_of_ne hne]
  rw [hval, hv2]
  have hs : 1 ≤ s2 n := Nat.succ_le_of_lt (s2_pos_of_pos (by omega))
  omega

lemma aperyT_tail_term_val {n : ℕ} {w : ℤ} (hw : w ≠ 0) {k : ℕ} (hk : k ≤ n) :
    padicValInt 2
      (((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)) =
      aperyTau n k (padicValInt 2 w) :=
  aperyT_term_val hw k hk

def aperyT_term (n : ℕ) (w : ℤ) (k : ℕ) : ℤ :=
  ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)

lemma aperyT_eq_twoTerm_add_tail {n : ℕ} {w : ℤ} (hn : 2 ≤ n) :
    aperyT n w =
      (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
        ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
          (-1 : ℤ) ^ (n - 1) * w) +
      ∑ k ∈ Finset.range (n - 1), aperyT_term n w k := by
  simpa [aperyT_term] using aperyT_sum_split_two hn (w := w)

lemma aperyT_ne_zero_of_twoTerm_lt_tail {n : ℕ} {w : ℤ}
    (hn : 2 ≤ n) (hw : w ≠ 0)
    (hmin : ∀ k ∈ Finset.range (n - 1),
      padicValInt 2
          (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
            ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
              (-1 : ℤ) ^ (n - 1) * w) <
        padicValInt 2 (aperyT_term n w k)) :
    aperyT n w ≠ 0 := by
  haveI := two_prime_fact
  set twoTerm : ℤ :=
    ((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
      ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
        (-1 : ℤ) ^ (n - 1) * w
  have hTTne : twoTerm ≠ 0 := by
    have heq := apery_two_term_eq (by omega : 1 ≤ n) (w := w)
    simp only [twoTerm]
    rw [heq]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by decide)) ?_) (two_sub_n2w_ne_zero hn hw)
    exact_mod_cast (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
  have hsplit := aperyT_eq_twoTerm_add_tail hn (w := w)
  intro hT0
  set m := padicValInt 2 twoTerm
  have hrest : (2 : ℤ) ^ (m + 1) ∣
      ∑ k ∈ Finset.range (n - 1), aperyT_term n w k := by
    apply Finset.dvd_sum
    intro k hk
    have hlt := hmin k hk
    have hne : aperyT_term n w k ≠ 0 := by
      have hk' : k ≤ n := by
        have := Finset.mem_range.mp hk; omega
      have hc := apery_coeff_ne_zero hk'
      exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by decide))) (pow_ne_zero _ hw)
    have : m + 1 ≤ padicValInt 2 (aperyT_term n w k) := Nat.succ_le_iff.mpr hlt
    exact (padicValInt_dvd_iff (p := 2) (n := m + 1) _).mpr (Or.inr this)
  have : (2 : ℤ) ^ (m + 1) ∣ aperyT n w := by
    rw [hT0]; exact dvd_zero _
  have : (2 : ℤ) ^ (m + 1) ∣ twoTerm := by
    have hsum := hsplit
    -- `aperyT = twoTerm + tail`
    change aperyT n w = twoTerm + ∑ k ∈ Finset.range (n - 1), aperyT_term n w k at hsum
    rw [hsum] at this
    exact (dvd_add_left hrest).mp this
  have hnd : ¬ (2 : ℤ) ^ (m + 1) ∣ twoTerm := by
    intro h
    have : m + 1 ≤ padicValInt 2 twoTerm :=
      ((padicValInt_dvd_iff (p := 2) (n := m + 1) _).mp h).resolve_left hTTne
    simp [m] at this
  exact hnd this

lemma aperyT_ne_zero_of_tail_lt {n : ℕ} {w : ℤ} {k0 : ℕ}
    (hn : 2 ≤ n) (hw : w ≠ 0) (hk0 : k0 ∈ Finset.range (n - 1))
    (hminT : padicValInt 2 (aperyT_term n w k0) <
      padicValInt 2
        (((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
          ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
            (-1 : ℤ) ^ (n - 1) * w))
    (hminK : ∀ k ∈ Finset.range (n - 1), k ≠ k0 →
      padicValInt 2 (aperyT_term n w k0) < padicValInt 2 (aperyT_term n w k)) :
    aperyT n w ≠ 0 := by
  haveI := two_prime_fact
  set twoTerm : ℤ :=
    ((n + n).choose n : ℤ) * (-1 : ℤ) ^ n +
      ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) *
        (-1 : ℤ) ^ (n - 1) * w
  have hsplit := aperyT_eq_twoTerm_add_tail hn (w := w)
  have hk0' : k0 ≤ n := by
    have := Finset.mem_range.mp hk0; omega
  have hterm0 : aperyT_term n w k0 ≠ 0 := by
    have hc := apery_coeff_ne_zero hk0'
    exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by decide))) (pow_ne_zero _ hw)
  intro hT0
  set m := padicValInt 2 (aperyT_term n w k0)
  have hTTdvd : (2 : ℤ) ^ (m + 1) ∣ twoTerm := by
    have : m + 1 ≤ padicValInt 2 twoTerm := Nat.succ_le_iff.mpr hminT
    exact (padicValInt_dvd_iff (p := 2) (n := m + 1) _).mpr (Or.inr this)
  have hrest : (2 : ℤ) ^ (m + 1) ∣
      ∑ k ∈ (Finset.range (n - 1)).erase k0, aperyT_term n w k := by
    apply Finset.dvd_sum
    intro k hk
    have hk' : k ∈ Finset.range (n - 1) := Finset.mem_of_mem_erase hk
    have hne : k ≠ k0 := Finset.ne_of_mem_erase hk
    have hlt := hminK k hk' hne
    have hknz : aperyT_term n w k ≠ 0 := by
      have hkk : k ≤ n := by
        have := Finset.mem_range.mp hk'; omega
      have hc := apery_coeff_ne_zero hkk
      exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by decide))) (pow_ne_zero _ hw)
    have : m + 1 ≤ padicValInt 2 (aperyT_term n w k) := Nat.succ_le_iff.mpr hlt
    exact (padicValInt_dvd_iff (p := 2) (n := m + 1) _).mpr (Or.inr this)
  have hsumtail :
      ∑ k ∈ Finset.range (n - 1), aperyT_term n w k =
        aperyT_term n w k0 + ∑ k ∈ (Finset.range (n - 1)).erase k0, aperyT_term n w k := by
    rw [add_comm, Finset.sum_erase_add _ _ hk0]
  have : (2 : ℤ) ^ (m + 1) ∣ aperyT n w := by
    rw [hT0]; exact dvd_zero _
  have : (2 : ℤ) ^ (m + 1) ∣ aperyT_term n w k0 := by
    have hsum := hsplit
    change aperyT n w = twoTerm + ∑ k ∈ Finset.range (n - 1), aperyT_term n w k at hsum
    rw [hsum, hsumtail] at this
    have hoth : (2 : ℤ) ^ (m + 1) ∣
        twoTerm + ∑ k ∈ (Finset.range (n - 1)).erase k0, aperyT_term n w k :=
      dvd_add hTTdvd hrest
    have hre :
        twoTerm + (aperyT_term n w k0 +
          ∑ k ∈ (Finset.range (n - 1)).erase k0, aperyT_term n w k) =
        aperyT_term n w k0 +
          (twoTerm + ∑ k ∈ (Finset.range (n - 1)).erase k0, aperyT_term n w k) := by
      ring
    rw [hre] at this
    exact (dvd_add_left hoth).mp this
  have hnd : ¬ (2 : ℤ) ^ (m + 1) ∣ aperyT_term n w k0 := by
    intro h
    have : m + 1 ≤ padicValInt 2 (aperyT_term n w k0) :=
      ((padicValInt_dvd_iff (p := 2) (n := m + 1) _).mp h).resolve_left hterm0
    simp [m] at this
  exact hnd this

lemma aperyT_tail_val_ge {n : ℕ} {w : ℤ} {k : ℕ}
    (hw : w ≠ 0) (hv : padicValInt 2 w = 1) (hk : k ≤ n) :
    padicValInt 2 (aperyT_term n w k) = aperyTau n k 1 := by
  simpa [aperyT_term, hv] using aperyT_term_val hw k hk

lemma padicValInt_neg_one_pow_p {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    padicValInt p ((-1 : ℤ) ^ k) = 0 := by
  have h : ((-1 : ℤ) ^ k) = 1 ∨ ((-1 : ℤ) ^ k) = -1 := by
    rcases Nat.even_or_odd k with h | h
    · exact Or.inl (Even.neg_one_pow h)
    · exact Or.inr (Odd.neg_one_pow h)
  have hnd : ¬ (p : ℤ) ∣ (1 : ℤ) := by
    intro hd
    exact hp.out.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using hd))
  rcases h with h | h
  · rw [h]; exact padicValInt.eq_zero_of_not_dvd hnd
  · rw [h]; exact padicValInt.eq_zero_of_not_dvd (mt dvd_neg.mp hnd)

lemma aperyT_term_val_p {p : ℕ} [Fact p.Prime] {n : ℕ} {w : ℤ}
    (hw : w ≠ 0) (k : ℕ) (hk : k ≤ n) :
    padicValInt p
      (((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)) =
      padicValInt p ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) +
        (n - k) * padicValInt p w := by
  have hc : (n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) ≠ 0 := apery_coeff_ne_zero hk
  have hneg : (-1 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  have hwpow : w ^ (n - k) ≠ 0 := pow_ne_zero _ hw
  rw [mul_assoc, padicValInt.mul (p := p) hc (mul_ne_zero hneg hwpow),
    padicValInt.mul (p := p) hneg hwpow, padicValInt_neg_one_pow_p, zero_add,
    padicValInt_pow hw]

lemma padicValInt_choose_central {p n : ℕ} [hp : Fact p.Prime] :
    padicValInt p (((n + n).choose n : ℤ)) = padicValNat p ((n + n).choose n) := by
  simp [padicValInt]

lemma padicValNat_choose_two_mul_pred {p n : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    padicValNat p ((2 * n - 1).choose (n - 1)) = padicValNat p ((n + n).choose n) := by
  have hrel := choose_two_mul_eq_two_mul_pred n hn
  have hne : (2 * n - 1).choose (n - 1) ≠ 0 :=
    (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
  have h2ne : (2 : ℕ) ≠ 0 := by decide
  have : padicValNat p ((n + n).choose n) =
      padicValNat p 2 + padicValNat p ((2 * n - 1).choose (n - 1)) := by
    rw [hrel, padicValNat.mul h2ne hne]
  have h2 : padicValNat p 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd
    exact hp2 this
  omega

lemma padicValInt_pos_of_dvd {p : ℕ} [hp : Fact p.Prime] {w : ℤ}
    (hw : w ≠ 0) (hd : (p : ℤ) ∣ w) : 1 ≤ padicValInt p w := by
  have hne : padicValInt p w ≠ 0 := by
    intro h
    rcases padicValInt.eq_zero_iff.mp h with h | h | h
    · exact hp.out.ne_one h
    · exact hw h
    · exact h hd
  omega

/-- If an odd prime `q` divides `w` and `v_q(C(2n,n)) = 1`, the last term of
`aperyT` is the unique `q`-adic minimum. -/
lemma aperyT_ne_zero_of_odd_prime_val_one {n : ℕ} {w : ℤ} {q : ℕ}
    [hq : Fact q.Prime] (hq2 : q ≠ 2) (hw : w ≠ 0)
    (hqw : (q : ℤ) ∣ w) (hn : 1 ≤ n)
    (hC : padicValNat q ((n + n).choose n) = 1) :
    aperyT n w ≠ 0 := by
  let f : ℕ → ℤ := fun k =>
    ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)
  have hnmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hterm0 : f n ≠ 0 := by
    have hc := apery_coeff_ne_zero (le_rfl : n ≤ n)
    exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by decide : (-1 : ℤ) ≠ 0)))
      (pow_ne_zero _ hw)
  have hwn : 1 ≤ padicValInt q w := padicValInt_pos_of_dvd hw hqw
  have hvaln : padicValInt q (f n) = 1 := by
    have hv := aperyT_term_val_p (p := q) hw n le_rfl
    have hsub : n - n = 0 := Nat.sub_self n
    simp only [hsub, zero_mul, add_zero] at hv
    have hcn : padicValInt q ((n.choose n : ℤ) ^ 2 * ((n + n).choose n : ℤ)) =
        padicValNat q ((n + n).choose n) := by
      simp [padicValInt, Nat.choose_self]
    have : f n = ((n.choose n : ℤ) ^ 2 * ((n + n).choose n : ℤ)) *
        (-1 : ℤ) ^ n * w ^ (n - n) := rfl
    rw [this, aperyT_term_val_p (p := q) hw n le_rfl, hsub, zero_mul, add_zero, hcn, hC]
  have hmin : ∀ k ∈ Finset.range (n + 1), k ≠ n →
      padicValInt q (f n) < padicValInt q (f k) ∨ f k = 0 := by
    intro k hk hne
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hz : f k = 0
    · exact Or.inr hz
    · refine Or.inl ?_
      rw [hvaln, show f k =
          ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) * (-1 : ℤ) ^ k * w ^ (n - k)
          from rfl, aperyT_term_val_p (p := q) hw k hk']
      have hnkpos : 0 < n - k := Nat.sub_pos_of_lt (lt_of_le_of_ne hk' hne)
      have hge : 1 ≤ (n - k) * padicValInt q w := by
        have : 1 ≤ n - k := Nat.succ_le_iff.mpr hnkpos
        exact one_le_mul_of_one_le_of_one_le this hwn
      have hrestnonneg :
          0 ≤ padicValInt q ((n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)) :=
        Nat.zero_le _
      rcases lt_or_ge 1 (n - k) with h2 | h1
      · -- `n - k ≥ 2`
        have : 2 ≤ (n - k) * padicValInt q w :=
          Nat.mul_le_mul (Nat.succ_le_iff.mpr h2) hwn
        omega
      · -- `n - k = 1`, so `k = n - 1`
        have hk1 : k = n - 1 := by omega
        subst hk1
        have hform :
            ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) =
              (n : ℤ) ^ 2 * ((2 * n - 1).choose (n - 1) : ℤ) := by
          exact_mod_cast (apery_coeff_pred n hn)
        have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have hch0 : ((2 * n - 1).choose (n - 1) : ℤ) ≠ 0 := by
          exact_mod_cast (choose_pos (by omega : n - 1 ≤ 2 * n - 1)).ne'
        have hval_a :
            padicValInt q
              ((n.choose (n - 1) : ℤ) ^ 2 * ((n + (n - 1)).choose (n - 1) : ℤ)) =
              2 * padicValInt q (n : ℤ) + padicValNat q ((n + n).choose n) := by
          rw [hform, padicValInt.mul (pow_ne_zero 2 hn0) hch0, padicValInt_pow hn0]
          have : padicValInt q ((2 * n - 1).choose (n - 1) : ℤ) =
              padicValNat q ((n + n).choose n) := by
            simp [padicValInt, padicValNat_choose_two_mul_pred hq2 hn]
          rw [this]
        rw [hval_a, hC]
        have hnk1 : n - (n - 1) = 1 := by omega
        rw [hnk1, one_mul]
        omega
  have hval := padicValInt_sum_of_unique_min (p := q) (s := Finset.range (n + 1))
    f hnmem hterm0 hmin
  intro h
  have hT : aperyT n w = ∑ k ∈ Finset.range (n + 1), f k := rfl
  have : padicValInt q (0 : ℤ) = 1 := by
    rw [← h, hT, hval, hvaln]
  simp [padicValInt.zero] at this

lemma exists_prime_dvd_natAbs {u : ℤ} (hu : 1 < u.natAbs) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ u.natAbs :=
  Nat.exists_prime_and_dvd (by omega)

lemma aperyT_ne_zero_of_w_neg_two {n : ℕ} (hn : 2 ≤ n) {w : ℤ} (hw : w = -2) :
    aperyT n w ≠ 0 := by
  have hpos : 0 < (apery_poly n).eval ((1 : ℚ) / 2) := by
    have : (0 : ℚ) ≤ 1 / 2 := by norm_num
    exact apery_poly_eval_pos this
  intro hT
  have hv : w ≠ 0 := by simp [hw]
  have hmul := aperyT_eq_mul_eval (n := n) hv
  have hT0 : (aperyT n w : ℚ) = 0 := by exact_mod_cast hT
  have hw0 : (w : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hv
  have hae : aeval ((-1 : ℚ) / (w : ℚ)) (aperyPolyZ n) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero n hw0)
    simpa [hT0] using hmul.symm
  have hr : (apery_poly n).eval ((-1 : ℚ) / (w : ℚ)) = 0 := by
    rwa [apery_poly_eval_eq_aeval]
  have heq : (-1 : ℚ) / (w : ℚ) = (1 : ℚ) / 2 := by
    simp [hw]
  rw [heq] at hr
  exact (ne_of_gt hpos) hr


lemma s2_eight_mul_add_one (m : ℕ) : s2 (8 * m + 1) = s2 m + 1 := by
  rw [show 8 * m + 1 = 2 * (4 * m) + 1 by omega, s2_odd,
    show 4 * m = 2 * (2 * m) by omega, s2_two_mul, s2_two_mul]

lemma padicValNat_div2_ge_two_of_mod_eight_one {n : ℕ} (hmod : n % 8 = 1)
    (h3 : 3 ≤ n) : 2 ≤ padicValNat 2 ((n - 1) / 2) := by
  haveI := two_prime_fact
  have hn1 : n - 1 = 8 * (n / 8) := by
    have := Nat.div_add_mod n 8
    omega
  have hdiv : 4 ∣ (n - 1) / 2 := ⟨n / 8, by omega⟩
  have hne : (n - 1) / 2 ≠ 0 := by omega
  have : (2 : ℕ) ^ 2 ∣ (n - 1) / 2 := by simpa using hdiv
  exact (padicValNat_dvd_iff_le hne).mp this

lemma aperyTau_sub_three_mod_eight_one {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hmod : n % 8 = 1) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - 3) 1 := by
  rw [aperyTau_sub_three hn h3]
  have := padicValNat_div2_ge_two_of_mod_eight_one hmod h3
  omega

lemma aperyTau_of_ge_eight {n j : ℕ} (hj : 8 ≤ j) (hjn : j ≤ n) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - j) 1 := by
  have h := aperyTau_sub_ge (v := 1) hjn
  haveI := two_prime_fact
  have h32 : (32 : ℕ) ∣ (8 : ℕ).factorial := by decide
  have h8j : (8 : ℕ).factorial ∣ j.factorial := Nat.factorial_dvd_factorial hj
  have hdiv : (32 : ℕ) ∣ j.factorial := dvd_trans h32 h8j
  have hne : j.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hpow : (2 : ℕ) ^ 5 ∣ j.factorial := by simpa using hdiv
  have hge : 5 ≤ padicValNat 2 j.factorial := (padicValNat_dvd_iff_le hne).mp hpow
  have hfac : padicValNat 2 j.factorial = j - s2 j := padicValNat_factorial_two j
  have hs : s2 j ≤ j := s2_le_self j
  have : aperyTau n n 1 = s2 n := aperyTau_n n 1
  omega

lemma s2_two : s2 2 = 1 := by
  rw [show 2 = 2 ^ 1 by rfl, s2_two_pow]

lemma s2_three : s2 3 = 2 := by
  rw [show 3 = 2 * 1 + 1 by rfl, s2_odd, s2_one]

lemma s2_four : s2 4 = 1 := by
  rw [show 4 = 2 ^ 2 by rfl, s2_two_pow]

lemma s2_five : s2 5 = 2 := by
  rw [show 5 = 2 * 2 + 1 by rfl, s2_odd, s2_two]

lemma s2_six : s2 6 = 2 := by
  rw [show 6 = 2 * 3 by rfl, s2_two_mul, s2_three]

lemma s2_seven : s2 7 = 3 := by
  rw [show 7 = 2 * 3 + 1 by rfl, s2_odd, s2_three]

lemma apery_extra_eq {n j : ℕ} (hj : j ≤ n) :
    aperyTau n (n - j) 1 + s2 n + s2 (2 * n - j) =
      3 * s2 (n - j) + 2 * s2 j + j := by
  have hrev := apery_coeff_val_rev (n := n) (j := j) hj
  have htau : aperyTau n (n - j) 1 =
      padicValNat 2 (n.choose (n - j) ^ 2 * (n + (n - j)).choose (n - j)) + j := by
    have : n - (n - j) = j := Nat.sub_sub_self hj
    unfold aperyTau; rw [this, mul_one]
  rw [htau]
  linarith [hrev]

lemma exists_eight_mul_add_one {n : ℕ} (hmod : n % 8 = 1) :
    ∃ m, n = 8 * m + 1 :=
  ⟨n / 8, by have := Nat.div_add_mod n 8; omega⟩

lemma s2_eight_mul_add_five (t : ℕ) : s2 (8 * t + 5) = s2 t + 2 := by
  rw [show 8 * t + 5 = 2 * (4 * t + 2) + 1 by omega, s2_odd,
    show 4 * t + 2 = 2 * (2 * t + 1) by omega, s2_two_mul, s2_odd]

lemma s2_eight_mul_add_three (t : ℕ) : s2 (8 * t + 3) = s2 t + 2 := by
  rw [show 8 * t + 3 = 2 * (4 * t + 1) + 1 by omega, s2_odd,
    show 4 * t + 1 = 2 * (2 * t) + 1 by omega, s2_odd, s2_two_mul]

lemma s2_eight_mul_add_seven (t : ℕ) : s2 (8 * t + 7) = s2 t + 3 := by
  rw [show 8 * t + 7 = 2 * (4 * t + 3) + 1 by omega, s2_odd,
    show 4 * t + 3 = 2 * (2 * t + 1) + 1 by omega, s2_odd, s2_odd]

lemma s2_eight_mul_add_two (t : ℕ) : s2 (8 * t + 2) = s2 t + 1 := by
  rw [show 8 * t + 2 = 2 * (4 * t + 1) by omega, s2_two_mul,
    show 4 * t + 1 = 2 * (2 * t) + 1 by omega, s2_odd, s2_two_mul]

lemma aperyTau_sub_four_mod_eight_one {n : ℕ} (hn : Odd n) (h4 : 4 ≤ n)
    (hmod : n % 8 = 1) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - 4) 1 := by
  have hex := apery_extra_eq (n := n) (j := 4) (by omega)
  obtain ⟨m, hm⟩ := exists_eight_mul_add_one hmod
  have hmpos : 1 ≤ m := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_eight_mul_add_one]
  have hs2nj : s2 (n - 4) = s2 (m - 1) + 2 := by
    have h : n - 4 = 8 * (m - 1) + 5 := by omega
    rw [h, s2_eight_mul_add_five]
  have hs22 : s2 (2 * n - 4) = s2 (m - 1) + 3 := by
    have h : 2 * n - 4 = 2 * (8 * m - 1) := by omega
    have h' : 8 * m - 1 = 8 * (m - 1) + 7 := by omega
    rw [h, s2_two_mul, h', s2_eight_mul_add_seven]
  have htau : aperyTau n n 1 = s2 n := aperyTau_n n 1
  have hsucc : s2 m ≤ s2 (m - 1) + 1 := by
    simpa [Nat.sub_add_cancel hmpos] using s2_succ_le (m - 1)
  -- `s2 n + 5 ≤ tau` iff `2 s2 n + s2(2n-4) + 5 ≤ 3 s2(n-4) + 2 s2 4 + 4`.
  have hkey : 2 * s2 n + s2 (2 * n - 4) + 5 ≤ 3 * s2 (n - 4) + 2 * s2 4 + 4 := by
    rw [hs2n, hs2nj, hs22, s2_four]
    omega
  have : aperyTau n n 1 + 5 + s2 n + s2 (2 * n - 4) ≤
      aperyTau n (n - 4) 1 + s2 n + s2 (2 * n - 4) := by
    rw [htau]; linarith [hkey, hex]
  omega


lemma aperyTau_sub_five_mod_eight_one {n : ℕ} (hmod : n % 8 = 1) (h5 : 5 ≤ n) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - 5) 1 := by
  have hex := apery_extra_eq (n := n) (j := 5) (by omega)
  obtain ⟨m, hm⟩ := exists_eight_mul_add_one hmod
  have hmpos : 1 ≤ m := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_eight_mul_add_one]
  have hs2nj : s2 (n - 5) = s2 (m - 1) + 1 := by
    have h : n - 5 = 8 * (m - 1) + 4 := by omega
    rw [h, show 8 * (m - 1) + 4 = 2 * (2 * (2 * (m - 1) + 1)) by omega,
      s2_two_mul, s2_two_mul, s2_odd]
  have hs22 : s2 (2 * n - 5) = s2 (m - 1) + 3 := by
    have hx : 2 * n - 5 = 2 * (8 * m - 2) + 1 := by omega
    have h'' : 8 * m - 2 = 8 * (m - 1) + 6 := by omega
    rw [hx, s2_odd, h'', show 8 * (m - 1) + 6 = 2 * (4 * (m - 1) + 3) by omega,
      s2_two_mul, show 4 * (m - 1) + 3 = 2 * (2 * (m - 1) + 1) + 1 by omega,
      s2_odd, s2_odd]
  have htau : aperyTau n n 1 = s2 n := aperyTau_n n 1
  have hsucc : s2 m ≤ s2 (m - 1) + 1 := by
    simpa [Nat.sub_add_cancel hmpos] using s2_succ_le (m - 1)
  have hkey : 2 * s2 n + s2 (2 * n - 5) + 5 ≤ 3 * s2 (n - 5) + 2 * s2 5 + 5 := by
    rw [hs2n, hs2nj, hs22, s2_five]
    omega
  have : aperyTau n n 1 + 5 + s2 n + s2 (2 * n - 5) ≤
      aperyTau n (n - 5) 1 + s2 n + s2 (2 * n - 5) := by
    rw [htau]; linarith [hkey, hex]
  omega

lemma aperyTau_sub_six_mod_eight_one {n : ℕ} (hmod : n % 8 = 1) (h6 : 6 ≤ n) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - 6) 1 := by
  have hex := apery_extra_eq (n := n) (j := 6) (by omega)
  obtain ⟨m, hm⟩ := exists_eight_mul_add_one hmod
  have hmpos : 1 ≤ m := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_eight_mul_add_one]
  have hs2nj : s2 (n - 6) = s2 (m - 1) + 2 := by
    have h : n - 6 = 8 * (m - 1) + 3 := by omega
    rw [h, s2_eight_mul_add_three]
  have hs22 : s2 (2 * n - 6) = s2 (m - 1) + 2 := by
    have h : 2 * n - 6 = 2 * (8 * m - 2) := by omega
    have h' : 8 * m - 2 = 8 * (m - 1) + 6 := by omega
    rw [h, s2_two_mul, h', show 8 * (m - 1) + 6 = 2 * (4 * (m - 1) + 3) by omega,
      s2_two_mul, show 4 * (m - 1) + 3 = 2 * (2 * (m - 1) + 1) + 1 by omega,
      s2_odd, s2_odd]
  have htau : aperyTau n n 1 = s2 n := aperyTau_n n 1
  have hsucc : s2 m ≤ s2 (m - 1) + 1 := by
    simpa [Nat.sub_add_cancel hmpos] using s2_succ_le (m - 1)
  have hkey : 2 * s2 n + s2 (2 * n - 6) + 5 ≤ 3 * s2 (n - 6) + 2 * s2 6 + 6 := by
    rw [hs2n, hs2nj, hs22, s2_six]
    omega
  have : aperyTau n n 1 + 5 + s2 n + s2 (2 * n - 6) ≤
      aperyTau n (n - 6) 1 + s2 n + s2 (2 * n - 6) := by
    rw [htau]; linarith [hkey, hex]
  omega

lemma aperyTau_sub_seven_mod_eight_one {n : ℕ} (hmod : n % 8 = 1) (h7 : 7 ≤ n) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - 7) 1 := by
  have hex := apery_extra_eq (n := n) (j := 7) (by omega)
  obtain ⟨m, hm⟩ := exists_eight_mul_add_one hmod
  have hmpos : 1 ≤ m := by omega
  have hs2n : s2 n = s2 m + 1 := by rw [hm, s2_eight_mul_add_one]
  have hs2nj : s2 (n - 7) = s2 (m - 1) + 1 := by
    have h : n - 7 = 8 * (m - 1) + 2 := by omega
    rw [h, s2_eight_mul_add_two]
  have hs22 : s2 (2 * n - 7) = s2 (m - 1) + 3 := by
    have hx : 2 * n - 7 = 2 * (8 * m - 3) + 1 := by omega
    have h' : 8 * m - 3 = 8 * (m - 1) + 5 := by omega
    rw [hx, s2_odd, h', s2_eight_mul_add_five]
  have htau : aperyTau n n 1 = s2 n := aperyTau_n n 1
  have hsucc : s2 m ≤ s2 (m - 1) + 1 := by
    simpa [Nat.sub_add_cancel hmpos] using s2_succ_le (m - 1)
  have hkey : 2 * s2 n + s2 (2 * n - 7) + 5 ≤ 3 * s2 (n - 7) + 2 * s2 7 + 7 := by
    rw [hs2n, hs2nj, hs22, s2_seven]
    omega
  have : aperyTau n n 1 + 5 + s2 n + s2 (2 * n - 7) ≤
      aperyTau n (n - 7) 1 + s2 n + s2 (2 * n - 7) := by
    rw [htau]; linarith [hkey, hex]
  omega

lemma aperyTau_sub_j_mod_eight_one {n j : ℕ} (hodd : Odd n) (hmod : n % 8 = 1)
    (hn : 8 ≤ n) (hj : 2 ≤ j) (hjn : j ≤ n) (hj7 : j ≤ 7) :
    aperyTau n n 1 + 5 ≤ aperyTau n (n - j) 1 := by
  interval_cases j
  · exact aperyTau_sub_two_of_mod_four_one hodd (by omega) (by omega)
  · exact aperyTau_sub_three_mod_eight_one hodd (by omega) hmod
  · exact aperyTau_sub_four_mod_eight_one hodd (by omega) hmod
  · exact aperyTau_sub_five_mod_eight_one hmod (by omega)
  · exact aperyTau_sub_six_mod_eight_one hmod (by omega)
  · exact aperyTau_sub_seven_mod_eight_one hmod (by omega)

lemma aperyTau_tail_ge_five_of_mod_eight_one {n k : ℕ}
    (hodd : Odd n) (hmod : n % 8 = 1) (hn : 8 ≤ n) (hk : k < n - 1) :
    aperyTau n n 1 + 5 ≤ aperyTau n k 1 := by
  have hk' : k ≤ n := by omega
  have hrew : n - (n - k) = k := Nat.sub_sub_self hk'
  rcases le_or_gt 8 (n - k) with h8 | h8
  · have := aperyTau_of_ge_eight h8 (Nat.sub_le _ _)
    simpa [hrew] using this
  · have hj : 2 ≤ n - k := by omega
    have hj7 : n - k ≤ 7 := by omega
    have := aperyTau_sub_j_mod_eight_one hodd hmod hn hj (Nat.sub_le _ _) hj7
    simpa [hrew] using this

lemma padicValInt_n2_sub_one_mod_eight {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n)
    (hmod : n % 8 = 1) :
    4 ≤ padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2) := by
  haveI := two_prime_fact
  have hne : (1 : ℤ) - (n : ℤ) ^ 2 ≠ 0 := by
    have : (3 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hfact : (1 : ℤ) - (n : ℤ) ^ 2 = -(((n : ℤ) - 1) * ((n : ℤ) + 1)) := by ring
  have hne1 : (n : ℤ) - 1 ≠ 0 := by
    have : (3 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  have hne2 : (n : ℤ) + 1 ≠ 0 := by nlinarith
  have hv1 : 3 ≤ padicValInt 2 ((n : ℤ) - 1) := by
    have heq : (n : ℤ) - 1 = 8 * ((n / 8 : ℕ) : ℤ) := by
      have : n - 1 = 8 * (n / 8) := by
        have := Nat.div_add_mod n 8; omega
      have hZ : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) :=
        (Int.natCast_sub (by omega : 1 ≤ n)).symm
      calc
        (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := hZ
        _ = ((8 * (n / 8) : ℕ) : ℤ) := by rw [this]
        _ = 8 * ((n / 8 : ℕ) : ℤ) := by norm_cast
    have hdiv : (2 : ℤ) ^ 3 ∣ (n : ℤ) - 1 := ⟨((n / 8 : ℕ) : ℤ), heq⟩
    exact ((padicValInt_dvd_iff (p := 2) (n := 3) _).mp hdiv).resolve_left hne1
  have hv2 : 1 ≤ padicValInt 2 ((n : ℤ) + 1) := by
    have : Odd (n : ℤ) := (Int.odd_coe_nat _).mpr hodd
    have : Even ((n : ℤ) + 1) := by
      simpa [Int.even_add_one] using Int.not_even_iff_odd.mpr this
    exact padicValInt_pos_of_two_dvd hne2 (even_iff_two_dvd.mp this)
  have : padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2) =
      padicValInt 2 (((n : ℤ) - 1) * ((n : ℤ) + 1)) := by
    rw [hfact, padicValInt, Int.natAbs_neg, ← padicValInt]
  rw [this, padicValInt.mul hne1 hne2]
  omega

lemma aperyT_five_two : aperyT 5 2 ≠ 0 := by decide

lemma eight_dvd_n2_sub_one_of_mod_four_three {n : ℕ} (hodd : Odd n)
    (hmod : n % 4 = 3) : (8 : ℤ) ∣ (n : ℤ) ^ 2 - 1 := by
  have hnZ : Odd (n : ℤ) := (Int.odd_coe_nat _).mpr hodd
  obtain ⟨m, hm⟩ := hnZ
  have hsq : (n : ℤ) ^ 2 - 1 = 4 * m * (m + 1) := by rw [hm]; ring
  have he : Even (m * (m + 1)) := Int.even_mul_succ_self m
  obtain ⟨t, ht⟩ := even_iff_two_dvd.mp he
  have : (n : ℤ) ^ 2 - 1 = 8 * t := by
    calc
      (n : ℤ) ^ 2 - 1 = 4 * m * (m + 1) := hsq
      _ = 4 * (m * (m + 1)) := by ring
      _ = 4 * (2 * t) := by rw [ht]
      _ = 8 * t := by ring
  exact ⟨t, this⟩

lemma aperyT_thirteen_two : aperyT 13 2 ≠ 0 := by decide

lemma aperyT_twentyone_two : aperyT 21 2 ≠ 0 := by decide

/-- For odd `n ≡ 3 [MOD 4]` and `w = 2`, the index `k = n-3` is a unique
2-adic minimum of the tail, strictly below the two-term block. -/
lemma aperyT_ne_zero_of_w_two_mod_four_three {n : ℕ} {w : ℤ}
    (hn : 2 ≤ n) (hodd : Odd n) (hmod3 : n % 4 = 3) (hw : w = 2) :
    aperyT n w ≠ 0 := by
  haveI := two_prime_fact
  have hw0 : w ≠ 0 := by simp [hw]
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hu : Odd (1 : ℤ) := by decide
  have hwu : w = 2 * (1 : ℤ) := by simp [hw]
  apply aperyT_ne_zero_of_tail_lt (k0 := n - 3) hn hw0
  · exact Finset.mem_range.mpr (by omega)
  · have hTTval := apery_two_term_val_cancel hn hodd hw0 hu hwu
    have hne : (1 : ℤ) - (n : ℤ) ^ 2 ≠ 0 := by
      have : (3 : ℤ) ≤ n := by exact_mod_cast hn3
      nlinarith
    have h8 : (8 : ℤ) ∣ (n : ℤ) ^ 2 - 1 :=
      eight_dvd_n2_sub_one_of_mod_four_three hodd hmod3
    have : (8 : ℤ) ∣ (1 : ℤ) - (n : ℤ) ^ 2 :=
      (dvd_neg.mpr h8).trans (by simp)
    have : (2 : ℤ) ^ 3 ∣ (1 : ℤ) - (n : ℤ) ^ 2 := by
      simpa using this
    have hle3 : 3 ≤ padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2) :=
      ((padicValInt_dvd_iff (p := 2) (n := 3) _).mp this).resolve_left hne
    have hvc2 : 2 ≤ padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2 * (1 : ℤ)) := by
      simpa using (le_trans (by decide : 2 ≤ 3) hle3)
    rw [aperyT_term, aperyT_tail_term_val hw0 (by omega : n - 3 ≤ n),
      show padicValInt 2 w = 1 by simp [hw, padicValInt], hTTval]
    have h3eq := aperyTau_sub_three_of_mod_four hodd hn3 hmod3
    have : aperyTau n (n - 3) 1 = s2 n + 1 := by simpa [aperyTau_n] using h3eq
    omega
  · intro k hk hkne
    have hv : padicValInt 2 w = 1 := by simp [hw, padicValInt]
    rw [aperyT_term, aperyT_tail_term_val hw0 (by omega : n - 3 ≤ n), hv,
      aperyT_term, aperyT_tail_term_val hw0
        (by have := Finset.mem_range.mp hk; omega), hv]
    have h3eq := aperyTau_sub_three_of_mod_four hodd hn3 hmod3
    have h3val : aperyTau n (n - 3) 1 = s2 n + 1 := by
      simpa [aperyTau_n] using h3eq
    have hrew : n - (n - k) = k := Nat.sub_sub_self (by
      have := Finset.mem_range.mp hk; omega)
    rcases le_or_gt 4 (n - k) with h4 | h4
    · have hge := aperyTau_of_ge_four (n := n) (j := n - k) h4 (Nat.sub_le _ _)
      have : s2 n + 2 ≤ aperyTau n k 1 := by
        simpa [hrew, aperyTau_n] using hge
      omega
    · have hj : n - k = 2 ∨ n - k = 3 := by
        have hklt : k < n - 1 := Finset.mem_range.mp hk
        omega
      rcases hj with hj2 | hj3
      · have hge := aperyTau_sub_two_ge hodd (by omega)
        have hk2 : k = n - 2 := by omega
        have : s2 n + 2 ≤ aperyTau n k 1 := by
          simpa [aperyTau_n, hk2] using hge
        omega
      · exact (hkne (by omega)).elim

lemma padicValInt_n2_sub_one_mod_sixteen_nine {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n)
    (hmod : n % 16 = 9) :
    padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2) = 4 := by
  haveI := two_prime_fact
  have hne : (1 : ℤ) - (n : ℤ) ^ 2 ≠ 0 := by
    have : (3 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hfact : (1 : ℤ) - (n : ℤ) ^ 2 = -(((n : ℤ) - 1) * ((n : ℤ) + 1)) := by ring
  have hne1 : (n : ℤ) - 1 ≠ 0 := by
    have : (3 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  have hne2 : (n : ℤ) + 1 ≠ 0 := by nlinarith
  have hv1 : padicValInt 2 ((n : ℤ) - 1) = 3 := by
    have heq : (n : ℤ) - 1 = 8 * (2 * ((n / 16 : ℕ) : ℤ) + 1) := by
      have : n - 1 = 8 * (2 * (n / 16) + 1) := by
        have := Nat.div_add_mod n 16; omega
      have hZ : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) :=
        (Int.natCast_sub (by omega : 1 ≤ n)).symm
      calc
        (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := hZ
        _ = ((8 * (2 * (n / 16) + 1) : ℕ) : ℤ) := by rw [this]
        _ = 8 * (2 * ((n / 16 : ℕ) : ℤ) + 1) := by norm_cast
    have hodd' : Odd (2 * ((n / 16 : ℕ) : ℤ) + 1) := by
      refine ⟨((n / 16 : ℕ) : ℤ), ?_⟩
      ring
    have h8 : padicValInt 2 (8 : ℤ) = 3 := by
      have : (8 : ℤ) = 2 ^ 3 := by norm_num
      rw [this, padicValInt_pow (by decide : (2 : ℤ) ≠ 0)]
      simp [padicValInt]
    have hnz : (2 * ((n / 16 : ℕ) : ℤ) + 1) ≠ 0 := by
      intro h; linarith
    have hodd0 : padicValInt 2 (2 * ((n / 16 : ℕ) : ℤ) + 1) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hd
      exact Int.not_even_iff_odd.mpr hodd' (even_iff_two_dvd.mpr hd)
    rw [heq, padicValInt.mul (by decide : (8 : ℤ) ≠ 0) hnz, h8, hodd0]
  have hv2 : padicValInt 2 ((n : ℤ) + 1) = 1 := by
    have heq : (n : ℤ) + 1 = 2 * (8 * ((n / 16 : ℕ) : ℤ) + 5) := by
      have : n + 1 = 2 * (8 * (n / 16) + 5) := by
        have := Nat.div_add_mod n 16; omega
      have hZ : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by norm_cast
      calc
        (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := hZ
        _ = ((2 * (8 * (n / 16) + 5) : ℕ) : ℤ) := by rw [this]
        _ = 2 * (8 * ((n / 16 : ℕ) : ℤ) + 5) := by norm_cast
    have hodd5 : Odd (8 * ((n / 16 : ℕ) : ℤ) + 5) := by
      refine ⟨4 * ((n / 16 : ℕ) : ℤ) + 2, ?_⟩
      ring
    have hnz : (8 * ((n / 16 : ℕ) : ℤ) + 5) ≠ 0 := by
      intro h; linarith
    have hodd0 : padicValInt 2 (8 * ((n / 16 : ℕ) : ℤ) + 5) = 0 :=
      padicValInt.eq_zero_of_not_dvd (fun hd =>
        Int.not_even_iff_odd.mpr hodd5 (even_iff_two_dvd.mpr hd))
    have h2 : padicValInt 2 (2 : ℤ) = 1 := by simp [padicValInt]
    rw [heq, padicValInt.mul (by decide : (2 : ℤ) ≠ 0) hnz, h2, hodd0]
  have : padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2) =
      padicValInt 2 (((n : ℤ) - 1) * ((n : ℤ) + 1)) := by
    rw [hfact, padicValInt, Int.natAbs_neg, ← padicValInt]
  rw [this, padicValInt.mul hne1 hne2, hv1, hv2]

/-- For odd `n ≡ 9 [MOD 16]` and `w = 2`, the two-term 2-adic valuation is
strictly below the tail. -/
lemma aperyT_ne_zero_of_w_two_mod_sixteen_nine {n : ℕ} {w : ℤ}
    (hn : 2 ≤ n) (hodd : Odd n) (hmod : n % 16 = 9) (hw : w = 2) :
    aperyT n w ≠ 0 := by
  haveI := two_prime_fact
  have hw0 : w ≠ 0 := by simp [hw]
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hu : Odd (1 : ℤ) := by decide
  have hwu : w = 2 * (1 : ℤ) := by simp [hw]
  have hTTval := apery_two_term_val_cancel hn hodd hw0 hu hwu
  have hn8 : 8 ≤ n := by omega
  have hmod8 : n % 8 = 1 := by omega
  have hvc : padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2) = 4 :=
    padicValInt_n2_sub_one_mod_sixteen_nine hodd hn3 hmod
  have hvc' : padicValInt 2 ((1 : ℤ) - (n : ℤ) ^ 2 * (1 : ℤ)) = 4 := by
    simpa using hvc
  have hv : padicValInt 2 w = 1 := by simp [hw, padicValInt]
  apply aperyT_ne_zero_of_twoTerm_lt_tail hn hw0
  intro k hk
  have hk' : k ≤ n := by
    have := Finset.mem_range.mp hk; omega
  have hklt : k < n - 1 := Finset.mem_range.mp hk
  rw [hTTval, aperyT_tail_val_ge hw0 hv hk', hvc']
  have htail := aperyTau_tail_ge_five_of_mod_eight_one hodd hmod8 hn8 hklt
  have hsn : aperyTau n n 1 = s2 n := aperyTau_n n 1
  omega

lemma aperyT_ne_zero_of_w_two_mod_four_or_sixteen {n : ℕ} {w : ℤ}
    (hn : 2 ≤ n) (hodd : Odd n) (hw : w = 2)
    (hcase : n % 4 = 3 ∨ n % 16 = 9) : aperyT n w ≠ 0 := by
  rcases hcase with h3 | h9
  · exact aperyT_ne_zero_of_w_two_mod_four_three hn hodd h3 hw
  · exact aperyT_ne_zero_of_w_two_mod_sixteen_nine hn hodd h9 hw

lemma aperyT_ne_zero_of_even_n {n : ℕ} {w : ℤ} (hn : 1 ≤ n) (he : Even n)
    (hw : w ≠ 0) : aperyT n w ≠ 0 := by
  haveI := two_prime_fact
  rcases lt_trichotomy (padicValInt 2 w) 1 with h | h | h
  · have hodd : Odd w := by
      refine Int.not_even_iff_odd.mp ?_
      intro hev
      have hd : (2 : ℤ) ∣ w := even_iff_two_dvd.mp hev
      have : 1 ≤ padicValInt 2 w := padicValInt_pos_of_two_dvd hw hd
      omega
    exact aperyT_ne_zero_of_odd hodd
  · exact aperyT_ne_zero_of_val_one_even hn he hw h
  · exact aperyT_ne_zero_of_val_ge_two hw (Nat.succ_le_iff.mpr h)

lemma apery_poly_no_rational_root_even {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (r : ℚ) : (apery_poly n).eval r ≠ 0 := by
  intro hr
  obtain ⟨w, hwpos, -, hrfl⟩ := apery_poly_rational_root_form hr
  have hw0 : w ≠ 0 := ne_of_gt hwpos
  have hT : aperyT n w = 0 := aperyT_eq_zero_of_root hw0 (hrfl ▸ hr)
  exact aperyT_ne_zero_of_even_n (by omega) he hw0 hT

/-- If `n+2` is prime then `n` is odd (for `n ≥ 2`). -/
lemma odd_of_succ_succ_prime {n : ℕ} (hn : 2 ≤ n) (hp : Nat.Prime (n + 2)) : Odd n := by
  have hne : n + 2 ≠ 2 := by omega
  have : (n + 2) % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hne
  rw [Nat.odd_iff]
  omega

lemma dvd_of_padicValNat_pos {p a : ℕ} [hp : Fact p.Prime]
    (h : 0 < padicValNat p a) : p ∣ a := by
  have ha : a ≠ 0 := by
    intro h0; subst h0; simp at h
  have : p ^ 1 ∣ a := (padicValNat_dvd_iff_le ha).mpr (by omega)
  simpa using this

lemma aperyPolyZ_map_coeff_eq_zero_of_prime {n p k : ℕ} (hp : Nat.Prime p)
    (hnp : n < p) (hk : k ≤ n) (hpk : p ≤ n + k) :
    ((aperyPolyZ n).map (Int.castRingHom (ZMod p))).coeff k = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [coeff_map, aperyPolyZ_coeff, eq_intCast, CharP.intCast_eq_zero_iff (ZMod p) p]
  have hdiv : p ∣ n.choose k ^ 2 * (n + k).choose k :=
    dvd_of_padicValNat_pos (by
      have hval : padicValNat p (n.choose k ^ 2 * (n + k).choose k) = 1 := by
        simpa [if_pos hpk] using apery_coeff_val_of_prime hp hnp hk
      omega)
  exact_mod_cast hdiv

lemma aperyPolyZ_map_coeff_ne_zero_of_prime {n p k : ℕ} (hp : Nat.Prime p)
    (hnp : n < p) (hk : k ≤ n) (hpk : n + k < p) :
    ((aperyPolyZ n).map (Int.castRingHom (ZMod p))).coeff k ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [coeff_map, aperyPolyZ_coeff, eq_intCast]
  have hval : padicValNat p (n.choose k ^ 2 * (n + k).choose k) = 0 := by
    simpa [if_neg (Nat.not_le.mpr hpk)] using apery_coeff_val_of_prime hp hnp hk
  have hne : n.choose k ^ 2 * (n + k).choose k ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (choose_pos hk).ne')
      (choose_pos (Nat.le_add_left _ _)).ne'
  intro h0
  rw [CharP.intCast_eq_zero_iff (ZMod p) p] at h0
  have hdiv : p ∣ n.choose k ^ 2 * (n + k).choose k := by exact_mod_cast h0
  have : p ^ 1 ∣ n.choose k ^ 2 * (n + k).choose k := by simpa using hdiv
  have : 1 ≤ padicValNat p (n.choose k ^ 2 * (n + k).choose k) :=
    (padicValNat_dvd_iff_le hne).mp this
  omega

/-- Mapping `aperyPolyZ n` modulo a prime `p` with `n < p ≤ 2n` has degree `p - n - 1`. -/
lemma aperyPolyZ_map_degree_of_prime {n p : ℕ} (hp : Nat.Prime p) (hnp : n < p)
    (hp2n : p ≤ n + n) :
    ((aperyPolyZ n).map (Int.castRingHom (ZMod p))).natDegree = p - n - 1 := by
  have hδ : p - n - 1 ≤ n := by omega
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    by_cases hNn : n < N
    · rw [coeff_map, aperyPolyZ_coeff]
      simp [choose_eq_zero_of_lt hNn]
    · have hNle : N ≤ n := Nat.not_lt.mp hNn
      have hpk : p ≤ n + N := by omega
      exact aperyPolyZ_map_coeff_eq_zero_of_prime hp hnp hNle hpk
  · have hpk : n + (p - n - 1) < p := by omega
    exact aperyPolyZ_map_coeff_ne_zero_of_prime hp hnp hδ hpk

lemma s2_two_pow_mul (v t : ℕ) : s2 (2 ^ v * t) = s2 t := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hrew : 2 ^ (v + 1) * t = 2 * (2 ^ v * t) := by
      rw [pow_succ, mul_left_comm, mul_assoc]
    rw [hrew, s2_two_mul, ih]

lemma s2_eq_one_iff {n : ℕ} (hn : n ≠ 0) : s2 n = 1 ↔ ∃ m, n = 2 ^ m := by
  constructor
  · intro h
    obtain ⟨v, t, htodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
    have hst : s2 t = 1 := (s2_two_pow_mul v t).symm.trans h
    obtain ⟨k, hk⟩ := htodd
    have hk0 : k = 0 := by
      have : s2 t = s2 k + 1 := by rw [hk, s2_odd]
      have : s2 k = 0 := by omega
      exact s2_eq_zero_iff.mp this
    refine ⟨v, ?_⟩
    rw [hk, hk0]
    ring
  · rintro ⟨m, rfl⟩
    exact s2_two_pow m

lemma apery_poly_irreducible_of_s2_eq_one {n : ℕ} (hn : n ≠ 0) (h : s2 n = 1) :
    Irreducible (apery_poly n) := by
  obtain ⟨m, rfl⟩ := (s2_eq_one_iff hn).mp h
  exact apery_poly_irreducible_two_pow m

lemma padicValNat_central_of_mem_Ioc {n p : ℕ} (hp : Nat.Prime p)
    (hnp : n < p) (hp2n : p ≤ n + n) :
    padicValNat p ((n + n).choose n) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdiv : n.factorial * n.factorial ∣ (n + n).factorial := by
    simpa [Nat.add_sub_cancel] using
      Nat.factorial_mul_factorial_dvd_factorial (Nat.le_add_left n n)
  have hform : (n + n).choose n =
      (n + n).factorial / (n.factorial * n.factorial) := by
    simpa [Nat.add_sub_cancel] using
      Nat.choose_eq_factorial_div_factorial (Nat.le_add_left n n)
  rw [hform, padicValNat.div_of_dvd hdiv,
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat_factorial_eq_zero_of_lt hp hnp]
  simp
  exact padicValNat_factorial_one_of_mem_Ico hp hp2n (by omega)

lemma aperyPolyZ_leading_val {n p : ℕ} (hp : Nat.Prime p)
    (hnp : n < p) (hp2n : p ≤ n + n) :
    padicValInt p (aperyPolyZ n).leadingCoeff = 1 := by
  rw [aperyPolyZ_leadingCoeff, padicValInt, Int.natAbs_natCast,
    padicValNat_central_of_mem_Ioc hp hnp hp2n]

lemma natDegree_map_eq_of_not_dvd_leading {p : ℕ} [Fact p.Prime] {f : ℤ[X]}
    (hf : ¬ (p : ℤ) ∣ f.leadingCoeff) (_hf0 : f ≠ 0) :
    (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree := by
  apply natDegree_map_of_leadingCoeff_ne_zero
  rw [eq_intCast, Ne, CharP.intCast_eq_zero_iff (ZMod p) p]
  exact hf

/-- If `aperyPolyZ n = f * g` with both factors of positive degree and
`n < p ≤ 2n` is prime, then one of the factors has degree at most `p - n - 1`. -/
lemma apery_factor_degree_le {n p : ℕ} {f g : ℤ[X]}
    (hp : Nat.Prime p) (hnp : n < p) (hp2n : p ≤ n + n)
    (hfac : aperyPolyZ n = f * g)
    (hdf : 0 < f.natDegree) (hdg : 0 < g.natDegree) :
    f.natDegree ≤ p - n - 1 ∨ g.natDegree ≤ p - n - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hf0 : f ≠ 0 := fun h => by subst h; simp at hdf
  have hg0 : g ≠ 0 := fun h => by subst h; simp at hdg
  have hlead : f.leadingCoeff * g.leadingCoeff = ((n + n).choose n : ℤ) := by
    have hlc := congr_arg leadingCoeff hfac
    rw [leadingCoeff_mul, aperyPolyZ_leadingCoeff] at hlc
    exact hlc.symm
  have hv : padicValInt p (((n + n).choose n : ℤ)) = 1 := by
    rw [padicValInt, Int.natAbs_natCast, padicValNat_central_of_mem_Ioc hp hnp hp2n]
  have hlf : f.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hf0
  have hlg : g.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hg0
  have hsum : padicValInt p f.leadingCoeff + padicValInt p g.leadingCoeff = 1 := by
    rw [← padicValInt.mul hlf hlg, hlead, hv]
  have hmap : (aperyPolyZ n).map (Int.castRingHom (ZMod p)) =
      f.map (Int.castRingHom (ZMod p)) * g.map (Int.castRingHom (ZMod p)) := by
    rw [hfac, Polynomial.map_mul]
  have hdegp := aperyPolyZ_map_degree_of_prime hp hnp hp2n
  have hf00 : f.coeff 0 * g.coeff 0 = 1 := by
    have hconst := congr_arg constantCoeff hfac
    simpa [map_mul, aperyPolyZ_coeff_zero] using hconst.symm
  have hfbar0 : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro hz
    have hz0 : (f.map (Int.castRingHom (ZMod p))).coeff 0 = 0 := by simp [hz]
    rw [coeff_map, eq_intCast, CharP.intCast_eq_zero_iff (ZMod p) p] at hz0
    have : (p : ℤ) ∣ 1 := hz0.trans ⟨g.coeff 0, hf00.symm⟩
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using this))
  have hgbar0 : g.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro hz
    have hz0 : (g.map (Int.castRingHom (ZMod p))).coeff 0 = 0 := by simp [hz]
    rw [coeff_map, eq_intCast, CharP.intCast_eq_zero_iff (ZMod p) p] at hz0
    have : (p : ℤ) ∣ 1 := hz0.trans ⟨f.coeff 0, by rw [mul_comm, hf00]⟩
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using this))
  have hdeq : ((aperyPolyZ n).map (Int.castRingHom (ZMod p))).natDegree =
      (f.map (Int.castRingHom (ZMod p))).natDegree +
        (g.map (Int.castRingHom (ZMod p))).natDegree := by
    rw [hmap, natDegree_mul hfbar0 hgbar0]
  have hcases : (p : ℤ) ∣ f.leadingCoeff ∨ (p : ℤ) ∣ g.leadingCoeff := by
    by_contra h
    push_neg at h
    have hf1 : padicValInt p f.leadingCoeff = 0 :=
      padicValInt.eq_zero_of_not_dvd h.1
    have hg1 : padicValInt p g.leadingCoeff = 0 :=
      padicValInt.eq_zero_of_not_dvd h.2
    omega
  rcases hcases with hdfp | hdgp
  · have hng : ¬ (p : ℤ) ∣ g.leadingCoeff := by
      intro hg
      have : 1 ≤ padicValInt p f.leadingCoeff := padicValInt_pos_of_dvd hlf hdfp
      have : 1 ≤ padicValInt p g.leadingCoeff := padicValInt_pos_of_dvd hlg hg
      omega
    have hdg' : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree :=
      natDegree_map_eq_of_not_dvd_leading hng hg0
    have hle : g.natDegree ≤ p - n - 1 := by
      have := (f.map (Int.castRingHom (ZMod p))).natDegree
      omega
    exact Or.inr hle
  · have hnf : ¬ (p : ℤ) ∣ f.leadingCoeff := by
      intro hf
      have : 1 ≤ padicValInt p f.leadingCoeff := padicValInt_pos_of_dvd hlf hf
      have : 1 ≤ padicValInt p g.leadingCoeff := padicValInt_pos_of_dvd hlg hdgp
      omega
    have hdf' : (f.map (Int.castRingHom (ZMod p))).natDegree = f.natDegree :=
      natDegree_map_eq_of_not_dvd_leading hnf hf0
    have hle : f.natDegree ≤ p - n - 1 := by omega
    exact Or.inl hle

lemma aperyPolyZ_not_isUnit {n : ℕ} (hn : 1 ≤ n) : ¬ IsUnit (aperyPolyZ n) := by
  intro h
  have := natDegree_eq_zero_of_isUnit h
  rw [aperyPolyZ_natDegree] at this
  omega

lemma exists_mul_of_not_irreducible {n : ℕ} (hn : 1 ≤ n)
    (h : ¬ Irreducible (aperyPolyZ n)) :
    ∃ f g : ℤ[X], aperyPolyZ n = f * g ∧ 0 < f.natDegree ∧ 0 < g.natDegree := by
  have hnz : aperyPolyZ n ≠ 0 := by
    intro h0
    have := aperyPolyZ_natDegree n
    simp [h0] at this
    omega
  have hnu : ¬ IsUnit (aperyPolyZ n) := aperyPolyZ_not_isUnit hn
  rw [irreducible_iff] at h
  push_neg at h
  specialize h hnu
  obtain ⟨f, g, hfg, hfnu, hgnu⟩ := h
  have hf0 : f ≠ 0 := fun hf => by simp [hf] at hfg; exact hnz hfg
  have hg0 : g ≠ 0 := fun hg => by simp [hg] at hfg; exact hnz hfg
  have hdf : 0 < f.natDegree := by
    by_contra hle
    have hd0 : f.natDegree = 0 := by omega
    set c := f.coeff 0
    have hfC : f = C c := eq_C_of_natDegree_eq_zero hd0
    rw [hfC] at hfnu hfg
    have : IsUnit (C c) :=
      isUnit_C.mpr ((aperyPolyZ_isPrimitive n) _ ⟨g, hfg⟩)
    exact hfnu this
  have hdg : 0 < g.natDegree := by
    by_contra hle
    have hd0 : g.natDegree = 0 := by omega
    set c := g.coeff 0
    have hgC : g = C c := eq_C_of_natDegree_eq_zero hd0
    rw [hgC] at hgnu hfg
    have : IsUnit (C c) :=
      isUnit_C.mpr ((aperyPolyZ_isPrimitive n) _ ⟨f, by rw [hfg, mul_comm]⟩)
    exact hgnu this
  exact ⟨f, g, hfg, hdf, hdg⟩

lemma linear_has_rational_root {f : ℤ[X]} (hf : f.natDegree = 1) :
    ∃ r : ℚ, aeval r f = 0 := by
  have hf0 : f ≠ 0 := fun h => by simp [h] at hf
  have hlc : f.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hf0
  have hlcQ : (f.leadingCoeff : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hlc
  let r : ℚ := -((f.coeff 0 : ℚ) / (f.leadingCoeff : ℚ))
  refine ⟨r, ?_⟩
  have hform : f = C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one (by omega)
  have h1 : f.coeff 1 = f.leadingCoeff := by rw [leadingCoeff, hf]
  rw [hform, h1, aeval_add, aeval_mul, aeval_C, aeval_C, aeval_X]
  change (f.leadingCoeff : ℚ) * r + (f.coeff 0 : ℚ) = 0
  simp only [r]
  rw [mul_neg, mul_div_cancel₀ _ hlcQ, neg_add_cancel]

lemma no_deg_one_factor_of_no_rat_root {n : ℕ} {f g : ℤ[X]}
    (hfac : aperyPolyZ n = f * g) (hdf : f.natDegree = 1)
    (hnoroot : ∀ r : ℚ, (apery_poly n).eval r ≠ 0) : False := by
  obtain ⟨r, hr⟩ := linear_has_rational_root hdf
  have : (apery_poly n).eval r = 0 := by
    rw [apery_poly_eval_eq_aeval, hfac, aeval_mul, hr, zero_mul]
  exact hnoroot r this

lemma apery_poly_irreducible_of_bound_le_one {n p : ℕ}
    (hn : 1 ≤ n) (hp : Nat.Prime p) (hnp : n < p) (hp2n : p ≤ n + n)
    (hbound : p - n - 1 ≤ 1)
    (hnoroot : ∀ r : ℚ, (apery_poly n).eval r ≠ 0) :
    Irreducible (apery_poly n) := by
  rw [apery_poly_irreducible_iff]
  by_contra hred
  obtain ⟨f, g, hfac, hdf, hdg⟩ := exists_mul_of_not_irreducible hn hred
  have hle := apery_factor_degree_le hp hnp hp2n hfac hdf hdg
  have : f.natDegree = 1 ∨ g.natDegree = 1 := by omega
  rcases this with h1 | h1
  · exact no_deg_one_factor_of_no_rat_root hfac h1 hnoroot
  · exact no_deg_one_factor_of_no_rat_root (by rw [hfac, mul_comm]) h1 hnoroot

lemma apery_poly_irreducible_of_even_small_gap {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {p : ℕ} (hp : Nat.Prime p) (hnp : n < p) (hp2n : p ≤ n + n)
    (hbound : p - n - 1 ≤ 1) : Irreducible (apery_poly n) :=
  apery_poly_irreducible_of_bound_le_one (by omega) hp hnp hp2n hbound
    (apery_poly_no_rational_root_even hn he)

