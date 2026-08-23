import FormalConjectures.Util.ProblemImports

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.style.moduleDocstring false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option warningAsError false

open Nat Finset

/-!
# Supercongruences for OEIS A361883

We prove that the sequence
`a(n) = (1/n) ∑_{k=0}^n (n+2k) binom(n+k-1, k)^3`
satisfies the Wolstenholme-type supercongruences
`a(n * p^r) ≡ a(n * p^{r-1}) [MOD p^{3r}]`
for primes `p ≥ 5` and positive integers `n, r`.
-/

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

/- ## Basic binomial identities -/

/-- Rising binomial `C(n+k-1, k)`. For `n ≥ 1` this equals `C(n+k-1, n-1)`. -/
lemma choose_add_sub_one_eq {n k : ℕ} (hn : 1 ≤ n) :
    (n + k - 1).choose (n - 1) = (n + k - 1).choose k := by
  have hle : n - 1 ≤ n + k - 1 := by omega
  have hdiff : n + k - 1 - (n - 1) = k := by omega
  rw [← choose_symm hle, hdiff]

lemma a_eq_sum_div {n : ℕ} (hn : 0 < n) :
    a n = (∑ k ∈ range (n + 1),
      (n + 2 * k) * ((n + k - 1).choose k) ^ 3) / n := by
  unfold a
  simp only [hn.ne']
  refine congrArg (fun s => s / n) ?_
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [choose_add_sub_one_eq (by omega)]

/-- `k * C(n+k-1, k) = n * C(n+k-1, k-1)` for `k ≥ 1`. -/
lemma mul_choose_rising {n k : ℕ} (hk : 1 ≤ k) :
    k * (n + k - 1).choose k = n * (n + k - 1).choose (k - 1) := by
  cases n with
  | zero =>
    have : k - 1 < k := Nat.sub_lt (by omega) (by omega)
    simp [choose_eq_zero_of_lt this]
  | succ n =>
    have h1 : n + 1 + k - 1 = n + k := by omega
    have h2 : k - 1 + 1 = k := by omega
    rw [h1]
    have h3 : (n + k).choose k * k = (n + k).choose (k - 1) * (n + 1) := by
      have := choose_succ_right_eq (n + k) (k - 1)
      rw [h2] at this
      convert this using 2
      omega
    linarith

/-- Each summand is of the form `n * (integer)`. -/
lemma rising_summand_dvd (n k : ℕ) :
    n ∣ (n + 2 * k) * ((n + k - 1).choose k) ^ 3 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have hmul := mul_choose_rising (n := n) (k := k) (by omega)
    refine ⟨((n + k - 1).choose k) ^ 3 +
        2 * ((n + k - 1).choose (k - 1)) * ((n + k - 1).choose k) ^ 2, ?_⟩
    have : (n + 2 * k) * ((n + k - 1).choose k) ^ 3 =
        n * ((n + k - 1).choose k) ^ 3 +
          2 * (k * ((n + k - 1).choose k)) * ((n + k - 1).choose k) ^ 2 := by
      ring
    rw [this, hmul]
    ring

lemma sum_rising_dvd (n : ℕ) :
    n ∣ ∑ k ∈ range (n + 1), (n + 2 * k) * ((n + k - 1).choose k) ^ 3 := by
  refine dvd_sum fun k hk => rising_summand_dvd n k

lemma a_mul (n : ℕ) (hn : 0 < n) :
    a n * n = ∑ k ∈ range (n + 1),
      (n + 2 * k) * ((n + k - 1).choose k) ^ 3 := by
  rw [a_eq_sum_div hn, Nat.div_mul_cancel (sum_rising_dvd n)]

/- ## Generalized harmonic numbers and Wolstenholme's theorem -/

/-- The generalized harmonic number `H_n^{(m)} = ∑_{k=1}^n k^{-m}`. -/
def harmonicGen (m n : ℕ) : ℚ :=
  ∑ i ∈ range n, (1 : ℚ) / ((i + 1 : ℚ) ^ m)

lemma harmonicGen_one (n : ℕ) : harmonicGen 1 n = harmonic n := by
  simp [harmonicGen, harmonic, pow_one]

lemma harmonicGen_zero (m : ℕ) : harmonicGen m 0 = 0 := by
  simp [harmonicGen]

lemma harmonicGen_succ (m n : ℕ) :
    harmonicGen m (n + 1) = harmonicGen m n + 1 / ((n + 1 : ℚ) ^ m) := by
  simp [harmonicGen, sum_range_succ]

/-- `p` does not divide `(p-1)!`. -/
lemma prime_not_dvd_factorial_sub_one {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ (p - 1)! := by
  rw [hp.dvd_factorial]
  have : 1 ≤ p := hp.one_le
  omega

lemma padicValNat_factorial_sub_one {p : ℕ} (hp : p.Prime) :
    padicValNat p (p - 1)! = 0 :=
  padicValNat.eq_zero_of_not_dvd (prime_not_dvd_factorial_sub_one hp)

/-- Cast of `n! / k` is an integer when `1 ≤ k ≤ n`. -/
lemma factorial_div_mem {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n ! / k : ℕ) : ℚ) = (n ! : ℚ) / k := by
  have hdiv : k ∣ n ! := (dvd_factorial hk (le_refl _)).trans (factorial_dvd_factorial hkn)
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  rw [eq_div_iff hk0]
  exact_mod_cast Nat.div_mul_cancel hdiv

/-- In `𝔽_p`, `∑_{x=1}^{p-1} x^{p-3} = 0` for `p ≥ 5`. -/
lemma sum_pow_p_sub_three {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ (p - 3) = 0 := by
  have hlt : p - 3 < p - 1 := by omega
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 3) (by
    simpa [ZMod.card] using hlt)

/-- In `𝔽_p`, `a^{-2} = a^{p-3}` for `a ≠ 0` and `p ≥ 5`. -/
lemma inv_sq_eq_pow_p_sub_three {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {a : ZMod p} (ha : a ≠ 0) :
    a⁻¹ ^ 2 = a ^ (p - 3) := by
  have hfermat : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hdecomp : p - 1 = (p - 3) + 2 := by omega
  have hmul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  calc a⁻¹ ^ 2
      = a ^ (p - 1) * a⁻¹ ^ 2 := by rw [hfermat, one_mul]
    _ = a ^ ((p - 3) + 2) * a⁻¹ ^ 2 := by rw [hdecomp]
    _ = a ^ (p - 3) * (a ^ 2 * a⁻¹ ^ 2) := by rw [pow_add]; ring
    _ = a ^ (p - 3) * (a * a⁻¹) ^ 2 := by rw [← mul_pow]
    _ = a ^ (p - 3) * 1 ^ 2 := by rw [hmul]
    _ = a ^ (p - 3) := by simp

/-- `∑_{k ∈ 𝔽_p^×} k^{-2} = 0` for `p ≥ 5`. -/
lemma sum_inv_sq_eq_zero {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k : (ZMod p)ˣ, ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  have hfermat : ∀ k : (ZMod p)ˣ, ((k : ZMod p)⁻¹) ^ 2 = (k : ZMod p) ^ (p - 3) :=
    fun k => inv_sq_eq_pow_p_sub_three hp5 (Units.ne_zero k)
  simp_rw [hfermat]
  have hdiv : ¬ (p - 1) ∣ (p - 3) := by
    intro h
    have hpos : 0 < p - 3 := by omega
    have := Nat.le_of_dvd hpos h
    omega
  have hsum := FiniteField.sum_pow_units (ZMod p) (p - 3)
  simpa [ZMod.card, if_neg hdiv] using hsum

/-- `Icc 1 (p-1)` is the image of `range (p-1)` under `i ↦ i+1`. -/
lemma range_map_add_one_eq_Icc (n : ℕ) :
    (range n).map ⟨fun i => i + 1, add_left_injective 1⟩ = Icc 1 n := by
  ext x
  simp only [mem_map, mem_range, mem_Icc, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro hx; exact ⟨x - 1, by omega, by omega⟩

/-- `k : ZMod p` is a unit for `1 ≤ k ≤ p-1`. -/
lemma isUnit_of_mem_Icc_pred {p k : ℕ} [hp : Fact p.Prime]
    (hk : k ∈ Icc 1 (p - 1)) : IsUnit (k : ZMod p) := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hle : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hlt : k < p := Nat.lt_of_le_pred hppos hle
  have hkpos : 0 < k := Nat.succ_le_iff.mp (mem_Icc.mp hk).1
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hkpos hlt)

/-- `(p-1)! / k` (integer division) reduces to `(p-1)! * k⁻¹` in `𝔽_p`. -/
lemma factorial_div_zmod {p k : ℕ} [hp : Fact p.Prime]
    (hk : k ∈ Icc 1 (p - 1)) :
    (((p - 1)! / k : ℕ) : ZMod p) = ((p - 1)! : ZMod p) * (k : ZMod p)⁻¹ := by
  have hkp : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hkpos : 0 < k := by
    have := (mem_Icc.mp hk).1
    omega
  have hdiv : k ∣ (p - 1)! := Nat.dvd_factorial hkpos hkp
  have hunit := isUnit_of_mem_Icc_pred hk
  have hmul : ((p - 1)! / k) * k = (p - 1)! := Nat.div_mul_cancel hdiv
  have hcast : (((p - 1)! / k : ℕ) : ZMod p) * (k : ZMod p) = ((p - 1)! : ZMod p) := by
    rw [← Nat.cast_mul, hmul]
  calc (((p - 1)! / k : ℕ) : ZMod p)
      = (((p - 1)! / k : ℕ) : ZMod p) * (k : ZMod p) * (k : ZMod p)⁻¹ := by
        rw [mul_assoc, ZMod.mul_inv_of_unit _ hunit, mul_one]
    _ = ((p - 1)! : ZMod p) * (k : ZMod p)⁻¹ := by rw [hcast]

/-- The integer `∑_{k=1}^{p-1} ((p-1)!/k)^2` is divisible by `p`. -/
lemma wolstenholme_two_int {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ ∑ k ∈ Icc 1 (p - 1), ((p - 1)! / k) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      (((p - 1)! / k : ℕ) : ZMod p) ^ 2 =
        ((p - 1)! : ZMod p) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 := by
    intro k hk
    rw [factorial_div_zmod hk, mul_pow]
  rw [sum_congr rfl hterm, ← mul_sum]
  have hunits : ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ 2 := by
    refine sum_bij (fun k hk => (isUnit_of_mem_Icc_pred hk).unit) ?_ ?_ ?_ ?_
    · intro k hk; simp
    · intro a ha b hb h
      have ha' : a < p := by have := (mem_Icc.mp ha).2; omega
      have hb' : b < p := by have := (mem_Icc.mp hb).2; omega
      have hcoe : (a : ZMod p) = (b : ZMod p) := by
        simpa using congrArg Units.val h
      have : (a : ZMod p).val = (b : ZMod p).val := by rw [hcoe]
      rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
    · intro u _
      refine ⟨u.val.val, ?_, ?_⟩
      · have hval : u.val.val < p := ZMod.val_lt u.val
        have hne : u.val.val ≠ 0 := by
          intro h0
          have : (u : ZMod p) = 0 := (ZMod.val_eq_zero u.val).mp h0
          exact Units.ne_zero u this
        simp [mem_Icc]
        omega
      · apply Units.ext
        simp [ZMod.natCast_zmod_val]
    · intro k hk
      simp
  rw [hunits, sum_inv_sq_eq_zero hp5, mul_zero]

/-- Wolstenholme: `H_{p-1}^{(2)}` is a `p`-integer divisible by `p`. -/
lemma harmonicGen_two_eq {n : ℕ} :
    harmonicGen 2 n =
      ((∑ k ∈ Icc 1 n, (n ! / k) ^ 2 : ℕ) : ℚ) / (n ! : ℚ) ^ 2 := by
  have hden : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  refine (eq_div_iff (pow_ne_zero 2 hden)).mpr ?_
  have hterm : ∀ k ∈ Icc 1 n,
      (1 : ℚ) / (k : ℚ) ^ 2 * (n ! : ℚ) ^ 2 = ((n ! / k : ℕ) : ℚ) ^ 2 := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hkn : k ≤ n := (mem_Icc.mp hk).2
    have hcast := factorial_div_mem hk1 hkn
    have hsq : ((n ! / k : ℕ) : ℚ) ^ 2 = (n ! : ℚ) ^ 2 / (k : ℚ) ^ 2 := by
      rw [hcast, div_pow]
    rw [hsq]
    field_simp
  have hL : harmonicGen 2 n * (n ! : ℚ) ^ 2 =
      ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2 * (n ! : ℚ) ^ 2 := by
    rw [harmonicGen, ← range_map_add_one_eq_Icc, sum_map]
    simp only [Function.Embedding.coeFn_mk, Nat.cast_add, Nat.cast_one, ← sum_mul]
  rw [hL, sum_congr rfl hterm]
  simp [Nat.cast_sum, Nat.cast_pow]

lemma wolstenholme_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    padicValRat p (harmonicGen 2 (p - 1)) ≥ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [harmonicGen_two_eq]
  set M := ∑ k ∈ Icc 1 (p - 1), ((p - 1)! / k) ^ 2
  have hMne : (M : ℚ) ≠ 0 := by
    have hpos : 0 < M := by
      refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
      · simp [mem_Icc]; have := hp.two_le; omega
      · simp [Nat.factorial_pos]
    exact_mod_cast hpos.ne'
  have hden : ((p - 1)! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  rw [padicValRat.div hMne (pow_ne_zero 2 hden), padicValRat.pow hden]
  have hvfact : padicValRat p ((p - 1)! : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat_factorial_sub_one hp
  simp only [hvfact, mul_zero, sub_zero]
  have hpdvd : p ∣ M := wolstenholme_two_int hp hp5
  have hMneN : M ≠ 0 := by exact_mod_cast hMne
  have : 1 ≤ padicValNat p M :=
    one_le_padicValNat_of_dvd hMneN hpdvd
  simpa [padicValRat.of_nat] using this

/-- `p` is odd when `p ≥ 5` is prime, so `(p-1)/2` is an integer. -/
lemma mid_mul_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    2 * ((p - 1) / 2) = p - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  exact Nat.two_mul_div_two_of_even (Nat.Odd.sub_odd hodd odd_one)

lemma mid_pos {p : ℕ} (hp5 : 5 ≤ p) : 0 < (p - 1) / 2 := by
  have : 4 ≤ p - 1 := by omega
  omega

lemma cast_sub_of_le {p k : ℕ} (h : k ≤ p) :
    ((p - k : ℕ) : ℚ) = (p : ℚ) - k :=
  Nat.cast_sub h

/- ## p-adic congruence infrastructure -/

variable {ι : Type*}

/-- A rational is a `p`-integer when its `p`-adic valuation is nonnegative. -/
def IsPInt (p : ℕ) (x : ℚ) : Prop := 0 ≤ padicValRat p x

lemma isPInt_zero (p : ℕ) : IsPInt p 0 := by
  simp [IsPInt, padicValRat.zero]

lemma isPInt_nat (p n : ℕ) : IsPInt p (n : ℚ) :=
  zero_le_padicValRat_of_nat n

lemma isPInt_int (p : ℕ) (z : ℤ) : IsPInt p (z : ℚ) := by
  simp [IsPInt]

lemma isPInt_one (p : ℕ) : IsPInt p 1 := isPInt_nat p 1

lemma isPInt_of_padicValRat_ge {p : ℕ} {x : ℚ} {m : ℤ} (hm : 0 ≤ m)
    (h : m ≤ padicValRat p x) : IsPInt p x :=
  le_trans hm h

lemma isPInt_neg {p : ℕ} {x : ℚ} (h : IsPInt p x) : IsPInt p (-x) := by
  simpa [IsPInt, padicValRat.neg] using h

lemma isPInt_add {p : ℕ} [Fact p.Prime] {x y : ℚ} (hx : IsPInt p x) (hy : IsPInt p y) :
    IsPInt p (x + y) := by
  rcases eq_or_ne (x + y) 0 with h0 | h0
  · simp [IsPInt, h0]
  · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add h0)

lemma isPInt_sub {p : ℕ} [Fact p.Prime] {x y : ℚ} (hx : IsPInt p x) (hy : IsPInt p y) :
    IsPInt p (x - y) := by
  simpa [sub_eq_add_neg] using isPInt_add hx (isPInt_neg hy)

lemma isPInt_mul {p : ℕ} [hp : Fact p.Prime] {x y : ℚ}
    (hx : IsPInt p x) (hy : IsPInt p y) : IsPInt p (x * y) := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [IsPInt, hx0]
  rcases eq_or_ne y 0 with hy0 | hy0
  · simp [IsPInt, hy0]
  · rw [IsPInt, padicValRat.mul hx0 hy0]
    exact add_nonneg hx hy

lemma isPInt_pow {p : ℕ} [hp : Fact p.Prime] {x : ℚ} (hx : IsPInt p x) (k : ℕ) :
    IsPInt p (x ^ k) := by
  induction k with
  | zero => simp [IsPInt]
  | succ k ih =>
    rw [pow_succ]
    exact isPInt_mul ih hx

lemma isPInt_sum {p : ℕ} [Fact p.Prime] {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, IsPInt p (f i)) : IsPInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [IsPInt]
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact isPInt_add (h a (mem_insert_self _ _))
      (ih fun i hi => h i (mem_insert_of_mem hi))

lemma isPInt_prod {p : ℕ} [hp : Fact p.Prime] {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, IsPInt p (f i)) :
    IsPInt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [IsPInt]
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact isPInt_mul (h a (mem_insert_self _ _))
      (ih fun i hi => h i (mem_insert_of_mem hi))

lemma isPInt_inv_of_not_dvd {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0)
    (hnd : ¬ p ∣ k) : IsPInt p (k : ℚ)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [IsPInt, padicValRat.inv, padicValRat.of_nat, neg_nonneg]
  have : padicValNat p k = 0 := padicValNat.eq_zero_of_not_dvd hnd
  simp [this]

/-- Congruence `x ≡ y` modulo `p^m` in the `p`-adic sense. -/
def PCongr (p : ℕ) (m : ℤ) (x y : ℚ) : Prop :=
  x = y ∨ m ≤ padicValRat p (x - y)

lemma pCongr_refl (p : ℕ) (m : ℤ) (x : ℚ) : PCongr p m x x :=
  Or.inl rfl

lemma pCongr_zero_iff_isPInt {p : ℕ} {x : ℚ} :
    PCongr p 0 x 0 ↔ IsPInt p x := by
  constructor
  · rintro (h | h)
    · simp [IsPInt, h]
    · simpa [IsPInt, sub_zero] using h
  · intro h
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simpa [IsPInt, sub_zero] using h)

lemma pCongr_symm {p : ℕ} {m : ℤ} {x y : ℚ} (h : PCongr p m x y) :
    PCongr p m y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    have hneg : y - x = -(x - y) := by ring
    rw [hneg, padicValRat.neg]
    exact h

lemma pCongr_trans {p : ℕ} [Fact p.Prime] {m : ℤ} {x y z : ℚ}
    (hxy : PCongr p m x y) (hyz : PCongr p m y z) : PCongr p m x z := by
  rcases eq_or_ne x z with hxz | hxz
  · exact Or.inl hxz
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  refine Or.inr ?_
  have hsum : x - z = (x - y) + (y - z) := by ring
  rw [hsum]
  have hne : (x - y) + (y - z) ≠ 0 := by
    rwa [← hsum, sub_ne_zero]
  exact le_trans (le_min hxy hyz) (padicValRat.min_le_padicValRat_add hne)

lemma pCongr_add {p : ℕ} [Fact p.Prime] {m : ℤ} {x₁ y₁ x₂ y₂ : ℚ}
    (h1 : PCongr p m x₁ y₁) (h2 : PCongr p m x₂ y₂) :
    PCongr p m (x₁ + x₂) (y₁ + y₂) := by
  rcases eq_or_ne (x₁ + x₂) (y₁ + y₂) with h | h
  · exact Or.inl h
  have hdiff : (x₁ + x₂) - (y₁ + y₂) = (x₁ - y₁) + (x₂ - y₂) := by ring
  refine Or.inr ?_
  rw [hdiff]
  have hne : (x₁ - y₁) + (x₂ - y₂) ≠ 0 := by
    rwa [← hdiff, sub_ne_zero]
  have hx : m ≤ padicValRat p (x₁ - y₁) ∨ x₁ = y₁ := by
    rcases h1 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  have hy : m ≤ padicValRat p (x₂ - y₂) ∨ x₂ = y₂ := by
    rcases h2 with h2 | h2
    · exact Or.inr h2
    · exact Or.inl h2
  -- Handle vanishing differences
  rcases eq_or_ne x₁ y₁ with hxeq | hxeq <;> rcases eq_or_ne x₂ y₂ with hyeq | hyeq
  · exact (h (by simp [hxeq, hyeq])).elim
  · have : (x₁ - y₁) + (x₂ - y₂) = x₂ - y₂ := by simp [hxeq]
    rw [this]
    rcases h2 with h2 | h2
    · exact (hyeq h2).elim
    · exact h2
  · have : (x₁ - y₁) + (x₂ - y₂) = x₁ - y₁ := by simp [hyeq]
    rw [this]
    rcases h1 with h1 | h1
    · exact (hxeq h1).elim
    · exact h1
  · have h1' : m ≤ padicValRat p (x₁ - y₁) := h1.resolve_left hxeq
    have h2' : m ≤ padicValRat p (x₂ - y₂) := h2.resolve_left hyeq
    exact le_trans (le_min h1' h2') (padicValRat.min_le_padicValRat_add hne)

lemma pCongr_neg {p : ℕ} {m : ℤ} {x y : ℚ} (h : PCongr p m x y) :
    PCongr p m (-x) (-y) := by
  rcases h with h | h
  · exact Or.inl (by simp [h])
  · refine Or.inr ?_
    have : -x - -y = -(x - y) := by ring
    rw [this, padicValRat.neg]
    exact h

lemma pCongr_sub {p : ℕ} [Fact p.Prime] {m : ℤ} {x₁ y₁ x₂ y₂ : ℚ}
    (h1 : PCongr p m x₁ y₁) (h2 : PCongr p m x₂ y₂) :
    PCongr p m (x₁ - x₂) (y₁ - y₂) := by
  simpa [sub_eq_add_neg] using pCongr_add h1 (pCongr_neg h2)

lemma pCongr_sum {p : ℕ} [Fact p.Prime] {m : ℤ} {s : Finset ι} {f g : ι → ℚ}
    (h : ∀ i ∈ s, PCongr p m (f i) (g i)) :
    PCongr p m (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pCongr_refl]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact pCongr_add (h a (mem_insert_self _ _))
      (ih fun i hi => h i (mem_insert_of_mem hi))

lemma pCongr_of_isPInt_div {p : ℕ} [hp : Fact p.Prime] {m : ℕ} {x y : ℚ}
    (h : IsPInt p ((x - y) / (p : ℚ) ^ m)) : PCongr p m x y := by
  rcases eq_or_ne x y with hxy | hxy
  · exact Or.inl hxy
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpow : ((p : ℚ) ^ m) ≠ 0 := pow_ne_zero _ hp0
  have : m ≤ padicValRat p (x - y) := by
    have hv := h
    rw [IsPInt, padicValRat.div hxy' hpow, padicValRat.pow hp0] at hv
    have : padicValRat p (p : ℚ) = 1 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.self (Nat.Prime.one_lt hp.out)
    rw [this, mul_one] at hv
    linarith
  exact Or.inr (by exact_mod_cast this)

lemma pCongr_nat_modEq {p : ℕ} (hp : p.Prime) {m a b : ℕ}
    (h : PCongr p m a b) : a ≡ b [MOD p ^ m] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.modEq_iff_dvd]
  rcases h with h | h
  · have : a = b := Nat.cast_injective h
    simp [this]
  · have hsub : (a : ℚ) - (b : ℚ) = ((a : ℤ) - (b : ℤ) : ℚ) := by
      norm_cast
    have hv : m ≤ padicValInt p ((a : ℤ) - b) := by
      have hcast : ((a : ℤ) - (b : ℤ) : ℚ) = ↑((a : ℤ) - b) := by
        norm_cast
      have : (m : ℤ) ≤ (padicValInt p ((a : ℤ) - b) : ℤ) := by
        have h' := h
        rw [hsub, hcast, padicValRat.of_int] at h'
        exact h'
      exact_mod_cast this
    have hdiv : (p : ℤ) ^ m ∣ (a : ℤ) - b :=
      (padicValInt_dvd_iff m ((a : ℤ) - b)).mpr (Or.inr hv)
    have : (p ^ m : ℤ) ∣ (b : ℤ) - a := by
      rw [← dvd_neg, neg_sub]
      simpa [Int.natCast_pow] using hdiv
    exact this

lemma padicValRat_p [hp : Fact p.Prime] : padicValRat p (p : ℚ) = 1 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.self (Nat.Prime.one_lt hp.out)

lemma isPInt_div_of_val {p : ℕ} [Fact p.Prime] {x : ℚ} {m : ℕ}
    (hx : x ≠ 0) (h : (m : ℤ) ≤ padicValRat p x) :
    IsPInt p (x / (p : ℚ) ^ m) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [IsPInt, padicValRat.div hx (pow_ne_zero _ hp0), padicValRat.pow hp0,
    padicValRat_p, mul_one]
  linarith


/- ## Completing Wolstenholme's theorem -/

lemma image_sub_Icc_pred {p : ℕ} (hp : 0 < p) :
    (Icc 1 (p - 1)).image (fun x => p - x) = Icc 1 (p - 1) := by
  ext y
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    constructor <;> omega
  · intro hy
    refine ⟨p - y, ⟨by omega, by omega⟩, Nat.sub_sub_self (by omega)⟩

lemma injOn_sub_Icc_pred {p : ℕ} :
    Set.InjOn (fun x : ℕ => p - x) ↑(Icc 1 (p - 1)) := by
  intro a ha b hb h
  simp only [mem_coe, mem_Icc] at ha hb
  have ha' : a ≤ p := le_trans ha.2 (Nat.sub_le _ _)
  have hb' : b ≤ p := le_trans hb.2 (Nat.sub_le _ _)
  have h' : p - a = p - b := h
  calc
    a = p - (p - a) := (Nat.sub_sub_self ha').symm
    _ = p - (p - b) := by rw [h']
    _ = b := Nat.sub_sub_self hb'

/-- Pairing: `H_{p-1} = (p/2) * ∑_{k=1}^{p-1} 1/(k(p-k))`. -/
lemma harmonic_pairing {p : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p) :
    harmonic (p - 1) =
      (p : ℚ) / 2 * ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k * (p - k) : ℕ) := by
  have hH : harmonic (p - 1) = ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k := by
    simpa [div_eq_mul_inv, one_mul] using (harmonic_eq_sum_Icc (n := p - 1))
  have hreind : ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k =
      ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (p - k : ℕ) := by
    conv_rhs => rw [← image_sub_Icc_pred hp.pos]
    rw [sum_image injOn_sub_Icc_pred]
    refine sum_congr rfl fun x hx => ?_
    simp only [mem_Icc] at hx
    have : p - (p - x) = x := Nat.sub_sub_self (by omega)
    simp [this]
  have havg : 2 * harmonic (p - 1) =
      ∑ k ∈ Icc 1 (p - 1), ((1 : ℚ) / k + 1 / (p - k : ℕ)) := by
    rw [hH, two_mul]
    conv => lhs; rhs; rw [hreind]
    rw [← sum_add_distrib]
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      (1 : ℚ) / k + 1 / (p - k : ℕ) = (p : ℚ) * ((1 : ℚ) / (k * (p - k) : ℕ)) := by
    intro k hk
    simp only [mem_Icc] at hk
    have hklep : k ≤ p := by omega
    have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hp.pos hk.2)
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpkpos.ne'
    have hcast := cast_sub_of_le hklep
    have hmul : ((k * (p - k) : ℕ) : ℚ) = (k : ℚ) * (p - k : ℕ) := Nat.cast_mul _ _
    have hpk0' : (p : ℚ) - k ≠ 0 := by
      rw [← hcast]; exact hpk0
    have hexp : (1 : ℚ) / k + 1 / ((p : ℚ) - k) =
        (p : ℚ) / (k * ((p : ℚ) - k)) := by
      field_simp
      ring
    rw [show (1 : ℚ) / k + 1 / (p - k : ℕ) = (1 : ℚ) / k + 1 / ((p : ℚ) - k) by rw [hcast]]
    rw [show (p : ℚ) * ((1 : ℚ) / (k * (p - k) : ℕ)) =
        (p : ℚ) / (k * ((p : ℚ) - k)) by rw [hmul, hcast]; field_simp]
    exact hexp
  rw [sum_congr rfl hterm] at havg
  have havg' : 2 * harmonic (p - 1) =
      (p : ℚ) * ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k * (p - k) : ℕ) := by
    rw [havg, ← mul_sum]
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h2
  convert havg' using 1 <;> field_simp <;> ring


lemma harmonicGen_two_Icc (n : ℕ) :
    harmonicGen 2 n = ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2 := by
  rw [harmonicGen, ← range_map_add_one_eq_Icc, sum_map]
  simp [Nat.cast_add, Nat.cast_one]

lemma pairing_term_identity {p k : ℕ} (hk : 1 ≤ k) (hkle : k ≤ p - 1)
    (hppos : 0 < p) :
    (1 : ℚ) / (k * (p - k) : ℕ) =
      (p : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ)) - (1 : ℚ) / (k : ℚ) ^ 2 := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hklep : k ≤ p := le_trans hkle (Nat.sub_le _ _)
  have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hppos hkle)
  have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpkpos.ne'
  have hcast : ((p - k : ℕ) : ℚ) = (p : ℚ) - (k : ℚ) := Nat.cast_sub hklep
  have hmul : ((k * (p - k) : ℕ) : ℚ) = (k : ℚ) * (p - k : ℕ) := Nat.cast_mul _ _
  have hpk0' : (p : ℚ) - k ≠ 0 := by rwa [← hcast]
  have hden0 : (k : ℚ) ^ 2 * ((p : ℚ) - k) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hk0) hpk0'
  calc
    (1 : ℚ) / (k * (p - k) : ℕ)
        = (1 : ℚ) / ((k : ℚ) * (p - k : ℕ)) := by rw [hmul]
    _ = (1 : ℚ) / (k * ((p : ℚ) - k)) := by rw [hcast]
    _ = (p : ℚ) / (k ^ 2 * ((p : ℚ) - k)) - 1 / k ^ 2 := by
        field_simp [hk0, hpk0']
        ring
    _ = (p : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ)) - (1 : ℚ) / (k : ℚ) ^ 2 := by
        rw [hcast]

lemma isPInt_inv_k2_pk {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ∈ Icc 1 (p - 1)) :
    IsPInt p (((k : ℚ) ^ 2 * (p - k : ℕ))⁻¹) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hp.pos hk2)
  have hnd : ¬ p ∣ k ^ 2 * (p - k) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact Nat.not_dvd_of_pos_of_lt (by omega)
        (Nat.lt_of_le_pred hp.pos hk2) (hp.dvd_of_dvd_pow h)
    · exact Nat.not_dvd_of_pos_of_lt hpkpos (Nat.sub_lt hp.pos (by omega)) h
  have heq : (k : ℚ) ^ 2 * (p - k : ℕ) = ((k ^ 2 * (p - k) : ℕ) : ℚ) := by
    push_cast; rfl
  rw [heq]
  exact isPInt_inv_of_not_dvd hp (by positivity) hnd

/-- Wolstenholme: `H_{p-1}` has `p`-adic valuation at least `2`. -/
lemma wolstenholme_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (2 : ℤ) ≤ padicValRat p (harmonic (p - 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpair := harmonic_pairing hp hp5
  set S := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k * (p - k) : ℕ)
  have hH2eq := harmonicGen_two_Icc (p - 1)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h20 : (2 : ℚ) ≠ 0 := by norm_num
  have hHpos : 0 < harmonic (p - 1) := harmonic_pos (by omega : p - 1 ≠ 0)
  have hHne : harmonic (p - 1) ≠ 0 := hHpos.ne'
  have hS0 : S ≠ 0 := by
    intro h0
    have : harmonic (p - 1) = 0 := by
      rw [hpair, h0, mul_zero]
    exact hHne this
  have h2val : padicValRat p (2 : ℚ) = 0 := by
    have hnd : ¬ p ∣ 2 := by
      intro hd
      have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      omega
    have hnat : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd hnd
    change padicValRat p (2 : ℕ) = 0
    rw [padicValRat.of_nat]
    exact_mod_cast hnat
  -- S + H^{(2)} = p * ∑ 1/(k^2 (p-k))
  have hdecomp :
      S + harmonicGen 2 (p - 1) =
        (p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ)) := by
    have hterm : ∀ k ∈ Icc 1 (p - 1),
        (1 : ℚ) / (k * (p - k) : ℕ) + (1 : ℚ) / (k : ℚ) ^ 2 =
          (p : ℚ) * ((1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
      have hid := pairing_term_identity hk1 hk2 hp.pos
      linear_combination hid
    have hsum := Finset.sum_congr (s₁ := Icc 1 (p - 1)) rfl hterm
    have hsum' :
        (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k * (p - k) : ℕ)) +
          ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2 =
        (p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ)) := by
      rw [← sum_add_distrib, hsum, ← mul_sum]
    simpa [S, hH2eq] using hsum'
  have hT : IsPInt p (∑ k ∈ Icc 1 (p - 1),
      (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) := by
    refine isPInt_sum fun k hk => ?_
    simpa [div_eq_mul_inv] using isPInt_inv_k2_pk hp hk
  have hH2val := wolstenholme_two hp hp5
  have hH2ne : harmonicGen 2 (p - 1) ≠ 0 := by
    intro h0
    rw [h0, padicValRat.zero] at hH2val
    exact (lt_irrefl (0 : ℤ)) (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) hH2val)
  -- val(S + H2) ≥ 1
  have hsumval : 1 ≤ padicValRat p (S + harmonicGen 2 (p - 1)) ∨
      S + harmonicGen 2 (p - 1) = 0 := by
    by_cases hz : S + harmonicGen 2 (p - 1) = 0
    · exact Or.inr hz
    · left
      rw [hdecomp] at hz ⊢
      have hT0 : ∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ)) ≠ 0 := by
        intro hT0
        rw [hT0, mul_zero] at hz
        exact hz rfl
      rw [padicValRat.mul hp0 hT0, padicValRat_p]
      have : 0 ≤ padicValRat p (∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) := hT
      linarith
  -- val(S) ≥ 1 by ultrametric
  have hSval : 1 ≤ padicValRat p S := by
    rcases hsumval with hge | hsum0
    · rcases eq_or_ne (S + harmonicGen 2 (p - 1)) 0 with hsum0 | hsumne
      · have : S = -harmonicGen 2 (p - 1) := eq_neg_of_add_eq_zero_left hsum0
        rw [this, padicValRat.neg]
        exact hH2val
      · have hdecompS : S = (S + harmonicGen 2 (p - 1)) + (-harmonicGen 2 (p - 1)) := by
          ring
        have hne : (S + harmonicGen 2 (p - 1)) + (-harmonicGen 2 (p - 1)) ≠ 0 := by
          rwa [← hdecompS]
        have hmin := padicValRat.min_le_padicValRat_add (p := p) hne
        rw [← hdecompS] at hmin
        have hH2' : 1 ≤ padicValRat p (-harmonicGen 2 (p - 1)) := by
          rw [padicValRat.neg]; exact hH2val
        exact le_trans (le_min hge hH2') hmin
    · have : S = -harmonicGen 2 (p - 1) := eq_neg_of_add_eq_zero_left hsum0
      rw [this, padicValRat.neg]
      exact hH2val
  have hhalf : (p : ℚ) / 2 ≠ 0 := div_ne_zero hp0 h20
  have hvH : padicValRat p (harmonic (p - 1)) =
      padicValRat p ((p : ℚ) / 2) + padicValRat p S := by
    rw [hpair, padicValRat.mul hhalf hS0]
  rw [hvH, padicValRat.div hp0 h20, padicValRat_p, h2val]
  linarith

/- ## Further p-adic congruence lemmas -/

lemma pCongr_zero_of_eq {p : ℕ} {m : ℤ} {x : ℚ} (h : x = 0) : PCongr p m x 0 :=
  Or.inl h

lemma pCongr_zero_of_val {p : ℕ} {m : ℤ} {x : ℚ} (h : m ≤ padicValRat p x) :
    PCongr p m x 0 := by
  rcases eq_or_ne x 0 with hx | hx
  · exact Or.inl hx
  · exact Or.inr (by simpa [sub_zero] using h)

lemma pCongr_zero_iff {p : ℕ} {m : ℤ} {x : ℚ} :
    PCongr p m x 0 ↔ x = 0 ∨ m ≤ padicValRat p x := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by simpa [sub_zero] using h)
  · rintro (h | h)
    · exact Or.inl h
    · exact pCongr_zero_of_val h

lemma pCongr_mul_zero {p : ℕ} [hp : Fact p.Prime] {m₁ m₂ : ℤ} {x y : ℚ}
    (hx : PCongr p m₁ x 0) (hy : PCongr p m₂ y 0) :
    PCongr p (m₁ + m₂) (x * y) 0 := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0, pCongr_refl]
  rcases eq_or_ne y 0 with hy0 | hy0
  · simp [hy0, pCongr_refl]
  have hx' : m₁ ≤ padicValRat p x := by
    simpa [pCongr_zero_iff, hx0] using hx
  have hy' : m₂ ≤ padicValRat p y := by
    simpa [pCongr_zero_iff, hy0] using hy
  refine pCongr_zero_of_val ?_
  rw [padicValRat.mul hx0 hy0]
  linarith

lemma pCongr_mul_isPInt {p : ℕ} [hp : Fact p.Prime] {m : ℤ} {x y : ℚ}
    (hx : PCongr p m x 0) (hy : IsPInt p y) :
    PCongr p m (x * y) 0 := by
  have hy0 : PCongr p 0 y 0 := pCongr_zero_iff_isPInt.mpr hy
  have := pCongr_mul_zero hx hy0
  simpa using this

lemma pCongr_sub_zero {p : ℕ} {m : ℤ} {x y : ℚ} (h : PCongr p m x y) :
    PCongr p m (x - y) 0 := by
  rcases h with h | h
  · simp [h, pCongr_refl]
  · exact pCongr_zero_of_val (by simpa [sub_zero] using h)

lemma pCongr_mul {p : ℕ} [hp : Fact p.Prime] {m : ℤ} {x₁ y₁ x₂ y₂ : ℚ}
    (h1 : PCongr p m x₁ y₁) (h2 : PCongr p m x₂ y₂)
    (hx1 : IsPInt p x₁) (hy2 : IsPInt p y₂) :
    PCongr p m (x₁ * x₂) (y₁ * y₂) := by
  have hdiff : x₁ * x₂ - y₁ * y₂ = x₁ * (x₂ - y₂) + y₂ * (x₁ - y₁) := by ring
  have hdx : PCongr p m (x₁ - y₁) 0 := pCongr_sub_zero h1
  have hdy : PCongr p m (x₂ - y₂) 0 := pCongr_sub_zero h2
  have hA : PCongr p m ((x₂ - y₂) * x₁) 0 := pCongr_mul_isPInt hdy hx1
  have hA' : PCongr p m (x₁ * (x₂ - y₂)) 0 := by
    simpa [mul_comm] using hA
  have hB : PCongr p m ((x₁ - y₁) * y₂) 0 := pCongr_mul_isPInt hdx hy2
  have hB' : PCongr p m (y₂ * (x₁ - y₁)) 0 := by
    simpa [mul_comm] using hB
  have hsum := pCongr_add (p := p) (m := m) hA' hB'
  rw [zero_add] at hsum
  rcases hsum with h0 | hv
  · exact Or.inl (sub_eq_zero.mp (hdiff.trans h0))
  · exact Or.inr (by simpa [hdiff] using hv)

lemma pCongr_pow_of {p : ℕ} [hp : Fact p.Prime] {m : ℤ} {x y : ℚ} (k : ℕ)
    (h : PCongr p m x y) (hx : IsPInt p x) (hy : IsPInt p y) :
    PCongr p m (x ^ k) (y ^ k) := by
  induction k with
  | zero => simp [pCongr_refl]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact pCongr_mul ih h (isPInt_pow hx k) hy

lemma isPInt_of_pCongr_one {p : ℕ} [hp : Fact p.Prime] {m : ℤ} {x : ℚ}
    (hm : 0 ≤ m) (h : PCongr p m x 1) : IsPInt p x := by
  have h1 : IsPInt p (1 : ℚ) := isPInt_one p
  have hdiff : IsPInt p (x - 1) := by
    rcases h with h | h
    · simp [IsPInt, h]
    · exact isPInt_of_padicValRat_ge hm (by simpa [sub_zero] using
        (by simpa : m ≤ padicValRat p (x - 1)))
  simpa [sub_add_cancel] using isPInt_add hdiff h1

lemma padicValRat_two_eq_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    padicValRat p (2 : ℚ) = 0 := by
  have hnd : ¬ p ∣ 2 := by
    intro hd
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hnat : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd hnd
  change padicValRat p (2 : ℕ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast hnat

lemma isPInt_inv_of_mem_Icc {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    IsPInt p ((k : ℚ)⁻¹) := by
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hnd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega)
    (Nat.lt_of_le_pred hp.pos hk2)
  exact isPInt_inv_of_not_dvd hp (by omega) hnd

lemma harmonicGen_isPInt {p : ℕ} (hp : p.Prime) (d n : ℕ) (hn : n < p) :
    IsPInt p (harmonicGen d n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine isPInt_sum fun i hi => ?_
  have hi' : i + 1 < p := by
    have : i < n := List.mem_range.mp (by simpa [mem_range] using hi)
    omega
  have hnd : ¬ p ∣ (i + 1) := Nat.not_dvd_of_pos_of_lt (by omega) hi'
  have hinv : IsPInt p (((i + 1 : ℕ) : ℚ)⁻¹) :=
    isPInt_inv_of_not_dvd hp (by omega) hnd
  simpa [div_eq_mul_inv] using isPInt_pow hinv d

lemma harmonicGen_two_isPInt {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPInt p (harmonicGen 2 (p - 1)) :=
  isPInt_of_padicValRat_ge (by norm_num : (0 : ℤ) ≤ 1) (wolstenholme_two hp hp5)

/- ## The integer sum `S n = n * a n` -/

def Ssum (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n + 2 * k) * ((n + k - 1).choose k) ^ 3

lemma Ssum_eq_a_mul (n : ℕ) (hn : 0 < n) : Ssum n = a n * n := by
  rw [Ssum, a_mul n hn]

lemma a_eq_Ssum_div (n : ℕ) (hn : 0 < n) : a n = Ssum n / n := by
  rw [Ssum_eq_a_mul n hn, Nat.mul_div_cancel _ hn]

/-- Congruence of `a` follows from a sufficiently strong congruence of `Ssum`. -/
lemma a_modEq_of_Ssum {p n₁ n₂ t : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (h : Ssum n₂ * n₁ ≡ Ssum n₁ * n₂ [MOD p ^ t * n₁ * n₂]) :
    a n₂ ≡ a n₁ [MOD p ^ t] := by
  have hS₁ : Ssum n₁ = a n₁ * n₁ := Ssum_eq_a_mul n₁ hn₁
  have hS₂ : Ssum n₂ = a n₂ * n₂ := Ssum_eq_a_mul n₂ hn₂
  rw [hS₁, hS₂, Nat.modEq_iff_dvd] at h
  rw [Nat.modEq_iff_dvd]
  -- h : p^t * n₁ * n₂ ∣ (a n₁ * n₁ * n₂ - a n₂ * n₂ * n₁)
  have hne : (n₁ * n₂ : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hn₁ hn₂).ne'
  have h' : (p ^ t * (n₁ * n₂) : ℤ) ∣
      ((a n₁ : ℤ) - a n₂) * (n₁ * n₂) := by
    convert h using 1
    · push_cast; ring
    · push_cast; ring
  exact (mul_dvd_mul_iff_right hne).mp h'

/- ## Product formula for the aligned binomials -/

/-- The `p`-free index set `{j | 1 ≤ j ≤ B p, p ∤ j}`. -/
def pFreeBelow (p B : ℕ) : Finset ℕ :=
  (Icc 1 (B * p)).filter (fun j => ¬ p ∣ j)

lemma mem_pFreeBelow {p B j : ℕ} :
    j ∈ pFreeBelow p B ↔ j ∈ Icc 1 (B * p) ∧ ¬ p ∣ j := by
  simp [pFreeBelow]

lemma pFreeBelow_subset_Icc (p B : ℕ) :
    pFreeBelow p B ⊆ Icc 1 (B * p) :=
  filter_subset _ _

/-- `n.choose k = ∏_{j=1}^{k} (n+1-j)/j` as rationals, when `k ≤ n`. -/
lemma choose_eq_prod {n k : ℕ} (hkn : k ≤ n) :
    (n.choose k : ℚ) = ∏ j ∈ Icc 1 k, ((n + 1 - j : ℕ) : ℚ) / j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hkn
    have hdisj : Disjoint (Icc 1 k) ({k + 1} : Finset ℕ) := by
      simp [disjoint_left]; omega
    have hunion : Icc 1 (k + 1) = Icc 1 k ∪ {k + 1} := by
      ext x; simp [mem_Icc]; omega
    have hcastk : ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 := Nat.cast_succ k
    rw [hunion, prod_union hdisj, prod_singleton, ← ih hk', hcastk]
    have hnk : n + 1 - (k + 1) = n - k := by omega
    rw [hnk]
    have hrel : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) :=
      choose_succ_right_eq n k
    have hk0 : (k : ℚ) + 1 ≠ 0 := by
      exact_mod_cast (k + 1).succ_ne_zero
    field_simp [hk0]
    exact_mod_cast hrel

lemma Icc_filter_dvd_eq_image (p B : ℕ) (hp : 0 < p) :
    (Icc 1 (B * p)).filter (p ∣ ·) =
      (Icc 1 B).image (fun q => q * p) := by
  ext j
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · intro ⟨⟨hj1, hj2⟩, hdvd⟩
    obtain ⟨q, hq⟩ := hdvd
    have hq' : j = q * p := by rw [hq, mul_comm]
    refine ⟨q, ⟨?_, ?_⟩, hq'.symm⟩
    · have : 0 < q * p := by
        rwa [← hq']
      exact Nat.pos_of_mul_pos_right this
    · have : q * p ≤ B * p := by
        rwa [← hq']
      exact Nat.le_of_mul_le_mul_right this hp
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hq1 hp, Nat.mul_le_mul_right p hq2⟩, ?_⟩
    exact ⟨q, mul_comm q p⟩

lemma nat_cast_sub_eq {a b : ℕ} (h : b ≤ a) :
    ((a - b : ℕ) : ℚ) = (a : ℚ) - b :=
  Nat.cast_sub h

lemma choose_aligned_ratio {A B p : ℕ} (hp : p.Prime) (hBA : B < A) :
    (((A * p - 1).choose (B * p) : ℚ) /
      ((A - 1).choose B : ℚ)) =
    ∏ j ∈ pFreeBelow p B, ((A * p : ℚ) - j) / j := by
  have hppos : 0 < p := hp.pos
  have hA1 : 1 ≤ A := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le B) hBA)
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0; simp [pFreeBelow]
  have hdenle : B ≤ A - 1 := Nat.le_pred_of_lt hBA
  have hle : B * p ≤ A * p - 1 := by
    have hlt : B * p < A * p := Nat.mul_lt_mul_of_pos_right hBA hppos
    exact Nat.le_pred_of_lt hlt
  have hnum := choose_eq_prod (n := A * p - 1) (k := B * p) hle
  have hden := choose_eq_prod (n := A - 1) (k := B) hdenle
  have hdenne : ((A - 1).choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos hdenle).ne'
  have hcastN : ∀ j ∈ Icc 1 (B * p),
      ((A * p - 1 + 1 - j : ℕ) : ℚ) = (A * p : ℚ) - j := by
    intro j hj
    have hj2 : j ≤ B * p := (mem_Icc.mp hj).2
    have h1 : A * p - 1 + 1 = A * p := Nat.sub_add_cancel (by
      have : 1 ≤ A * p := Nat.mul_le_mul hA1 hp.one_le
      exact this)
    rw [h1, nat_cast_sub_eq (le_trans hj2 (Nat.mul_le_mul_right p hBA.le)),
      Nat.cast_mul]
  have hcastD : ∀ q ∈ Icc 1 B,
      ((A - 1 + 1 - q : ℕ) : ℚ) = (A : ℚ) - q := by
    intro q hq
    have hq2 : q ≤ B := (mem_Icc.mp hq).2
    have h1 : A - 1 + 1 = A := Nat.sub_add_cancel hA1
    rw [h1]
    exact nat_cast_sub_eq (le_trans hq2 hBA.le)
  have hnum' : ((A * p - 1).choose (B * p) : ℚ) =
      ∏ j ∈ Icc 1 (B * p), ((A * p : ℚ) - j) / j := by
    rw [hnum]
    refine prod_congr rfl fun j hj => ?_
    rw [hcastN j hj]
  have hden' : ((A - 1).choose B : ℚ) =
      ∏ q ∈ Icc 1 B, ((A : ℚ) - q) / q := by
    rw [hden]
    refine prod_congr rfl fun q hq => ?_
    rw [hcastD q hq]
  have hdisj : Disjoint ((Icc 1 (B * p)).filter (p ∣ ·)) (pFreeBelow p B) := by
    refine disjoint_left.mpr ?_
    intro a ha hb
    simp [pFreeBelow, mem_filter] at ha hb
    exact hb.2 ha.2
  have hunion : Icc 1 (B * p) =
      (Icc 1 (B * p)).filter (p ∣ ·) ∪ pFreeBelow p B := by
    ext j
    simp [pFreeBelow, mem_filter, mem_Icc]
    tauto
  have hsplit :
      ∏ j ∈ Icc 1 (B * p), ((A * p : ℚ) - j) / j =
        (∏ j ∈ (Icc 1 (B * p)).filter (p ∣ ·), ((A * p : ℚ) - j) / j) *
        (∏ j ∈ pFreeBelow p B, ((A * p : ℚ) - j) / j) := by
    nth_rw 1 [hunion]
    rw [prod_union hdisj]
  have hdivprod :
      ∏ j ∈ (Icc 1 (B * p)).filter (p ∣ ·), ((A * p : ℚ) - j) / j =
        ∏ q ∈ Icc 1 B, ((A : ℚ) - q) / q := by
    rw [Icc_filter_dvd_eq_image p B hppos, prod_image]
    · refine prod_congr rfl fun q hq => ?_
      have hq0 : (q : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hq).1)
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      simp [Nat.cast_mul]
      field_simp [hq0, hp0]
    · intro q _ q' _ heq
      exact Nat.eq_of_mul_eq_mul_right hppos heq
  rw [hnum', hden', hsplit, hdivprod]
  have hQne : ∏ q ∈ Icc 1 B, ((A : ℚ) - q) / q ≠ 0 := by
    rw [← hden']
    exact hdenne
  field_simp [hQne]


lemma isPInt_inv_pFree {p B j : ℕ} (hp : p.Prime) (hj : j ∈ pFreeBelow p B) :
    IsPInt p ((j : ℚ)⁻¹) := by
  have ⟨hjI, hnd⟩ := mem_pFreeBelow.mp hj
  have hj0 : j ≠ 0 := Nat.pos_iff_ne_zero.mp (mem_Icc.mp hjI).1
  exact isPInt_inv_of_not_dvd hp hj0 hnd

lemma isPInt_of_pFree_div {p B j : ℕ} (hp : p.Prime) (hj : j ∈ pFreeBelow p B)
    (x : ℚ) (hx : IsPInt p x) :
    IsPInt p (x / j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  simpa [div_eq_mul_inv] using isPInt_mul hx (isPInt_inv_pFree hp hj)

lemma pCongr_of_le {p : ℕ} {m n : ℤ} {x y : ℚ} (hmn : n ≤ m)
    (h : PCongr p m x y) : PCongr p n x y := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hmn h)

lemma pCongr_sum_zero {ι : Type*} {p : ℕ} [Fact p.Prime] {m : ℤ}
    {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, PCongr p m (f i) 0) :
    PCongr p m (∑ i ∈ s, f i) 0 := by
  have := pCongr_sum (s := s) (f := f) (g := fun _ => (0 : ℚ)) h
  simpa using this

lemma pCongr_prod {ι : Type*} {p : ℕ} [Fact p.Prime] {m : ℤ}
    {s : Finset ι} {f g : ι → ℚ}
    (h : ∀ i ∈ s, PCongr p m (f i) (g i))
    (hf : ∀ i ∈ s, IsPInt p (f i))
    (hg : ∀ i ∈ s, IsPInt p (g i)) :
    PCongr p m (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pCongr_refl]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    refine pCongr_mul (h a (mem_insert_self _ _))
      (ih (fun i hi => h i (mem_insert_of_mem hi))
        (fun i hi => hf i (mem_insert_of_mem hi))
        (fun i hi => hg i (mem_insert_of_mem hi)))
      (hf a (mem_insert_self _ _))
      (isPInt_prod fun i hi => hg i (mem_insert_of_mem hi))

/-- `1/(qp+t) = 1/t - qp/t^2 + (qp)^2/(t^2 (qp+t))`. -/
lemma inv_add_expansion (q t p : ℕ) (ht : t ≠ 0) :
    (1 : ℚ) / (q * p + t) =
      (1 : ℚ) / t - (q * p : ℚ) / t ^ 2 +
        (q * p : ℚ) ^ 2 / (t ^ 2 * (q * p + t)) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hden : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_eq_zero_iff.not.mpr (fun h => ht h.2))
  field_simp [ht0, hden]
  ring


/- ## Block decomposition of `pFreeBelow` -/

lemma add_mul_div_of_lt {q t p : ℕ} (hp : 0 < p) (ht : t < p) :
    (q * p + t) / p = q := by
  rw [show q * p + t = t + p * q by ring, Nat.add_mul_div_left t q hp,
      Nat.div_eq_of_lt ht, zero_add]

lemma add_mul_mod_of_lt {q t p : ℕ} (hp : 0 < p) (ht : t < p) :
    (q * p + t) % p = t := by
  rw [show q * p + t = t + p * q by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

lemma mem_pFreeBelow_of_block {p B q t : ℕ} (hp : p.Prime)
    (hq : q < B) (ht : t ∈ Icc 1 (p - 1)) :
    q * p + t ∈ pFreeBelow p B := by
  have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
  have ht2 : t ≤ p - 1 := (mem_Icc.mp ht).2
  have htlt : t < p := Nat.lt_of_le_pred hp.pos ht2
  rw [mem_pFreeBelow]
  constructor
  · refine mem_Icc.mpr ⟨Nat.add_pos_right _ ht1, ?_⟩
    have hq' : q + 1 ≤ B := Nat.succ_le_of_lt hq
    have h1 : q * p + t ≤ q * p + (p - 1) := Nat.add_le_add_left ht2 _
    have h2 : q * p + (p - 1) = (q + 1) * p - 1 := by
      have : q * p + p = (q + 1) * p := by ring
      have : 1 ≤ p := hp.one_le
      omega
    have h3 : (q + 1) * p - 1 ≤ B * p - 1 := by
      have : (q + 1) * p ≤ B * p := Nat.mul_le_mul_right p hq'
      omega
    exact (h1.trans (h2.symm ▸ h3)).trans (Nat.sub_le _ _)
  · intro hd
    have hmod : (q * p + t) % p = t := add_mul_mod_of_lt hp.pos htlt
    have : t = 0 := by
      rw [← hmod]
      exact Nat.dvd_iff_mod_eq_zero.mp hd
    omega

lemma pFreeBelow_eq_biUnion (p B : ℕ) (hp : p.Prime) :
    pFreeBelow p B =
      (range B).biUnion (fun q => (Icc 1 (p - 1)).image (fun t => q * p + t)) := by
  ext j
  constructor
  · intro hj
    have ⟨hjI, hnd⟩ := mem_pFreeBelow.mp hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hjI).1
    have hj2 : j ≤ B * p := (mem_Icc.mp hjI).2
    have hmod0 : j % p ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
    have hmodlt : j % p < p := Nat.mod_lt j hp.pos
    have hjlt : j < B * p ∨ j = B * p := lt_or_eq_of_le hj2
    have hjlt' : j < B * p := by
      rcases hjlt with h | h
      · exact h
      · exact (hnd (by rw [h]; exact dvd_mul_left p B)).elim
    refine mem_biUnion.mpr ⟨j / p, ?_, ?_⟩
    · exact mem_range.mpr (Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hjlt'))
    · refine mem_image.mpr ⟨j % p, ?_, ?_⟩
      · exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmod0, Nat.le_pred_of_lt hmodlt⟩
      · have := Nat.div_add_mod j p
        linarith
  · intro hj
    obtain ⟨q, hq, hx⟩ := mem_biUnion.mp hj
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
    exact mem_pFreeBelow_of_block hp (mem_range.mp hq) ht

lemma pairwiseDisjoint_pFree_blocks (p B : ℕ) (hp : p.Prime) :
    Set.PairwiseDisjoint (range B : Set ℕ)
      (fun q => (Icc 1 (p - 1)).image (fun t => q * p + t)) := by
  intro q _ q' _ hne
  refine disjoint_left.mpr ?_
  intro x hx hx'
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
  obtain ⟨t', ht', heq⟩ := mem_image.mp hx'
  have htlt : t < p := Nat.lt_of_le_pred hp.pos (mem_Icc.mp ht).2
  have ht'lt : t' < p := Nat.lt_of_le_pred hp.pos (mem_Icc.mp ht').2
  have hq1 : (q * p + t) / p = q := add_mul_div_of_lt hp.pos htlt
  have hq2 : (q' * p + t') / p = q' := add_mul_div_of_lt hp.pos ht'lt
  have : q = q' :=
    calc
      q = (q * p + t) / p := hq1.symm
      _ = (q' * p + t') / p := by rw [← heq]
      _ = q' := hq2
  exact hne this

lemma injOn_block (p q : ℕ) :
    Set.InjOn (fun t : ℕ => q * p + t) ↑(Icc 1 (p - 1)) :=
  fun _ _ _ _ h => Nat.add_left_cancel h

lemma card_pFreeBelow (p B : ℕ) (hp : p.Prime) :
    (pFreeBelow p B).card = B * (p - 1) := by
  rw [pFreeBelow_eq_biUnion p B hp,
      card_biUnion (pairwiseDisjoint_pFree_blocks p B hp)]
  have hcard : ∀ q ∈ range B,
      ((Icc 1 (p - 1)).image (fun t => q * p + t)).card = p - 1 := by
    intro q _
    rw [Finset.card_image_of_injOn (injOn_block p q), Nat.card_Icc]
    omega
  rw [sum_congr rfl hcard, sum_const, card_range, smul_eq_mul]

lemma even_card_pFreeBelow (p B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Even (pFreeBelow p B).card := by
  rw [card_pFreeBelow p B hp]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  exact (Nat.Odd.sub_odd hodd odd_one).mul_left B

lemma sum_pFreeBelow_block (p B : ℕ) (hp : p.Prime) (f : ℕ → ℚ) :
    ∑ j ∈ pFreeBelow p B, f j =
      ∑ q ∈ range B, ∑ t ∈ Icc 1 (p - 1), f (q * p + t) := by
  rw [pFreeBelow_eq_biUnion p B hp,
      sum_biUnion (pairwiseDisjoint_pFree_blocks p B hp)]
  refine sum_congr rfl fun q _ => sum_image (injOn_block p q)


/- ## Inverse expansion remainders -/

lemma not_dvd_add_mul {p q t : ℕ} (hp : p.Prime)
    (ht : t ∈ Icc 1 (p - 1)) : ¬ p ∣ (q * p + t) := by
  intro hd
  have htlt : t < p := Nat.lt_of_le_pred hp.pos (mem_Icc.mp ht).2
  have : (q * p + t) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have : t = 0 := by rwa [add_mul_mod_of_lt hp.pos htlt] at this
  have : 1 ≤ t := (mem_Icc.mp ht).1
  omega

lemma isPInt_inv_block {p q t : ℕ} (hp : p.Prime)
    (ht : t ∈ Icc 1 (p - 1)) :
    IsPInt p (((q * p + t : ℕ) : ℚ)⁻¹) := by
  have hpos : 0 < q * p + t := Nat.add_pos_right _ (mem_Icc.mp ht).1
  exact isPInt_inv_of_not_dvd hp hpos.ne' (not_dvd_add_mul hp ht)

lemma pCongr_p_pow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    PCongr p k ((p : ℚ) ^ k) 0 := by
  refine pCongr_zero_of_val ?_
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValRat.pow hp0, padicValRat_p]
  linarith

lemma rem_inv_eq {q t p : ℕ} (ht : t ≠ 0) (hp0 : p ≠ 0) (hsum : q * p + t ≠ 0) :
    (q * p : ℚ) ^ 2 / ((t : ℚ) ^ 2 * (q * p + t : ℕ)) =
      (p : ℚ) ^ 2 * ((q : ℚ) ^ 2 * ((t : ℚ)⁻¹) ^ 2 *
        (((q * p + t : ℕ) : ℚ)⁻¹)) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hpp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hd0 : ((q * p + t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsum
  field_simp [ht0, hpp, hd0]

lemma rem_inv_pCongr (q t p : ℕ) (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 2 ((q * p : ℚ) ^ 2 / ((t : ℚ) ^ 2 * (q * p + t : ℕ))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htp : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  have hinv : IsPInt p (((q * p + t : ℕ) : ℚ)⁻¹) := isPInt_inv_block hp ht
  have hx : IsPInt p
      ((q : ℚ) ^ 2 * ((t : ℚ)⁻¹) ^ 2 * (((q * p + t : ℕ) : ℚ)⁻¹)) :=
    isPInt_mul (isPInt_mul (isPInt_pow (isPInt_nat p q) 2) (isPInt_pow htp 2)) hinv
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1
  have hsum : q * p + t ≠ 0 := (Nat.add_pos_right _ (mem_Icc.mp ht).1).ne'
  rw [rem_inv_eq ht0 hp.ne_zero hsum]
  exact pCongr_mul_isPInt (pCongr_p_pow 2) hx

lemma inv_block_expansion_pCongr (q t p : ℕ) (hp : p.Prime)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 2 ((1 : ℚ) / (q * p + t : ℕ) - (1 : ℚ) / t + (q * p : ℚ) / t ^ 2) 0 := by
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1
  have hexp := inv_add_expansion q t p ht0
  have hcast : ((q * p + t : ℕ) : ℚ) = (q : ℚ) * p + t := by push_cast; rfl
  have : (1 : ℚ) / (q * p + t : ℕ) - (1 : ℚ) / t + (q * p : ℚ) / t ^ 2 =
      (q * p : ℚ) ^ 2 / ((t : ℚ) ^ 2 * (q * p + t : ℕ)) := by
    rw [hcast]
    linarith [hexp]
  rw [this]
  exact rem_inv_pCongr q t p hp ht

lemma harmonicGen_one_Icc (n : ℕ) :
    harmonicGen 1 n = ∑ t ∈ Icc 1 n, (1 : ℚ) / t := by
  rw [harmonicGen_one]
  simpa [div_eq_mul_inv, one_mul] using (harmonic_eq_sum_Icc (n := n))

lemma pCongr_mul_p {p : ℕ} [Fact p.Prime] (q : ℕ) :
    PCongr p 1 ((q : ℚ) * p) 0 := by
  have hp1 : PCongr p 1 (p : ℚ) 0 :=
    pCongr_zero_of_val (by simp [padicValRat_p])
  simpa [mul_comm] using pCongr_mul_isPInt hp1 (isPInt_nat p q)

lemma block_inv_sum_pCongr (q p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 2 (∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrew :
      ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) =
        harmonicGen 1 (p - 1) -
          ((q : ℚ) * p) * harmonicGen 2 (p - 1) +
        ∑ t ∈ Icc 1 (p - 1),
          ((1 : ℚ) / (q * p + t : ℕ) - (1 : ℚ) / t + (q * p : ℚ) / t ^ 2) := by
    have hH1eq := harmonicGen_one_Icc (p - 1)
    have hH2eq := harmonicGen_two_Icc (p - 1)
    rw [hH1eq, hH2eq, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    ring
  rw [hrew]
  have h1 : PCongr p 2 (harmonicGen 1 (p - 1)) 0 :=
    pCongr_zero_of_val (by
      rw [harmonicGen_one]
      exact wolstenholme_one hp hp5)
  have hqp : PCongr p 1 ((q : ℚ) * p) 0 := pCongr_mul_p q
  have hH2 : PCongr p 1 (harmonicGen 2 (p - 1)) 0 :=
    pCongr_zero_of_val (wolstenholme_two hp hp5)
  have h2 : PCongr p 2 (((q : ℚ) * p) * harmonicGen 2 (p - 1)) 0 :=
    pCongr_mul_zero hqp hH2
  have h3 := pCongr_sum_zero (s := Icc 1 (p - 1))
    (fun t ht => inv_block_expansion_pCongr q t p hp ht)
  have h12 := pCongr_sub h1 h2
  simpa [sub_eq_add_neg, add_assoc] using pCongr_add h12 h3

lemma sum_inv_pFree_val {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 2 (∑ j ∈ pFreeBelow p B, (1 : ℚ) / j) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_pFreeBelow_block p B hp (fun j => (1 : ℚ) / j)]
  refine pCongr_sum_zero ?_
  intro q hq
  -- `1 / ↑(q*p+t)` vs `1 / (q*p+t : ℕ)`
  simpa using block_inv_sum_pCongr q p hp hp5


/- ## Inverse-square sums over p-free indices -/

lemma inv_sq_diff (q t p : ℕ) (ht : t ≠ 0) :
    (1 : ℚ) / (q * p + t : ℕ) ^ 2 - (1 : ℚ) / t ^ 2 =
      - ((2 : ℚ) * q * p * t + (q * p : ℚ) ^ 2) /
        ((t : ℚ) ^ 2 * (q * p + t : ℕ) ^ 2) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hden : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_eq_zero_iff.not.mpr (fun h => ht h.2))
  have hcast : ((q * p + t : ℕ) : ℚ) = (q : ℚ) * p + t := by push_cast; rfl
  field_simp [ht0, hden]
  rw [hcast]
  ring

lemma inv_sq_diff_pCongr (q t p : ℕ) (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 1 ((1 : ℚ) / (q * p + t : ℕ) ^ 2 - (1 : ℚ) / t ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1
  rw [inv_sq_diff q t p ht0]
  -- factor p out of the numerator
  have hform :
      - ((2 : ℚ) * q * p * t + (q * p : ℚ) ^ 2) /
          ((t : ℚ) ^ 2 * (q * p + t : ℕ) ^ 2) =
        (p : ℚ) *
          (- ((2 : ℚ) * q * t + (q : ℚ) ^ 2 * p) /
            ((t : ℚ) ^ 2 * (q * p + t : ℕ) ^ 2)) := by
    have ht0' : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht0
    have hd0 : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp ht).1).ne'
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp [ht0', hd0, hp0]
  rw [hform]
  have htp : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  have hinv : IsPInt p (((q * p + t : ℕ) : ℚ)⁻¹) := isPInt_inv_block hp ht
  have hnum : IsPInt p (- ((2 : ℚ) * q * t + (q : ℚ) ^ 2 * p)) :=
    isPInt_neg (isPInt_add
      (isPInt_mul (isPInt_mul (isPInt_nat p 2) (isPInt_nat p q)) (isPInt_nat p t))
      (isPInt_mul (isPInt_pow (isPInt_nat p q) 2) (isPInt_nat p p)))
  have hdenI : IsPInt p
      (((t : ℚ)⁻¹) ^ 2 * (((q * p + t : ℕ) : ℚ)⁻¹) ^ 2) :=
    isPInt_mul (isPInt_pow htp 2) (isPInt_pow hinv 2)
  have hx : IsPInt p
      (- ((2 : ℚ) * q * t + (q : ℚ) ^ 2 * p) /
        ((t : ℚ) ^ 2 * (q * p + t : ℕ) ^ 2)) := by
    have : (- ((2 : ℚ) * q * t + (q : ℚ) ^ 2 * p) /
        ((t : ℚ) ^ 2 * (q * p + t : ℕ) ^ 2)) =
        (- ((2 : ℚ) * q * t + (q : ℚ) ^ 2 * p)) *
          (((t : ℚ)⁻¹) ^ 2 * (((q * p + t : ℕ) : ℚ)⁻¹) ^ 2) := by
      have ht0' : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht0
      have hd0 : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp ht).1).ne'
      field_simp [ht0', hd0]
    rw [this]
    exact isPInt_mul hnum hdenI
  have hp1 : PCongr p 1 (p : ℚ) 0 :=
    pCongr_zero_of_val (by simp [padicValRat_p])
  exact pCongr_mul_isPInt hp1 hx

lemma block_inv_sq_pCongr (q p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 1 (∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrew :
      ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) ^ 2 =
        harmonicGen 2 (p - 1) +
          ∑ t ∈ Icc 1 (p - 1),
            ((1 : ℚ) / (q * p + t : ℕ) ^ 2 - (1 : ℚ) / t ^ 2) := by
    have hH2 := harmonicGen_two_Icc (p - 1)
    rw [hH2, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    ring
  rw [hrew]
  have h1 : PCongr p 1 (harmonicGen 2 (p - 1)) 0 :=
    pCongr_zero_of_val (wolstenholme_two hp hp5)
  have h2 := pCongr_sum_zero (fun t ht => inv_sq_diff_pCongr q t p hp ht)
  simpa using pCongr_add h1 h2

lemma sum_inv_sq_pFree_val {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 1 (∑ j ∈ pFreeBelow p B, (1 : ℚ) / (j : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_pFreeBelow_block p B hp (fun j => (1 : ℚ) / (j : ℚ) ^ 2)]
  refine pCongr_sum_zero ?_
  intro q hq
  simpa using block_inv_sq_pCongr q p hp hp5

lemma sum_inv_sq_pFree_isPInt {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPInt p (∑ j ∈ pFreeBelow p B, (1 : ℚ) / (j : ℚ) ^ 2) :=
  pCongr_zero_iff_isPInt.mp
    (pCongr_of_le (by norm_num : (0 : ℤ) ≤ 1) (sum_inv_sq_pFree_val hp hp5))

/- ## Product expansion `∏ (1 + x_j)` -/

lemma isPInt_two_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPInt p ((2 : ℚ)⁻¹) :=
  isPInt_inv_of_not_dvd hp (by norm_num) (by
    intro hd
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega)


/-- Remainder after the degree-≤2 truncation of `∏ (1 + x_j)`. -/
noncomputable def prodRemainder (s : Finset ℕ) (x : ℕ → ℚ) : ℚ :=
  (∏ j ∈ s, (1 + x j)) - 1 - (∑ j ∈ s, x j) -
    ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2

lemma prodRemainder_empty (x : ℕ → ℚ) : prodRemainder ∅ x = 0 := by
  simp [prodRemainder]

lemma e2_insert (s : Finset ℕ) (a : ℕ) (x : ℕ → ℚ) (ha : a ∉ s) :
    ((∑ j ∈ insert a s, x j) ^ 2 - ∑ j ∈ insert a s, x j ^ 2) / 2 =
      ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2 +
        x a * ∑ j ∈ s, x j := by
  rw [sum_insert ha, sum_insert ha]
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  field_simp [h2]
  ring

lemma prodRemainder_insert (s : Finset ℕ) (a : ℕ) (x : ℕ → ℚ) (ha : a ∉ s) :
    prodRemainder (insert a s) x =
      prodRemainder s x + x a * prodRemainder s x +
        x a * (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2) := by
  unfold prodRemainder
  rw [prod_insert ha, e2_insert s a x ha, sum_insert ha]
  ring

lemma pCongr_e2_of_val1 {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : ∀ j ∈ s, PCongr p 1 (x j) 0)
    (hxI : ∀ j ∈ s, IsPInt p (x j)) :
    PCongr p 2 (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2) 0 := by
  have hsum1 : PCongr p 1 (∑ j ∈ s, x j) 0 := pCongr_sum_zero hx
  have hsq : PCongr p 2 ((∑ j ∈ s, x j) ^ 2) 0 := by
    simpa [pow_two] using pCongr_mul_zero hsum1 hsum1
  have hsum2 : PCongr p 2 (∑ j ∈ s, x j ^ 2) 0 :=
    pCongr_sum_zero fun j hj => by
      simpa [pow_two] using pCongr_mul_zero (hx j hj) (hx j hj)
  have hsub : PCongr p 2 ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) 0 := by
    simpa using pCongr_sub hsq hsum2
  have h2I : IsPInt p ((2 : ℚ)⁻¹) := isPInt_two_inv hp hp5
  have : ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2 =
      ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) * (2 : ℚ)⁻¹ := by
    field_simp
  rw [this]
  exact pCongr_mul_isPInt hsub h2I

lemma pCongr_prodRemainder {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : ∀ j ∈ s, PCongr p 1 (x j) 0)
    (hxI : ∀ j ∈ s, IsPInt p (x j)) :
    PCongr p 3 (prodRemainder s x) 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [prodRemainder, pCongr_refl]
  | insert a s ha ih =>
    rw [prodRemainder_insert s a x ha]
    have ha1 : PCongr p 1 (x a) 0 := hx a (mem_insert_self _ _)
    have hs : ∀ j ∈ s, PCongr p 1 (x j) 0 := fun j hj => hx j (mem_insert_of_mem hj)
    have hsI : ∀ j ∈ s, IsPInt p (x j) := fun j hj => hxI j (mem_insert_of_mem hj)
    have ih' := ih hs hsI
    have he2 := pCongr_e2_of_val1 hp hp5 hs hsI
    have h1 : PCongr p 3 (x a * prodRemainder s x) 0 :=
      pCongr_of_le (by norm_num : (3 : ℤ) ≤ 1 + 3)
        (pCongr_mul_zero ha1 ih')
    have h2 : PCongr p 3
        (x a * (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2)) 0 :=
      pCongr_mul_zero ha1 he2
    simpa using pCongr_add (pCongr_add ih' h1) h2

lemma pCongr_prod_one_add {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : ∀ j ∈ s, PCongr p 1 (x j) 0)
    (hxI : ∀ j ∈ s, IsPInt p (x j))
    (hsum : PCongr p 3 (∑ j ∈ s, x j) 0)
    (hsum2 : PCongr p 3 (∑ j ∈ s, x j ^ 2) 0) :
    PCongr p 3 (∏ j ∈ s, (1 + x j)) 1 := by
  have hR := pCongr_prodRemainder hp hp5 hx hxI
  have he2 : PCongr p 3 (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2) 0 := by
    have hsq : PCongr p 6 ((∑ j ∈ s, x j) ^ 2) 0 := by
      simpa [pow_two] using pCongr_mul_zero hsum hsum
    have hsub : PCongr p 3
        ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) 0 := by
      simpa using pCongr_sub (pCongr_of_le (by norm_num : (3 : ℤ) ≤ 6) hsq) hsum2
    have h2I : IsPInt p ((2 : ℚ)⁻¹) := isPInt_two_inv hp hp5
    have : ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2 =
        ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) * (2 : ℚ)⁻¹ := by field_simp
    rw [this]
    exact pCongr_mul_isPInt hsub h2I
  -- ∏ = R + 1 + ∑x + e2
  have hdecomp : ∏ j ∈ s, (1 + x j) =
      prodRemainder s x + 1 + ∑ j ∈ s, x j +
        ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2 := by
    unfold prodRemainder; ring
  rw [hdecomp]
  have hadd := pCongr_add (pCongr_add (pCongr_add hR (pCongr_refl p 3 1)) hsum) he2
  simpa [add_assoc] using hadd

/-- The aligned binomial ratio is `1` modulo `p^3`. -/
lemma choose_aligned_pCongr {A B p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B < A) :
    PCongr p 3
      (((A * p - 1).choose (B * p) : ℚ) / ((A - 1).choose B : ℚ)) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [choose_aligned_ratio hp hBA]
  set s := pFreeBelow p B
  set c : ℚ := (A : ℚ) * p
  have hsign : ∏ j ∈ s, ((A * p : ℚ) - j) / j =
      ∏ j ∈ s, (1 - c / j) := by
    -- (Ap - j)/j = - (1 - Ap/j), and there are evenly many factors
    have hfac : ∀ j ∈ s, ((A * p : ℚ) - j) / j = - (1 - c / j) := by
      intro j hj
      have hj0 : (j : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
      field_simp [hj0, c]
      ring
    have hprod : ∏ j ∈ s, ((A * p : ℚ) - j) / j =
        ∏ j ∈ s, (- (1 - c / j)) := prod_congr rfl hfac
    rw [hprod, prod_neg]
    have hcard : Even s.card := even_card_pFreeBelow p B hp hp5
    rw [Even.neg_one_pow hcard, one_mul]
  rw [hsign]
  set x : ℕ → ℚ := fun j => - c / j
  have hx1 : ∀ j ∈ s, PCongr p 1 (x j) 0 := by
    intro j hj
    have : x j = -c * (j : ℚ)⁻¹ := by simp [x, c, div_eq_mul_inv]
    rw [this]
    have hc : PCongr p 1 c 0 := by
      simp only [c]
      exact pCongr_mul_p (p := p) A
    simpa [neg_mul] using pCongr_neg (pCongr_mul_isPInt hc (isPInt_inv_pFree hp hj))
  have hxI : ∀ j ∈ s, IsPInt p (x j) := by
    intro j hj
    have : x j = -c * (j : ℚ)⁻¹ := by simp [x, c, div_eq_mul_inv]
    rw [this]
    have hcI : IsPInt p c := by
      simp only [c]; exact isPInt_mul (isPInt_nat p A) (isPInt_nat p p)
    simpa [neg_mul] using isPInt_neg (isPInt_mul hcI (isPInt_inv_pFree hp hj))
  have hsumx : PCongr p 3 (∑ j ∈ s, x j) 0 := by
    have : ∑ j ∈ s, x j = -c * ∑ j ∈ s, (1 : ℚ) / j := by
      simp only [x, div_eq_mul_inv, mul_sum]
      ring
    rw [this]
    have hσ := sum_inv_pFree_val (B := B) hp hp5
    have hc : PCongr p 1 c 0 := by
      simp only [c]; exact pCongr_mul_p (p := p) A
    simpa [neg_mul] using pCongr_neg (pCongr_mul_zero hc hσ)
  have hsumx2 : PCongr p 3 (∑ j ∈ s, x j ^ 2) 0 := by
    have : ∑ j ∈ s, x j ^ 2 = c ^ 2 * ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2 := by
      simp only [x, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (j : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
      field_simp [hj0, c]
    rw [this]
    have hσ2 : PCongr p 1 (∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2) 0 :=
      sum_inv_sq_pFree_val (B := B) hp hp5
    have hc2 : PCongr p 2 (c ^ 2) 0 := by
      have hc : PCongr p 1 c 0 := by
        simp only [c]; exact pCongr_mul_p (p := p) A
      simpa [pow_two] using pCongr_mul_zero hc hc
    simpa using pCongr_mul_zero hc2 hσ2
  have hprod := pCongr_prod_one_add hp hp5 hx1 hxI hsumx hsumx2
  have hxeq : ∏ j ∈ s, (1 - c / j) = ∏ j ∈ s, (1 + x j) := by
    refine prod_congr rfl fun j _ => ?_
    simp only [x]
    ring
  rwa [hxeq]



/- ## Kummer valuations for rising binomials -/

lemma nat_sub_one_mod_of_dvd {a n : ℕ} (hdiv : n ∣ a) (ha : 0 < a) (hn : 0 < n) :
    (a - 1) % n = n - 1 := by
  have hle : n ≤ a := Nat.le_of_dvd ha hdiv
  have hQ : 1 ≤ a / n := Nat.div_pos hle hn
  have hcancel := Nat.div_mul_cancel hdiv
  have h1 : (a / n - 1) * n = a / n * n - n := by
    simpa using Nat.mul_sub_right_distrib (a / n) 1 n
  have h2 : a / n * n - n + (n - 1) = a / n * n - 1 :=
    Nat.sub_add_sub_cancel (hcancel.symm ▸ hle) (Nat.succ_le_of_lt hn)
  have hrepr : (a / n - 1) * n + (n - 1) = a - 1 := by
    rw [h1, h2, hcancel]
  rw [← hrepr, add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (Nat.sub_lt hn (by norm_num))]

lemma pm_sub_one_mod_pow {p m i : ℕ} [hp : Fact p.Prime]
    (hi : i ≤ padicValNat p m + 1) (hm : m ≠ 0) :
    (p * m - 1) % p ^ i = p ^ i - 1 := by
  have hpm0 : p * m ≠ 0 := mul_ne_zero hp.out.ne_zero hm
  have hpow : p ^ i ∣ p * m := by
    have hv : i ≤ padicValNat p (p * m) := by
      rw [padicValNat.mul hp.out.ne_zero hm, padicValNat_self]
      omega
    exact (padicValNat_dvd_iff_le hpm0).mpr hv
  exact nat_sub_one_mod_of_dvd hpow (Nat.pos_of_ne_zero hpm0) (pow_pos hp.out.pos i)

lemma m_sub_one_mod_pow {p m i : ℕ} [hp : Fact p.Prime]
    (hi : i ≤ padicValNat p m) (hm : m ≠ 0) :
    (m - 1) % p ^ i = p ^ i - 1 := by
  have hpow : p ^ i ∣ m := (padicValNat_dvd_iff_le hm).mpr hi
  exact nat_sub_one_mod_of_dvd hpow (Nat.pos_of_ne_zero hm) (pow_pos hp.out.pos i)

lemma rising_unaligned_val {p m k : ℕ} [hp : Fact p.Prime]
    (hm : m ≠ 0) (hk : ¬ p ∣ k) (hkpos : 0 < k) :
    padicValNat p m + 1 ≤ padicValNat p ((p * m + k - 1).choose k) := by
  have hsum : p * m - 1 + k = p * m + k - 1 := by
    have : 1 ≤ p * m := Nat.mul_pos hp.out.pos (Nat.pos_of_ne_zero hm)
    omega
  rw [← hsum]
  set v := padicValNat p m
  have hx0 : (p * m - 1) + k ≠ 0 := by omega
  have hlog : log p ((p * m - 1) + k) < v + 3 + ((p * m - 1) + k) := by
    have := Nat.log_lt_self (b := p) hx0
    omega
  have hK := padicValNat_choose' (p := p) (n := p * m - 1) (k := k)
      (b := v + 3 + (p * m - 1 + k)) hlog
  rw [hK]
  have hsubset : (Icc 1 (v + 1) : Finset ℕ) ⊆
      (Ico 1 (v + 3 + (p * m - 1 + k))).filter
        (fun i => p ^ i ≤ k % p ^ i + (p * m - 1) % p ^ i) := by
    intro i hi
    have ⟨hi1, hi2⟩ := mem_Icc.mp hi
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨hi1, by omega⟩, ?_⟩
    have hmod : (p * m - 1) % p ^ i = p ^ i - 1 :=
      pm_sub_one_mod_pow (by omega) hm
    rw [hmod]
    have hki : k % p ^ i ≠ 0 := by
      intro h0
      have : p ^ i ∣ k := Nat.dvd_of_mod_eq_zero h0
      have : p ∣ k := (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hi1)).trans this
      exact hk this
    have : 0 < k % p ^ i := Nat.pos_of_ne_zero hki
    omega
  have hle := card_le_card hsubset
  have hcard : (Icc 1 (v + 1)).card = v + 1 := by
    rw [Nat.card_Icc]; omega
  omega

/-- Kummer: if `q ≠ 0` then `v_p(C(m+q-1,q)) ≥ v_p(m) - v_p(q)`. -/
lemma rising_aligned_base_val {p m q : ℕ} [hp : Fact p.Prime]
    (hm : m ≠ 0) (hq : q ≠ 0) :
    padicValNat p m - padicValNat p q ≤
      padicValNat p ((m + q - 1).choose q) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hsum : (m - 1) + q = m + q - 1 := by
    have : 1 ≤ m := Nat.pos_of_ne_zero hm
    omega
  by_cases hle : padicValNat p m ≤ padicValNat p q
  · have : padicValNat p m - padicValNat p q = 0 := Nat.sub_eq_zero_of_le hle
    rw [this]
    exact Nat.zero_le _
  set v := padicValNat p m
  set e := padicValNat p q
  have hev : e < v := Nat.lt_of_not_ge hle
  have hx0 : (m - 1) + q ≠ 0 := by omega
  have hlog : log p ((m - 1) + q) < v + 3 + ((m - 1) + q) := by
    have := Nat.log_lt_self (b := p) hx0
    omega
  rw [← hsum]
  have hK := padicValNat_choose' (p := p) (n := m - 1) (k := q)
      (b := v + 3 + (m - 1 + q)) hlog
  rw [hK]
  have hsubset : (Icc (e + 1) v : Finset ℕ) ⊆
      (Ico 1 (v + 3 + (m - 1 + q))).filter
        (fun i => p ^ i ≤ q % p ^ i + (m - 1) % p ^ i) := by
    intro i hi
    have ⟨hi1, hi2⟩ := mem_Icc.mp hi
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have hmodm : (m - 1) % p ^ i = p ^ i - 1 :=
      m_sub_one_mod_pow (by omega) hm
    rw [hmodm]
    have hqi : q % p ^ i ≠ 0 := by
      intro h0
      have : p ^ i ∣ q := Nat.dvd_of_mod_eq_zero h0
      have : i ≤ e := (padicValNat_dvd_iff_le hq).mp this
      omega
    have : 0 < q % p ^ i := Nat.pos_of_ne_zero hqi
    omega
  have hle' := card_le_card hsubset
  have hcard : (Icc (e + 1) v).card = v - e := by
    rw [Nat.card_Icc]; omega
  omega

/- ## The identity `n * C(n-1,k) = (n-k) * C(n,k)` -/

lemma choose_succ_pred_mul {n k : ℕ} (hn : 0 < n) :
    n * (n - 1).choose k = (n - k) * n.choose k := by
  have h := choose_mul_succ_eq (n - 1) k
  have : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [this] at h
  linarith

lemma choose_aligned_nat {A B p : ℕ} (hp : p.Prime) (hBA : B < A) :
    (A * p - 1).choose (B * p) * A.choose B =
      (A * p).choose (B * p) * (A - 1).choose B := by
  have hA : 0 < A := Nat.zero_lt_of_lt hBA
  have h1 := choose_succ_pred_mul (n := A) (k := B) hA
  have h2 := choose_succ_pred_mul (n := A * p) (k := B * p) (Nat.mul_pos hA hp.pos)
  have hAB : A * p - B * p = (A - B) * p := (Nat.mul_sub_right_distrib A B p).symm
  have mul_eq :
      A * p * ((A * p - 1).choose (B * p) * A.choose B) =
        A * p * ((A * p).choose (B * p) * (A - 1).choose B) := by
    calc
      A * p * ((A * p - 1).choose (B * p) * A.choose B)
          = (A * p * (A * p - 1).choose (B * p)) * A.choose B := by ring
      _ = ((A * p - B * p) * (A * p).choose (B * p)) * A.choose B := by rw [h2]
      _ = ((A - B) * p * (A * p).choose (B * p)) * A.choose B := by rw [hAB]
      _ = (A * p).choose (B * p) * ((A - B) * A.choose B) * p := by ring
      _ = (A * p).choose (B * p) * (A * (A - 1).choose B) * p := by rw [h1]
      _ = A * p * ((A * p).choose (B * p) * (A - 1).choose B) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hA hp.pos) mul_eq

lemma choose_aligned_as_standard {A B p : ℕ} (hp : p.Prime) (hBA : B < A) :
    (((A * p - 1).choose (B * p) : ℚ) / ((A - 1).choose B : ℚ)) =
      ((A * p).choose (B * p) : ℚ) / (A.choose B : ℚ) := by
  have hden0 : ((A - 1).choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.le_pred_of_lt hBA)).ne'
  have hden1 : (A.choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos hBA.le).ne'
  have hnat := choose_aligned_nat hp hBA
  apply (div_eq_div_iff hden0 hden1).mpr
  exact_mod_cast hnat

/- ## Helper: `p`-adic valuation of a natural as a rational -/

lemma padicValRat_natCast {p n : ℕ} [Fact p.Prime] (_hn : n ≠ 0) :
    padicValRat p (n : ℚ) = padicValNat p n :=
  padicValRat.of_nat

lemma pCongr_nat_of_val {p n t : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (h : t ≤ padicValNat p n) : PCongr p t (n : ℚ) 0 :=
  pCongr_zero_of_val (by
    rw [padicValRat_natCast hn]
    exact_mod_cast h)

lemma padicValNat_mul_p_pow {p n r : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p (n * p ^ r) = padicValNat p n + r := by
  rw [padicValNat.mul hn (pow_ne_zero r (Fact.out : p.Prime).ne_zero),
      padicValNat.prime_pow]

lemma pCongr_pow_sub_one {p : ℕ} [Fact p.Prime] {m : ℤ} {x : ℚ}
    (h : PCongr p m x 1) (hx : IsPInt p x) (k : ℕ) :
    PCongr p m (x ^ k - 1) 0 := by
  have hpwd := pCongr_pow_of k h hx (isPInt_one p)
  have : x ^ k - 1 = x ^ k - (1 : ℚ) ^ k := by simp
  rw [this]
  exact pCongr_sub_zero hpwd




/- ## Odd-power Wolstenholme: `H_{p-1}^{(3)} ≡ 0 (mod p)` -/

lemma harmonicGen_three_Icc (n : ℕ) :
    harmonicGen 3 n = ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 3 := by
  rw [harmonicGen, ← range_map_add_one_eq_Icc, sum_map]
  simp [Nat.cast_add, Nat.cast_one]

lemma inv_cube_pair_eq {p k : ℕ} (hk : 1 ≤ k) (hkle : k ≤ p - 1) (hppos : 0 < p) :
    (1 : ℚ) / (k : ℚ) ^ 3 + (1 : ℚ) / ((p - k : ℕ) : ℚ) ^ 3 =
      (p : ℚ) * (((p : ℚ) ^ 2 - 3 * p * k + 3 * k ^ 2) /
        ((k : ℚ) ^ 3 * ((p - k : ℕ) : ℚ) ^ 3)) := by
  have hklep : k ≤ p := le_trans hkle (Nat.sub_le _ _)
  have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hppos hkle)
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((p - k : ℕ) : ℚ) = (p : ℚ) - k := Nat.cast_sub hklep
  have hpk0' : (p : ℚ) - k ≠ 0 := by
    rw [← hcast]; exact Nat.cast_ne_zero.mpr hpkpos.ne'
  rw [hcast]
  field_simp [hk0, hpk0']
  ring

lemma isPInt_inv_k3_pk {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    IsPInt p ((((p : ℚ) ^ 2 - 3 * p * k + 3 * k ^ 2) /
      ((k : ℚ) ^ 3 * ((p - k : ℕ) : ℚ) ^ 3))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hp.pos hk2)
  have hnumI : IsPInt p ((p : ℚ) ^ 2 - 3 * p * k + 3 * k ^ 2) := by
    refine isPInt_add ?_ ?_
    · refine isPInt_sub (isPInt_pow (isPInt_nat p p) 2) ?_
      exact isPInt_mul (isPInt_mul (isPInt_nat p 3) (isPInt_nat p p)) (isPInt_nat p k)
    · exact isPInt_mul (isPInt_nat p 3) (isPInt_pow (isPInt_nat p k) 2)
  have hkd : ¬ p ∣ k :=
    Nat.not_dvd_of_pos_of_lt (by omega) (Nat.lt_of_le_pred hp.pos hk2)
  have hpkd : ¬ p ∣ (p - k) :=
    Nat.not_dvd_of_pos_of_lt hpkpos (Nat.sub_lt hp.pos (by omega))
  have hkinv : IsPInt p ((k : ℚ)⁻¹) := isPInt_inv_of_not_dvd hp (by omega) hkd
  have hpkinv : IsPInt p (((p - k : ℕ) : ℚ)⁻¹) :=
    isPInt_inv_of_not_dvd hp hpkpos.ne' hpkd
  have hdeninv : IsPInt p (((k : ℚ) ^ 3 * ((p - k : ℕ) : ℚ) ^ 3)⁻¹) := by
    rw [mul_inv]
    simpa [inv_pow] using isPInt_mul (isPInt_pow hkinv 3) (isPInt_pow hpkinv 3)
  simpa [div_eq_mul_inv] using isPInt_mul hnumI hdeninv

lemma inv_cube_pair_pCongr {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    PCongr p 1 ((1 : ℚ) / (k : ℚ) ^ 3 + (1 : ℚ) / ((p - k : ℕ) : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hid := inv_cube_pair_eq (mem_Icc.mp hk).1 (mem_Icc.mp hk).2 hp.pos
  rw [hid]
  have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
  exact pCongr_mul_isPInt hp1 (isPInt_inv_k3_pk hp hk)

lemma wolstenholme_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 1 (harmonicGen 3 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hH : harmonicGen 3 (p - 1) =
      ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 3 := harmonicGen_three_Icc _
  have hreind :
      ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 3 =
        ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / ((p - k : ℕ) : ℚ) ^ 3 := by
    conv_rhs => rw [← image_sub_Icc_pred hp.pos]
    rw [sum_image injOn_sub_Icc_pred]
    refine sum_congr rfl fun x hx => ?_
    have : p - (p - x) = x := by
      simp only [mem_Icc] at hx
      exact Nat.sub_sub_self (by omega)
    simp [this]
  have h2 : (2 : ℚ) * harmonicGen 3 (p - 1) =
      ∑ k ∈ Icc 1 (p - 1),
        ((1 : ℚ) / (k : ℚ) ^ 3 + (1 : ℚ) / ((p - k : ℕ) : ℚ) ^ 3) := by
    rw [hH, two_mul]
    conv => lhs; rhs; rw [hreind]
    rw [← sum_add_distrib]
  have hsum := pCongr_sum_zero (s := Icc 1 (p - 1))
    (fun k hk => inv_cube_pair_pCongr hp hk)
  have h2H : PCongr p 1 ((2 : ℚ) * harmonicGen 3 (p - 1)) 0 := by
    rw [h2]; exact hsum
  have h20 : (2 : ℚ) ≠ 0 := by norm_num
  have h2val : padicValRat p (2 : ℚ) = 0 := padicValRat_two_eq_zero hp hp5
  rcases eq_or_ne (harmonicGen 3 (p - 1)) 0 with hz | hne
  · exact Or.inl hz
  · have h2H' : 1 ≤ padicValRat p ((2 : ℚ) * harmonicGen 3 (p - 1)) := by
      have hne2 : (2 : ℚ) * harmonicGen 3 (p - 1) ≠ 0 := mul_ne_zero h20 hne
      rcases h2H with h0 | hv
      · exact (hne2 h0).elim
      · simpa [sub_zero] using hv
    refine pCongr_zero_of_val ?_
    have hmul := padicValRat.mul (p := p) h20 hne
    have : padicValRat p ((2 : ℚ) * harmonicGen 3 (p - 1)) =
        padicValRat p (harmonicGen 3 (p - 1)) := by
      rw [hmul, h2val, zero_add]
    rwa [← this]

lemma T_add_H3_eq {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) +
      harmonicGen 3 (p - 1) =
    (p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
      (1 : ℚ) / ((k : ℚ) ^ 3 * (p - k : ℕ)) := by
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ)) + (1 : ℚ) / (k : ℚ) ^ 3 =
        (p : ℚ) / ((k : ℚ) ^ 3 * (p - k : ℕ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
    have hklep : k ≤ p := le_trans hk2 (Nat.sub_le _ _)
    have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hp.pos hk2)
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((p - k : ℕ) : ℚ) = (p : ℚ) - k := Nat.cast_sub hklep
    have hpk0' : (p : ℚ) - k ≠ 0 := by
      rw [← hcast]; exact Nat.cast_ne_zero.mpr hpkpos.ne'
    rw [hcast]
    field_simp [hk0, hpk0']
    ring
  rw [harmonicGen_three_Icc, ← sum_add_distrib]
  have hsum := sum_congr (s₁ := Icc 1 (p - 1)) rfl hterm
  rw [hsum]
  have hrew : ∀ k ∈ Icc 1 (p - 1),
      (p : ℚ) / ((k : ℚ) ^ 3 * (p - k : ℕ)) =
        (p : ℚ) * (1 / ((k : ℚ) ^ 3 * (p - k : ℕ))) := by
    intro k _; rw [div_eq_mul_inv, one_div]
  rw [sum_congr rfl hrew, ← mul_sum]

lemma isPInt_inv_k3_pk_one {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    IsPInt p ((1 : ℚ) / ((k : ℚ) ^ 3 * (p - k : ℕ))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hpkpos : 0 < p - k := Nat.sub_pos_of_lt (Nat.lt_of_le_pred hp.pos hk2)
  have hkd : ¬ p ∣ k :=
    Nat.not_dvd_of_pos_of_lt (by omega) (Nat.lt_of_le_pred hp.pos hk2)
  have hpkd : ¬ p ∣ (p - k) :=
    Nat.not_dvd_of_pos_of_lt hpkpos (Nat.sub_lt hp.pos (by omega))
  have hkinv : IsPInt p ((k : ℚ)⁻¹) := isPInt_inv_of_not_dvd hp (by omega) hkd
  have hpkinv : IsPInt p (((p - k : ℕ) : ℚ)⁻¹) :=
    isPInt_inv_of_not_dvd hp hpkpos.ne' hpkd
  have : (1 : ℚ) / ((k : ℚ) ^ 3 * (p - k : ℕ)) =
      ((k : ℚ)⁻¹) ^ 3 * ((p - k : ℕ) : ℚ)⁻¹ := by
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpkpos.ne'
    field_simp [hk0, hpk0]
  rw [this]
  exact isPInt_mul (isPInt_pow hkinv 3) hpkinv

lemma T_add_H3_pCongr {p : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p) :
    PCongr p 1
      ((∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) +
        harmonicGen 3 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [T_add_H3_eq hp]
  have hI : IsPInt p
      (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / ((k : ℚ) ^ 3 * (p - k : ℕ))) :=
    isPInt_sum fun k hk => isPInt_inv_k3_pk_one hp hk
  have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
  exact pCongr_mul_isPInt hp1 hI

lemma T_sub_H2_pCongr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 1
      ((∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) -
        harmonicGen 2 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hT3 := T_add_H3_pCongr hp hp5
  have hH3 := wolstenholme_three hp hp5
  have hH2 : PCongr p 1 (harmonicGen 2 (p - 1)) 0 :=
    pCongr_zero_of_val (wolstenholme_two hp hp5)
  have : (∑ k ∈ Icc 1 (p - 1),
        (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) - harmonicGen 2 (p - 1) =
      ((∑ k ∈ Icc 1 (p - 1),
          (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) + harmonicGen 3 (p - 1)) +
        (-harmonicGen 3 (p - 1)) + (-harmonicGen 2 (p - 1)) := by ring
  rw [this]
  simpa using pCongr_add (pCongr_add hT3 (pCongr_neg hH3)) (pCongr_neg hH2)

/-- `H_{p-1} - p(p-1)/2 · H_{p-1}^{(2)}` has valuation at least `3`. -/
lemma wolstenholme_H_H2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 3
      (harmonic (p - 1) -
        ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) * harmonicGen 2 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpair := harmonic_pairing hp hp5
  set S := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k * (p - k) : ℕ)
  set T := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))
  have hH2eq := harmonicGen_two_Icc (p - 1)
  have hdecomp : S + harmonicGen 2 (p - 1) = (p : ℚ) * T := by
    have hterm : ∀ k ∈ Icc 1 (p - 1),
        (1 : ℚ) / (k * (p - k) : ℕ) + (1 : ℚ) / (k : ℚ) ^ 2 =
          (p : ℚ) * ((1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) := by
      intro k hk
      have hid := pairing_term_identity (mem_Icc.mp hk).1 (mem_Icc.mp hk).2 hp.pos
      linear_combination hid
    have hsum := sum_congr (s₁ := Icc 1 (p - 1)) rfl hterm
    calc
      S + harmonicGen 2 (p - 1)
          = (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k * (p - k) : ℕ)) +
              ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2 := by
            simp only [S, hH2eq]
      _ = ∑ k ∈ Icc 1 (p - 1),
            ((1 : ℚ) / (k * (p - k) : ℕ) + (1 : ℚ) / (k : ℚ) ^ 2) := by
            rw [← sum_add_distrib]
      _ = ∑ k ∈ Icc 1 (p - 1),
            (p : ℚ) * ((1 : ℚ) / ((k : ℚ) ^ 2 * (p - k : ℕ))) := hsum
      _ = (p : ℚ) * T := by rw [← mul_sum]
  have hS : S = (p : ℚ) * T - harmonicGen 2 (p - 1) := by linarith [hdecomp]
  have h20 : (2 : ℚ) ≠ 0 := by norm_num
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 :=
    Nat.cast_sub (Nat.succ_le_of_lt hp.pos)
  have hexp : harmonic (p - 1) -
        ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) * harmonicGen 2 (p - 1) =
      ((p : ℚ) ^ 2 / 2) * (T - harmonicGen 2 (p - 1)) := by
    rw [hpair, hS, hcast]
    field_simp [h20, hp0]
    ring
  rw [hexp]
  have hTH2 := T_sub_H2_pCongr hp hp5
  have hp2 : PCongr p 2 ((p : ℚ) ^ 2) 0 := pCongr_p_pow 2
  have hhalf : IsPInt p (2 : ℚ)⁻¹ := by
    have hnd : ¬ p ∣ 2 := by
      intro hd
      have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      omega

    exact isPInt_inv_of_not_dvd hp (by norm_num) hnd
  have hp2half : PCongr p 2 ((p : ℚ) ^ 2 / 2) 0 := by
    simpa [div_eq_mul_inv] using pCongr_mul_isPInt hp2 hhalf
  exact pCongr_mul_zero hp2half hTH2



/- ## Extra PCongr utilities -/

lemma pCongr_pow_zero {p : ℕ} [Fact p.Prime] {m : ℤ} {x : ℚ} (k : ℕ)
    (hx : PCongr p m x 0) : PCongr p (k * m) (x ^ k) 0 := by
  induction k with
  | zero =>
    simpa using (pCongr_zero_iff_isPInt (p := p) (x := (1 : ℚ))).mpr (isPInt_one p)
  | succ k ih =>
    rw [pow_succ]
    have hkm : ((k + 1 : ℕ) : ℤ) * m = (k : ℤ) * m + m := by
      push_cast; ring
    rw [hkm]
    exact pCongr_mul_zero ih hx

lemma isPInt_of_pCongr {p : ℕ} {m : ℤ} {x : ℚ} (hm : 0 ≤ m)
    (h : PCongr p m x 0) : IsPInt p x :=
  pCongr_zero_iff_isPInt.mp (pCongr_of_le hm h)

lemma pCongr_coe_val {p n : ℕ} [Fact p.Prime] :
    PCongr p (padicValNat p n) (n : ℚ) 0 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [pCongr_refl]
  · exact pCongr_nat_of_val hn le_rfl

lemma pCongr_mul_coe {p n : ℕ} [Fact p.Prime] {x : ℚ} (hx : IsPInt p x) :
    PCongr p (padicValNat p n) ((n : ℚ) * x) 0 :=
  pCongr_mul_isPInt pCongr_coe_val hx

lemma isPInt_div_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {x : ℚ}
    (hx : IsPInt p x) : IsPInt p (x / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  simpa [div_eq_mul_inv] using isPInt_mul hx (isPInt_two_inv hp hp5)

lemma pCongr_div_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {m : ℤ} {x : ℚ}
    (hx : PCongr p m x 0) : PCongr p m (x / 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  simpa [div_eq_mul_inv] using pCongr_mul_isPInt hx (isPInt_two_inv hp hp5)

lemma isPInt_six_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPInt p ((6 : ℚ)⁻¹) :=
  isPInt_inv_of_not_dvd hp (by norm_num) (by
    intro hd
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have : p = 5 ∨ p = 6 := by omega
    rcases this with rfl | rfl
    · norm_num at hd
    · exact Nat.not_prime_mul (by norm_num : (2 : ℕ) ≠ 1) (by norm_num : (3 : ℕ) ≠ 1) hp)

/-- `∑_{q < B} q = B(B-1)/2` as rationals. -/
lemma sum_range_rat (B : ℕ) :
    ∑ q ∈ range B, (q : ℚ) = (B : ℚ) * ((B : ℚ) - 1) / 2 := by
  have hnat := sum_range_id_mul_two B
  have hcast : (∑ q ∈ range B, (q : ℚ)) * 2 =
      (B : ℚ) * ((B - 1 : ℕ) : ℚ) := by
    rw [← Nat.cast_sum, ← Nat.cast_two, ← Nat.cast_mul, hnat, Nat.cast_mul]
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  apply (eq_div_iff h2).mpr
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB; simp
  · have hsub : ((B - 1 : ℕ) : ℚ) = (B : ℚ) - 1 :=
      Nat.cast_sub (Nat.succ_le_of_lt hB)
    rwa [hsub] at hcast

/-- `∑_{q < B} q^2 = B(B-1)(2B-1)/6` as rationals. -/
lemma sum_range_rat_sq (B : ℕ) :
    ∑ q ∈ range B, (q : ℚ) ^ 2 =
      (B : ℚ) * ((B : ℚ) - 1) * (2 * (B : ℚ) - 1) / 6 := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    have h6 : (6 : ℚ) ≠ 0 := by norm_num
    field_simp [h6]
    ring

/-- `∑_{q < B} q^3 = (B(B-1)/2)^2` as rationals. -/
lemma sum_range_rat_cube (B : ℕ) :
    ∑ q ∈ range B, (q : ℚ) ^ 3 = ((B : ℚ) * ((B : ℚ) - 1) / 2) ^ 2 := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    field_simp [h2]
    ring

lemma pCongr_sum_range {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p (padicValNat p B) (∑ q ∈ range B, (q : ℚ)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_range_rat]
  have hB : PCongr p (padicValNat p B) (B : ℚ) 0 := pCongr_coe_val
  have hrest : IsPInt p (((B : ℚ) - 1) / 2) :=
    isPInt_div_two hp hp5 (isPInt_sub (isPInt_nat p B) (isPInt_one p))
  have : (B : ℚ) * ((B : ℚ) - 1) / 2 = (B : ℚ) * (((B : ℚ) - 1) / 2) := by
    ring
  rw [this]
  exact pCongr_mul_isPInt hB hrest

lemma pCongr_sum_range_sq {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p (padicValNat p B) (∑ q ∈ range B, (q : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_range_rat_sq]
  have hB : PCongr p (padicValNat p B) (B : ℚ) 0 := pCongr_coe_val
  have hrest : IsPInt p ((((B : ℚ) - 1) * (2 * (B : ℚ) - 1) / 6)) := by
    have h1 : IsPInt p ((B : ℚ) - 1) :=
      isPInt_sub (isPInt_nat p B) (isPInt_one p)
    have h2 : IsPInt p (2 * (B : ℚ) - 1) :=
      isPInt_sub (isPInt_mul (isPInt_nat p 2) (isPInt_nat p B)) (isPInt_one p)
    have h6 : IsPInt p ((6 : ℚ)⁻¹) := isPInt_six_inv hp hp5
    simpa [div_eq_mul_inv, mul_assoc] using isPInt_mul (isPInt_mul h1 h2) h6
  have : (B : ℚ) * ((B : ℚ) - 1) * (2 * (B : ℚ) - 1) / 6 =
      (B : ℚ) * (((B : ℚ) - 1) * (2 * (B : ℚ) - 1) / 6) := by ring
  rw [this]
  exact pCongr_mul_isPInt hB hrest

lemma pCongr_sum_range_cube {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p (2 * padicValNat p B) (∑ q ∈ range B, (q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_range_rat_cube, pow_two]
  have h : PCongr p (padicValNat p B) ((B : ℚ) * ((B : ℚ) - 1) / 2) 0 := by
    have hB : PCongr p (padicValNat p B) (B : ℚ) 0 := pCongr_coe_val
    have hrest : IsPInt p (((B : ℚ) - 1) / 2) :=
      isPInt_div_two hp hp5 (isPInt_sub (isPInt_nat p B) (isPInt_one p))
    have : (B : ℚ) * ((B : ℚ) - 1) / 2 = (B : ℚ) * (((B : ℚ) - 1) / 2) := by ring
    rw [this]
    exact pCongr_mul_isPInt hB hrest
  simpa [two_mul] using pCongr_mul_zero h h


/- ## Product expansion with extra valuation -/

lemma pCongr_e2_of {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ} {α : ℤ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : ∀ j ∈ s, PCongr p α (x j) 0) :
    PCongr p (2 * α) (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2) 0 := by
  have hsum1 : PCongr p α (∑ j ∈ s, x j) 0 := pCongr_sum_zero hx
  have hsq : PCongr p (2 * α) ((∑ j ∈ s, x j) ^ 2) 0 := by
    simpa [pow_two, two_mul] using pCongr_mul_zero hsum1 hsum1
  have hsum2 : PCongr p (2 * α) (∑ j ∈ s, x j ^ 2) 0 :=
    pCongr_sum_zero fun j hj => by
      simpa [pow_two, two_mul] using pCongr_mul_zero (hx j hj) (hx j hj)
  have hsub : PCongr p (2 * α) ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) 0 := by
    simpa using pCongr_sub hsq hsum2
  exact pCongr_div_two hp hp5 hsub

lemma pCongr_prodRemainder_of {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ}
    {α : ℤ} (hp : p.Prime) (hp5 : 5 ≤ p) (hα : 0 ≤ α)
    (hx : ∀ j ∈ s, PCongr p α (x j) 0)
    (hxI : ∀ j ∈ s, IsPInt p (x j)) :
    PCongr p (3 * α) (prodRemainder s x) 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [prodRemainder, pCongr_refl]
  | insert a s ha ih =>
    rw [prodRemainder_insert s a x ha]
    have ha1 : PCongr p α (x a) 0 := hx a (mem_insert_self _ _)
    have hs : ∀ j ∈ s, PCongr p α (x j) 0 :=
      fun j hj => hx j (mem_insert_of_mem hj)
    have hsI : ∀ j ∈ s, IsPInt p (x j) :=
      fun j hj => hxI j (mem_insert_of_mem hj)
    have ih' := ih hs hsI
    have he2 := pCongr_e2_of hp hp5 hs
    have h1 : PCongr p (3 * α) (x a * prodRemainder s x) 0 :=
      pCongr_of_le (by nlinarith) (pCongr_mul_zero ha1 ih')
    have h2 : PCongr p (3 * α)
        (x a * (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2)) 0 :=
      pCongr_of_le (by nlinarith) (pCongr_mul_zero ha1 he2)
    simpa using pCongr_add (pCongr_add ih' h1) h2

/-- `∏(1+x_j) ≡ 1` to precision `δ`, given componentwise and sum bounds. -/
lemma pCongr_prod_one_add_of {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ}
    {α β γ δ : ℤ} (hp : p.Prime) (hp5 : 5 ≤ p) (hα : 0 ≤ α)
    (hx : ∀ j ∈ s, PCongr p α (x j) 0)
    (hxI : ∀ j ∈ s, IsPInt p (x j))
    (hsum : PCongr p β (∑ j ∈ s, x j) 0)
    (hsum2 : PCongr p γ (∑ j ∈ s, x j ^ 2) 0)
    (hδβ : δ ≤ β) (hδγ : δ ≤ γ) (hδ2β : δ ≤ 2 * β) (hδα : δ ≤ 3 * α) :
    PCongr p δ (∏ j ∈ s, (1 + x j)) 1 := by
  have hR : PCongr p δ (prodRemainder s x) 0 :=
    pCongr_of_le hδα (pCongr_prodRemainder_of hp hp5 hα hx hxI)
  have he2 : PCongr p δ (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2) 0 := by
    have hsq : PCongr p (2 * β) ((∑ j ∈ s, x j) ^ 2) 0 := by
      simpa [pow_two, two_mul] using pCongr_mul_zero hsum hsum
    have hsub : PCongr p δ ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) 0 := by
      have h1 : PCongr p δ ((∑ j ∈ s, x j) ^ 2) 0 := pCongr_of_le hδ2β hsq
      have h2 : PCongr p δ (∑ j ∈ s, x j ^ 2) 0 := pCongr_of_le hδγ hsum2
      simpa using pCongr_sub h1 h2
    exact pCongr_div_two hp hp5 hsub
  have hS : PCongr p δ (∑ j ∈ s, x j) 0 := pCongr_of_le hδβ hsum
  have hdecomp : ∏ j ∈ s, (1 + x j) =
      prodRemainder s x + 1 + ∑ j ∈ s, x j +
        ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2 := by
    unfold prodRemainder; ring
  rw [hdecomp]
  have hadd :=
    pCongr_add (pCongr_add (pCongr_add hR (pCongr_refl p δ 1)) hS) he2
  simpa [add_assoc] using hadd

/- ## `W(k) = C(kp-1, p-1) ≡ 1 (mod p^{3+v_p(k)})` -/

lemma choose_pred_prod {k p : ℕ} (hk : 0 < k) (hppos : 0 < p) :
    ((k * p - 1).choose (p - 1) : ℚ) =
      ∏ j ∈ Icc 1 (p - 1), ((k * p : ℚ) - j) / j := by
  have hle : p - 1 ≤ k * p - 1 := by
    have : p ≤ k * p := Nat.le_mul_of_pos_left p hk
    omega
  have hprod := choose_eq_prod (n := k * p - 1) (k := p - 1) hle
  rw [hprod]
  refine prod_congr rfl fun j hj => ?_
  have hj2 : j ≤ p - 1 := (mem_Icc.mp hj).2
  have h1 : k * p - 1 + 1 = k * p := Nat.sub_add_cancel (Nat.mul_pos hk hppos)
  have hcast : ((k * p - 1 + 1 - j : ℕ) : ℚ) = (k * p : ℚ) - j := by
    rw [h1]
    have : j ≤ k * p :=
      le_trans hj2 (le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_left p hk))
    rw [nat_cast_sub_eq this, Nat.cast_mul]
  rw [hcast]

lemma wolstenholme_W {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    PCongr p (3 + padicValNat p k)
      ((k * p - 1).choose (p - 1) : ℚ) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [choose_pred_prod hk hp.pos]
  set s := Icc 1 (p - 1)
  set c : ℚ := (k : ℚ) * p
  have hsign : ∏ j ∈ s, ((k * p : ℚ) - j) / j = ∏ j ∈ s, (1 - c / j) := by
    have hfac : ∀ j ∈ s, ((k * p : ℚ) - j) / j = - (1 - c / j) := by
      intro j hj
      have hj0 : (j : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hj).1)
      field_simp [hj0, c]
      ring
    have hprod : ∏ j ∈ s, ((k * p : ℚ) - j) / j =
        ∏ j ∈ s, (- (1 - c / j)) := prod_congr rfl hfac
    rw [hprod, prod_neg]
    have hcard : Even s.card := by
      rw [Nat.card_Icc]
      have : (p - 1) + 1 - 1 = p - 1 := by omega
      rw [this]
      exact Nat.Odd.sub_odd (hp.odd_of_ne_two (by omega)) odd_one
    rw [Even.neg_one_pow hcard, one_mul]
  rw [hsign]
  set x : ℕ → ℚ := fun j => - c / j
  have hkn : k ≠ 0 := hk.ne'
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hkn
  have hcval : PCongr p (1 + padicValNat p k) c 0 := by
    refine pCongr_zero_of_val ?_
    simp only [c]
    rw [padicValRat.mul hk0 hp0, padicValRat_natCast hkn, padicValRat_p]
    linarith
  have hx1 : ∀ j ∈ s, PCongr p (1 + padicValNat p k) (x j) 0 := by
    intro j hj
    have : x j = -c * (j : ℚ)⁻¹ := by simp [x, c, div_eq_mul_inv]
    rw [this]
    simpa [neg_mul] using
      pCongr_neg (pCongr_mul_isPInt hcval (isPInt_inv_of_mem_Icc hp hj))
  have hxI : ∀ j ∈ s, IsPInt p (x j) := by
    intro j hj
    have : x j = -c * (j : ℚ)⁻¹ := by simp [x, c, div_eq_mul_inv]
    rw [this]
    have hcI : IsPInt p c := by
      simp only [c]; exact isPInt_mul (isPInt_nat p k) (isPInt_nat p p)
    simpa [neg_mul] using isPInt_neg (isPInt_mul hcI (isPInt_inv_of_mem_Icc hp hj))
  have hsumx : PCongr p (3 + padicValNat p k) (∑ j ∈ s, x j) 0 := by
    have : ∑ j ∈ s, x j = -c * ∑ j ∈ s, (1 : ℚ) / j := by
      simp only [x, div_eq_mul_inv, mul_sum]; ring
    rw [this]
    have hσ : PCongr p 2 (∑ j ∈ s, (1 : ℚ) / j) 0 :=
      pCongr_zero_of_val (by
        have : ∑ j ∈ s, (1 : ℚ) / j = harmonic (p - 1) := by
          simpa [s, div_eq_mul_inv, one_mul] using
            (harmonic_eq_sum_Icc (n := p - 1)).symm
        rw [this]
        exact wolstenholme_one hp hp5)
    have hmul := pCongr_neg (pCongr_mul_zero hcval hσ)
    simpa [neg_mul] using
      (pCongr_of_le (by linarith : (3 + padicValNat p k : ℤ) ≤
        (1 + padicValNat p k) + 2) hmul)
  have hsumx2 : PCongr p (3 + 2 * padicValNat p k) (∑ j ∈ s, x j ^ 2) 0 := by
    have : ∑ j ∈ s, x j ^ 2 = c ^ 2 * ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2 := by
      simp only [x, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (j : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hj).1)
      field_simp [hj0, c]
    rw [this]
    have hσ2 : PCongr p 1 (∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2) 0 :=
      pCongr_zero_of_val (by
        have : ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2 = harmonicGen 2 (p - 1) := by
          simpa [s] using (harmonicGen_two_Icc (p - 1)).symm
        rw [this]
        exact wolstenholme_two hp hp5)
    have hc2 : PCongr p (2 + 2 * padicValNat p k) (c ^ 2) 0 := by
      have hc0 : c ≠ 0 := mul_ne_zero hk0 hp0
      refine pCongr_zero_of_val ?_
      simp only [c]
      rw [pow_two, padicValRat.mul hc0 hc0, padicValRat.mul hk0 hp0,
          padicValRat_natCast hkn, padicValRat_p]
      linarith
    have hmul := pCongr_mul_zero hc2 hσ2
    exact pCongr_of_le (by linarith) hmul
  have hxeq : ∏ j ∈ s, (1 - c / j) = ∏ j ∈ s, (1 + x j) := by
    refine prod_congr rfl fun j _ => ?_
    simp only [x]; ring
  rw [hxeq]
  refine pCongr_prod_one_add_of (α := 1 + padicValNat p k)
      (β := 3 + padicValNat p k) (γ := 3 + 2 * padicValNat p k)
      (δ := 3 + padicValNat p k) hp hp5 (by linarith) hx1 hxI hsumx hsumx2
      le_rfl (by linarith) (by linarith) (by linarith)


/- ## Three-term inverse expansion and `σ₁(p)`, `σ₂(p)` -/

lemma inv_add_expansion3 (q t p : ℕ) (ht : t ≠ 0) :
    (1 : ℚ) / (q * p + t : ℕ) =
      (1 : ℚ) / t - (q * p : ℚ) / t ^ 2 + (q * p : ℚ) ^ 2 / t ^ 3 -
        (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hsum : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (Nat.pos_of_ne_zero ht)).ne'
  have hcast : ((q * p + t : ℕ) : ℚ) = (q : ℚ) * p + t := by push_cast; rfl
  rw [hcast] at hsum ⊢
  field_simp [ht0, hsum]
  ring

lemma inv_sq_expansion2 (q t p : ℕ) (ht : t ≠ 0) :
    (1 : ℚ) / (q * p + t : ℕ) ^ 2 =
      (1 : ℚ) / t ^ 2 - (2 : ℚ) * (q * p : ℚ) / t ^ 3 +
        (q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
          (t ^ 3 * (q * p + t : ℕ) ^ 2) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hsum : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (Nat.pos_of_ne_zero ht)).ne'
  have hcast : ((q * p + t : ℕ) : ℚ) = (q : ℚ) * p + t := by push_cast; rfl
  rw [hcast] at hsum ⊢
  field_simp [ht0, hsum]
  ring

lemma rem3_pCongr (q t p : ℕ) (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 3
      ((q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1
  have htp : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  have hinv : IsPInt p (((q * p + t : ℕ) : ℚ)⁻¹) := isPInt_inv_block hp ht
  have hx : IsPInt p
      ((q : ℚ) ^ 3 * ((t : ℚ)⁻¹) ^ 3 * (((q * p + t : ℕ) : ℚ)⁻¹)) :=
    isPInt_mul (isPInt_mul (isPInt_pow (isPInt_nat p q) 3) (isPInt_pow htp 3))
      hinv
  have hform :
      (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) =
        (p : ℚ) ^ 3 *
          ((q : ℚ) ^ 3 * ((t : ℚ)⁻¹) ^ 3 * (((q * p + t : ℕ) : ℚ)⁻¹)) := by
    have ht0' : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht0
    have hd0 : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp ht).1).ne'
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp [ht0', hd0, hp0]
  rw [hform]
  exact pCongr_mul_isPInt (pCongr_p_pow 3) hx

lemma rem_sq2_pCongr (q t p : ℕ) (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 2
      ((q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
        (t ^ 3 * (q * p + t : ℕ) ^ 2)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1
  have htp : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  have hinv : IsPInt p (((q * p + t : ℕ) : ℚ)⁻¹) := isPInt_inv_block hp ht
  have hnum : IsPInt p (3 * (t : ℚ) + 2 * (q * p : ℚ)) :=
    isPInt_add (isPInt_mul (isPInt_nat p 3) (isPInt_nat p t))
      (isPInt_mul (isPInt_nat p 2) (isPInt_mul (isPInt_nat p q) (isPInt_nat p p)))
  have hx : IsPInt p
      ((q : ℚ) ^ 2 * (3 * (t : ℚ) + 2 * (q * p : ℚ)) *
        ((t : ℚ)⁻¹) ^ 3 * (((q * p + t : ℕ) : ℚ)⁻¹) ^ 2) :=
    isPInt_mul (isPInt_mul (isPInt_mul (isPInt_pow (isPInt_nat p q) 2) hnum)
      (isPInt_pow htp 3)) (isPInt_pow hinv 2)
  have hform :
      (q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
          (t ^ 3 * (q * p + t : ℕ) ^ 2) =
        (p : ℚ) ^ 2 *
          ((q : ℚ) ^ 2 * (3 * (t : ℚ) + 2 * (q * p : ℚ)) *
            ((t : ℚ)⁻¹) ^ 3 * (((q * p + t : ℕ) : ℚ)⁻¹) ^ 2) := by
    have ht0' : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht0
    have hd0 : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp ht).1).ne'
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp [ht0', hd0, hp0]
  rw [hform]
  exact pCongr_mul_isPInt (pCongr_p_pow 2) hx

lemma rem3_split (q t p : ℕ) (ht : t ≠ 0) :
    (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) =
      (q * p : ℚ) ^ 3 / t ^ 4 -
        (q * p : ℚ) ^ 4 / (t ^ 4 * (q * p + t : ℕ)) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hsum : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (Nat.pos_of_ne_zero ht)).ne'
  have hcast : ((q * p + t : ℕ) : ℚ) = (q : ℚ) * p + t := by push_cast; rfl
  rw [hcast] at hsum ⊢
  field_simp [ht0, hsum]
  ring

lemma rem3_first_pCongr (q t p : ℕ) (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 3 ((q * p : ℚ) ^ 3 / t ^ 4) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htp : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  have hx : IsPInt p ((q : ℚ) ^ 3 * ((t : ℚ)⁻¹) ^ 4) :=
    isPInt_mul (isPInt_pow (isPInt_nat p q) 3) (isPInt_pow htp 4)
  have hform : (q * p : ℚ) ^ 3 / t ^ 4 =
      (p : ℚ) ^ 3 * ((q : ℚ) ^ 3 * ((t : ℚ)⁻¹) ^ 4) := by
    have ht0 : (t : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp [ht0, hp0]
  rw [hform]
  exact pCongr_mul_isPInt (pCongr_p_pow 3) hx

lemma rem3_second_pCongr (q t p : ℕ) (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 4 ((q * p : ℚ) ^ 4 / (t ^ 4 * (q * p + t : ℕ))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htp : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  have hinv : IsPInt p (((q * p + t : ℕ) : ℚ)⁻¹) := isPInt_inv_block hp ht
  have hx : IsPInt p
      ((q : ℚ) ^ 4 * ((t : ℚ)⁻¹) ^ 4 * (((q * p + t : ℕ) : ℚ)⁻¹)) :=
    isPInt_mul (isPInt_mul (isPInt_pow (isPInt_nat p q) 4) (isPInt_pow htp 4))
      hinv
  have hform : (q * p : ℚ) ^ 4 / (t ^ 4 * (q * p + t : ℕ)) =
      (p : ℚ) ^ 4 *
        ((q : ℚ) ^ 4 * ((t : ℚ)⁻¹) ^ 4 * (((q * p + t : ℕ) : ℚ)⁻¹)) := by
    have ht0 : (t : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
    have hd0 : ((q * p + t : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp ht).1).ne'
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp [ht0, hd0, hp0]
  rw [hform]
  exact pCongr_mul_isPInt (pCongr_p_pow 4) hx



lemma mul_sum_pow_three (p : ℕ) :
    ∑ q ∈ range p, (q * p : ℚ) ^ 3 = (p : ℚ) ^ 3 * ∑ q ∈ range p, (q : ℚ) ^ 3 := by
  have h : ∀ q ∈ range p, (q * p : ℚ) ^ 3 = (p : ℚ) ^ 3 * (q : ℚ) ^ 3 := by
    intro q _; rw [mul_pow, mul_comm ((q : ℚ) ^ 3)]
  rw [sum_congr rfl h, ← mul_sum]

lemma mul_sum_pow_two (p : ℕ) :
    ∑ q ∈ range p, (q * p : ℚ) ^ 2 = (p : ℚ) ^ 2 * ∑ q ∈ range p, (q : ℚ) ^ 2 := by
  have h : ∀ q ∈ range p, (q * p : ℚ) ^ 2 = (p : ℚ) ^ 2 * (q : ℚ) ^ 2 := by
    intro q _; rw [mul_pow, mul_comm ((q : ℚ) ^ 2)]
  rw [sum_congr rfl h, ← mul_sum]

lemma sum_mul_inv_pow (s : Finset ℕ) (c : ℚ) (n : ℕ) :
    ∑ t ∈ s, c / (t : ℚ) ^ n = c * ∑ t ∈ s, (1 : ℚ) / (t : ℚ) ^ n := by
  simp [div_eq_mul_inv, mul_sum, one_mul]

lemma rem3_sum_pCongr (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 4
      (∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
        (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinner : ∀ q ∈ range p,
      ∑ t ∈ Icc 1 (p - 1),
          (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) =
        ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 3 / t ^ 4 -
          ∑ t ∈ Icc 1 (p - 1),
            (q * p : ℚ) ^ 4 / (t ^ 4 * (q * p + t : ℕ)) := by
    intro q _
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun t ht =>
      rem3_split q t p (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
  have hsplit :
      ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
          (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) =
        ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 3 / t ^ 4 -
          ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
            (q * p : ℚ) ^ 4 / (t ^ 4 * (q * p + t : ℕ)) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl hinner
  rw [hsplit]
  have hswap :
      ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 3 / t ^ 4 =
        (∑ q ∈ range p, (q * p : ℚ) ^ 3) *
          ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 4 := by
    have h : ∀ q ∈ range p,
        ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 3 / t ^ 4 =
          (q * p : ℚ) ^ 3 * ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 4 :=
      fun q _ => sum_mul_inv_pow _ _ 4
    rw [sum_congr rfl h, ← sum_mul]
  have h1 : PCongr p 4
      (∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 3 / t ^ 4) 0 := by
    rw [hswap, mul_sum_pow_three]
    have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := pCongr_p_pow 3
    have hcube : PCongr p 2 (∑ q ∈ range p, (q : ℚ) ^ 3) 0 := by
      have := pCongr_sum_range_cube hp hp5 (B := p)
      simpa [padicValNat.self hp.one_lt] using this
    have hH4 : IsPInt p (∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 4) :=
      isPInt_sum fun t ht => by
        have hinv : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
        simpa [div_eq_mul_inv] using isPInt_pow hinv 4
    exact pCongr_of_le (by norm_num : (4 : ℤ) ≤ 3 + 2)
      (pCongr_mul_isPInt (pCongr_mul_zero hp3 hcube) hH4)
  have h2 : PCongr p 4
      (∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
        (q * p : ℚ) ^ 4 / (t ^ 4 * (q * p + t : ℕ))) 0 :=
    pCongr_sum_zero fun q _ => pCongr_sum_zero fun t ht =>
      rem3_second_pCongr q t p hp ht
  simpa using pCongr_sub h1 h2

lemma sum_block_one (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t =
      (p : ℚ) * harmonic (p - 1) := by
  have hH : ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t = harmonic (p - 1) := by
    simpa [div_eq_mul_inv, one_mul] using (harmonic_eq_sum_Icc (n := p - 1)).symm
  have : ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t =
      ∑ q ∈ range p, harmonic (p - 1) :=
    sum_congr rfl fun _ _ => hH
  rw [this, sum_const, card_range, nsmul_eq_mul]

lemma sum_block_qp_inv_sq (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) / t ^ 2 =
      ((p : ℚ) * ((p : ℚ) - 1) / 2) * (p : ℚ) * harmonicGen 2 (p - 1) := by
  have hH := (harmonicGen_two_Icc (p - 1)).symm
  have h : ∀ q ∈ range p,
      ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) / t ^ 2 =
        (q * p : ℚ) * ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 2 :=
    fun q _ => sum_mul_inv_pow _ _ 2
  rw [sum_congr rfl h, ← sum_mul, hH]
  have : ∑ q ∈ range p, (q * p : ℚ) = (∑ q ∈ range p, (q : ℚ)) * (p : ℚ) := by
    simp [sum_mul]
  rw [this, sum_range_rat]

lemma sum_block_qp_sq_inv_cube (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 2 / t ^ 3 =
      (p : ℚ) ^ 2 * (∑ q ∈ range p, (q : ℚ) ^ 2) * harmonicGen 3 (p - 1) := by
  have hH := (harmonicGen_three_Icc (p - 1)).symm
  have h : ∀ q ∈ range p,
      ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 2 / t ^ 3 =
        (q * p : ℚ) ^ 2 * ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 3 :=
    fun q _ => sum_mul_inv_pow _ ( (q * p : ℚ) ^ 2 ) 3
  rw [sum_congr rfl h, ← sum_mul, hH, mul_sum_pow_two]

lemma sum_four_terms {α : Type*} [AddCommGroup α] (s : Finset ℕ) (a b c d : ℕ → α) :
    ∑ i ∈ s, (a i - b i + c i - d i) =
      ∑ i ∈ s, a i - ∑ i ∈ s, b i + ∑ i ∈ s, c i - ∑ i ∈ s, d i := by
  simp [sub_eq_add_neg, sum_add_distrib, sum_neg_distrib]

lemma sum_block_inv_expand (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) =
      ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t -
        ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) / t ^ 2 +
        ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 2 / t ^ 3 -
        ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
          (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) := by
  have hinner : ∀ q ∈ range p,
      ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) =
        ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t -
          ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) / t ^ 2 +
          ∑ t ∈ Icc 1 (p - 1), (q * p : ℚ) ^ 2 / t ^ 3 -
          ∑ t ∈ Icc 1 (p - 1),
            (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) := by
    intro q _
    have ht : ∀ t ∈ Icc 1 (p - 1),
        (1 : ℚ) / (q * p + t : ℕ) =
          (1 : ℚ) / t - (q * p : ℚ) / t ^ 2 + (q * p : ℚ) ^ 2 / t ^ 3 -
            (q * p : ℚ) ^ 3 / (t ^ 3 * (q * p + t : ℕ)) :=
      fun t h => inv_add_expansion3 q t p
        (Nat.pos_iff_ne_zero.mp (mem_Icc.mp h).1)
    rw [sum_congr rfl ht]
    exact sum_four_terms (Icc 1 (p - 1)) _ _ _ _
  rw [sum_congr rfl hinner]
  exact sum_four_terms (range p) _ _ _ _

/-- `σ₁` at `B = p` has valuation at least `4`. -/
lemma sum_inv_pFree_val_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 4 (∑ j ∈ pFreeBelow p p, (1 : ℚ) / j) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_pFreeBelow_block p p hp, sum_block_inv_expand p,
      sum_block_one p, sum_block_qp_inv_sq p, sum_block_qp_sq_inv_cube p]
  have hmain : PCongr p 4
      ((p : ℚ) * harmonic (p - 1) -
        ((p : ℚ) * ((p : ℚ) - 1) / 2) * (p : ℚ) * harmonicGen 2 (p - 1)) 0 := by
    have : (p : ℚ) * harmonic (p - 1) -
        ((p : ℚ) * ((p : ℚ) - 1) / 2) * (p : ℚ) * harmonicGen 2 (p - 1) =
      (p : ℚ) * (harmonic (p - 1) -
        ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) * harmonicGen 2 (p - 1)) := by
      have hcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 :=
        Nat.cast_sub (Nat.succ_le_of_lt hp.pos)
      rw [hcast]; ring
    rw [this]
    have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
    exact pCongr_mul_zero hp1 (wolstenholme_H_H2 hp hp5)
  have hH3term : PCongr p 4
      ((p : ℚ) ^ 2 * (∑ q ∈ range p, (q : ℚ) ^ 2) * harmonicGen 3 (p - 1)) 0 := by
    have hp2 : PCongr p 2 ((p : ℚ) ^ 2) 0 := pCongr_p_pow 2
    have hsq : PCongr p 1 (∑ q ∈ range p, (q : ℚ) ^ 2) 0 := by
      have := pCongr_sum_range_sq hp hp5 (B := p)
      simpa [padicValNat.self hp.one_lt] using this
    have hH3p : PCongr p 1 (harmonicGen 3 (p - 1)) 0 :=
      wolstenholme_three hp hp5
    exact pCongr_of_le (by norm_num : (4 : ℤ) ≤ 2 + 1 + 1)
      (pCongr_mul_zero (pCongr_mul_zero hp2 hsq) hH3p)
  have hrem := rem3_sum_pCongr p hp hp5
  have h12 := pCongr_add hmain hH3term
  simpa [sub_eq_add_neg] using pCongr_add h12 (pCongr_neg hrem)


lemma sum_block_inv_sq_expand (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) ^ 2 =
      ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 2 -
        ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (q * p : ℚ) / t ^ 3 +
        ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
          (q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
            (t ^ 3 * (q * p + t : ℕ) ^ 2) := by
  have hinner : ∀ q ∈ range p,
      ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / (q * p + t : ℕ) ^ 2 =
        ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 2 -
          ∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (q * p : ℚ) / t ^ 3 +
          ∑ t ∈ Icc 1 (p - 1),
            (q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
              (t ^ 3 * (q * p + t : ℕ) ^ 2) := by
    intro q _
    have ht : ∀ t ∈ Icc 1 (p - 1),
        (1 : ℚ) / (q * p + t : ℕ) ^ 2 =
          (1 : ℚ) / t ^ 2 - (2 : ℚ) * (q * p : ℚ) / t ^ 3 +
            (q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
              (t ^ 3 * (q * p + t : ℕ) ^ 2) :=
      fun t h => inv_sq_expansion2 q t p
        (Nat.pos_iff_ne_zero.mp (mem_Icc.mp h).1)
    rw [sum_congr rfl ht, sum_add_distrib, sum_sub_distrib]
  have := sum_congr (s₁ := range p) rfl hinner
  rw [this, sum_add_distrib, sum_sub_distrib]

lemma sum_block_two_qp_inv_cube (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (q * p : ℚ) / t ^ 3 =
      (2 : ℚ) * ((p : ℚ) * ((p : ℚ) - 1) / 2) * (p : ℚ) *
        harmonicGen 3 (p - 1) := by
  have hH := (harmonicGen_three_Icc (p - 1)).symm
  have h : ∀ q ∈ range p,
      ∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (q * p : ℚ) / t ^ 3 =
        ((2 : ℚ) * (q * p : ℚ)) * ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 3 :=
    fun q _ => sum_mul_inv_pow _ (2 * (q * p : ℚ)) 3
  rw [sum_congr rfl h, ← sum_mul, hH]
  have : ∑ q ∈ range p, (2 : ℚ) * (q * p : ℚ) =
      (2 : ℚ) * (∑ q ∈ range p, (q : ℚ)) * p := by
    have h : ∀ q ∈ range p, (2 : ℚ) * (q * p : ℚ) = (2 : ℚ) * (q : ℚ) * p :=
      fun q _ => by ring
    rw [sum_congr rfl h]
    have h2 : ∑ q ∈ range p, (2 : ℚ) * (q : ℚ) * p =
        (∑ q ∈ range p, (2 : ℚ) * (q : ℚ)) * p := (sum_mul _ _ _).symm
    rw [h2]
    have h3 : ∑ q ∈ range p, (2 : ℚ) * (q : ℚ) =
        (2 : ℚ) * ∑ q ∈ range p, (q : ℚ) := (mul_sum _ _ _).symm
    rw [h3]
  rw [this, sum_range_rat]

lemma sum_block_inv_sq_one (p : ℕ) :
    ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 2 =
      (p : ℚ) * harmonicGen 2 (p - 1) := by
  have hH := (harmonicGen_two_Icc (p - 1)).symm
  have : ∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1), (1 : ℚ) / t ^ 2 =
      ∑ q ∈ range p, harmonicGen 2 (p - 1) :=
    sum_congr rfl fun _ _ => hH
  rw [this, sum_const, card_range, nsmul_eq_mul]

/-- `σ₂` at `B = p` has valuation at least `2`. -/
lemma sum_inv_sq_pFree_val_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 2 (∑ j ∈ pFreeBelow p p, (1 : ℚ) / (j : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_pFreeBelow_block p p hp (fun j => (1 : ℚ) / (j : ℚ) ^ 2),
      sum_block_inv_sq_expand p, sum_block_inv_sq_one p,
      sum_block_two_qp_inv_cube p]
  have h1 : PCongr p 2 ((p : ℚ) * harmonicGen 2 (p - 1)) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
    exact pCongr_mul_zero hp1 (pCongr_zero_of_val (wolstenholme_two hp hp5))
  have h2 : PCongr p 2
      ((2 : ℚ) * ((p : ℚ) * ((p : ℚ) - 1) / 2) * (p : ℚ) *
        harmonicGen 3 (p - 1)) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
    have hH3 : PCongr p 1 (harmonicGen 3 (p - 1)) 0 :=
      wolstenholme_three hp hp5
    have hrest : IsPInt p ((2 : ℚ) * ((p : ℚ) * ((p : ℚ) - 1) / 2)) := by
      have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
      have hhalf : IsPInt p (((p : ℚ) * ((p : ℚ) - 1) / 2)) :=
        isPInt_div_two hp hp5
          (isPInt_mul (isPInt_nat p p) (isPInt_sub (isPInt_nat p p) (isPInt_one p)))
      exact isPInt_mul h2I hhalf
    have hmul := pCongr_mul_isPInt (pCongr_mul_zero hp1 hH3) hrest
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hrem : PCongr p 2
      (∑ q ∈ range p, ∑ t ∈ Icc 1 (p - 1),
        (q * p : ℚ) ^ 2 * (3 * t + 2 * (q * p : ℚ)) /
          (t ^ 3 * (q * p + t : ℕ) ^ 2)) 0 :=
    pCongr_sum_zero fun q _ => pCongr_sum_zero fun t ht =>
      rem_sq2_pCongr q t p hp ht
  have h12 := pCongr_sub h1 h2
  simpa [sub_eq_add_neg] using pCongr_add h12 hrem




/- ## Grouping `pFreeBelow p (p*C)` -/

lemma p_mul_p_eq_pow (p : ℕ) : p * p = p ^ 2 := (pow_two p).symm

lemma pFreeBelow_mul_mem {p C j β : ℕ} (hp : p.Prime)
    (hj : j ∈ pFreeBelow p p) (hβ : β < C) :
    j + β * p ^ 2 ∈ pFreeBelow p (p * C) := by
  have ⟨hjI, hnd⟩ := mem_pFreeBelow.mp hj
  have hj1 : 1 ≤ j := (mem_Icc.mp hjI).1
  have hj2 : j ≤ p ^ 2 := by
    have := (mem_Icc.mp hjI).2
    simpa [p_mul_p_eq_pow] using this
  have hCpos : 0 < C := Nat.zero_lt_of_lt hβ
  rw [mem_pFreeBelow, mem_Icc]
  constructor
  · constructor
    · exact Nat.add_pos_left hj1 _
    · have hβle : β + 1 ≤ C := Nat.succ_le_of_lt hβ
      have : j + β * p ^ 2 ≤ C * p ^ 2 := by
        calc
          j + β * p ^ 2 ≤ p ^ 2 + β * p ^ 2 := Nat.add_le_add_right hj2 _
          _ = (β + 1) * p ^ 2 := by ring
          _ ≤ C * p ^ 2 := Nat.mul_le_mul_right _ hβle
      convert this using 1
      ring
  · intro hd
    have hpow : p ∣ β * p ^ 2 :=
      dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) _
    exact hnd ((Nat.dvd_add_iff_left hpow).mpr hd)

lemma pFreeBelow_mod_mem {p x : ℕ} (hp : p.Prime)
    (hx : x ∈ pFreeBelow p (p * (x / p ^ 2 + 1)))
    (hmod0 : x % p ^ 2 ≠ 0) :
    x % p ^ 2 ∈ pFreeBelow p p := by
  have hnd := (mem_pFreeBelow.mp hx).2
  have hmodlt : x % p ^ 2 < p ^ 2 := Nat.mod_lt _ (pow_pos hp.pos 2)
  have hndj : ¬ p ∣ x % p ^ 2 := by
    intro hd
    have hdecomp := Nat.div_add_mod x (p ^ 2)
    have hp2 : p ∣ p ^ 2 := dvd_pow_self p (by omega)
    have : p ∣ x := by
      rw [← hdecomp]
      exact dvd_add (dvd_mul_of_dvd_left hp2 _) hd
    exact hnd this
  refine mem_pFreeBelow.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmod0, ?_⟩, hndj⟩
  have : x % p ^ 2 ≤ p * p := by
    have : x % p ^ 2 ≤ p ^ 2 - 1 := Nat.le_pred_of_lt hmodlt
    have : p ^ 2 - 1 ≤ p * p := by
      rw [p_mul_p_eq_pow]; exact Nat.sub_le _ _
    exact le_trans (Nat.le_pred_of_lt hmodlt) this
  exact this

lemma pFreeBelow_mul_eq (p C : ℕ) (hp : p.Prime) :
    pFreeBelow p (p * C) =
      (range C).biUnion fun β =>
        (pFreeBelow p p).image (fun j => j + β * p ^ 2) := by
  ext x
  constructor
  · intro hx
    have ⟨hxI, hnd⟩ := mem_pFreeBelow.mp hx
    have hx2 : x ≤ C * p ^ 2 := by
      have := (mem_Icc.mp hxI).2
      convert this using 1; ring
    have hlt : x < C * p ^ 2 :=
      lt_of_le_of_ne hx2 (fun h => hnd (by
        rw [h]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) _))
    have hβ : x / p ^ 2 < C :=
      Nat.div_lt_of_lt_mul (by convert hlt using 1; ring)
    have hmod0 : x % p ^ 2 ≠ 0 := by
      intro h0
      exact hnd ((dvd_pow_self p (by norm_num)).trans (Nat.dvd_of_mod_eq_zero h0))
    refine mem_biUnion.mpr ⟨x / p ^ 2, mem_range.mpr hβ, ?_⟩
    refine mem_image.mpr ⟨x % p ^ 2, ?_, ?_⟩
    · have hmodlt : x % p ^ 2 < p ^ 2 := Nat.mod_lt _ (pow_pos hp.pos 2)
      have hndj : ¬ p ∣ x % p ^ 2 := by
        intro hd
        have hdecomp := Nat.div_add_mod x (p ^ 2)
        have hp2 : p ∣ p ^ 2 := dvd_pow_self p (by omega)
        have : p ∣ x := by
          rw [← hdecomp]
          exact dvd_add (dvd_mul_of_dvd_left hp2 _) hd
        exact hnd this
      refine mem_pFreeBelow.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmod0, ?_⟩, hndj⟩
      have : x % p ^ 2 ≤ p ^ 2 - 1 := Nat.le_pred_of_lt hmodlt
      have : p ^ 2 - 1 ≤ p * p := by rw [p_mul_p_eq_pow]; exact Nat.sub_le _ _
      exact le_trans (Nat.le_pred_of_lt hmodlt) this
    · have := Nat.div_add_mod x (p ^ 2)
      linarith
  · intro hx
    obtain ⟨β, hβ, hx'⟩ := mem_biUnion.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx'
    exact pFreeBelow_mul_mem hp hj (mem_range.mp hβ)

lemma div_add_pow {j β p : ℕ} (hp : 0 < p) (hj : j < p ^ 2) :
    (j + β * p ^ 2) / p ^ 2 = β := by
  rw [Nat.add_mul_div_right _ _ (pow_pos hp 2), Nat.div_eq_of_lt hj, zero_add]

lemma pairwiseDisjoint_pFree_scale (p C : ℕ) (hp : p.Prime) :
    Set.PairwiseDisjoint (range C : Set ℕ)
      (fun β => (pFreeBelow p p).image (fun j => j + β * p ^ 2)) := by
  intro β _ β' _ hne
  refine disjoint_left.mpr ?_
  intro x hx hx'
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
  obtain ⟨j', hj', heq⟩ := mem_image.mp hx'
  have hjlt : j < p ^ 2 := by
    have hle : j ≤ p * p := (mem_Icc.mp (mem_pFreeBelow.mp hj).1).2
    have hle' : j ≤ p ^ 2 := by simpa [p_mul_p_eq_pow] using hle
    refine lt_of_le_of_ne hle' ?_
    intro h
    exact (mem_pFreeBelow.mp hj).2 (by rw [h]; exact dvd_pow_self p (by norm_num))
  have hj'lt : j' < p ^ 2 := by
    have hle : j' ≤ p * p := (mem_Icc.mp (mem_pFreeBelow.mp hj').1).2
    have hle' : j' ≤ p ^ 2 := by simpa [p_mul_p_eq_pow] using hle
    refine lt_of_le_of_ne hle' ?_
    intro h
    exact (mem_pFreeBelow.mp hj').2 (by rw [h]; exact dvd_pow_self p (by norm_num))
  have : β = β' := by
    calc
      β = (j + β * p ^ 2) / p ^ 2 := (div_add_pow hp.pos hjlt).symm
      _ = (j' + β' * p ^ 2) / p ^ 2 := by rw [heq]
      _ = β' := div_add_pow hp.pos hj'lt
  exact hne this

lemma sum_pFreeBelow_scale (p C : ℕ) (hp : p.Prime) (f : ℕ → ℚ) :
    ∑ j ∈ pFreeBelow p (p * C), f j =
      ∑ β ∈ range C, ∑ j ∈ pFreeBelow p p, f (j + β * p ^ 2) := by
  rw [pFreeBelow_mul_eq p C hp,
      sum_biUnion (pairwiseDisjoint_pFree_scale p C hp)]
  refine sum_congr rfl fun β _ =>
    sum_image fun a _ b _ h => Nat.add_right_cancel h


/- ## Expansion of `C(pM+t-1, t)` -/

/-- Split `C(pM+t-1, t)` as `(pM/t)` times a product over `Icc 1 (t-1)`. -/
lemma choose_pm_t_prod {M t p : ℕ} (ht : 0 < t) (hpm : 1 ≤ p * M) :
    ((p * M + t - 1).choose t : ℚ) =
      ((p * M : ℚ) / t) *
        ∏ j ∈ Icc 1 (t - 1), ((p * M + t : ℚ) - j) / j := by
  have hle : t ≤ p * M + t - 1 := by omega
  have hprod := choose_eq_prod (n := p * M + t - 1) (k := t) hle
  have h1 : p * M + t - 1 + 1 = p * M + t :=
    Nat.sub_add_cancel (Nat.add_pos_right _ ht)
  have hcast : ∀ j ∈ Icc 1 t,
      ((p * M + t - 1 + 1 - j : ℕ) : ℚ) = (p * M + t : ℚ) - j := by
    intro j hj
    have ⟨hj1, hj2⟩ := mem_Icc.mp hj
    have hjle : j ≤ p * M + t := by
      exact le_trans hj2 (Nat.le_add_left t (p * M))
    rw [h1, nat_cast_sub_eq hjle, Nat.cast_add, Nat.cast_mul]
  have hprod' : ((p * M + t - 1).choose t : ℚ) =
      ∏ j ∈ Icc 1 t, ((p * M + t : ℚ) - j) / j := by
    rw [hprod]
    refine prod_congr rfl fun j hj => ?_
    rw [hcast j hj]
  have hdisj : Disjoint (Icc 1 (t - 1)) ({t} : Finset ℕ) := by
    simp [disjoint_left]; omega
  have hunion : Icc 1 t = Icc 1 (t - 1) ∪ {t} := by
    ext x; simp [mem_Icc]; omega
  rw [hprod', hunion, prod_union hdisj, prod_singleton]
  have hlast : ((p * M + t : ℚ) - t) / t = (p * M : ℚ) / t := by ring
  rw [hlast, mul_comm]

/-- `∏_{j=1}^{t-1} (t-j)/j = 1`. -/
lemma prod_falling_over_range (t : ℕ) :
    ∏ j ∈ Icc 1 (t - 1), ((t : ℚ) - j) / j = 1 := by
  rcases Nat.eq_zero_or_pos t with ht0 | ht
  · simp [ht0]
  have hle : t - 1 ≤ t - 1 := le_rfl
  have hprod := choose_eq_prod (n := t - 1) (k := t - 1) hle
  have hC : ((t - 1).choose (t - 1) : ℚ) = 1 := by
    exact_mod_cast choose_self (t - 1)
  rw [← hC, hprod]
  refine prod_congr rfl fun j hj => ?_
  have ⟨hj1, hj2⟩ := mem_Icc.mp hj
  have h1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hcast : ((t - 1 + 1 - j : ℕ) : ℚ) = (t : ℚ) - j := by
    rw [h1, nat_cast_sub_eq (by omega)]
  rw [hcast]

/-- `C(pM+t-1, t) = (pM/t) ∏_{j=1}^{t-1} (1 + pM/(t-j))`. -/
lemma choose_pm_t_one_add {M t p : ℕ} (ht : 0 < t) (hpm : 1 ≤ p * M) :
    ((p * M + t - 1).choose t : ℚ) =
      ((p * M : ℚ) / t) *
        ∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) := by
  rw [choose_pm_t_prod ht hpm]
  refine congrArg (fun s => (p * M : ℚ) / t * s) ?_
  have hsplit :
      ∏ j ∈ Icc 1 (t - 1), ((p * M + t : ℚ) - j) / j =
        (∏ j ∈ Icc 1 (t - 1), ((t : ℚ) - j) / j) *
        (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j))) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun j hj => ?_
    have ⟨hj1, hj2⟩ := mem_Icc.mp hj
    have htj : (t : ℚ) - j ≠ 0 := by
      have hlt : j < t := Nat.lt_of_le_pred ht hj2
      exact sub_ne_zero.mpr (Nat.cast_injective.ne hlt.ne).symm
    have hj0 : (j : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj1)
    field_simp [htj, hj0]
    ring
  rw [hsplit, prod_falling_over_range, one_mul]


/- ## The ratio identity `C(n+t, k+t)/C(n,k) = C(n+t, t)/C(k+t, t)` -/

lemma choose_add_ratio {n k t : ℕ} :
    ((n + t).choose (k + t) : ℚ) * ((k + t).choose t : ℚ) =
      ((n + t).choose t : ℚ) * (n.choose k : ℚ) := by
  have h3 : t ≤ k + t := Nat.le_add_left t k
  have hmul := choose_mul (n := n + t) (k := k + t) (s := t) h3
  have hsub1 : n + t - t = n := Nat.add_sub_cancel n t
  have hsub2 : k + t - t = k := Nat.add_sub_cancel k t
  rw [hsub1, hsub2] at hmul
  exact_mod_cast hmul

lemma choose_shift_ratio {n k t : ℕ}
    (hden : (k + t).choose t ≠ 0) :
    ((n + t).choose (k + t) : ℚ) =
      ((n + t).choose t : ℚ) / ((k + t).choose t : ℚ) * (n.choose k : ℚ) := by
  have h := choose_add_ratio (n := n) (k := k) (t := t)
  have hd : ((k + t).choose t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hden
  have : ((n + t).choose (k + t) : ℚ) * ((k + t).choose t : ℚ) =
      ((n + t).choose t : ℚ) * (n.choose k : ℚ) := h
  calc ((n + t).choose (k + t) : ℚ)
      = ((n + t).choose (k + t) : ℚ) * ((k + t).choose t : ℚ) /
          ((k + t).choose t : ℚ) := (mul_div_cancel_right₀ _ hd).symm
    _ = ((n + t).choose t : ℚ) * (n.choose k : ℚ) /
          ((k + t).choose t : ℚ) := by rw [this]
    _ = ((n + t).choose t : ℚ) / ((k + t).choose t : ℚ) * (n.choose k : ℚ) := by
        ring

/-- Unaligned binomial as aligned times a small factor.
`C(pM+t-1, pB+t) = C(pM-1, pB) * C(pM+t-1, t) / C(pB+t, t)`. -/
lemma choose_unalign_eq {M B t p : ℕ} (hBM : B < M) (hp : 0 < p) :
    ((p * M + t - 1).choose (p * B + t) : ℚ) =
      ((p * M - 1).choose (p * B) : ℚ) *
        ((p * M + t - 1).choose t : ℚ) /
        ((p * B + t).choose t : ℚ) := by
  have hM : 1 ≤ p * M := Nat.mul_le_mul hp (Nat.zero_lt_of_lt hBM)
  have hnt : p * M - 1 + t = p * M + t - 1 := by omega
  have hden : (p * B + t).choose t ≠ 0 :=
    (choose_pos (Nat.le_add_left t (p * B))).ne'
  have h := choose_shift_ratio (n := p * M - 1) (k := p * B) (t := t) hden
  rw [hnt] at h
  convert h using 1
  ring


/- ## `C(pB+t, t) ≡ 1 (mod p)` for `1 ≤ t < p` -/

lemma choose_succ_succ_mul {n k : ℕ} :
    (n + 1).choose (k + 1) * (k + 1) = n.choose k * (n + 1) := by
  have h1 := choose_succ_right_eq (n + 1) k
  -- (n+1).choose (k+1) * (k+1) = (n+1).choose k * (n+1-k)
  have h2 := choose_mul_succ_eq n k
  -- n.choose k * (n+1) = (n+1).choose k * (n+1-k)
  have : (n + 1).choose (k + 1) * (k + 1) = (n + 1).choose k * (n + 1 - k) := h1
  have : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := h2
  linarith

lemma choose_succ_succ_ratio {n k : ℕ} :
    ((n + 1).choose (k + 1) : ℚ) =
      (n.choose k : ℚ) * ((n + 1 : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) := by
  have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have h := choose_succ_succ_mul (n := n) (k := k)
  have hc : ((n + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
      (n.choose k : ℚ) * ((n + 1 : ℕ) : ℚ) := by
    exact_mod_cast h
  exact (eq_div_iff hk0).mpr hc

lemma choose_pB_t_prod {B t p : ℕ} (ht : 0 < t) :
    ((p * B + t).choose t : ℚ) =
      ∏ i ∈ Icc 1 t, ((p * B : ℚ) + i) / i := by
  induction t with
  | zero => exact (Nat.lt_irrefl 0 ht).elim
  | succ t ih =>
    cases t with
    | zero =>
      simp [choose_one_right]
    | succ t' =>
      have ht0 : 0 < t' + 1 := Nat.succ_pos _
      have ih' := ih ht0
      have hrec := choose_succ_succ_ratio (n := p * B + (t' + 1)) (k := t' + 1)
      have hunion : Icc 1 (t' + 2) = Icc 1 (t' + 1) ∪ {t' + 2} := by
        ext x; simp [mem_Icc]; omega
      have hdisj : Disjoint (Icc 1 (t' + 1)) ({t' + 2} : Finset ℕ) := by
        simp [disjoint_left]; omega
      have hn : p * B + (t' + 1) + 1 = p * B + (t' + 2) := by omega
      rw [hn] at hrec
      rw [hrec, ih', hunion, prod_union hdisj, prod_singleton]
      push_cast
      ring

lemma choose_pB_t_one_add' {B t p : ℕ} (ht : 0 < t) :
    ((p * B + t).choose t : ℚ) =
      ∏ i ∈ Icc 1 t, (1 + (p * B : ℚ) / i) := by
  rw [choose_pB_t_prod ht]
  refine prod_congr rfl fun i hi => ?_
  have hi0 : (i : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hi).1)
  field_simp [hi0]
  ring

/-- `C(pB+t, t)` is a `p`-integer congruent to `1` modulo `p` when `t < p`. -/
lemma choose_pB_t_pCongr {B t p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 1 ((p * B + t).choose t : ℚ) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  rw [choose_pB_t_one_add' htpos]
  set s := Icc 1 t
  set x : ℕ → ℚ := fun i => (p * B : ℚ) / i
  have hx1 : ∀ i ∈ s, PCongr p 1 (x i) 0 := by
    intro i hi
    have : x i = (p : ℚ) * ((B : ℚ) * (i : ℚ)⁻¹) := by
      simp [x, div_eq_mul_inv, mul_assoc]
    rw [this]
    have hp1 : PCongr p 1 (p : ℚ) 0 := by
      refine pCongr_zero_of_val ?_
      simp [padicValRat_p]
    have hrest : IsPInt p ((B : ℚ) * (i : ℚ)⁻¹) := by
      have hiI : i ∈ Icc 1 (p - 1) := by
        have ⟨hi1, hi2⟩ := mem_Icc.mp hi
        have : i ≤ p - 1 := le_trans hi2 (mem_Icc.mp ht).2
        exact mem_Icc.mpr ⟨hi1, this⟩
      exact isPInt_mul (isPInt_nat p B) (isPInt_inv_of_mem_Icc hp hiI)
    simpa [mul_assoc] using pCongr_mul_isPInt hp1 hrest
  have hxI : ∀ i ∈ s, IsPInt p (x i) := by
    intro i hi
    exact isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) (hx1 i hi)
  -- Use the crude estimate ∏(1+x) ≡ 1 mod p (since each x ≡ 0 mod p)
  have hα : (1 : ℤ) ≤ 1 := le_rfl
  refine pCongr_prod_one_add_of (α := 1) (β := 1) (γ := 2) (δ := 1)
    hp hp5 (by norm_num) hx1 hxI ?_ ?_ le_rfl (by norm_num) (by norm_num) (by norm_num)
  · exact pCongr_sum_zero hx1
  · have : PCongr p 2 (∑ i ∈ s, x i ^ 2) 0 := by
      refine pCongr_sum_zero ?_
      intro i hi
      have hxi := hx1 i hi
      simpa [pow_two] using pCongr_mul_zero hxi hxi
    exact this


/- ## The case `a(p) ≡ 4 (mod p^3)` -/

lemma choose_p_t_pCongr {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 2 (((p + t - 1).choose t : ℚ) - (p : ℚ) / t) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have hpm : 1 ≤ p * 1 := by omega
  have h := choose_pm_t_one_add (M := 1) (t := t) (p := p) htpos (by omega)
  have h' : ((p + t - 1).choose t : ℚ) =
      ((p : ℚ) / t) *
        ∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) / ((t : ℚ) - j)) := by
    convert h using 2 <;> simp
  rw [h']
  -- (p/t) * (∏ (1 + p/(t-j)) - 1) has val ≥ 2
  have hprod : PCongr p 1
      (∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) / ((t : ℚ) - j))) 1 := by
    set s := Icc 1 (t - 1)
    set x : ℕ → ℚ := fun j => (p : ℚ) / ((t : ℚ) - j)
    have hx1 : ∀ j ∈ s, PCongr p 1 (x j) 0 := by
      intro j hj
      have ⟨hj1, hj2⟩ := mem_Icc.mp hj
      have htj : (t : ℚ) - j ≠ 0 := by
        have hlt : j < t := Nat.lt_of_le_pred htpos hj2
        exact sub_ne_zero.mpr (Nat.cast_injective.ne hlt.ne).symm
      have : x j = (p : ℚ) * (((t : ℚ) - j)⁻¹) := by
        simp [x, div_eq_mul_inv]
      rw [this]
      have hp1 : PCongr p 1 (p : ℚ) 0 := by
        refine pCongr_zero_of_val ?_
        simp [padicValRat_p]
      have hinv : IsPInt p (((t : ℚ) - j)⁻¹) := by
        -- t-j ∈ Icc 1 (p-1)
        have htjN : t - j ∈ Icc 1 (p - 1) := by
          have : 1 ≤ t - j := by omega
          have : t - j ≤ p - 1 := by
            have := (mem_Icc.mp ht).2; omega
          exact mem_Icc.mpr ⟨by omega, this⟩
        -- (t:ℚ) - j = ↑(t-j)
        have hcast : (t : ℚ) - j = ((t - j : ℕ) : ℚ) :=
          (nat_cast_sub_eq (by omega)).symm
        rw [hcast]
        exact isPInt_inv_of_mem_Icc hp htjN
      simpa using pCongr_mul_isPInt hp1 hinv
    have hxI : ∀ j ∈ s, IsPInt p (x j) :=
      fun j hj => isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) (hx1 j hj)
    refine pCongr_prod_one_add_of (α := 1) (β := 1) (γ := 2) (δ := 1)
      hp hp5 (by norm_num) hx1 hxI (pCongr_sum_zero hx1) ?_
      le_rfl (by norm_num) (by norm_num) (by norm_num)
    refine pCongr_sum_zero ?_
    intro j hj
    have hxi := hx1 j hj
    simpa [pow_two] using pCongr_mul_zero hxi hxi
  -- (p/t)*∏ = (p/t)*1 + (p/t)*(∏-1), second term val ≥ 1+1=2
  have ht0 : (t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp htpos)
  have hp_over_t : PCongr p 1 ((p : ℚ) / t) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := by
      refine pCongr_zero_of_val ?_
      simp [padicValRat_p]
    have hinv : IsPInt p ((t : ℚ)⁻¹) :=
      isPInt_inv_of_mem_Icc hp ht
    simpa [div_eq_mul_inv] using pCongr_mul_isPInt hp1 hinv
  have hdiff : PCongr p 1
      (∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) / ((t : ℚ) - j)) - 1) 0 := by
    simpa using pCongr_sub hprod (pCongr_refl p 1 1)
  have hmul := pCongr_mul_zero hp_over_t hdiff
  have heq : ((p : ℚ) / t) * ∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) / ((t : ℚ) - j)) -
      (p : ℚ) / t =
      ((p : ℚ) / t) *
        (∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) / ((t : ℚ) - j)) - 1) := by ring
  have hmul' : PCongr p 2
      (((p : ℚ) / t) * ∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) / ((t : ℚ) - j)) -
        (p : ℚ) / t) 0 := by
    rw [heq]
    exact pCongr_of_le (by norm_num : (2 : ℤ) ≤ 1 + 1) hmul
  exact hmul'


lemma pCongr_cube_of_val2 {p : ℕ} [Fact p.Prime] {x a : ℚ}
    (hxa : PCongr p 2 (x - a) 0) (ha : PCongr p 1 a 0) (haI : IsPInt p a)
    (hxI : IsPInt p x) :
    PCongr p 4 (x ^ 3 - a ^ 3) 0 := by
  have hdiff : x ^ 3 - a ^ 3 = (x - a) * (x ^ 2 + x * a + a ^ 2) := by ring
  rw [hdiff]
  have hx : PCongr p 1 x 0 := by
    have : x = (x - a) + a := by ring
    rw [this]
    have hadd := pCongr_add (pCongr_of_le (by norm_num : (1 : ℤ) ≤ 2) hxa) ha
    simpa using hadd
  have hsq : PCongr p 2 (x ^ 2 + x * a + a ^ 2) 0 := by
    have h1 : PCongr p 2 (x ^ 2) 0 := by
      simpa [pow_two] using pCongr_mul_zero hx hx
    have h2 : PCongr p 2 (x * a) 0 := pCongr_mul_zero hx ha
    have h3 : PCongr p 2 (a ^ 2) 0 := by
      simpa [pow_two] using pCongr_mul_zero ha ha
    simpa [add_assoc] using pCongr_add (pCongr_add h1 h2) h3
  exact pCongr_mul_zero hxa hsq

lemma unalign_term_p_leading {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 4
      (((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3 -
        (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have ha : PCongr p 1 ((p : ℚ) / t) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := by
      refine pCongr_zero_of_val ?_; simp [padicValRat_p]
    have hinv : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
    simpa [div_eq_mul_inv] using pCongr_mul_isPInt hp1 hinv
  have hxa := choose_p_t_pCongr hp hp5 ht
  have haI : IsPInt p ((p : ℚ) / t) :=
    isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) ha
  have hxI : IsPInt p ((p + t - 1).choose t : ℚ) := isPInt_nat p _
  have hcube := pCongr_cube_of_val2 hxa ha haI hxI
  -- (p+2t) C^3 - (p+2t) (p/t)^3 has val ≥ 4 (since p+2t is p-integer)
  have hpt : IsPInt p ((p + 2 * t : ℕ) : ℚ) := isPInt_nat p _
  have h1 : PCongr p 4
      (((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3 -
        ((p + 2 * t : ℕ) : ℚ) * ((p : ℚ) / t) ^ 3) 0 := by
    have : ((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3 -
        ((p + 2 * t : ℕ) : ℚ) * ((p : ℚ) / t) ^ 3 =
        ((p + 2 * t : ℕ) : ℚ) *
          (((p + t - 1).choose t : ℚ) ^ 3 - ((p : ℚ) / t) ^ 3) := by ring
    rw [this]
    simpa [mul_comm] using pCongr_mul_isPInt hcube hpt
  -- (p+2t)(p/t)^3 - 2 p^3 / t^2 = p^4 / t^3 has val ≥ 4
  have h2 : PCongr p 4
      (((p + 2 * t : ℕ) : ℚ) * ((p : ℚ) / t) ^ 3 -
        (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2) 0 := by
    have heq : ((p + 2 * t : ℕ) : ℚ) * ((p : ℚ) / t) ^ 3 -
        (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2 =
        (p : ℚ) ^ 4 / (t : ℚ) ^ 3 := by
      have hcast : ((p + 2 * t : ℕ) : ℚ) = (p : ℚ) + 2 * t := by push_cast; rfl
      rw [hcast]
      field_simp [ht0]
      ring
    rw [heq]
    have hp4 : PCongr p 4 ((p : ℚ) ^ 4) 0 := pCongr_p_pow 4
    have hinv : IsPInt p (((t : ℚ) ^ 3)⁻¹) := by
      have htI : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
      simpa [inv_pow] using isPInt_pow htI 3
    simpa [div_eq_mul_inv] using pCongr_mul_isPInt hp4 hinv
  have hadd := pCongr_add h1 h2
  have heq :
      (((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3 -
        (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2) =
      (((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3 -
        ((p + 2 * t : ℕ) : ℚ) * ((p : ℚ) / t) ^ 3) +
      (((p + 2 * t : ℕ) : ℚ) * ((p : ℚ) / t) ^ 3 -
        (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2) := by ring
  rw [heq]
  simpa using hadd

lemma unalign_sum_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 4
      (∑ t ∈ Icc 1 (p - 1),
        ((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlead : PCongr p 4
      (∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2) 0 := by
    have : ∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2 =
        (2 : ℚ) * (p : ℚ) ^ 3 * harmonicGen 2 (p - 1) := by
      rw [harmonicGen_two_Icc, mul_sum]
      refine sum_congr rfl fun t ht => ?_
      ring
    rw [this]
    have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := pCongr_p_pow 3
    have hH2 : PCongr p 1 (harmonicGen 2 (p - 1)) 0 :=
      pCongr_zero_of_val (wolstenholme_two hp hp5)
    have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
    have hmul := pCongr_mul_zero hp3 hH2
    have hmul' := pCongr_mul_isPInt hmul h2I
    have heq : (2 : ℚ) * (p : ℚ) ^ 3 * harmonicGen 2 (p - 1) =
        ((p : ℚ) ^ 3 * harmonicGen 2 (p - 1)) * 2 := by ring
    rw [heq]
    exact pCongr_of_le (by norm_num : (4 : ℤ) ≤ 3 + 1) hmul'
  have hterm := pCongr_sum (s := Icc 1 (p - 1))
    (fun t ht => unalign_term_p_leading hp hp5 ht)
  have hadd := pCongr_add hterm hlead
  have heq :
      (∑ t ∈ Icc 1 (p - 1),
        ((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3) =
      (∑ t ∈ Icc 1 (p - 1),
        (((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3 -
          (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2)) +
      (∑ t ∈ Icc 1 (p - 1), (2 : ℚ) * (p : ℚ) ^ 3 / (t : ℚ) ^ 2) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    ring
  rw [heq]
  simpa using hadd


lemma W_two_eq {p : ℕ} (hp : 0 < p) :
    ((2 * p - 1).choose p : ℕ) = (2 * p - 1).choose (p - 1) := by
  have hle : p - 1 ≤ 2 * p - 1 := by omega
  have hdiff : 2 * p - 1 - (p - 1) = p := by omega
  rw [← choose_symm hle, hdiff]

lemma range_succ_split {p : ℕ} (hp : 1 < p) :
    range (p + 1) = {0} ∪ Icc 1 (p - 1) ∪ {p} := by
  ext x
  simp only [mem_range, mem_union, mem_singleton, mem_Icc]
  omega

lemma range_succ_disj1 {p : ℕ} :
    Disjoint ({0} : Finset ℕ) (Icc 1 (p - 1)) := by
  simp [disjoint_left]

lemma range_succ_disj2 {p : ℕ} (hp : 1 < p) :
    Disjoint ({0} ∪ Icc 1 (p - 1) : Finset ℕ) {p} := by
  refine disjoint_left.mpr ?_
  intro x hx
  simp only [mem_union, mem_singleton, mem_Icc] at hx ⊢
  intro hxp
  rcases hx with hx0 | hxI
  · exact (hx0 ▸ hxp ▸ hp).not_gt Nat.zero_lt_one
  · have : x ≤ p - 1 := hxI.2
    have : x < p := Nat.lt_of_le_pred (by omega) this
    exact this.ne hxp

lemma Ssum_term_zero (n : ℕ) :
    ((n + 2 * 0 : ℕ) : ℚ) * ((n + 0 - 1).choose 0 : ℚ) ^ 3 = n := by
  simp

lemma Ssum_term_self {p : ℕ} (hp : 0 < p) :
    ((p + 2 * p : ℕ) : ℚ) * ((p + p - 1).choose p : ℚ) ^ 3 =
      ((3 * p : ℕ) : ℚ) * ((2 * p - 1).choose p : ℚ) ^ 3 := by
  have h1 : p + 2 * p = 3 * p := by ring
  have h2 : p + p - 1 = 2 * p - 1 := by omega
  simp [h1, h2]

lemma Ssum_p_split {p : ℕ} (hp : 1 < p) :
    (Ssum p : ℚ) =
      (p : ℚ) +
      (∑ t ∈ Icc 1 (p - 1),
        ((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3) +
      ((3 * p : ℕ) : ℚ) * ((2 * p - 1).choose p : ℚ) ^ 3 := by
  unfold Ssum
  rw [range_succ_split hp, sum_union (range_succ_disj2 hp),
      sum_union range_succ_disj1, sum_singleton, sum_singleton]
  have hppos : 0 < p := by omega
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sum]
  have h0 := Ssum_term_zero p
  have hpterm := Ssum_term_self hppos
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [h0, hpterm]
  push_cast
  rfl

lemma padicValNat_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    padicValNat p 2 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by
    intro hd
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega)

lemma W_two_pCongr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 3 ((2 * p - 1).choose (p - 1) : ℚ) 1 := by
  have h := wolstenholme_W hp hp5 (k := 2) (by norm_num)
  simpa [padicValNat_two hp hp5] using h

lemma W_two_cube_pCongr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 3 (((2 * p - 1).choose p : ℚ) ^ 3) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hW : PCongr p 3 ((2 * p - 1).choose p : ℚ) 1 := by
    rw [W_two_eq hp.pos]
    exact W_two_pCongr hp hp5
  have hI : IsPInt p ((2 * p - 1).choose p : ℚ) := isPInt_nat p _
  have hpow := pCongr_pow_of 3 hW hI (isPInt_one p)
  simpa using hpow

lemma Ssum_p_endpoint {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 4
      ((p : ℚ) + ((3 * p : ℕ) : ℚ) * ((2 * p - 1).choose p : ℚ) ^ 3 -
        (4 : ℚ) * p) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcube := W_two_cube_pCongr hp hp5
  have hdiff : PCongr p 3
      (((2 * p - 1).choose p : ℚ) ^ 3 - 1) 0 :=
    pCongr_sub_zero hcube
  have hp1 : PCongr p 1 ((p : ℚ)) 0 := by
    refine pCongr_zero_of_val ?_
    simp [padicValRat_p]
  have h3I : IsPInt p (3 : ℚ) := isPInt_nat p 3
  have h3p : PCongr p 1 ((3 : ℚ) * p) 0 := by
    simpa [mul_comm] using pCongr_mul_isPInt hp1 h3I
  have hmul : PCongr p 4
      (((3 : ℚ) * p) * (((2 * p - 1).choose p : ℚ) ^ 3 - 1)) 0 :=
    pCongr_of_le (by norm_num : (4 : ℤ) ≤ 1 + 3) (pCongr_mul_zero h3p hdiff)
  have heq :
      (p : ℚ) + ((3 * p : ℕ) : ℚ) * ((2 * p - 1).choose p : ℚ) ^ 3 -
        (4 : ℚ) * p =
      ((3 : ℚ) * p) * (((2 * p - 1).choose p : ℚ) ^ 3 - 1) := by
    push_cast
    ring
  rw [heq]
  exact hmul

lemma Ssum_p_sub_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p 4 ((Ssum p : ℚ) - 4 * p) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  rw [Ssum_p_split hp1]
  have hunalign := unalign_sum_p hp hp5
  have hend := Ssum_p_endpoint hp hp5
  have heq :
      (p : ℚ) +
        (∑ t ∈ Icc 1 (p - 1),
          ((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3) +
        ((3 * p : ℕ) : ℚ) * ((2 * p - 1).choose p : ℚ) ^ 3 -
        4 * p =
      (∑ t ∈ Icc 1 (p - 1),
        ((p + 2 * t : ℕ) : ℚ) * ((p + t - 1).choose t : ℚ) ^ 3) +
      ((p : ℚ) + ((3 * p : ℕ) : ℚ) * ((2 * p - 1).choose p : ℚ) ^ 3 -
        (4 : ℚ) * p) := by
    ring
  rw [heq]
  simpa using pCongr_add hunalign hend

lemma a_one : a 1 = 4 := by
  rw [a_eq_Ssum_div 1 Nat.zero_lt_one]
  unfold Ssum
  rw [Nat.div_one]
  simp [sum_range_succ, choose_zero_right, choose_self]

lemma a_cast_eq {n : ℕ} (hn : 0 < n) :
    (a n : ℚ) = (Ssum n : ℚ) / n := by
  have h := Ssum_eq_a_mul n hn
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  apply (eq_div_iff hn0).mpr
  exact_mod_cast h.symm

/-- If `x ≡ 0` to precision `m + v_p(y)` then `x/y ≡ 0` to precision `m`. -/
lemma pCongr_div_of_val {p : ℕ} [Fact p.Prime] {m : ℤ} {x y : ℚ}
    (hy : y ≠ 0)
    (h : PCongr p (m + padicValRat p y) x 0) :
    PCongr p m (x / y) 0 := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx, pCongr_refl]
  refine pCongr_zero_of_val ?_
  have hx0 : padicValRat p x = padicValRat p (x - 0) := by simp
  have hval : m + padicValRat p y ≤ padicValRat p x := by
    rcases h with h | h
    · exact (hx h).elim
    · simpa [hx0] using h
  have : x / y = x * y⁻¹ := div_eq_mul_inv _ _
  rw [this, padicValRat.mul hx (inv_ne_zero hy), padicValRat.inv y]
  linarith

lemma pCongr_of_sub_zero {p : ℕ} {m : ℤ} {x y : ℚ}
    (h : PCongr p m (x - y) 0) : PCongr p m x y := by
  rcases h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by simpa [sub_zero] using h)

lemma pCongr_a_of_Ssum {p N m : ℕ} (hp : p.Prime) (hN : 0 < N)
    (h : PCongr p (m + 1 + padicValNat p N)
      ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) 0) :
    PCongr p m (a (p * N) : ℚ) (a N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpN : 0 < p * N := Nat.mul_pos hp.pos hN
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hden : (p : ℚ) * N ≠ 0 := mul_ne_zero hp0 hN0
  rw [a_cast_eq hpN, a_cast_eq hN]
  apply pCongr_of_sub_zero
  have hcast : ((p * N : ℕ) : ℚ) = (p : ℚ) * N := by push_cast; rfl
  have heq :
      (Ssum (p * N) : ℚ) / (p * N : ℕ) - (Ssum N : ℚ) / N =
        ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) / ((p : ℚ) * N) := by
    rw [hcast]
    field_simp [hp0, hN0]
  rw [heq]
  have hvil : padicValRat p ((p : ℚ) * N) = 1 + padicValNat p N := by
    rw [padicValRat.mul hp0 hN0, padicValRat_p, padicValRat.of_nat]
  have hmod : (m : ℤ) + padicValRat p ((p : ℚ) * N) =
      m + 1 + padicValNat p N := by
    rw [hvil]; ring
  rw [← hmod] at h
  exact pCongr_div_of_val hden h

/- ## Aligned terms for `S(pN)` vs `p S(N)` -/

/-- `C_big / C_small ≡ 1` upgrades to `C_big ≡ C_small` at precision `m + v(C_small)`. -/
lemma pCongr_mul_denom {p : ℕ} [Fact p.Prime] {m : ℤ} {x y : ℚ}
    (hy : y ≠ 0) (h : PCongr p m (x / y) 1) :
    PCongr p (m + padicValRat p y) x y := by
  have heq : x - y = y * (x / y - 1) := by
    field_simp [hy]
  rcases eq_or_ne x y with hxy | hxy
  · exact Or.inl hxy
  refine Or.inr ?_
  have hne : x / y - 1 ≠ 0 := by
    intro hz
    have : x / y = 1 := sub_eq_zero.mp hz
    have : x = y := (div_eq_one_iff_eq hy).mp this
    exact hxy this
  rw [heq, padicValRat.mul hy hne]
  rcases h with h | h
  · exact (hne (by simp [h])).elim
  linarith

lemma padicValRat_choose (p n k : ℕ) [Fact p.Prime] :
    padicValRat p ((n.choose k : ℚ)) = padicValNat p (n.choose k) :=
  padicValRat.of_nat

lemma padicValNat_two_mul {p q : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hq : q ≠ 0) :
    padicValNat p (2 * q) = padicValNat p q := by
  have h2 : padicValNat p 2 = 0 := padicValNat_two Fact.out hp5
  rw [padicValNat.mul (by norm_num) hq, h2, zero_add]

/-- `v_p(N) ≤ v_p(N+2q) + v_p(C(N+q-1,q))`. -/
lemma aligned_kummer_bound {p N q : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hN : N ≠ 0) :
    (padicValNat p N : ℤ) ≤
      padicValNat p (N + 2 * q) +
        padicValNat p ((N + q - 1).choose q) := by
  rcases eq_or_ne q 0 with hq0 | hq0
  · subst hq0; simp
  have hC : padicValNat p N - padicValNat p q ≤
      padicValNat p ((N + q - 1).choose q) :=
    rising_aligned_base_val (p := p) (m := N) (q := q) hN hq0
  have h2q : padicValNat p (2 * q) = padicValNat p q :=
    padicValNat_two_mul hp5 hq0
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hsum0 : ((N : ℚ) + (2 * q : ℕ)) ≠ 0 := by
    exact_mod_cast (Nat.add_pos_left hNpos (2 * q)).ne'
  have hcast : ((N + 2 * q : ℕ) : ℚ) = (N : ℚ) + (2 * q : ℕ) := by
    push_cast; rfl
  have hmin : min (padicValRat p (N : ℚ)) (padicValRat p (2 * q : ℕ)) ≤
      padicValRat p ((N + 2 * q : ℕ) : ℚ) := by
    rw [hcast]
    exact padicValRat.min_le_padicValRat_add hsum0
  have hvN : padicValRat p (N : ℚ) = padicValNat p N := padicValRat.of_nat
  have hv2q : padicValRat p ((2 * q : ℕ) : ℚ) = padicValNat p (2 * q) :=
    padicValRat.of_nat
  have hvsum : padicValRat p ((N + 2 * q : ℕ) : ℚ) = padicValNat p (N + 2 * q) :=
    padicValRat.of_nat
  rw [hvN, hv2q, hvsum, h2q] at hmin
  by_cases hle : padicValNat p q ≤ padicValNat p N
  · have hqle : (padicValNat p q : ℤ) ≤ padicValNat p N := Nat.cast_le.mpr hle
    have hminq : (padicValNat p q : ℤ) ≤ padicValNat p (N + 2 * q) := by
      rwa [min_eq_right hqle] at hmin
    have hCℤ : (padicValNat p N : ℤ) ≤
        (padicValNat p q : ℤ) + padicValNat p ((N + q - 1).choose q) := by
      have hC' : ((padicValNat p N - padicValNat p q : ℕ) : ℤ) ≤
          (padicValNat p ((N + q - 1).choose q) : ℤ) :=
        Nat.cast_le.mpr hC
      rw [Nat.cast_sub hle] at hC'
      linarith
    linarith
  · have hge : padicValNat p N ≤ padicValNat p q := Nat.le_of_not_ge hle
    have hNle : (padicValNat p N : ℤ) ≤ padicValNat p q := Nat.cast_le.mpr hge
    have hminN : (padicValNat p N : ℤ) ≤ padicValNat p (N + 2 * q) := by
      rwa [min_eq_left hNle] at hmin
    have : (0 : ℤ) ≤ padicValNat p ((N + q - 1).choose q) :=
      Nat.cast_nonneg _
    linarith

/-- The aligned binomials are congruent at precision `3 + v(C_small)`. -/
lemma aligned_choose_pCongr {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (3 + padicValNat p ((N + q - 1).choose q))
      (((p * (N + q) - 1).choose (p * q) : ℚ))
      (((N + q - 1).choose q : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBA : q < N + q := by omega
  have hρ := choose_aligned_pCongr (A := N + q) (B := q) hp hp5 hBA
  have hden : ((N + q - 1).choose q : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (by omega)).ne'
  have h := pCongr_mul_denom hden hρ
  have hmul1 : (N + q) * p = p * (N + q) := Nat.mul_comm _ _
  have hmul2 : q * p = p * q := Nat.mul_comm _ _
  rw [hmul1, hmul2] at h
  simpa [padicValRat_choose] using h

lemma aligned_choose_cube_pCongr {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (3 + padicValNat p ((N + q - 1).choose q))
      ((((p * (N + q) - 1).choose (p * q) : ℚ)) ^ 3)
      ((((N + q - 1).choose q : ℚ)) ^ 3) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pCongr_pow_of 3 (aligned_choose_pCongr hp hp5 hN)
    (isPInt_nat p _) (isPInt_nat p _)

/-- One aligned summand of `S(pN)` matches the corresponding summand of `p S(N)`
at precision `4 + v_p(N)`. -/
lemma aligned_term_pCongr {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + padicValNat p N)
      (((p * N + 2 * (p * q) : ℕ) : ℚ) *
        (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3))
      (((p : ℚ) * (N + 2 * q : ℕ) *
        (((N + q - 1).choose q : ℚ) ^ 3))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcube := aligned_choose_cube_pCongr hp hp5 hN (q := q)
  have hidx : p * N + p * q - 1 = p * (N + q) - 1 := by
    rw [← Nat.mul_add]
  have hidx' : p * N + 2 * (p * q) = p * (N + 2 * q) := by ring
  rw [hidx, hidx']
  have hpref_eq : ((p * (N + 2 * q) : ℕ) : ℚ) =
      (p : ℚ) * (N + 2 * q : ℕ) := by push_cast; rfl
  -- difference = p(N+2q) * (C_big^3 - C_small^3)
  apply pCongr_of_sub_zero
  have hdiff :
      ((p * (N + 2 * q) : ℕ) : ℚ) *
          (((p * (N + q) - 1).choose (p * q) : ℚ) ^ 3) -
        (p : ℚ) * (N + 2 * q : ℕ) *
          (((N + q - 1).choose q : ℚ) ^ 3) =
      ((p : ℚ) * (N + 2 * q : ℕ)) *
        ((((p * (N + q) - 1).choose (p * q) : ℚ) ^ 3) -
          (((N + q - 1).choose q : ℚ) ^ 3)) := by
    rw [hpref_eq]
    ring
  rw [hdiff]
  have hcdiff : PCongr p (3 + padicValNat p ((N + q - 1).choose q))
      ((((p * (N + q) - 1).choose (p * q) : ℚ) ^ 3) -
        (((N + q - 1).choose q : ℚ) ^ 3)) 0 :=
    pCongr_sub_zero hcube
  have hp1 : PCongr p 1 (p : ℚ) 0 := by
    refine pCongr_zero_of_val ?_
    simp [padicValRat_p]
  have hN2 : PCongr p (padicValNat p (N + 2 * q))
      ((N + 2 * q : ℕ) : ℚ) 0 := pCongr_coe_val
  have hpref : PCongr p (1 + padicValNat p (N + 2 * q))
      ((p : ℚ) * (N + 2 * q : ℕ)) 0 :=
    pCongr_mul_zero hp1 hN2
  have hmul := pCongr_mul_zero hpref hcdiff
  have hneed : (4 + padicValNat p N : ℤ) ≤
      (1 + padicValNat p (N + 2 * q)) +
        (3 + padicValNat p ((N + q - 1).choose q)) := by
    have hb := aligned_kummer_bound (p := p) hp5 (hN := hN.ne') (q := q)
    linarith
  exact pCongr_of_le hneed hmul

lemma aligned_sum_pCongr {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + padicValNat p N)
      (∑ q ∈ range (N + 1),
        ((p * N + 2 * (p * q) : ℕ) : ℚ) *
          (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3))
      ((p : ℚ) * Ssum N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hterm := pCongr_sum (s := range (N + 1))
    (fun q _ => aligned_term_pCongr hp hp5 hN (q := q))
  have hrhs :
      ∑ q ∈ range (N + 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (((N + q - 1).choose q : ℚ) ^ 3) =
      (p : ℚ) * Ssum N := by
    unfold Ssum
    rw [Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun q hq => ?_
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring
  rw [← hrhs]
  exact hterm

lemma image_mul_range (p N : ℕ) (hp : 0 < p) :
    (range (N + 1)).image (fun q => p * q) =
      (range (p * N + 1)).filter (p ∣ ·) := by
  ext k
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨q, hq, rfl⟩
    constructor
    · have : p * q ≤ p * N := Nat.mul_le_mul_left p (Nat.lt_succ_iff.mp hq)
      omega
    · exact ⟨q, rfl⟩
  · rintro ⟨hk, ⟨q, rfl⟩⟩
    refine ⟨q, ?_, rfl⟩
    have hle : p * q ≤ p * N := by omega
    exact Nat.lt_succ_iff.mpr (Nat.le_of_mul_le_mul_left hle hp)

lemma Ssum_split_aligned {p N : ℕ} (hp : p.Prime) (hN : 0 < N) :
    (Ssum (p * N) : ℚ) =
      (∑ q ∈ range (N + 1),
        ((p * N + 2 * (p * q) : ℕ) : ℚ) *
          (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3)) +
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) := by
  unfold Ssum
  have hdisj :
      Disjoint ((range (p * N + 1)).filter (p ∣ ·))
        ((range (p * N + 1)).filter (fun k => ¬ p ∣ k)) :=
    disjoint_filter_filter_not _ _ _
  have hunion :
      range (p * N + 1) =
        (range (p * N + 1)).filter (p ∣ ·) ∪
          (range (p * N + 1)).filter (fun k => ¬ p ∣ k) :=
    (filter_union_filter_not_eq (p := fun k : ℕ => p ∣ k) (range (p * N + 1))).symm
  rw [Nat.cast_sum (R := ℚ)]
  nth_rw 1 [hunion]
  rw [sum_union hdisj]
  have himg := image_mul_range p N hp.pos
  have hinj : Set.InjOn (fun q => p * q) (range (N + 1) : Set ℕ) := by
    intro q _ q' _ heq
    exact Nat.eq_of_mul_eq_mul_left hp.pos heq
  have h1 :
      ∑ k ∈ (range (p * N + 1)).filter (p ∣ ·),
        (((p * N + 2 * k) * ((p * N + k - 1).choose k) ^ 3 : ℕ) : ℚ) =
      ∑ q ∈ range (N + 1),
        ((p * N + 2 * (p * q) : ℕ) : ℚ) *
          (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3) := by
    rw [← himg, sum_image hinj]
    refine sum_congr rfl fun q hq => ?_
    push_cast
    rfl
  have h2 :
      ∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        (((p * N + 2 * k) * ((p * N + k - 1).choose k) ^ 3 : ℕ) : ℚ) =
      ∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3) :=
    sum_congr rfl fun k hk => by push_cast; rfl
  rw [h1, h2]

/-- An unaligned rising binomial at `pN` has valuation at least `v_p(N)+1`. -/
lemma unalign_choose_val {p N k : ℕ} [Fact p.Prime]
    (hN : N ≠ 0) (hkp : ¬ p ∣ k) (hk : 0 < k) :
    padicValNat p N + 1 ≤ padicValNat p ((p * N + k - 1).choose k) :=
  rising_unaligned_val hN hkp hk

lemma unalign_term_val {p N k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : N ≠ 0) (hkp : ¬ p ∣ k) (hk : 0 < k) :
    PCongr p (3 * (padicValNat p N + 1))
      (((p * N + 2 * k : ℕ) : ℚ) *
        (((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hC : (padicValNat p N + 1 : ℤ) ≤
      padicValNat p ((p * N + k - 1).choose k) :=
    Nat.cast_le.mpr (unalign_choose_val hN hkp hk)
  have hC3 : PCongr p (3 * (padicValNat p N + 1))
      ((((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
    have h1 : PCongr p (padicValNat p ((p * N + k - 1).choose k))
        (((p * N + k - 1).choose k : ℚ)) 0 := pCongr_coe_val
    have h3 := pCongr_pow_zero (k := 3) h1
    refine pCongr_of_le ?_ h3
    have : (3 * (padicValNat p N + 1) : ℤ) ≤
        3 * (padicValNat p ((p * N + k - 1).choose k) : ℤ) := by
      nlinarith
    simpa using this
  have hpref : IsPInt p ((p * N + 2 * k : ℕ) : ℚ) := isPInt_nat p _
  simpa [mul_comm] using pCongr_mul_isPInt hC3 hpref

/-- For `v_p(N) ≥ 1` every unaligned term already has valuation `≥ 4 + v_p(N)`. -/
lemma unalign_term_of_pos_val {p N k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : N ≠ 0) (hv : 1 ≤ padicValNat p N)
    (hkp : ¬ p ∣ k) (hk : 0 < k) :
    PCongr p (4 + padicValNat p N)
      (((p * N + 2 * k : ℕ) : ℚ) *
        (((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
  have h := unalign_term_val hp hp5 hN hkp hk
  refine pCongr_of_le ?_ h
  have : (4 + padicValNat p N : ℤ) ≤ 3 * (padicValNat p N + 1) := by
    have : (1 : ℤ) ≤ padicValNat p N := Nat.cast_le.mpr hv
    linarith
  exact this

lemma unalign_sum_of_pos_val {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hv : 1 ≤ padicValNat p N) :
    PCongr p (4 + padicValNat p N)
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pCongr_sum_zero ?_
  intro k hk
  have ⟨hkR, hkp⟩ := mem_filter.mp hk
  have hkpos : 0 < k := by
    have : k ≠ 0 := by
      intro h0
      subst h0
      exact hkp (dvd_zero p)
    exact Nat.pos_of_ne_zero this
  exact unalign_term_of_pos_val hp hp5 hN.ne' hv hkp hkpos

/-- `S(pN) ≡ p S(N)` at precision `4+v_p(N)` when `v_p(N) ≥ 1`. -/
lemma Ssum_pN_of_pos_val {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hv : 1 ≤ padicValNat p N) :
    PCongr p (4 + padicValNat p N)
      ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Ssum_split_aligned hp hN]
  have hal := aligned_sum_pCongr hp hp5 hN
  have hun := unalign_sum_of_pos_val hp hp5 hN hv
  have heq :
      (∑ q ∈ range (N + 1),
          ((p * N + 2 * (p * q) : ℕ) : ℚ) *
            (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3)) +
        (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
          ((p * N + 2 * k : ℕ) : ℚ) *
            (((p * N + k - 1).choose k : ℚ) ^ 3)) -
        (p : ℚ) * Ssum N =
      (∑ q ∈ range (N + 1),
          ((p * N + 2 * (p * q) : ℕ) : ℚ) *
            (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3) -
        (p : ℚ) * Ssum N) +
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) := by
    ring
  rw [heq]
  have hal0 := pCongr_sub_zero hal
  simpa using pCongr_add hal0 hun

/- ## Unaligned leading terms when `p ∤ N` -/

lemma choose_pM_t_pCongr {p M t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 2
      (((p * M + t - 1).choose t : ℚ) - ((p * M : ℚ) / t)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have hpm : 1 ≤ p * M := Nat.mul_le_mul hp.pos hM
  rw [choose_pm_t_one_add htpos hpm]
  have hprod : PCongr p 1
      (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j))) 1 := by
    set s := Icc 1 (t - 1)
    set x : ℕ → ℚ := fun j => (p * M : ℚ) / ((t : ℚ) - j)
    have hx1 : ∀ j ∈ s, PCongr p 1 (x j) 0 := by
      intro j hj
      have ⟨hj1, hj2⟩ := mem_Icc.mp hj
      have : x j = (p : ℚ) * ((M : ℚ) * ((t : ℚ) - j)⁻¹) := by
        simp [x, div_eq_mul_inv, mul_assoc]
      rw [this]
      have hp1 : PCongr p 1 (p : ℚ) 0 := pCongr_zero_of_val (by simp [padicValRat_p])
      have htjN : t - j ∈ Icc 1 (p - 1) := by
        have : 1 ≤ t - j := by omega
        have : t - j ≤ p - 1 := by
          have := (mem_Icc.mp ht).2; omega
        exact mem_Icc.mpr ⟨by omega, this⟩
      have hcast : (t : ℚ) - j = ((t - j : ℕ) : ℚ) :=
        (nat_cast_sub_eq (by omega)).symm
      have hinv : IsPInt p (((t : ℚ) - j)⁻¹) := by
        rw [hcast]; exact isPInt_inv_of_mem_Icc hp htjN
      have hrest : IsPInt p ((M : ℚ) * ((t : ℚ) - j)⁻¹) :=
        isPInt_mul (isPInt_nat p M) hinv
      simpa [mul_assoc] using pCongr_mul_isPInt hp1 hrest
    have hxI : ∀ j ∈ s, IsPInt p (x j) :=
      fun j hj => isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) (hx1 j hj)
    refine pCongr_prod_one_add_of (α := 1) (β := 1) (γ := 2) (δ := 1)
      hp hp5 (by norm_num) hx1 hxI (pCongr_sum_zero hx1) ?_
      le_rfl (by norm_num) (by norm_num) (by norm_num)
    refine pCongr_sum_zero ?_
    intro j hj
    simpa [pow_two] using pCongr_mul_zero (hx1 j hj) (hx1 j hj)
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have hpM_over_t : PCongr p 1 ((p * M : ℚ) / t) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := pCongr_zero_of_val (by simp [padicValRat_p])
    have hrest : IsPInt p ((M : ℚ) * (t : ℚ)⁻¹) :=
      isPInt_mul (isPInt_nat p M) (isPInt_inv_of_mem_Icc hp ht)
    simpa [div_eq_mul_inv, mul_assoc] using pCongr_mul_isPInt hp1 hrest
  have hdiff : PCongr p 1
      (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) - 1) 0 :=
    pCongr_sub_zero hprod
  have heq : ((p * M : ℚ) / t) *
        ∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) -
      (p * M : ℚ) / t =
      ((p * M : ℚ) / t) *
        (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) - 1) := by
    ring
  rw [heq]
  exact pCongr_of_le (by norm_num : (2 : ℤ) ≤ 1 + 1) (pCongr_mul_zero hpM_over_t hdiff)

lemma padicValRat_one (p : ℕ) [Fact p.Prime] : padicValRat p (1 : ℚ) = 0 := by
  simp [padicValRat.of_nat]

lemma pCongr_inv_one {p : ℕ} [Fact p.Prime] {m : ℤ} {x : ℚ}
    (hm : 1 ≤ m) (h : PCongr p m x 1) (hx0 : x ≠ 0) :
    PCongr p m x⁻¹ 1 := by
  rcases eq_or_ne x 1 with hx | hx
  · simp [hx, pCongr_refl]
  have hne : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hval : m ≤ padicValRat p (x - 1) := h.resolve_left hx
  have hxval : padicValRat p x = 0 := by
    have hsum : x = (1 : ℚ) + (x - 1) := by ring
    have hone : padicValRat p (1 : ℚ) = 0 := padicValRat_one p
    have hlt : padicValRat p (1 : ℚ) < padicValRat p (x - 1) := by
      rw [hone]; linarith
    have hqr : (1 : ℚ) + (x - 1) ≠ 0 := by
      rw [← hsum]; exact hx0
    rw [hsum, padicValRat.add_eq_of_lt hqr (by norm_num) hne hlt, hone]
  have heq : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by
    field_simp [hx0]
    ring
  refine Or.inr ?_
  rw [heq, padicValRat.mul (neg_ne_zero.mpr hne) (inv_ne_zero hx0),
      padicValRat.neg, padicValRat.inv x, hxval]
  simpa using hval

lemma unalign_div_lt {p N k : ℕ} (hp : p.Prime) (hN : 0 < N)
    (hk : k < p * N + 1) (hkp : ¬ p ∣ k) :
    k / p < N := by
  have hne : k ≠ p * N := fun heq => hkp (heq ▸ dvd_mul_right p N)
  have hk' : k ≤ p * N - 1 := by omega
  have hle : k / p ≤ (p * N - 1) / p := Nat.div_le_div_right hk'
  have hdiv : (p * N - 1) / p = N - 1 := by
    have hppos := hp.pos
    have hdecomp : p * N - 1 = (p - 1) + (N - 1) * p := by
      have hmul : p * N = p * (N - 1) + p := by
        nth_rw 1 [← Nat.sub_add_cancel (n := N) (m := 1) hN]
        rw [Nat.mul_add, mul_one]
      have h1 : p * N - 1 = p * (N - 1) + p - 1 := by rw [hmul]
      have h2 : p * (N - 1) + p - 1 = p * (N - 1) + (p - 1) :=
        Nat.add_sub_assoc hppos _
      rw [h1, h2, add_comm, mul_comm]
    rw [hdecomp, Nat.add_mul_div_right _ _ hppos,
        Nat.div_eq_of_lt (Nat.sub_lt hppos Nat.zero_lt_one), zero_add]
  rw [hdiv] at hle
  exact Nat.lt_of_le_pred hN hle

lemma unalign_mod_mem {p k : ℕ} (hp : p.Prime) (hkp : ¬ p ∣ k) :
    k % p ∈ Icc 1 (p - 1) := by
  have hmod : k % p < p := Nat.mod_lt k hp.pos
  have hne : k % p ≠ 0 := fun h0 => hkp (Nat.dvd_of_mod_eq_zero h0)
  exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hne, Nat.le_pred_of_lt hmod⟩

lemma unalign_choose_formula {p N k : ℕ} (hp : p.Prime) (hN : 0 < N)
    (hk : k < p * N + 1) (hkp : ¬ p ∣ k) :
    let q := k / p
    let t := k % p
    ((p * N + k - 1).choose k : ℚ) =
      ((p * (N + q) - 1).choose (p * q) : ℚ) *
        ((p * (N + q) + t - 1).choose t : ℚ) /
        ((p * q + t).choose t : ℚ) := by
  intro q t
  have ht := unalign_mod_mem hp hkp
  have hBM : q < N + q := by omega
  have hkeq : k = p * q + t := (Nat.div_add_mod k p).symm
  have hidx : p * N + k - 1 = p * (N + q) + t - 1 := by
    rw [hkeq]
    have : p * N + (p * q + t) = p * (N + q) + t := by
      rw [Nat.mul_add, add_assoc]
    have hpos : 1 ≤ p * N + k := Nat.succ_le_of_lt (Nat.add_pos_right _ (by
      exact Nat.pos_of_ne_zero (fun h0 => hkp (h0 ▸ dvd_zero p))))
    omega
  rw [hidx, hkeq]
  exact choose_unalign_eq (M := N + q) (B := q) (t := t) (p := p) hBM hp.pos

lemma dvd_add_val {p a : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hd : p ∣ a) :
    1 ≤ padicValNat p a :=
  (padicValNat_dvd_iff_le ha).mp (by simpa using hd)

/-- If `p ∣ (N+q)` then an unaligned term has valuation at least `4`. -/
lemma unalign_term_when_p_dvd_M {p N k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hkR : k < p * N + 1) (hkp : ¬ p ∣ k)
    (hM : p ∣ N + k / p) :
    PCongr p 4
      (((p * N + 2 * k : ℕ) : ℚ) *
        (((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set q := k / p
  set t := k % p
  have ht : t ∈ Icc 1 (p - 1) := unalign_mod_mem hp hkp
  have hMpos : 0 < N + q := Nat.add_pos_left hN _
  have hY0 : PCongr p 2 (((p * (N + q) + t - 1).choose t : ℚ)) 0 := by
    have hlead := choose_pM_t_pCongr hp hp5 hMpos ht
    have hp1 : PCongr p 1 (p : ℚ) 0 := pCongr_zero_of_val (by simp)
    have hMv : PCongr p 1 ((N + q : ℕ) : ℚ) 0 :=
      pCongr_nat_of_val hMpos.ne' (dvd_add_val hMpos.ne' hM)
    have hinv : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
    have hpM : PCongr p 2 ((p : ℚ) * ((N + q : ℕ) : ℚ) / t) 0 := by
      have : (p : ℚ) * ((N + q : ℕ) : ℚ) / t =
          (p : ℚ) * ((N + q : ℕ) : ℚ) * (t : ℚ)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [this]
      exact pCongr_of_le (by norm_num : (2 : ℤ) ≤ 1 + 1)
        (pCongr_mul_isPInt (pCongr_mul_zero hp1 hMv) hinv)
    exact pCongr_trans (pCongr_of_sub_zero hlead) hpM
  have hform := unalign_choose_formula hp hN hkR hkp
  have hZ0 : ((p * q + t).choose t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.le_add_left t (p * q))).ne'
  have hZ1 := choose_pB_t_pCongr (B := q) hp hp5 ht
  have hZinv := pCongr_inv_one (by norm_num : (1 : ℤ) ≤ 1) hZ1 hZ0
  have hZI : IsPInt p (((p * q + t).choose t : ℚ)⁻¹) :=
    isPInt_of_pCongr_one (by norm_num : (0 : ℤ) ≤ 1) hZinv
  have hX : IsPInt p ((p * (N + q) - 1).choose (p * q) : ℚ) := isPInt_nat p _
  have hC : PCongr p 2 ((p * N + k - 1).choose k : ℚ) 0 := by
    change ((p * N + k - 1).choose k : ℚ) =
        ((p * (N + q) - 1).choose (p * q) : ℚ) *
          ((p * (N + q) + t - 1).choose t : ℚ) /
          ((p * q + t).choose t : ℚ) at hform
    rw [hform]
    have hmul := pCongr_mul_isPInt hY0 hX
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      pCongr_mul_isPInt hmul hZI
  have hC3 : PCongr p 6 ((((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
    simpa using pCongr_pow_zero (k := 3) hC
  have hpref : IsPInt p ((p * N + 2 * k : ℕ) : ℚ) := isPInt_nat p _
  exact pCongr_of_le (by norm_num : (4 : ℤ) ≤ 6)
    (by simpa [mul_comm] using pCongr_mul_isPInt hC3 hpref)


/- ## Standard binomial product formula and strong JK -/

lemma prod_Icc_succ_div (k : ℕ) :
    ∏ i ∈ Icc 1 k, (i : ℚ) = (k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdisj : Disjoint (Icc 1 k) ({k + 1} : Finset ℕ) := by
      simp [disjoint_left]; omega
    have hunion : Icc 1 (k + 1) = Icc 1 k ∪ {k + 1} := by
      ext x; simp [mem_Icc]; omega
    rw [hunion, prod_union hdisj, prod_singleton, ih, factorial_succ]
    push_cast; ring

lemma prod_Icc_shift (n k : ℕ) (hkn : k ≤ n) :
    ∏ i ∈ Icc 1 k, ((n - k + i : ℕ) : ℚ) = (n.factorial : ℚ) / ((n - k).factorial : ℚ) := by
  have hden : ((n - k).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  apply (eq_div_iff hden).mpr
  have hsplit : Icc 1 n = Icc 1 (n - k) ∪ Icc (n - k + 1) n := by
    ext x; simp [mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 (n - k)) (Icc (n - k + 1) n) := by
    refine disjoint_left.mpr ?_
    intro a ha hb
    simp [mem_Icc] at ha hb; omega
  have hprod_all : ∏ i ∈ Icc 1 n, (i : ℚ) = (n.factorial : ℚ) :=
    prod_Icc_succ_div n
  have hprod_lo : ∏ i ∈ Icc 1 (n - k), (i : ℚ) = ((n - k).factorial : ℚ) :=
    prod_Icc_succ_div (n - k)
  have himg : (Icc 1 k).image (fun i => n - k + i) = Icc (n - k + 1) n := by
    ext x
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      exact ⟨by omega, by omega⟩
    · intro ⟨hx1, hx2⟩
      refine ⟨x - (n - k), ⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
  have hinj : Set.InjOn (fun i => n - k + i) (Icc 1 k : Set ℕ) := by
    intro a _ b _ h; exact Nat.add_left_cancel h
  have hprod_hi : ∏ i ∈ Icc (n - k + 1) n, (i : ℚ) =
      ∏ i ∈ Icc 1 k, ((n - k + i : ℕ) : ℚ) := by
    rw [← himg, prod_image hinj]
  rw [← hprod_all, hsplit, prod_union hdisj, hprod_lo, hprod_hi]
  ring

lemma choose_eq_prod_std {n k : ℕ} (hkn : k ≤ n) :
    (n.choose k : ℚ) = ∏ i ∈ Icc 1 k, ((n - k + i : ℕ) : ℚ) / i := by
  have hch : (n.choose k : ℚ) =
      (n.factorial : ℚ) / ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) := by
    have := choose_mul_factorial_mul_factorial hkn
    have hk0 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
    have hnk0 : ((n - k).factorial : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (factorial_ne_zero _)
    apply (eq_div_iff (mul_ne_zero hk0 hnk0)).mpr
    have hmul : n.choose k * (k.factorial * (n - k).factorial) = n.factorial := by
      rw [← mul_assoc, this]
    exact_mod_cast hmul
  rw [hch, prod_div_distrib, prod_Icc_succ_div, prod_Icc_shift n k hkn]
  have hk0 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  have hnk0 : ((n - k).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  field_simp [hk0, hnk0]

lemma choose_standard_ratio {A B p : ℕ} (hp : p.Prime) (hBA : B ≤ A) :
    ((A * p).choose (B * p) : ℚ) / (A.choose B : ℚ) =
      ∏ j ∈ pFreeBelow p B, (1 + ((A - B : ℕ) : ℚ) * p / j) := by
  have hppos : 0 < p := hp.pos
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0; simp [pFreeBelow]
  have hle : B * p ≤ A * p := Nat.mul_le_mul_right p hBA
  have hnum := choose_eq_prod_std (n := A * p) (k := B * p) hle
  have hden := choose_eq_prod_std (n := A) (k := B) hBA
  have hdenne : (A.choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos hBA).ne'
  have hC : A * p - B * p = (A - B) * p := (Nat.mul_sub_right_distrib A B p).symm
  have hnum' : ((A * p).choose (B * p) : ℚ) =
      ∏ i ∈ Icc 1 (B * p), ((((A - B) * p : ℕ) : ℚ) + (i : ℚ)) / i := by
    rw [hnum]
    refine prod_congr rfl fun i hi => ?_
    have : ((A * p - B * p + i : ℕ) : ℚ) =
        (((A - B) * p : ℕ) : ℚ) + (i : ℚ) := by
      rw [hC, Nat.cast_add]
    rw [this]
  have hden' : (A.choose B : ℚ) =
      ∏ q ∈ Icc 1 B, (((A - B : ℕ) : ℚ) + (q : ℚ)) / q := by
    rw [hden]
    refine prod_congr rfl fun q hq => ?_
    rw [Nat.cast_add]
  have hdisj : Disjoint ((Icc 1 (B * p)).filter (p ∣ ·)) (pFreeBelow p B) := by
    refine disjoint_left.mpr ?_
    intro a ha hb
    exact (mem_pFreeBelow.mp hb).2 (mem_filter.mp ha).2
  have hunion : Icc 1 (B * p) =
      (Icc 1 (B * p)).filter (p ∣ ·) ∪ pFreeBelow p B := by
    ext j
    simp [pFreeBelow, mem_filter, mem_Icc]
    tauto
  have hsplit :
      ∏ i ∈ Icc 1 (B * p), ((((A - B) * p : ℕ) : ℚ) + (i : ℚ)) / i =
        (∏ i ∈ (Icc 1 (B * p)).filter (p ∣ ·),
          ((((A - B) * p : ℕ) : ℚ) + (i : ℚ)) / i) *
        (∏ j ∈ pFreeBelow p B, ((((A - B) * p : ℕ) : ℚ) + (j : ℚ)) / j) := by
    nth_rw 1 [hunion]
    rw [prod_union hdisj]
  have hdivprod :
      ∏ i ∈ (Icc 1 (B * p)).filter (p ∣ ·),
        ((((A - B) * p : ℕ) : ℚ) + (i : ℚ)) / i =
      ∏ q ∈ Icc 1 B, (((A - B : ℕ) : ℚ) + (q : ℚ)) / q := by
    rw [Icc_filter_dvd_eq_image p B hppos, prod_image]
    · refine prod_congr rfl fun q hq => ?_
      have hq0 : (q : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hq).1)
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hcast : ((((A - B) * p : ℕ) : ℚ) + (q * p : ℕ)) =
          (((A - B : ℕ) : ℚ) + q) * p := by
        rw [Nat.cast_mul, Nat.cast_mul]; ring
      have hqp : ((q * p : ℕ) : ℚ) = (q : ℚ) * p := Nat.cast_mul _ _
      rw [hcast, hqp]
      field_simp [hq0, hp0]
    · intro q _ q' _ heq
      exact Nat.eq_of_mul_eq_mul_right hppos heq
  rw [hnum', hden', hsplit, hdivprod]
  have hQne : ∏ q ∈ Icc 1 B, (((A - B : ℕ) : ℚ) + (q : ℚ)) / q ≠ 0 := by
    rw [← hden']; exact hdenne
  have hfree :
      ∏ j ∈ pFreeBelow p B, ((((A - B) * p : ℕ) : ℚ) + (j : ℚ)) / j =
        ∏ j ∈ pFreeBelow p B, (1 + ((A - B : ℕ) : ℚ) * p / j) := by
    refine prod_congr rfl fun j hj => ?_
    have hj0 : (j : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
    have : ((((A - B) * p : ℕ) : ℚ) + (j : ℚ)) / j =
        1 + (((A - B) * p : ℕ) : ℚ) / j := by
      field_simp [hj0]
      ac_rfl
    rw [this, Nat.cast_mul]
  rw [hfree]
  field_simp [hQne]



/- ## Strong power-sum valuations `σ₁`, `σ₂` -/

lemma isPInt_three_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPInt p ((3 : ℚ)⁻¹) :=
  isPInt_inv_of_not_dvd hp (by norm_num) (by
    intro hd
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    omega)

lemma isPInt_four_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPInt p ((4 : ℚ)⁻¹) :=
  isPInt_inv_of_not_dvd hp (by norm_num) (by
    intro hd
    have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    omega)

lemma not_dvd_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 2 := by
  intro hd
  have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  omega

lemma pFreeBelow_pow_eq {p n : ℕ} (hn : 0 < n) :
    pFreeBelow p (p ^ (n - 1)) = (Icc 1 (p ^ n)).filter (fun j => ¬ p ∣ j) := by
  have : p ^ (n - 1) * p = p ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  simp only [pFreeBelow, this]

lemma mem_pFreeBelow_pow {p n j : ℕ} (hn : 0 < n) :
    j ∈ pFreeBelow p (p ^ (n - 1)) ↔ j ∈ Icc 1 (p ^ n) ∧ ¬ p ∣ j := by
  rw [pFreeBelow_pow_eq hn, mem_filter]

lemma pFreeBelow_pow_lt {p n j : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hj : j ∈ pFreeBelow p (p ^ (n - 1))) : j < p ^ n := by
  have ⟨hjI, hnd⟩ := (mem_pFreeBelow_pow hn).mp hj
  have hjle : j ≤ p ^ n := (mem_Icc.mp hjI).2
  refine lt_of_le_of_ne hjle ?_
  intro h
  exact hnd (by rw [h]; exact dvd_pow_self p hn.ne')

lemma two_mul_mod_mem_pFree {p n j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hj : j ∈ pFreeBelow p (p ^ (n - 1))) :
    (2 * j) % (p ^ n) ∈ pFreeBelow p (p ^ (n - 1)) := by
  have ⟨_, hnd⟩ := (mem_pFreeBelow_pow hn).mp hj
  have h2 := not_dvd_two hp hp5
  have hp2n : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have hmod0 : (2 * j) % (p ^ n) ≠ 0 := by
    intro h0
    have hdiv : p ^ n ∣ 2 * j := Nat.dvd_of_mod_eq_zero h0
    have : p ∣ 2 * j := hp2n.trans hdiv
    exact hnd ((Nat.Prime.dvd_mul hp).mp this |>.resolve_left h2)
  have hnd' : ¬ p ∣ (2 * j) % (p ^ n) := by
    intro hd
    have hdecomp := Nat.div_add_mod (2 * j) (p ^ n)
    have : p ∣ 2 * j := by
      rw [← hdecomp]
      exact dvd_add (dvd_mul_of_dvd_left hp2n _) hd
    exact hnd ((Nat.Prime.dvd_mul hp).mp this |>.resolve_left h2)
  refine (mem_pFreeBelow_pow hn).mpr ⟨?_, hnd'⟩
  exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmod0,
    (Nat.mod_lt _ (pow_pos hp.pos n)).le⟩

lemma two_mul_mod_inj {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    Set.InjOn (fun j : ℕ => (2 * j) % (p ^ n))
      (pFreeBelow p (p ^ (n - 1)) : Set ℕ) := by
  intro j hj j' hj' heq
  have hjlt := pFreeBelow_pow_lt hp hn hj
  have hj'lt := pFreeBelow_pow_lt hp hn hj'
  have h2u : IsUnit ((2 : ℕ) : ZMod (p ^ n)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_or_dvd_of_prime hp 2).resolve_right
      (not_dvd_two hp hp5)).symm.pow_right n
  have hmul : ((2 : ℕ) : ZMod (p ^ n)) * j = ((2 : ℕ) : ZMod (p ^ n)) * j' := by
    have hmod : 2 * j ≡ 2 * j' [MOD p ^ n] := by
      simpa [Nat.ModEq] using heq
    have := (ZMod.natCast_eq_natCast_iff (2 * j) (2 * j') (p ^ n)).mpr hmod
    simpa [Nat.cast_mul] using this
  have hij : (j : ZMod (p ^ n)) = (j' : ZMod (p ^ n)) :=
    h2u.mul_left_cancel hmul
  have hval := congrArg ZMod.val hij
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hjlt,
      Nat.mod_eq_of_lt hj'lt] at hval
  exact hval

lemma two_mul_mod_image {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    (pFreeBelow p (p ^ (n - 1))).image (fun j => (2 * j) % (p ^ n)) =
      pFreeBelow p (p ^ (n - 1)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    exact two_mul_mod_mem_pFree hp hp5 hn hj
  · rw [Finset.card_image_of_injOn (two_mul_mod_inj hp hp5 hn)]

lemma sum_two_mul_mod {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n)
    (f : ℕ → ℚ) :
    ∑ j ∈ pFreeBelow p (p ^ (n - 1)), f ((2 * j) % (p ^ n)) =
      ∑ j ∈ pFreeBelow p (p ^ (n - 1)), f j := by
  rw [← sum_image (two_mul_mod_inj hp hp5 hn), two_mul_mod_image hp hp5 hn]

lemma two_mul_div_le_one {p n j : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hj : j ∈ pFreeBelow p (p ^ (n - 1))) :
    (2 * j) / (p ^ n) ≤ 1 := by
  have hjlt := pFreeBelow_pow_lt hp hn hj
  have hlt : 2 * j < 2 * p ^ n := Nat.mul_lt_mul_of_pos_left hjlt (by norm_num)
  have : (2 * j) / (p ^ n) < 2 := Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hlt)
  exact Nat.lt_succ_iff.mp this

lemma two_mul_mod_eq {p n j : ℕ} :
    (2 * j) % (p ^ n) = 2 * j - (2 * j) / (p ^ n) * (p ^ n) := by
  have h := Nat.div_add_mod (2 * j) (p ^ n)
  -- h : p^n * ((2*j)/(p^n)) + (2*j)%(p^n) = 2*j
  have h' : (2 * j) % (p ^ n) + (2 * j) / (p ^ n) * (p ^ n) = 2 * j := by
    rw [add_comm, Nat.mul_comm]
    exact h
  exact Nat.eq_sub_of_add_eq h'

lemma inv_sq_double_diff (j q m : ℕ) (hj : j ≠ 0)
    (hle : q * m ≤ 2 * j) (hj' : 2 * j - q * m ≠ 0) :
    (1 : ℚ) / ((2 * j - q * m : ℕ) : ℚ) ^ 2 - (1 : ℚ) / ((4 : ℚ) * (j : ℚ) ^ 2) =
      ((q : ℚ) * m) * ((4 : ℚ) * j - (q : ℚ) * m) /
        ((4 : ℚ) * (j : ℚ) ^ 2 * ((2 * j - q * m : ℕ) : ℚ) ^ 2) := by
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj
  have hj'0 : ((2 * j - q * m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj'
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  field_simp [hj0, hj'0, h4]
  have hcast : ((2 * j - q * m : ℕ) : ℚ) = (2 : ℚ) * j - (q : ℚ) * m := by
    rw [Nat.cast_sub hle, Nat.cast_mul]
    push_cast; rfl
  rw [hcast]
  ring

lemma inv_sq_double_diff_pCongr {p n j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hj : j ∈ pFreeBelow p (p ^ (n - 1))) :
    PCongr p n
      ((1 : ℚ) / (((2 * j) % (p ^ n) : ℕ) : ℚ) ^ 2 -
        (1 : ℚ) / ((4 : ℚ) * (j : ℚ) ^ 2)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set q := (2 * j) / (p ^ n)
  set m := p ^ n
  have hj0 : j ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1
  have hmod : (2 * j) % m = 2 * j - q * m := by
    simpa [q, m, Nat.mul_comm q] using two_mul_mod_eq (p := p) (n := n) (j := j)
  have hle : q * m ≤ 2 * j := by
    simpa [q, m, mul_comm] using Nat.mul_div_le (2 * j) (p ^ n)
  have hj'sub : 2 * j - q * m ≠ 0 := by
    have hmem := two_mul_mod_mem_pFree hp hp5 hn hj
    have : (2 * j) % m ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hmem).1).1
    rwa [hmod] at this
  rw [hmod, inv_sq_double_diff j q m hj0 hle hj'sub]
  have hj0' : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
  have hj'0 : ((2 * j - q * m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj'sub
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hform :
      ((q : ℚ) * m) * ((4 : ℚ) * j - (q : ℚ) * m) /
        ((4 : ℚ) * (j : ℚ) ^ 2 * ((2 * j - q * m : ℕ) : ℚ) ^ 2) =
      (p : ℚ) ^ n *
        ((q : ℚ) * ((4 : ℚ) * j - (q : ℚ) * m) /
          ((4 : ℚ) * (j : ℚ) ^ 2 * ((2 * j - q * m : ℕ) : ℚ) ^ 2)) := by
    simp only [m]
    push_cast
    field_simp [hj0', hj'0, h4, hp0]
  rw [hform]
  have hrest : IsPInt p
      ((q : ℚ) * ((4 : ℚ) * j - (q : ℚ) * m) /
        ((4 : ℚ) * (j : ℚ) ^ 2 * ((2 * j - q * m : ℕ) : ℚ) ^ 2)) := by
    have heq :
        ((q : ℚ) * ((4 : ℚ) * j - (q : ℚ) * m) /
          ((4 : ℚ) * (j : ℚ) ^ 2 * ((2 * j - q * m : ℕ) : ℚ) ^ 2)) =
        (q : ℚ) * ((4 : ℚ) * j - (q : ℚ) * m) *
          ((4 : ℚ)⁻¹ * ((j : ℚ)⁻¹) ^ 2 * (((2 * j - q * m : ℕ) : ℚ)⁻¹) ^ 2) := by
      field_simp [hj0', hj'0, h4]
    rw [heq]
    have hjI := isPInt_inv_pFree hp hj
    have hj'I : IsPInt p (((2 * j - q * m : ℕ) : ℚ)⁻¹) := by
      have hmem := two_mul_mod_mem_pFree hp hp5 hn hj
      have : (2 * j - q * m : ℕ) = (2 * j) % (p ^ n) := by
        simpa [m] using hmod.symm
      rw [this]
      exact isPInt_inv_pFree hp hmem
    have hlin : IsPInt p ((4 : ℚ) * j - (q : ℚ) * m) :=
      isPInt_sub (isPInt_mul (isPInt_nat p 4) (isPInt_nat p j))
        (isPInt_mul (isPInt_nat p q) (isPInt_nat p m))
    exact isPInt_mul (isPInt_mul (isPInt_nat p q) hlin)
      (isPInt_mul (isPInt_mul (isPInt_four_inv hp hp5) (isPInt_pow hjI 2))
        (isPInt_pow hj'I 2))
  exact pCongr_mul_isPInt (pCongr_p_pow n) hrest

/-- `σ₂` at a pure power `B = p^{n-1}` has valuation at least `n`. -/
lemma sum_inv_sq_pFree_pow {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    PCongr p n
      (∑ j ∈ pFreeBelow p (p ^ (n - 1)), (1 : ℚ) / (j : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := pFreeBelow p (p ^ (n - 1))
  set σ : ℚ := ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2
  have hperm : ∑ j ∈ s, (1 : ℚ) / (((2 * j) % (p ^ n) : ℕ) : ℚ) ^ 2 = σ :=
    sum_two_mul_mod hp hp5 hn (fun j => (1 : ℚ) / (j : ℚ) ^ 2)
  have hdiff : PCongr p n
      (∑ j ∈ s, ((1 : ℚ) / (((2 * j) % (p ^ n) : ℕ) : ℚ) ^ 2 -
        (1 : ℚ) / ((4 : ℚ) * (j : ℚ) ^ 2))) 0 :=
    pCongr_sum_zero fun j hj => inv_sq_double_diff_pCongr hp hp5 hn hj
  have hsum :
      ∑ j ∈ s, ((1 : ℚ) / (((2 * j) % (p ^ n) : ℕ) : ℚ) ^ 2 -
        (1 : ℚ) / ((4 : ℚ) * (j : ℚ) ^ 2)) =
      σ - (1 / 4 : ℚ) * σ := by
    have h1 : ∑ j ∈ s, (1 : ℚ) / (((2 * j) % (p ^ n) : ℕ) : ℚ) ^ 2 = σ := hperm
    have h2 : ∑ j ∈ s, (1 : ℚ) / ((4 : ℚ) * (j : ℚ) ^ 2) = (1 / 4 : ℚ) * σ := by
      have : ∑ j ∈ s, (1 : ℚ) / ((4 : ℚ) * (j : ℚ) ^ 2) =
          ∑ j ∈ s, (1 / 4 : ℚ) * ((1 : ℚ) / (j : ℚ) ^ 2) := by
        refine sum_congr rfl fun j hj => ?_
        have hj0 : (j : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr
            (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
        field_simp [hj0]
      rw [this, ← mul_sum]
    rw [sum_sub_distrib, h1, h2]
  rw [hsum] at hdiff
  have heq : σ - (1 / 4 : ℚ) * σ = (3 / 4 : ℚ) * σ := by ring
  rw [heq] at hdiff
  -- σ = (4/3) * ((3/4) σ)
  have h34 : (3 / 4 : ℚ) * σ = (3 / 4 : ℚ) * σ := rfl
  have h43 : IsPInt p ((4 : ℚ) / 3) :=
    isPInt_mul (isPInt_nat p 4) (isPInt_three_inv hp hp5)
  have : σ = ((3 / 4 : ℚ) * σ) * ((4 : ℚ) / 3) := by ring
  rw [this]
  exact pCongr_mul_isPInt hdiff h43

lemma pFreeBelow_pow_sub_mem {p n j : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hj : j ∈ pFreeBelow p (p ^ (n - 1))) :
    p ^ n - j ∈ pFreeBelow p (p ^ (n - 1)) := by
  have ⟨hjI, hnd⟩ := (mem_pFreeBelow_pow hn).mp hj
  have hj1 : 1 ≤ j := (mem_Icc.mp hjI).1
  have hjlt := pFreeBelow_pow_lt hp hn hj
  have hle : j ≤ p ^ n := hjlt.le
  have hpos : 1 ≤ p ^ n - j := by
    have : j ≤ p ^ n - 1 := Nat.le_pred_of_lt hjlt
    omega
  have hle' : p ^ n - j ≤ p ^ n := Nat.sub_le _ _
  have hnd' : ¬ p ∣ (p ^ n - j) := by
    intro hd
    have hpown : p ∣ p ^ n := dvd_pow_self p hn.ne'
    have hsub : p ∣ (p ^ n - (p ^ n - j)) := Nat.dvd_sub hpown hd
    have : p ^ n - (p ^ n - j) = j := Nat.sub_sub_self hle
    exact hnd (this ▸ hsub)
  exact (mem_pFreeBelow_pow hn).mpr ⟨mem_Icc.mpr ⟨hpos, hle'⟩, hnd'⟩

lemma inv_pair_identity {p n j : ℕ} (hj : 0 < j) (hjlt : j < p ^ n) :
    (1 : ℚ) / j + (1 : ℚ) / (p ^ n - j : ℕ) =
      (p : ℚ) ^ n / ((j : ℚ) * (p ^ n - j : ℕ)) := by
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hj'0 : ((p ^ n - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_iff_lt.mpr hjlt)
  have hcast : ((p ^ n - j : ℕ) : ℚ) = (p : ℚ) ^ n - j := by
    rw [Nat.cast_sub hjlt.le, Nat.cast_pow]
  field_simp [hj0, hj'0]
  rw [hcast]
  ring

lemma inv_pair_sq_identity {j m : ℕ} (hj : j ≠ 0) (hj' : m - j ≠ 0)
    (hle : j ≤ m) :
    (1 : ℚ) / ((j : ℚ) * (m - j : ℕ)) =
      - (1 : ℚ) / (j : ℚ) ^ 2 + (m : ℚ) / ((j : ℚ) ^ 2 * (m - j : ℕ)) := by
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj
  have hj'0 : ((m - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj'
  have hcast : ((m - j : ℕ) : ℚ) = (m : ℚ) - j := Nat.cast_sub hle
  field_simp [hj0, hj'0]
  rw [hcast]
  ring

/-- `σ₁` at a pure power `B = p^{n-1}` has valuation at least `2n`. -/
lemma sum_inv_pFree_pow {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    PCongr p (2 * n)
      (∑ j ∈ pFreeBelow p (p ^ (n - 1)), (1 : ℚ) / j) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := pFreeBelow p (p ^ (n - 1))
  set σ1 : ℚ := ∑ j ∈ s, (1 : ℚ) / j
  set σ2 : ℚ := ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2
  have hpair : σ1 = (1 / 2 : ℚ) *
      ∑ j ∈ s, ((1 : ℚ) / j + (1 : ℚ) / (p ^ n - j : ℕ)) := by
    have h2 : ∑ j ∈ s, ((1 : ℚ) / j + (1 : ℚ) / (p ^ n - j : ℕ)) =
        σ1 + ∑ j ∈ s, (1 : ℚ) / (p ^ n - j : ℕ) := sum_add_distrib
    have hperm : ∑ j ∈ s, (1 : ℚ) / (p ^ n - j : ℕ) = σ1 := by
      have hinj : Set.InjOn (fun j : ℕ => p ^ n - j) (s : Set ℕ) := by
        intro a ha b hb heq
        have halt := pFreeBelow_pow_lt hp hn ha
        have hblt := pFreeBelow_pow_lt hp hn hb
        change p ^ n - a = p ^ n - b at heq
        have ha' : a = p ^ n - (p ^ n - a) := (Nat.sub_sub_self halt.le).symm
        have hb' : b = p ^ n - (p ^ n - b) := (Nat.sub_sub_self hblt.le).symm
        rwa [heq, ← hb'] at ha'
      have himg : s.image (fun j => p ^ n - j) = s := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
          exact pFreeBelow_pow_sub_mem hp hn hj
        · rw [Finset.card_image_of_injOn hinj]
      have : ∑ j ∈ s, (1 : ℚ) / (p ^ n - j : ℕ) =
          ∑ j ∈ s.image (fun j => p ^ n - j), (1 : ℚ) / j := by
        rw [sum_image hinj]
      rw [this, himg]
    rw [h2, hperm]
    ring
  have hid : ∀ j ∈ s,
      (1 : ℚ) / j + (1 : ℚ) / (p ^ n - j : ℕ) =
        (p : ℚ) ^ n / ((j : ℚ) * (p ^ n - j : ℕ)) := by
    intro j hj
    have hj1 : 0 < j := (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1
    exact inv_pair_identity hj1 (pFreeBelow_pow_lt hp hn hj)
  rw [hpair, sum_congr rfl hid]
  have hsplit : ∀ j ∈ s,
      (p : ℚ) ^ n / ((j : ℚ) * (p ^ n - j : ℕ)) =
        (p : ℚ) ^ n * (- (1 : ℚ) / (j : ℚ) ^ 2) +
          (p : ℚ) ^ n * ((p : ℚ) ^ n / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) := by
    intro j hj
    have hj0 : j ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1
    have hjlt := pFreeBelow_pow_lt hp hn hj
    have hj' : p ^ n - j ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hjlt
    have hle : j ≤ p ^ n := hjlt.le
    have h := inv_pair_sq_identity (m := p ^ n) hj0 hj' hle
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hj0' : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
    have hj'0 : ((p ^ n - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj'
    calc
      (p : ℚ) ^ n / ((j : ℚ) * (p ^ n - j : ℕ))
          = (p : ℚ) ^ n * ((1 : ℚ) / ((j : ℚ) * (p ^ n - j : ℕ))) := by
            field_simp [hp0, hj0', hj'0]
      _ = (p : ℚ) ^ n * (- (1 : ℚ) / (j : ℚ) ^ 2 +
            (p : ℚ) ^ n / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) := by
            rw [h]; simp [Nat.cast_pow]
      _ = (p : ℚ) ^ n * (- (1 : ℚ) / (j : ℚ) ^ 2) +
            (p : ℚ) ^ n * ((p : ℚ) ^ n / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) := by
            ring
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have h1 : ∑ j ∈ s, (p : ℚ) ^ n * (- (1 : ℚ) / (j : ℚ) ^ 2) =
      (p : ℚ) ^ n * (-σ2) := by
    have : ∑ j ∈ s, (p : ℚ) ^ n * (- (1 : ℚ) / (j : ℚ) ^ 2) =
        (p : ℚ) ^ n * ∑ j ∈ s, (- (1 : ℚ) / (j : ℚ) ^ 2) := (mul_sum _ _ _).symm
    rw [this]
    congr 1
    simp only [neg_div, ← sum_neg_distrib, σ2]
  have h2 : ∑ j ∈ s,
      (p : ℚ) ^ n * ((p : ℚ) ^ n / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) =
      (p : ℚ) ^ (2 * n) *
        ∑ j ∈ s, (1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ)) := by
    have : ∑ j ∈ s,
        (p : ℚ) ^ n * ((p : ℚ) ^ n / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) =
        (p : ℚ) ^ n * (p : ℚ) ^ n *
          ∑ j ∈ s, (1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ)) := by
      have hinner : ∀ j ∈ s,
          (p : ℚ) ^ n * ((p : ℚ) ^ n / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) =
          (p : ℚ) ^ n * (p : ℚ) ^ n *
            ((1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) := by
        intro j hj
        ring
      rw [sum_congr rfl hinner, ← mul_sum]
    rw [this, ← pow_add]
    congr 2
    ring
  rw [h1, h2]
  have hσ2 := sum_inv_sq_pFree_pow hp hp5 hn
  have hp2n : PCongr p (2 * n) ((p : ℚ) ^ n * (-σ2)) 0 := by
    have hp1 : PCongr p n ((p : ℚ) ^ n) 0 := pCongr_p_pow n
    have hneg : PCongr p n (-σ2) 0 := pCongr_neg hσ2
    simpa [two_mul] using pCongr_mul_zero hp1 hneg
  have hrem : PCongr p (2 * n)
      ((p : ℚ) ^ (2 * n) *
        ∑ j ∈ s, (1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) 0 := by
    have hpN : PCongr p (2 * n) ((p : ℚ) ^ (2 * n)) 0 := pCongr_p_pow (2 * n)
    have hI : IsPInt p (∑ j ∈ s, (1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) := by
      refine isPInt_sum ?_
      intro j hj
      have hjI := isPInt_inv_pFree hp hj
      have hj'I : IsPInt p (((p ^ n - j : ℕ) : ℚ)⁻¹) :=
        isPInt_inv_pFree hp (pFreeBelow_pow_sub_mem hp hn hj)
      have heq : (1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ)) =
          ((j : ℚ)⁻¹) ^ 2 * (((p ^ n - j : ℕ) : ℚ)⁻¹) := by
        have hj0 : (j : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr
            (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
        have hj'0 : ((p ^ n - j : ℕ) : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_iff_lt.mpr (pFreeBelow_pow_lt hp hn hj))
        field_simp [hj0, hj'0]
      rw [heq]
      exact isPInt_mul (isPInt_pow hjI 2) hj'I
    exact pCongr_mul_isPInt hpN hI
  have hsum := pCongr_add hp2n hrem
  have hsum0 : PCongr p (2 * n)
      ((p : ℚ) ^ n * (-σ2) +
        (p : ℚ) ^ (2 * n) *
          ∑ j ∈ s, (1 : ℚ) / ((j : ℚ) ^ 2 * (p ^ n - j : ℕ))) 0 := by
    simpa using hsum
  have hhalf := pCongr_div_two hp hp5 hsum0
  convert hhalf using 1
  ring

/- ## Strong `σ` for general `B` -/

lemma pFreeBelow_scale_mem {p m e α u : ℕ} (hp : p.Prime) (he : 0 < e ∨ 0 < m)
    (hα : α < m) (hu : u ∈ pFreeBelow p (p ^ e)) :
    u + α * p ^ (e + 1) ∈ pFreeBelow p (m * p ^ e) := by
  have ⟨huI, hnd⟩ := mem_pFreeBelow.mp hu
  have hu1 : 1 ≤ u := (mem_Icc.mp huI).1
  have hule : u ≤ p ^ e * p := (mem_Icc.mp huI).2
  have hule' : u ≤ p ^ (e + 1) := by
    simpa [pow_succ] using hule
  have hnd' : ¬ p ∣ (u + α * p ^ (e + 1)) := by
    intro hd
    have hpow : p ∣ α * p ^ (e + 1) :=
      dvd_mul_of_dvd_right (dvd_pow_self p (Nat.succ_ne_zero e)) _
    exact hnd ((Nat.dvd_add_iff_left hpow).mpr hd)
  have hpos : 1 ≤ u + α * p ^ (e + 1) := Nat.add_pos_left hu1 _
  have hle : u + α * p ^ (e + 1) ≤ m * p ^ e * p := by
    have : u + α * p ^ (e + 1) ≤ p ^ (e + 1) + α * p ^ (e + 1) :=
      Nat.add_le_add_right hule' _
    have : p ^ (e + 1) + α * p ^ (e + 1) = (α + 1) * p ^ (e + 1) := by ring
    have hα1 : α + 1 ≤ m := Nat.succ_le_of_lt hα
    have : (α + 1) * p ^ (e + 1) ≤ m * p ^ (e + 1) :=
      Nat.mul_le_mul_right _ hα1
    have hlast : m * p ^ e * p = m * p ^ (e + 1) := by
      rw [pow_succ, mul_assoc]
    omega
  exact mem_pFreeBelow.mpr ⟨mem_Icc.mpr ⟨hpos, hle⟩, hnd'⟩

lemma pFreeBelow_scale_eq {p m e : ℕ} (hp : p.Prime) :
    pFreeBelow p (m * p ^ e) =
      (range m).biUnion fun α =>
        (pFreeBelow p (p ^ e)).image (fun u => u + α * p ^ (e + 1)) := by
  ext x
  constructor
  · intro hx
    have ⟨hxI, hnd⟩ := mem_pFreeBelow.mp hx
    have hx1 : 1 ≤ x := (mem_Icc.mp hxI).1
    have hx2 : x ≤ m * p ^ e * p := (mem_Icc.mp hxI).2
    have hx2' : x ≤ m * p ^ (e + 1) := by
      convert hx2 using 1; rw [pow_succ, mul_assoc]
    have hlt : x < m * p ^ (e + 1) :=
      lt_of_le_of_ne hx2' (fun h => hnd (by
        rw [h]; exact dvd_mul_of_dvd_right (dvd_pow_self p (Nat.succ_ne_zero e)) _))
    have hα : x / p ^ (e + 1) < m :=
      Nat.div_lt_of_lt_mul (by convert hlt using 1; ring)
    have hmod0 : x % p ^ (e + 1) ≠ 0 := by
      intro h0
      exact hnd ((dvd_pow_self p (Nat.succ_ne_zero e)).trans (Nat.dvd_of_mod_eq_zero h0))
    refine mem_biUnion.mpr ⟨x / p ^ (e + 1), mem_range.mpr hα, ?_⟩
    refine mem_image.mpr ⟨x % p ^ (e + 1), ?_, ?_⟩
    · have hmodlt : x % p ^ (e + 1) < p ^ (e + 1) :=
        Nat.mod_lt _ (pow_pos hp.pos _)
      have hndj : ¬ p ∣ x % p ^ (e + 1) := by
        intro hd
        have hdecomp := Nat.div_add_mod x (p ^ (e + 1))
        have hpown : p ∣ p ^ (e + 1) := dvd_pow_self p (Nat.succ_ne_zero e)
        have : p ∣ x := by
          rw [← hdecomp]
          exact dvd_add (dvd_mul_of_dvd_left hpown _) hd
        exact hnd this
      have hmodle : x % p ^ (e + 1) ≤ p ^ e * p := by
        have : x % p ^ (e + 1) ≤ p ^ (e + 1) - 1 := Nat.le_pred_of_lt hmodlt
        have : p ^ (e + 1) - 1 ≤ p ^ e * p := by
          rw [pow_succ]; exact Nat.sub_le _ _
        exact le_trans (Nat.le_pred_of_lt hmodlt) this
      exact mem_pFreeBelow.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmod0, hmodle⟩, hndj⟩
    · have := Nat.div_add_mod x (p ^ (e + 1))
      linarith
  · intro hx
    obtain ⟨α, hα, hx'⟩ := mem_biUnion.mp hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx'
    exact pFreeBelow_scale_mem hp (Or.inr (Nat.zero_lt_of_lt (mem_range.mp hα)))
      (mem_range.mp hα) hu

lemma pairwiseDisjoint_pFree_scale_pow {p m e : ℕ} (hp : p.Prime) :
    Set.PairwiseDisjoint (range m : Set ℕ)
      (fun α => (pFreeBelow p (p ^ e)).image (fun u => u + α * p ^ (e + 1))) := by
  intro α _ α' _ hne
  refine disjoint_left.mpr ?_
  intro x hx hx'
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
  obtain ⟨u', hu', heq⟩ := mem_image.mp hx'
  have hult : u < p ^ (e + 1) := by
    have hle : u ≤ p ^ e * p := (mem_Icc.mp (mem_pFreeBelow.mp hu).1).2
    have hle' : u ≤ p ^ (e + 1) := by simpa [pow_succ] using hle
    refine lt_of_le_of_ne hle' ?_
    intro h
    exact (mem_pFreeBelow.mp hu).2 (by rw [h]; exact dvd_pow_self p (Nat.succ_ne_zero e))
  have hu'lt : u' < p ^ (e + 1) := by
    have hle : u' ≤ p ^ e * p := (mem_Icc.mp (mem_pFreeBelow.mp hu').1).2
    have hle' : u' ≤ p ^ (e + 1) := by simpa [pow_succ] using hle
    refine lt_of_le_of_ne hle' ?_
    intro h
    exact (mem_pFreeBelow.mp hu').2 (by rw [h]; exact dvd_pow_self p (Nat.succ_ne_zero e))
  have hαeq : α = α' := by
    have hα : α = (u + α * p ^ (e + 1)) / p ^ (e + 1) := by
      rw [Nat.add_mul_div_right u α (pow_pos hp.pos (e + 1)),
          Nat.div_eq_of_lt hult, zero_add]
    have hα' : α' = (u' + α' * p ^ (e + 1)) / p ^ (e + 1) := by
      rw [Nat.add_mul_div_right u' α' (pow_pos hp.pos (e + 1)),
          Nat.div_eq_of_lt hu'lt, zero_add]
    rw [hα, hα', heq]
  exact hne hαeq

lemma sum_pFreeBelow_scale_pow {p m e : ℕ} (hp : p.Prime) (f : ℕ → ℚ) :
    ∑ j ∈ pFreeBelow p (m * p ^ e), f j =
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), f (u + α * p ^ (e + 1)) := by
  rw [pFreeBelow_scale_eq hp,
      sum_biUnion (pairwiseDisjoint_pFree_scale_pow hp)]
  refine sum_congr rfl fun α _ =>
    sum_image fun a _ b _ h => Nat.add_right_cancel h

lemma inv_shift_diff (α u n : ℕ) (hu : u ≠ 0) :
    (1 : ℚ) / (u + α * n : ℕ) - (1 : ℚ) / u =
      - ((α : ℚ) * n) / ((u : ℚ) * (u + α * n : ℕ)) := by
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu
  have hsum0 : ((u + α * n : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_left (Nat.pos_of_ne_zero hu) _).ne'
  have hcast : ((u + α * n : ℕ) : ℚ) = (u : ℚ) + (α : ℚ) * n := by push_cast; rfl
  field_simp [hu0, hsum0]
  rw [hcast]
  ring

lemma inv_shift_two_term (α u n : ℕ) (hu : u ≠ 0) :
    (1 : ℚ) / (u + α * n : ℕ) =
      (1 : ℚ) / u - ((α : ℚ) * n) / (u : ℚ) ^ 2 +
        ((α : ℚ) * n) ^ 2 / ((u : ℚ) ^ 2 * (u + α * n : ℕ)) := by
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu
  have hsum0 : ((u + α * n : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_left (Nat.pos_of_ne_zero hu) _).ne'
  have hcast : ((u + α * n : ℕ) : ℚ) = (u : ℚ) + (α : ℚ) * n := by push_cast; rfl
  field_simp [hu0, hsum0]
  rw [hcast]
  ring

lemma inv_sq_shift_diff (α u n : ℕ) (hu : u ≠ 0) :
    (1 : ℚ) / (u + α * n : ℕ) ^ 2 - (1 : ℚ) / (u : ℚ) ^ 2 =
      - ((α : ℚ) * n) * ((2 : ℚ) * u + (α : ℚ) * n) /
        ((u : ℚ) ^ 2 * (u + α * n : ℕ) ^ 2) := by
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu
  have hsum0 : ((u + α * n : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_left (Nat.pos_of_ne_zero hu) _).ne'
  have hcast : ((u + α * n : ℕ) : ℚ) = (u : ℚ) + (α : ℚ) * n := by push_cast; rfl
  field_simp [hu0, hsum0]
  rw [hcast]
  ring

/-- Strong `σ₂`: valuation at least `1 + v_p(B)`. -/
lemma sum_inv_sq_pFree_strong {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p (1 + padicValNat p B)
      (∑ j ∈ pFreeBelow p B, (1 : ℚ) / (j : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne B 0 with hB0 | hB0
  · subst hB0; simp [pFreeBelow, pCongr_refl]
  set e := padicValNat p B
  set m := B / p ^ e
  have hB : B = m * p ^ e := by
    have := pow_padicValNat_dvd (p := p) (n := B)
    exact (Nat.mul_div_cancel' this).symm |>.trans (mul_comm _ _)
  have hmpos : 0 < m :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) pow_padicValNat_dvd)
      (pow_pos hp.pos _)
  have hn : 0 < e + 1 := Nat.succ_pos _
  rw [hB, sum_pFreeBelow_scale_pow hp]
  have hdecomp :
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        (1 : ℚ) / ((u + α * p ^ (e + 1) : ℕ) : ℚ) ^ 2 =
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2 +
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((1 : ℚ) / ((u + α * p ^ (e + 1) : ℕ) : ℚ) ^ 2 -
          (1 : ℚ) / (u : ℚ) ^ 2) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun α _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    ring
  rw [hdecomp]
  have hmain : PCongr p (1 + e)
      (∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2) 0 := by
    have : ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2 =
        (m : ℚ) * ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2 := by
      rw [sum_const, card_range, nsmul_eq_mul]
    rw [this]
    have hσ : PCongr p (e + 1)
        (∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2) 0 := by
      convert sum_inv_sq_pFree_pow hp hp5 (n := e + 1) hn using 3
    have hmI : IsPInt p (m : ℚ) := isPInt_nat p m
    have : (1 + e : ℤ) = e + 1 := by ring
    rw [this]
    simpa [mul_comm] using pCongr_mul_isPInt hσ hmI
  have hrem : PCongr p (1 + e)
      (∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((1 : ℚ) / ((u + α * p ^ (e + 1) : ℕ) : ℚ) ^ 2 -
          (1 : ℚ) / (u : ℚ) ^ 2)) 0 := by
    refine pCongr_sum_zero ?_
    intro α hα
    refine pCongr_sum_zero ?_
    intro u hu
    have hu0 : u ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hu).1).1
    rw [inv_sq_shift_diff α u (p ^ (e + 1)) hu0]
    have huI := isPInt_inv_pFree hp hu
    have hsumI : IsPInt p (((u + α * p ^ (e + 1) : ℕ) : ℚ)⁻¹) :=
      isPInt_inv_pFree hp (pFreeBelow_scale_mem hp (Or.inr hmpos) (mem_range.mp hα) hu)
    have hform :
        - ((α : ℚ) * (p ^ (e + 1) : ℕ)) * ((2 : ℚ) * u + (α : ℚ) * (p ^ (e + 1) : ℕ)) /
          ((u : ℚ) ^ 2 * (u + α * p ^ (e + 1) : ℕ) ^ 2) =
        (p : ℚ) ^ (e + 1) *
          (- (α : ℚ) * ((2 : ℚ) * u + (α : ℚ) * (p ^ (e + 1) : ℕ)) *
            ((u : ℚ)⁻¹) ^ 2 * (((u + α * p ^ (e + 1) : ℕ) : ℚ)⁻¹) ^ 2) := by
      have hu0' : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu0
      have hs0 : ((u + α * p ^ (e + 1) : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.add_pos_left (Nat.pos_of_ne_zero hu0) _).ne'
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      push_cast
      field_simp [hu0', hs0, hp0]
    rw [hform]
    have hrest : IsPInt p
        (- (α : ℚ) * ((2 : ℚ) * u + (α : ℚ) * (p ^ (e + 1) : ℕ)) *
          ((u : ℚ)⁻¹) ^ 2 * (((u + α * p ^ (e + 1) : ℕ) : ℚ)⁻¹) ^ 2) :=
      isPInt_mul (isPInt_mul (isPInt_mul
        (isPInt_neg (isPInt_nat p α))
        (isPInt_add (isPInt_mul (isPInt_nat p 2) (isPInt_nat p u))
          (isPInt_mul (isPInt_nat p α) (isPInt_nat p _))))
        (isPInt_pow huI 2)) (isPInt_pow hsumI 2)
    have : (1 + e : ℤ) = e + 1 := by ring
    rw [this]
    exact pCongr_mul_isPInt (pCongr_p_pow (e + 1)) hrest
  simpa using pCongr_add hmain hrem

/-- Strong `σ₁`: valuation at least `2 + 2 v_p(B)`. -/
lemma sum_inv_pFree_strong {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    PCongr p (2 + 2 * padicValNat p B)
      (∑ j ∈ pFreeBelow p B, (1 : ℚ) / j) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne B 0 with hB0 | hB0
  · subst hB0; simp [pFreeBelow, pCongr_refl]
  set e := padicValNat p B
  set m := B / p ^ e
  have hB : B = m * p ^ e := by
    have := pow_padicValNat_dvd (p := p) (n := B)
    exact (Nat.mul_div_cancel' this).symm |>.trans (mul_comm _ _)
  have hmpos : 0 < m :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) pow_padicValNat_dvd)
      (pow_pos hp.pos _)
  have hn : 0 < e + 1 := Nat.succ_pos _
  rw [hB, sum_pFreeBelow_scale_pow hp]
  have hdecomp :
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        (1 : ℚ) / (u + α * p ^ (e + 1) : ℕ) =
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / u -
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2 +
      ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((α : ℚ) * (p ^ (e + 1) : ℕ)) ^ 2 /
          ((u : ℚ) ^ 2 * (u + α * p ^ (e + 1) : ℕ)) := by
    have hinner : ∀ α ∈ range m,
        ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u + α * p ^ (e + 1) : ℕ) =
        ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / u -
        ∑ u ∈ pFreeBelow p (p ^ e), ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2 +
        ∑ u ∈ pFreeBelow p (p ^ e),
          ((α : ℚ) * (p ^ (e + 1) : ℕ)) ^ 2 /
            ((u : ℚ) ^ 2 * (u + α * p ^ (e + 1) : ℕ)) := by
      intro α _
      have ht : ∀ u ∈ pFreeBelow p (p ^ e),
          (1 : ℚ) / (u + α * p ^ (e + 1) : ℕ) =
            (1 : ℚ) / u - ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2 +
              ((α : ℚ) * (p ^ (e + 1) : ℕ)) ^ 2 /
                ((u : ℚ) ^ 2 * (u + α * p ^ (e + 1) : ℕ)) := by
        intro u hu
        have hu0 : u ≠ 0 :=
          Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hu).1).1
        exact inv_shift_two_term α u (p ^ (e + 1)) hu0
      rw [sum_congr rfl ht, sum_add_distrib, sum_sub_distrib]
    rw [sum_congr rfl hinner, sum_add_distrib, sum_sub_distrib]
  rw [hdecomp]
  have h0 : PCongr p (2 + 2 * e)
      (∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / u) 0 := by
    have : ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / u =
        (m : ℚ) * ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / u := by
      rw [sum_const, card_range, nsmul_eq_mul]
    rw [this]
    have hσ : PCongr p (2 * (e + 1))
        (∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / u) 0 := by
      have h := sum_inv_pFree_pow hp hp5 (n := e + 1) hn
      have heq : p ^ ((e + 1) - 1) = p ^ e := by simp
      simpa [heq] using h
    have : (2 + 2 * e : ℤ) = 2 * (e + 1) := by push_cast; ring
    rw [this]
    simpa [mul_comm] using pCongr_mul_isPInt hσ (isPInt_nat p m)
  have h1 : PCongr p (2 + 2 * e)
      (∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2) 0 := by
    have : ∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2 =
        (∑ α ∈ range m, (α : ℚ)) * (p : ℚ) ^ (e + 1) *
          ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2 := by
      have hα : ∀ α ∈ range m,
          ∑ u ∈ pFreeBelow p (p ^ e),
            ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2 =
          ((α : ℚ) * (p ^ (e + 1) : ℕ)) *
            ∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2 := by
        intro α _
        have : ∀ u ∈ pFreeBelow p (p ^ e),
            ((α : ℚ) * (p ^ (e + 1) : ℕ)) / (u : ℚ) ^ 2 =
            ((α : ℚ) * (p ^ (e + 1) : ℕ)) * ((1 : ℚ) / (u : ℚ) ^ 2) := by
          intro u hu
          have hu0 : (u : ℚ) ≠ 0 :=
            Nat.cast_ne_zero.mpr
              (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hu).1).1)
          field_simp [hu0]
        rw [sum_congr rfl this, ← mul_sum]
      rw [sum_congr rfl hα, ← sum_mul]
      have hfact : ∑ α ∈ range m, (α : ℚ) * (p ^ (e + 1) : ℕ) =
          (∑ α ∈ range m, (α : ℚ)) * (p ^ (e + 1) : ℕ) :=
        (sum_mul _ _ _).symm
      rw [hfact, Nat.cast_pow]
    rw [this]
    have hpN : PCongr p (e + 1) ((p : ℚ) ^ (e + 1)) 0 := pCongr_p_pow (e + 1)
    have hσ : PCongr p (e + 1)
        (∑ u ∈ pFreeBelow p (p ^ e), (1 : ℚ) / (u : ℚ) ^ 2) 0 := by
      have h := sum_inv_sq_pFree_pow hp hp5 (n := e + 1) hn
      have heq : p ^ ((e + 1) - 1) = p ^ e := by simp
      simpa [heq] using h
    have hαI : IsPInt p (∑ α ∈ range m, (α : ℚ)) := isPInt_sum (fun _ _ => isPInt_nat p _)
    have hmul := pCongr_mul_zero hpN hσ
    have : (2 + 2 * e : ℤ) ≤ (e + 1) + (e + 1) := by omega
    have hmul' := pCongr_mul_isPInt hmul hαI
    simpa [mul_comm, mul_left_comm, mul_assoc] using pCongr_of_le this hmul'
  have h2 : PCongr p (2 + 2 * e)
      (∑ α ∈ range m, ∑ u ∈ pFreeBelow p (p ^ e),
        ((α : ℚ) * (p ^ (e + 1) : ℕ)) ^ 2 /
          ((u : ℚ) ^ 2 * (u + α * p ^ (e + 1) : ℕ))) 0 := by
    refine pCongr_sum_zero ?_
    intro α hα
    refine pCongr_sum_zero ?_
    intro u hu
    have hu0 : u ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hu).1).1
    have huI := isPInt_inv_pFree hp hu
    have hsumI : IsPInt p (((u + α * p ^ (e + 1) : ℕ) : ℚ)⁻¹) :=
      isPInt_inv_pFree hp (pFreeBelow_scale_mem hp (Or.inr hmpos) (mem_range.mp hα) hu)
    have hform :
        ((α : ℚ) * (p ^ (e + 1) : ℕ)) ^ 2 /
          ((u : ℚ) ^ 2 * (u + α * p ^ (e + 1) : ℕ)) =
        (p : ℚ) ^ (2 * (e + 1)) *
          ((α : ℚ) ^ 2 * ((u : ℚ)⁻¹) ^ 2 * (((u + α * p ^ (e + 1) : ℕ) : ℚ)⁻¹)) := by
      have hu0' : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu0
      have hs0 : ((u + α * p ^ (e + 1) : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.add_pos_left (Nat.pos_of_ne_zero hu0) _).ne'
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      push_cast
      field_simp [hu0', hs0, hp0]
      ring
    rw [hform]
    have hrest : IsPInt p
        ((α : ℚ) ^ 2 * ((u : ℚ)⁻¹) ^ 2 * (((u + α * p ^ (e + 1) : ℕ) : ℚ)⁻¹)) :=
      isPInt_mul (isPInt_mul (isPInt_pow (isPInt_nat p α) 2) (isPInt_pow huI 2)) hsumI
    have : (2 + 2 * e : ℤ) ≤ 2 * (e + 1) := by omega
    exact pCongr_of_le this (pCongr_mul_isPInt (pCongr_p_pow (2 * (e + 1))) hrest)
  have h01 := pCongr_sub h0 h1
  simpa [sub_eq_add_neg] using pCongr_add h01 h2


/- ## Strong Jacobsthal–Kazandzidis -/

lemma prod_one_add_c_div {p B : ℕ} [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p)
    (c : ℚ) {γ : ℤ} (hγ : 0 ≤ γ) (hc : PCongr p γ c 0) (hcI : IsPInt p c) :
    PCongr p (min (γ + 2 + 2 * padicValNat p B)
      (min (2 * γ + 1 + padicValNat p B) (3 * γ)))
      (∏ j ∈ pFreeBelow p B, (1 + c / j)) 1 := by
  set s := pFreeBelow p B
  set x : ℕ → ℚ := fun j => c / j
  have hxeq : ∏ j ∈ s, (1 + c / j) = ∏ j ∈ s, (1 + x j) := rfl
  rw [hxeq]
  have hx : ∀ j ∈ s, PCongr p γ (x j) 0 := by
    intro j hj
    simpa [x, div_eq_mul_inv] using pCongr_mul_isPInt hc (isPInt_inv_pFree hp hj)
  have hxI : ∀ j ∈ s, IsPInt p (x j) :=
    fun j hj => isPInt_of_pCongr hγ (hx j hj)
  have hsum : PCongr p (γ + 2 + 2 * padicValNat p B) (∑ j ∈ s, x j) 0 := by
    have : ∑ j ∈ s, x j = c * ∑ j ∈ s, (1 : ℚ) / j := by
      simp only [x, div_eq_mul_inv, ← mul_sum, one_mul]
    rw [this]
    have hσ := sum_inv_pFree_strong (B := B) hp hp5
    have h := pCongr_mul_zero hc hσ
    have hmod : (γ + 2 + 2 * padicValNat p B : ℤ) =
        γ + (2 + 2 * padicValNat p B) := by ring
    rw [hmod]
    exact h
  have hsum2 : PCongr p (2 * γ + 1 + padicValNat p B) (∑ j ∈ s, x j ^ 2) 0 := by
    have : ∑ j ∈ s, x j ^ 2 = c ^ 2 * ∑ j ∈ s, (1 : ℚ) / (j : ℚ) ^ 2 := by
      simp only [x, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (j : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
      field_simp [hj0]
    rw [this]
    have hσ := sum_inv_sq_pFree_strong (B := B) hp hp5
    have hc2 : PCongr p (2 * γ) (c ^ 2) 0 := by
      simpa [pow_two, two_mul] using pCongr_mul_zero hc hc
    have h := pCongr_mul_zero hc2 hσ
    have hmod : (2 * γ + 1 + padicValNat p B : ℤ) =
        2 * γ + (1 + padicValNat p B) := by ring
    rw [hmod]
    exact h
  set δ : ℤ := min (γ + 2 + 2 * padicValNat p B)
    (min (2 * γ + 1 + padicValNat p B) (3 * γ))
  refine pCongr_prod_one_add_of (α := γ) (β := γ + 2 + 2 * padicValNat p B)
    (γ := 2 * γ + 1 + padicValNat p B) (δ := δ)
    hp hp5 hγ hx hxI hsum hsum2 ?_ ?_ ?_ ?_
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · have : δ ≤ 2 * (γ + 2 + 2 * padicValNat p B) := by
      have := min_le_left (γ + 2 + 2 * padicValNat p B)
        (min (2 * γ + 1 + padicValNat p B) (3 * γ))
      linarith
    simpa [two_mul] using this
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

lemma choose_standard_ratio_pCongr {A B p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) :
    PCongr p (min ((padicValNat p (A - B) : ℤ) + 1 + 2 + 2 * padicValNat p B)
      (min (2 * ((padicValNat p (A - B) : ℤ) + 1) + 1 + padicValNat p B)
        (3 * ((padicValNat p (A - B) : ℤ) + 1))))
      (((A * p).choose (B * p) : ℚ) / (A.choose B : ℚ)) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [choose_standard_ratio hp hBA]
  set Cnat := A - B
  have hc : PCongr p (padicValNat p Cnat + 1) (((Cnat : ℕ) : ℚ) * p) 0 := by
    have hC : PCongr p (padicValNat p Cnat) ((Cnat : ℕ) : ℚ) 0 := pCongr_coe_val
    have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
    exact pCongr_mul_zero hC hp1
  have hcI : IsPInt p (((Cnat : ℕ) : ℚ) * p) :=
    isPInt_mul (isPInt_nat p _) (isPInt_nat p _)
  simpa [Cnat] using
    prod_one_add_c_div (B := B) hp hp5 (((Cnat : ℕ) : ℚ) * p)
      (add_nonneg (Nat.cast_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)) hc hcI

lemma choose_aligned_ratio_pCongr_strong {A B p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B < A) :
    PCongr p (min ((padicValNat p A : ℤ) + 1 + 2 + 2 * padicValNat p B)
      (min (2 * ((padicValNat p A : ℤ) + 1) + 1 + padicValNat p B)
        (3 * ((padicValNat p A : ℤ) + 1))))
      (((A * p - 1).choose (B * p) : ℚ) / ((A - 1).choose B : ℚ)) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [choose_aligned_ratio hp hBA]
  set s := pFreeBelow p B
  set c : ℚ := (A : ℚ) * p
  have hsign : ∏ j ∈ s, ((A * p : ℚ) - j) / j = ∏ j ∈ s, (1 + (-c) / j) := by
    have hfac : ∀ j ∈ s, ((A * p : ℚ) - j) / j = - (1 - c / j) := by
      intro j hj
      have hj0 : (j : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (mem_Icc.mp (mem_pFreeBelow.mp hj).1).1)
      field_simp [hj0, c]; ring
    have hprod : ∏ j ∈ s, ((A * p : ℚ) - j) / j =
        ∏ j ∈ s, (- (1 - c / j)) := prod_congr rfl hfac
    rw [hprod, prod_neg]
    have hcard : Even s.card := even_card_pFreeBelow p B hp hp5
    rw [Even.neg_one_pow hcard, one_mul]
    refine prod_congr rfl fun j _ => ?_
    ring
  rw [hsign]
  have hc : PCongr p (padicValNat p A + 1) (-c) 0 := by
    have hA : PCongr p (padicValNat p A) (A : ℚ) 0 := pCongr_coe_val
    have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
    simpa [c, neg_mul] using pCongr_neg (pCongr_mul_zero hA hp1)
  have hcI : IsPInt p (-c) :=
    isPInt_neg (isPInt_mul (isPInt_nat p A) (isPInt_nat p p))
  exact prod_one_add_c_div (B := B) hp hp5 (-c)
    (add_nonneg (Nat.cast_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)) hc hcI

lemma val_add_eq_min_of_ne {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : padicValNat p a ≠ padicValNat p b) :
    padicValNat p (a + b) = min (padicValNat p a) (padicValNat p b) := by
  have hsum0 : (a : ℚ) + b ≠ 0 :=
    by exact_mod_cast (Nat.add_pos_left (Nat.pos_of_ne_zero ha) _).ne'
  have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hne' : (padicValNat p a : ℤ) ≠ padicValNat p b := by exact_mod_cast hne
  have hval : padicValRat p (a : ℚ) ≠ padicValRat p (b : ℚ) := by
    simpa [padicValRat.of_nat] using hne'
  have hmin := padicValRat.add_eq_min hsum0 ha0 hb0 hval
  have hab : ((a + b : ℕ) : ℚ) = (a : ℚ) + b := by push_cast; rfl
  have : (padicValNat p (a + b) : ℤ) =
      min (padicValNat p a : ℤ) (padicValNat p b) := by
    rw [← hab, padicValRat.of_nat] at hmin
    simpa using hmin
  exact_mod_cast this

lemma choose_ratio_symm {A B p : ℕ} (hBA : B ≤ A) :
    ((A * p).choose (B * p) : ℚ) / (A.choose B : ℚ) =
      ((A * p).choose ((A - B) * p) : ℚ) / (A.choose (A - B) : ℚ) := by
  have h1 : (A * p).choose (B * p) = (A * p).choose ((A - B) * p) := by
    have : A * p - B * p = (A - B) * p := (Nat.mul_sub_right_distrib A B p).symm
    have hle : B * p ≤ A * p := Nat.mul_le_mul_right p hBA
    rw [← choose_symm hle, this]
  have h2 : A.choose B = A.choose (A - B) := (choose_symm hBA).symm
  rw [h1, h2]

lemma choose_JK_strong {A B p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hA : A ≠ 0) :
    PCongr p (3 + padicValNat p A + padicValNat p B + padicValNat p (A - B))
      (((A * p).choose (B * p) : ℚ) / (A.choose B : ℚ)) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne B 0 with hB0 | hB0
  · subst hB0
    simp [choose_zero_right, pCongr_refl]
  rcases eq_or_ne B A with hBeq | hBne
  · subst hBeq
    simp [choose_self, Nat.sub_self, pCongr_refl]
  have hlt : B < A := lt_of_le_of_ne hBA hBne
  have hC0 : A - B ≠ 0 := Nat.sub_ne_zero_of_lt hlt
  have hstd := choose_standard_ratio_pCongr hp hp5 hBA
  have hstdC := choose_standard_ratio_pCongr (A := A) (B := A - B) hp hp5 (Nat.sub_le _ _)
  have hswap := choose_ratio_symm (A := A) (B := B) (p := p) hBA
  have hAC : A - (A - B) = B := Nat.sub_sub_self hBA
  rw [hAC] at hstdC
  by_cases hcmp : padicValNat p B ≤ padicValNat p (A - B)
  · -- Use the B-product (standard). When v(B) ≤ v(C) this hits the target,
    -- except when v(B) = v(C) < v(A), in which case we use the rising ratio.
    by_cases heq : padicValNat p B = padicValNat p (A - B)
    · by_cases hgt : padicValNat p B < padicValNat p A
      · have hrise := choose_aligned_ratio_pCongr_strong hp hp5 hlt
        have hid := choose_aligned_as_standard hp hlt
        rw [← hid]
        refine pCongr_of_le ?_ hrise
        have : padicValNat p (A - B) = padicValNat p B := heq.symm
        simp only [this]
        omega
      · refine pCongr_of_le ?_ hstd
        have : padicValNat p A ≤ padicValNat p B := Nat.le_of_not_gt hgt
        simp only [heq]
        omega
    · -- v(B) < v(C), so v(A) = v(B)
      have hne : padicValNat p B ≠ padicValNat p (A - B) :=
        fun h => heq h
      have hv : padicValNat p A =
          min (padicValNat p (A - B)) (padicValNat p B) := by
        have hsum := val_add_eq_min_of_ne (a := A - B) (b := B) hC0 hB0 (Ne.symm hne)
        rwa [Nat.sub_add_cancel hBA] at hsum
      refine pCongr_of_le ?_ hstd
      have hltBC : padicValNat p B < padicValNat p (A - B) :=
        lt_of_le_of_ne hcmp heq
      omega
  · -- v(C) < v(B), so use the swapped standard product
    have hltCB : padicValNat p (A - B) < padicValNat p B := Nat.lt_of_not_ge hcmp
    have hne : padicValNat p B ≠ padicValNat p (A - B) := hltCB.ne'
    have hv : padicValNat p A =
        min (padicValNat p (A - B)) (padicValNat p B) := by
      have hsum := val_add_eq_min_of_ne (a := A - B) (b := B) hC0 hB0 (Ne.symm hne)
      rwa [Nat.sub_add_cancel hBA] at hsum
    rw [hswap]
    refine pCongr_of_le ?_ hstdC
    omega

lemma choose_aligned_JK_strong {A B p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B < A) :
    PCongr p (3 + padicValNat p A + padicValNat p B + padicValNat p (A - B))
      (((A * p - 1).choose (B * p) : ℚ) / ((A - 1).choose B : ℚ)) 1 := by
  have hA : A ≠ 0 := (Nat.zero_lt_of_lt hBA).ne'
  rw [choose_aligned_as_standard hp hBA]
  exact choose_JK_strong hp hp5 hBA.le hA

lemma padicValNat_add_ge_min {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) :
    min (padicValNat p a) (padicValNat p b) ≤ padicValNat p (a + b) := by
  have hsum0 : ((a : ℚ) + (b : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.add_pos_left (Nat.pos_of_ne_zero ha) b).ne'
  have hab : ((a + b : ℕ) : ℚ) = (a : ℚ) + b := by push_cast; rfl
  have hmin := padicValRat.min_le_padicValRat_add (p := p) hsum0
  rw [← hab, padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat] at hmin
  exact_mod_cast hmin

lemma aligned_strong_val_bound {p N q : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hN : N ≠ 0) (hq : q ≠ 0) :
    (4 + 4 * padicValNat p N : ℤ) ≤
      4 + padicValNat p (N + 2 * q) +
        3 * padicValNat p ((N + q - 1).choose q) +
        padicValNat p (N + q) + padicValNat p q + padicValNat p N := by
  set e := padicValNat p N
  set f := padicValNat p q
  set c := padicValNat p ((N + q - 1).choose q)
  set s := padicValNat p (N + q)
  set t := padicValNat p (N + 2 * q)
  have hc0 : (e - f : ℕ) ≤ c :=
    rising_aligned_base_val (p := p) (m := N) (q := q) hN hq
  have hs : min e f ≤ s :=
    padicValNat_add_ge_min (p := p) (a := N) (b := q) hN
  have h2q : padicValNat p (2 * q) = f := padicValNat_two_mul hp5 hq
  have ht : min e f ≤ t := by
    have := padicValNat_add_ge_min (p := p) (a := N) (b := 2 * q) hN
    rwa [h2q] at this
  have he : (0 : ℤ) ≤ e := Nat.cast_nonneg _
  have hf : (0 : ℤ) ≤ f := Nat.cast_nonneg _
  have hc : (0 : ℤ) ≤ c := Nat.cast_nonneg _
  have hs0 : (0 : ℤ) ≤ s := Nat.cast_nonneg _
  have ht0 : (0 : ℤ) ≤ t := Nat.cast_nonneg _
  by_cases hle : e ≤ f
  · have : (e : ℤ) ≤ f := Nat.cast_le.mpr hle
    have hs' : (e : ℤ) ≤ s := by
      have h1 : ((min e f : ℕ) : ℤ) ≤ s := Nat.cast_le.mpr hs
      rwa [min_eq_left hle] at h1
    have ht' : (e : ℤ) ≤ t := by
      have h1 : ((min e f : ℕ) : ℤ) ≤ t := Nat.cast_le.mpr ht
      rwa [min_eq_left hle] at h1
    nlinarith
  · have hlt : f < e := Nat.lt_of_not_ge hle
    have : (f : ℤ) ≤ e := Nat.cast_le.mpr hlt.le
    have hs' : (f : ℤ) ≤ s := by
      have h1 : ((min e f : ℕ) : ℤ) ≤ s := Nat.cast_le.mpr hs
      rwa [min_eq_right hlt.le] at h1
    have ht' : (f : ℤ) ≤ t := by
      have h1 : ((min e f : ℕ) : ℤ) ≤ t := Nat.cast_le.mpr ht
      rwa [min_eq_right hlt.le] at h1
    have hc' : (e - f : ℤ) ≤ c := by
      have h1 : ((e - f : ℕ) : ℤ) ≤ c := Nat.cast_le.mpr hc0
      rwa [Nat.cast_sub hlt.le] at h1
    nlinarith

lemma aligned_choose_pCongr_strong {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N)
      (((p * (N + q) - 1).choose (p * q) : ℚ) /
        ((N + q - 1).choose q : ℚ)) 1 := by
  have hBA : q < N + q := by omega
  have h := choose_aligned_JK_strong (A := N + q) (B := q) hp hp5 hBA
  have hidx1 : (N + q) * p = p * (N + q) := Nat.mul_comm _ _
  have hidx2 : q * p = p * q := Nat.mul_comm _ _
  have hAB : N + q - q = N := Nat.add_sub_cancel _ _
  rw [hidx1, hidx2, hAB] at h
  exact h

lemma aligned_cube_diff_strong {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N +
        3 * padicValNat p ((N + q - 1).choose q))
      ((((p * (N + q) - 1).choose (p * q) : ℚ) ^ 3) -
        (((N + q - 1).choose q : ℚ) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Csmall : ℚ := ((N + q - 1).choose q : ℚ)
  set Cbig : ℚ := ((p * (N + q) - 1).choose (p * q) : ℚ)
  set ρ : ℚ := Cbig / Csmall
  have hC0 : Csmall ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (by omega : q ≤ N + q - 1)).ne'
  have hρ := aligned_choose_pCongr_strong hp hp5 hN (q := q)
  change PCongr p (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N)
    ρ 1 at hρ
  have hμ : (1 : ℤ) ≤
      3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N := by
    have : (0 : ℤ) ≤ padicValNat p (N + q) := Nat.cast_nonneg _
    have : (0 : ℤ) ≤ padicValNat p q := Nat.cast_nonneg _
    have : (0 : ℤ) ≤ padicValNat p N := Nat.cast_nonneg _
    omega
  have hρI : IsPInt p ρ := isPInt_of_pCongr_one (by omega) hρ
  have hρ3 := pCongr_pow_sub_one hρ hρI 3
  have heq : Cbig ^ 3 - Csmall ^ 3 = Csmall ^ 3 * (ρ ^ 3 - 1) := by
    have : ρ = Cbig / Csmall := rfl
    rw [this]
    field_simp [hC0]
  rw [heq]
  have hCval : PCongr p (padicValNat p ((N + q - 1).choose q)) Csmall 0 :=
    pCongr_coe_val
  have hC3 : PCongr p (3 * padicValNat p ((N + q - 1).choose q)) (Csmall ^ 3) 0 := by
    simpa using pCongr_pow_zero (k := 3) hCval
  have hmul := pCongr_mul_zero hC3 hρ3
  have hmod :
      (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N +
        3 * padicValNat p ((N + q - 1).choose q) : ℤ) =
      3 * padicValNat p ((N + q - 1).choose q) +
        (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N) := by
    ring
  rwa [hmod]

lemma aligned_term_pCongr_strong {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (((p * N + 2 * (p * q) : ℕ) : ℚ) *
        (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3))
      (((p : ℚ) * (N + 2 * q : ℕ) *
        (((N + q - 1).choose q : ℚ) ^ 3))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne q 0 with hq0 | hq0
  · subst hq0
    have hidx : p * N + p * 0 - 1 = p * N - 1 := by simp
    have hidx' : p * N + 2 * (p * 0) = p * N := by simp
    have hL : ((p * N + 2 * (p * 0) : ℕ) : ℚ) *
        (((p * N + p * 0 - 1).choose (p * 0) : ℚ) ^ 3) =
        (p * N : ℕ) := by
      simp [hidx, hidx']
    have hR : (p : ℚ) * (N + 2 * 0 : ℕ) * (((N + 0 - 1).choose 0 : ℚ) ^ 3) =
        (p : ℚ) * N := by
      simp
    have heq : ((p * N : ℕ) : ℚ) = (p : ℚ) * N := by push_cast; rfl
    rw [hL, hR, heq]
    exact pCongr_refl _ _ _
  have hidx : p * N + p * q - 1 = p * (N + q) - 1 := by rw [← Nat.mul_add]
  have hidx' : p * N + 2 * (p * q) = p * (N + 2 * q) := by ring
  rw [hidx, hidx']
  have hpref_eq : ((p * (N + 2 * q) : ℕ) : ℚ) =
      (p : ℚ) * (N + 2 * q : ℕ) := by push_cast; rfl
  apply pCongr_of_sub_zero
  have hdiff :
      ((p * (N + 2 * q) : ℕ) : ℚ) *
          (((p * (N + q) - 1).choose (p * q) : ℚ) ^ 3) -
        (p : ℚ) * (N + 2 * q : ℕ) *
          (((N + q - 1).choose q : ℚ) ^ 3) =
      ((p : ℚ) * (N + 2 * q : ℕ)) *
        ((((p * (N + q) - 1).choose (p * q) : ℚ) ^ 3) -
          (((N + q - 1).choose q : ℚ) ^ 3)) := by
    rw [hpref_eq]
    ring
  rw [hdiff]
  have hcdiff := aligned_cube_diff_strong hp hp5 hN (q := q)
  have hp1 : PCongr p 1 (p : ℚ) 0 := by
    refine pCongr_zero_of_val ?_
    simp [padicValRat_p]
  have hN2 : PCongr p (padicValNat p (N + 2 * q))
      ((N + 2 * q : ℕ) : ℚ) 0 := pCongr_coe_val
  have hpref : PCongr p (1 + padicValNat p (N + 2 * q))
      ((p : ℚ) * (N + 2 * q : ℕ)) 0 :=
    pCongr_mul_zero hp1 hN2
  have hmul := pCongr_mul_zero hpref hcdiff
  have hneed : (4 + 4 * padicValNat p N : ℤ) ≤
      (1 + padicValNat p (N + 2 * q)) +
        (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N +
          3 * padicValNat p ((N + q - 1).choose q)) := by
    have hb := aligned_strong_val_bound (p := p) hp5 hN.ne' hq0
    linarith
  exact pCongr_of_le hneed hmul

lemma aligned_sum_pCongr_strong {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range (N + 1),
        ((p * N + 2 * (p * q) : ℕ) : ℚ) *
          (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3))
      ((p : ℚ) * Ssum N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hterm := pCongr_sum (s := range (N + 1))
    (fun q _ => aligned_term_pCongr_strong hp hp5 hN (q := q))
  have hrhs :
      ∑ q ∈ range (N + 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (((N + q - 1).choose q : ℚ) ^ 3) =
      (p : ℚ) * Ssum N := by
    unfold Ssum
    rw [Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun q hq => ?_
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring
  rw [← hrhs]
  exact hterm

/- ## Unaligned double-index bijection -/

lemma unalign_mem_iff {p N k : ℕ} (hp : p.Prime) (hN : 0 < N) :
    k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k) ↔
      k / p < N ∧ k % p ∈ Icc 1 (p - 1) := by
  constructor
  · intro hk
    have ⟨hkR, hkp⟩ := mem_filter.mp hk
    exact ⟨unalign_div_lt hp hN (mem_range.mp hkR) hkp, unalign_mod_mem hp hkp⟩
  · intro ⟨hq, ht⟩
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    · have hkE : k = p * (k / p) + k % p := (Nat.div_add_mod k p).symm
      have h1 : p * (k / p) ≤ p * (N - 1) :=
        Nat.mul_le_mul_left p (Nat.le_pred_of_lt hq)
      have h2 : k % p ≤ p - 1 := (mem_Icc.mp ht).2
      have hle : k ≤ p * (N - 1) + (p - 1) := by
        rw [hkE]; exact Nat.add_le_add h1 h2
      have hmul : p * N = p * (N - 1) + p := by
        nth_rw 1 [← Nat.sub_add_cancel (n := N) (m := 1) hN]
        rw [Nat.mul_add, mul_one]
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
      have hEq : p * (N - 1) + (p - 1) + 1 = p * N := by
        rw [hmul, add_assoc, hp1]
      have : k < p * N + 1 := by
        have hsucc : k + 1 ≤ p * (N - 1) + (p - 1) + 1 := Nat.succ_le_succ hle
        rw [hEq] at hsucc
        exact lt_trans (Nat.lt_of_succ_le hsucc) (Nat.lt_succ_self _)
      exact this
    · intro hd
      have hpos : 0 < k % p := (mem_Icc.mp ht).1
      exact hpos.ne' (Nat.mod_eq_zero_of_dvd hd)

lemma unalign_div_mod (p q t : ℕ) (hppos : 0 < p) (ht : t < p) :
    (p * q + t) / p = q ∧ (p * q + t) % p = t := by
  constructor
  · rw [Nat.mul_add_div hppos, Nat.div_eq_of_lt ht, add_zero]
  · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

lemma unalign_sum_bilinear {p N : ℕ} (hp : p.Prime) (hN : 0 < N) (f : ℕ → ℚ) :
    ∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k), f k =
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1), f (p * q + t) := by
  have hbij :
      ∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k), f k =
        ∑ qt ∈ range N ×ˢ Icc 1 (p - 1), f (p * qt.1 + qt.2) := by
    refine Finset.sum_nbij (fun k => (k / p, k % p)) ?_ ?_ ?_ ?_
    · intro k hk
      have ⟨hq, ht⟩ := (unalign_mem_iff hp hN).mp hk
      exact mem_product.mpr ⟨mem_range.mpr hq, ht⟩
    · intro k _ k' _ heq
      injection heq with hdiv hmod
      calc
        k = p * (k / p) + k % p := (Nat.div_add_mod k p).symm
        _ = p * (k' / p) + k' % p := by rw [hdiv, hmod]
        _ = k' := Nat.div_add_mod k' p
    · intro qt hqt
      rcases mem_product.mp hqt with ⟨hq, ht⟩
      have htlt : qt.2 < p := Nat.lt_of_le_pred hp.pos (mem_Icc.mp ht).2
      have ⟨hdiv, hmod⟩ := unalign_div_mod p qt.1 qt.2 hp.pos htlt
      refine ⟨p * qt.1 + qt.2, ?_, ?_⟩
      · refine (unalign_mem_iff hp hN).mpr ⟨?_, ?_⟩
        · rw [hdiv]; exact mem_range.mp hq
        · rw [hmod]; exact ht
      · exact Prod.ext hdiv hmod
    · intro k _hk
      simp [Nat.div_add_mod]
  rw [hbij, Finset.sum_product]

/- ## Unaligned expansion at precision 4 -/

lemma unalign_Y3_pCongr {p M t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 4
      ((((p * M + t - 1).choose t : ℚ) ^ 3) -
        (((p : ℚ) * M / t) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha : PCongr p 1 ((p : ℚ) * M / t) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := pCongr_zero_of_val (by simp)
    have hrest : IsPInt p ((M : ℚ) * (t : ℚ)⁻¹) :=
      isPInt_mul (isPInt_nat p M) (isPInt_inv_of_mem_Icc hp ht)
    simpa [div_eq_mul_inv, mul_assoc] using pCongr_mul_isPInt hp1 hrest
  have hxa := choose_pM_t_pCongr hp hp5 hM ht
  have haI : IsPInt p ((p : ℚ) * M / t) :=
    isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) ha
  have hxI : IsPInt p ((p * M + t - 1).choose t : ℚ) := isPInt_nat p _
  have hxa' : PCongr p 2
      (((p * M + t - 1).choose t : ℚ) - ((p : ℚ) * M / t)) 0 := by
    have : (p * M : ℚ) / t = (p : ℚ) * M / t := by push_cast; rfl
    simpa [this] using hxa
  exact pCongr_cube_of_val2 hxa' ha haI hxI

lemma unalign_X3_pCongr {p M B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBM : B < M) :
    PCongr p 3
      ((((p * M - 1).choose (p * B) : ℚ) ^ 3) -
        ((((M - 1).choose B : ℚ) ^ 3))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : 0 < M - B := Nat.sub_pos_of_lt hBM
  have h := aligned_choose_cube_pCongr (N := M - B) (q := B) hp hp5 hN
  have hidx : p * (M - B + B) = p * M := by rw [Nat.sub_add_cancel hBM.le]
  have hidx2 : M - B + B - 1 = M - 1 := by omega
  have h' := pCongr_sub_zero h
  have hle : (3 : ℤ) ≤ 3 + padicValNat p ((M - B + B - 1).choose B) := by
    have : (0 : ℤ) ≤ padicValNat p ((M - B + B - 1).choose B) := Nat.cast_nonneg _
    omega
  simpa [hidx, hidx2] using pCongr_of_le hle h'

lemma unalign_Zinv3_pCongr {p B t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 1 ((((p * B + t).choose t : ℚ) ^ 3)⁻¹) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := choose_pB_t_pCongr (B := B) hp hp5 ht
  have hZ0 : ((p * B + t).choose t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.le_add_left t (p * B))).ne'
  have hZI : IsPInt p ((p * B + t).choose t : ℚ) := isPInt_nat p _
  have hZ3 := pCongr_pow_of 3 hZ hZI (isPInt_one p)
  exact pCongr_inv_one (by norm_num : (1 : ℤ) ≤ 1) hZ3 (pow_ne_zero 3 hZ0)

lemma unalign_Y_val1 {p M t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 1 ((p * M + t - 1).choose t : ℚ) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha : PCongr p 1 ((p : ℚ) * M / t) 0 := by
    have hp1 : PCongr p 1 (p : ℚ) 0 := pCongr_zero_of_val (by simp)
    have hrest : IsPInt p ((M : ℚ) * (t : ℚ)⁻¹) :=
      isPInt_mul (isPInt_nat p M) (isPInt_inv_of_mem_Icc hp ht)
    simpa [div_eq_mul_inv, mul_assoc] using pCongr_mul_isPInt hp1 hrest
  have hYa := choose_pM_t_pCongr hp hp5 hM ht
  have : ((p * M + t - 1).choose t : ℚ) =
      (((p * M + t - 1).choose t : ℚ) - (p * M : ℚ) / t) + (p * M : ℚ) / t := by
    ring
  rw [this]
  have ha' : PCongr p 1 ((p * M : ℚ) / t) 0 := by
    have : (p * M : ℚ) / t = (p : ℚ) * M / t := by push_cast; rfl
    simpa [this] using ha
  simpa using pCongr_add (pCongr_of_le (by norm_num : (1 : ℤ) ≤ 2) hYa) ha'

lemma unalign_C3_leading {p M B t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBM : B < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 4
      (((((p * M - 1).choose (p * B) : ℚ) *
            ((p * M + t - 1).choose t : ℚ) /
            ((p * B + t).choose t : ℚ)) ^ 3) -
        ((((M - 1).choose B : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set X : ℚ := ((p * M - 1).choose (p * B) : ℚ)
  set Y : ℚ := ((p * M + t - 1).choose t : ℚ)
  set Z : ℚ := ((p * B + t).choose t : ℚ)
  set Cs : ℚ := ((M - 1).choose B : ℚ)
  set a : ℚ := (p : ℚ) * M / t
  have hZ0 : Z ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.le_add_left t (p * B))).ne'
  have hX3 := unalign_X3_pCongr hp hp5 hBM
  have hY3 := unalign_Y3_pCongr hp hp5 (Nat.zero_lt_of_lt hBM) ht
  have hZinv := unalign_Zinv3_pCongr (B := B) hp hp5 ht
  have hX3I : IsPInt p (X ^ 3) := isPInt_pow (isPInt_nat p _) 3
  have hY0 := unalign_Y_val1 hp hp5 (Nat.zero_lt_of_lt hBM) ht
  have hY3z : PCongr p 3 (Y ^ 3) 0 := by simpa using pCongr_pow_zero (k := 3) hY0
  have heq :
      (X * Y / Z) ^ 3 - Cs ^ 3 * a ^ 3 =
        X ^ 3 * Y ^ 3 * ((Z ^ 3)⁻¹ - 1) +
          X ^ 3 * (Y ^ 3 - a ^ 3) +
          (X ^ 3 - Cs ^ 3) * a ^ 3 := by
    have : (X * Y / Z) ^ 3 = X ^ 3 * Y ^ 3 * (Z ^ 3)⁻¹ := by
      field_simp [hZ0]
    rw [this]; ring
  rw [heq]
  have h1 : PCongr p 4 (X ^ 3 * Y ^ 3 * ((Z ^ 3)⁻¹ - 1)) 0 := by
    have hd : PCongr p 1 ((Z ^ 3)⁻¹ - 1) 0 := pCongr_sub_zero hZinv
    have hmul := pCongr_mul_zero hY3z hd
    exact pCongr_of_le (by norm_num : (4 : ℤ) ≤ 3 + 1)
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using
        pCongr_mul_isPInt hmul hX3I)
  have h2 : PCongr p 4 (X ^ 3 * (Y ^ 3 - a ^ 3)) 0 :=
    by simpa [mul_comm] using pCongr_mul_isPInt hY3 hX3I
  have h3 : PCongr p 4 ((X ^ 3 - Cs ^ 3) * a ^ 3) 0 := by
    have ha1 : PCongr p 1 a 0 := by
      have hp1 : PCongr p 1 (p : ℚ) 0 := pCongr_zero_of_val (by simp)
      have hrest : IsPInt p ((M : ℚ) * (t : ℚ)⁻¹) :=
        isPInt_mul (isPInt_nat p M) (isPInt_inv_of_mem_Icc hp ht)
      simpa [a, div_eq_mul_inv, mul_assoc] using pCongr_mul_isPInt hp1 hrest
    have ha3 : PCongr p 3 (a ^ 3) 0 := by simpa using pCongr_pow_zero (k := 3) ha1
    exact pCongr_of_le (by norm_num : (4 : ℤ) ≤ 3 + 3) (pCongr_mul_zero hX3 ha3)
  simpa using pCongr_add (pCongr_add h1 h2) h3

lemma rising_mul_identity {N q : ℕ} (hN : 0 < N) :
    ((N + q : ℕ) : ℚ) * ((N + q - 1).choose q : ℚ) =
      (N : ℚ) * ((N + q).choose q : ℚ) := by
  have h := choose_succ_pred_mul (n := N + q) (k := q) (Nat.add_pos_left hN q)
  have hidx : N + q - q = N := Nat.add_sub_cancel _ _
  rw [hidx] at h
  have h' : ((N + q) * (N + q - 1).choose q : ℚ) =
      (N * (N + q).choose q : ℚ) := by exact_mod_cast h
  simpa [Nat.cast_mul] using h'

lemma unalign_k_mem {p N q t : ℕ} (hp : p.Prime) (hN : 0 < N)
    (hq : q < N) (ht : t ∈ Icc 1 (p - 1)) :
    p * q + t ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k) := by
  have htlt : t < p := Nat.lt_of_le_pred hp.pos (mem_Icc.mp ht).2
  have ⟨hdiv, hmod⟩ := unalign_div_mod p q t hp.pos htlt
  refine (unalign_mem_iff hp hN).mpr ⟨?_, ?_⟩
  · rw [hdiv]; exact hq
  · rw [hmod]; exact ht

lemma unalign_term_leading {p N q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hq : q < N) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p 4
      (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
        (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M := N + q
  set B := q
  have hBM : B < M := Nat.lt_add_of_pos_left hN
  have hkmem := unalign_k_mem hp hN hq ht
  have ⟨hkR, hkp⟩ := mem_filter.mp hkmem
  have hform := unalign_choose_formula (N := N) (k := p * q + t) hp hN
    (mem_range.mp hkR) hkp
  have htlt : t < p := Nat.lt_of_le_pred hp.pos (mem_Icc.mp ht).2
  have hdiv : (p * q + t) / p = q := (unalign_div_mod p q t hp.pos htlt).1
  have hmod : (p * q + t) % p = t := (unalign_div_mod p q t hp.pos htlt).2
  have hCeq :
      ((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) =
        ((p * M - 1).choose (p * B) : ℚ) *
          ((p * M + t - 1).choose t : ℚ) /
          ((p * B + t).choose t : ℚ) := by
    simpa [hdiv, hmod, M, B, Nat.mul_add] using hform
  have hC3 := unalign_C3_leading (M := M) (B := B) (t := t) hp hp5 hBM ht
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have hpref :
      ((p * N + 2 * (p * q + t) : ℕ) : ℚ) =
        (p : ℚ) * (N + 2 * q : ℕ) + 2 * t := by
    push_cast; ring
  have ha : ((p : ℚ) * M / t) ^ 3 =
      (p : ℚ) ^ 3 * (M : ℚ) ^ 3 / (t : ℚ) ^ 3 := by
    field_simp [ht0]
  have hCsI : IsPInt p (((N + q - 1).choose q : ℚ) ^ 3) :=
    isPInt_pow (isPInt_nat p _) 3
  have hCdiff : PCongr p 4
      (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3 -
        (((N + q - 1).choose q : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3)) 0 := by
    rw [hCeq]
    simpa [M, B] using hC3
  have hprefI : IsPInt p ((p * N + 2 * (p * q + t) : ℕ) : ℚ) := isPInt_nat p _
  have h1 : PCongr p 4
      (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
        (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3 -
          (((N + q - 1).choose q : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3))) 0 :=
    by simpa [mul_comm] using pCongr_mul_isPInt hCdiff hprefI
  have h2 : PCongr p 4
      (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          ((((N + q - 1).choose q : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3)) -
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) 0 := by
    have heq :
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            ((((N + q - 1).choose q : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3)) -
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
        (p : ℚ) ^ 4 * (N + 2 * q : ℕ) *
          (((N + q - 1).choose q : ℚ) ^ 3) * (M : ℚ) ^ 3 / (t : ℚ) ^ 3 := by
      rw [hpref, ha]
      field_simp [ht0]
      ring
    rw [heq]
    have hp4 : PCongr p 4 ((p : ℚ) ^ 4) 0 := pCongr_p_pow 4
    have hrest : IsPInt p
        ((N + 2 * q : ℕ) * (((N + q - 1).choose q : ℚ) ^ 3) *
          (M : ℚ) ^ 3 * ((t : ℚ) ^ 3)⁻¹) := by
      refine isPInt_mul (isPInt_mul (isPInt_mul (isPInt_nat p _) hCsI)
        (isPInt_pow (isPInt_nat p _) 3)) ?_
      simpa [inv_pow] using isPInt_pow (isPInt_inv_of_mem_Icc hp ht) 3
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      pCongr_mul_isPInt hp4 hrest
  have heq :
      ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
      ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
        (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3 -
          (((N + q - 1).choose q : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3)) +
      (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          ((((N + q - 1).choose q : ℚ) ^ 3) * (((p : ℚ) * M / t) ^ 3)) -
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) := by
    ring
  rw [heq]
  simpa using pCongr_add h1 h2

lemma unalign_sum_leading {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p 4
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
        (2 : ℚ) * (p : ℚ) ^ 3 *
          (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3)) *
          harmonicGen 2 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hterm : PCongr p 4
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2)) 0 := by
    refine pCongr_sum_zero ?_
    intro q hq
    refine pCongr_sum_zero ?_
    intro t ht
    exact unalign_term_leading hp hp5 hN (mem_range.mp hq) ht
  have hH :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
      (2 : ℚ) * (p : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3)) *
        harmonicGen 2 (p - 1) := by
    have hswap :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
        ∑ t ∈ Icc 1 (p - 1), ∑ q ∈ range N,
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 := by
      rw [sum_comm]
    rw [hswap]
    have : ∑ t ∈ Icc 1 (p - 1), ∑ q ∈ range N,
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
        ∑ t ∈ Icc 1 (p - 1),
          ((2 : ℚ) * (p : ℚ) ^ 3 *
            (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
              (((N + q - 1).choose q : ℚ) ^ 3))) * ((t : ℚ) ^ 2)⁻¹ := by
      refine sum_congr rfl fun t ht => ?_
      have ht0 : (t : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
      have hfactor :
          ∀ q, (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
              (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
            ((2 : ℚ) * (p : ℚ) ^ 3 * ((t : ℚ) ^ 2)⁻¹) *
              (((N + q : ℕ) : ℚ) ^ 3 * (((N + q - 1).choose q : ℚ) ^ 3)) := by
        intro q; field_simp [ht0]
      simp only [hfactor, ← mul_sum]
      ring
    rw [this, ← mul_sum, harmonicGen_two_Icc]
    simp only [div_eq_mul_inv]
    ring
  have heq :
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3)) -
      (2 : ℚ) * (p : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3)) *
        harmonicGen 2 (p - 1) =
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) := by
    rw [← hH, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [← sum_sub_distrib]
  rw [heq]
  exact hterm

lemma unalign_H2_block {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p 4
      ((2 : ℚ) * (p : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3)) *
        harmonicGen 2 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := pCongr_p_pow 3
  have hH2 : PCongr p 1 (harmonicGen 2 (p - 1)) 0 :=
    pCongr_zero_of_val (wolstenholme_two hp hp5)
  have hsumI : IsPInt p
      (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
        (((N + q - 1).choose q : ℚ) ^ 3)) := by
    refine isPInt_sum ?_
    intro q _
    exact isPInt_mul (isPInt_pow (isPInt_nat p _) 3)
      (isPInt_pow (isPInt_nat p _) 3)
  have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
  have hmul := pCongr_mul_zero hp3 hH2
  have hmul' := pCongr_mul_isPInt hmul hsumI
  have hmul'' := pCongr_mul_isPInt hmul' h2I
  refine pCongr_of_le (by norm_num : (4 : ℤ) ≤ 3 + 1) ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul''

lemma unalign_sum_pCongr_four {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p 4
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [unalign_sum_bilinear hp hN]
  have hlead := unalign_sum_leading hp hp5 hN
  have hH2 := unalign_H2_block hp hp5 hN
  have heq :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) =
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
        (2 : ℚ) * (p : ℚ) ^ 3 *
          (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3)) *
          harmonicGen 2 (p - 1)) +
      ((2 : ℚ) * (p : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3)) *
        harmonicGen 2 (p - 1)) := by
    ring
  rw [heq]
  simpa using pCongr_add hlead hH2

lemma Ssum_pN_four {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p 4 ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Ssum_split_aligned hp hN]
  have hal := aligned_sum_pCongr_strong hp hp5 hN
  have hun := unalign_sum_pCongr_four hp hp5 hN
  have heq :
      (∑ q ∈ range (N + 1),
          ((p * N + 2 * (p * q) : ℕ) : ℚ) *
            (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3)) +
        (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
          ((p * N + 2 * k : ℕ) : ℚ) *
            (((p * N + k - 1).choose k : ℚ) ^ 3)) -
        (p : ℚ) * Ssum N =
      (∑ q ∈ range (N + 1),
          ((p * N + 2 * (p * q) : ℕ) : ℚ) *
            (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3) -
        (p : ℚ) * Ssum N) +
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) := by
    ring
  rw [heq]
  have hle4 : (4 : ℤ) ≤ 4 + 4 * padicValNat p N :=
    Nat.cast_le.mpr (Nat.le_add_right _ _)
  have hal0 := pCongr_sub_zero (pCongr_of_le hle4 hal)
  simpa using pCongr_add hal0 hun

lemma Ssum_pN {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p (4 + padicValNat p N)
      ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) 0 := by
  by_cases hv : 1 ≤ padicValNat p N
  · exact Ssum_pN_of_pos_val hp hp5 hN hv
  · have hv0 : padicValNat p N = 0 := by omega
    have h := Ssum_pN_four hp hp5 hN
    simpa [hv0] using h

lemma a_pN_three {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p 3 (a (p * N) : ℚ) (a N) :=
  pCongr_a_of_Ssum hp hN (Ssum_pN hp hp5 hN)

/- ## Divisibility of `∑_{q < N} C(N+q,q)³` by `N` in the `p`-adic sense -/

lemma choose_add_prod (n k r : ℕ) :
    ((n + r).choose (k + r) : ℚ) * (∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ)) =
      (n.choose k : ℚ) * (∏ i ∈ Icc 1 r, ((n + i : ℕ) : ℚ)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hunion : Icc 1 (r + 1) = Icc 1 r ∪ {r + 1} := by
      ext x; simp [mem_Icc]; omega
    have hdisj : Disjoint (Icc 1 r) ({r + 1} : Finset ℕ) := by
      simp [disjoint_left]; omega
    rw [hunion, prod_union hdisj, prod_union hdisj, prod_singleton, prod_singleton]
    have hmul := choose_succ_succ_mul (n := n + r) (k := k + r)
    have hn : n + r + 1 = n + (r + 1) := by omega
    have hk : k + r + 1 = k + (r + 1) := by omega
    rw [hn, hk] at hmul
    have hsucc : ((n + (r + 1)).choose (k + (r + 1)) : ℚ) *
        ((k + (r + 1) : ℕ) : ℚ) =
        ((n + r).choose (k + r) : ℚ) * ((n + (r + 1) : ℕ) : ℚ) := by
      exact_mod_cast hmul
    calc
      ((n + (r + 1)).choose (k + (r + 1)) : ℚ) *
          ((∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ)) * ((k + (r + 1) : ℕ) : ℚ))
          = (((n + (r + 1)).choose (k + (r + 1)) : ℚ) *
              ((k + (r + 1) : ℕ) : ℚ)) *
            (∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ)) := by ring
      _ = ((n + r).choose (k + r) : ℚ) * ((n + (r + 1) : ℕ) : ℚ) *
            (∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ)) := by
          rw [hsucc]
      _ = (((n + r).choose (k + r) : ℚ) *
            (∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ))) *
          ((n + (r + 1) : ℕ) : ℚ) := by ring
      _ = ((n.choose k : ℚ) * (∏ i ∈ Icc 1 r, ((n + i : ℕ) : ℚ))) *
          ((n + (r + 1) : ℕ) : ℚ) := by rw [ih]
      _ = (n.choose k : ℚ) *
          ((∏ i ∈ Icc 1 r, ((n + i : ℕ) : ℚ)) * ((n + (r + 1) : ℕ) : ℚ)) := by ring

lemma choose_add_prod_div (n k r : ℕ) :
    ((n + r).choose (k + r) : ℚ) =
      (n.choose k : ℚ) *
        (∏ i ∈ Icc 1 r, ((n + i : ℕ) : ℚ) / ((k + i : ℕ) : ℚ)) := by
  have h := choose_add_prod n k r
  have hden : ∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    intro i hi
    exact Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp hi).1).ne'
  have hprod :
      ∏ i ∈ Icc 1 r, ((n + i : ℕ) : ℚ) / ((k + i : ℕ) : ℚ) =
        (∏ i ∈ Icc 1 r, ((n + i : ℕ) : ℚ)) /
          (∏ i ∈ Icc 1 r, ((k + i : ℕ) : ℚ)) :=
    prod_div_distrib _ _
  rw [hprod]
  field_simp [hden]
  linear_combination h

lemma choose_p_shift_prod (A B r p : ℕ) :
    ((p * A + r).choose (p * B + r) : ℚ) =
      ((p * A).choose (p * B) : ℚ) *
        (∏ i ∈ Icc 1 r, (1 + ((p : ℚ) * ((A : ℚ) - B)) / ((p * B + i : ℕ) : ℚ))) := by
  have h := choose_add_prod_div (n := p * A) (k := p * B) (r := r)
  rw [h]
  refine congrArg (fun s => ((p * A).choose (p * B) : ℚ) * s) ?_
  refine prod_congr rfl fun i hi => ?_
  have hi0 : ((p * B + i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp hi).1).ne'
  have : ((p * A + i : ℕ) : ℚ) / ((p * B + i : ℕ) : ℚ) =
      1 + ((p : ℚ) * ((A : ℚ) - B)) / ((p * B + i : ℕ) : ℚ) := by
    field_simp [hi0]
    push_cast
    ring
  exact this

lemma pB_add_i_not_dvd {p B i : ℕ} (hp : p.Prime) (hi : i ∈ Icc 1 (p - 1)) :
    ¬ p ∣ (p * B + i) := by
  intro hd
  have : p ∣ i := (Nat.dvd_add_right ⟨B, rfl⟩).mp hd
  have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
  have hi2 : i ≤ p - 1 := (mem_Icc.mp hi).2
  exact Nat.not_dvd_of_pos_of_lt hi1 (Nat.lt_of_le_pred hp.pos hi2) this

lemma isPInt_inv_pB_add_i {p B i : ℕ} (hp : p.Prime) (hi : i ∈ Icc 1 (p - 1)) :
    IsPInt p (((p * B + i : ℕ) : ℚ)⁻¹) :=
  isPInt_inv_of_not_dvd hp
    (Nat.add_pos_right _ (mem_Icc.mp hi).1).ne'
    (pB_add_i_not_dvd (B := B) hp hi)

lemma nat_cast_sub_of_le {A B : ℕ} (hBA : B ≤ A) :
    (A : ℚ) - B = ((A - B : ℕ) : ℚ) :=
  (Nat.cast_sub hBA).symm

/-- The shift product `∏ (1 + p(A-B)/(pB+i))` is `1` at precision `1+v(A-B)`. -/
lemma choose_shift_prod_pCongr {p A B r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hr : r < p) :
    PCongr p (1 + padicValNat p (A - B))
      (∏ i ∈ Icc 1 r,
        (1 + ((p : ℚ) * ((A : ℚ) - B)) / ((p * B + i : ℕ) : ℚ))) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := Icc 1 r
  set c : ℚ := (p : ℚ) * ((A - B : ℕ) : ℚ)
  set x : ℕ → ℚ := fun i => c / ((p * B + i : ℕ) : ℚ)
  have hcast : (A : ℚ) - B = ((A - B : ℕ) : ℚ) := nat_cast_sub_of_le hBA
  have hxeq :
      ∏ i ∈ s, (1 + ((p : ℚ) * ((A : ℚ) - B)) / ((p * B + i : ℕ) : ℚ)) =
        ∏ i ∈ s, (1 + x i) := by
    refine prod_congr rfl fun i _ => ?_
    simp only [x, c, hcast]
  rw [hxeq]
  have hrle : r ≤ p - 1 := Nat.le_pred_of_lt hr
  have hα : (0 : ℤ) ≤ 1 + padicValNat p (A - B) :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hx : ∀ i ∈ s, PCongr p (1 + padicValNat p (A - B)) (x i) 0 := by
    intro i hi
    have hiI : i ∈ Icc 1 (p - 1) := by
      have ⟨hi1, hi2⟩ := mem_Icc.mp hi
      exact mem_Icc.mpr ⟨hi1, le_trans hi2 hrle⟩
    have hc : PCongr p (1 + padicValNat p (A - B)) c 0 := by
      have hC : PCongr p (padicValNat p (A - B)) ((A - B : ℕ) : ℚ) 0 :=
        pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [c, add_comm] using pCongr_mul_zero hp1 hC
    have hinv : IsPInt p (((p * B + i : ℕ) : ℚ)⁻¹) :=
      isPInt_inv_pB_add_i (B := B) hp hiI
    simpa [x, div_eq_mul_inv] using pCongr_mul_isPInt hc hinv
  have hxI : ∀ i ∈ s, IsPInt p (x i) :=
    fun i hi => isPInt_of_pCongr hα (hx i hi)
  -- Each x_i has val ≥ 1+v(A-B), so the product is 1 at that precision
  -- via ∏(1+x) = 1 + ∑x + O(x²).
  refine pCongr_prod_one_add_of (α := 1 + padicValNat p (A - B))
    (β := 1 + padicValNat p (A - B)) (γ := 2 * (1 + padicValNat p (A - B)))
    (δ := 1 + padicValNat p (A - B))
    hp hp5 hα hx hxI ?_ ?_ le_rfl ?_ ?_ ?_
  · exact pCongr_sum_zero hx
  · refine pCongr_sum_zero ?_
    intro i hi
    simpa [pow_two, two_mul] using pCongr_mul_zero (hx i hi) (hx i hi)
  · have : (1 + padicValNat p (A - B) : ℤ) ≤
        2 * (1 + padicValNat p (A - B)) := by
      nlinarith [hα]
    exact this
  · have : (1 + padicValNat p (A - B) : ℤ) ≤
        2 * (1 + padicValNat p (A - B)) := by
      nlinarith [hα]
    exact this
  · have : (1 + padicValNat p (A - B) : ℤ) ≤
        3 * (1 + padicValNat p (A - B)) := by
      nlinarith [hα]
    exact this

/-- `C(pA+r, pB+r) / C(A,B) ≡ 1` at precision `1+v(A-B)`. -/
lemma choose_p_shift_ratio_pCongr {p A B r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hA : A ≠ 0) (hr : r < p) :
    PCongr p (1 + padicValNat p (A - B))
      (((p * A + r).choose (p * B + r) : ℚ) / (A.choose B : ℚ)) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hform := choose_p_shift_prod A B r p
  have hJK := choose_JK_strong (A := A) (B := B) hp hp5 hBA hA
  have hprod := choose_shift_prod_pCongr (A := A) (B := B) (r := r) hp hp5 hBA hr
  have hden : (A.choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos hBA).ne'
  have hdenp : ((p * A).choose (p * B) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.mul_le_mul_left p hBA)).ne'
  have heq :
      ((p * A + r).choose (p * B + r) : ℚ) / (A.choose B : ℚ) =
        (((p * A).choose (p * B) : ℚ) / (A.choose B : ℚ)) *
          (∏ i ∈ Icc 1 r,
            (1 + ((p : ℚ) * ((A : ℚ) - B)) / ((p * B + i : ℕ) : ℚ))) := by
    rw [hform]
    field_simp [hden]
  rw [heq]
  have hm : (1 + padicValNat p (A - B) : ℤ) ≤
      3 + padicValNat p A + padicValNat p B + padicValNat p (A - B) := by
    have : (0 : ℤ) ≤ padicValNat p A := Nat.cast_nonneg _
    have : (0 : ℤ) ≤ padicValNat p B := Nat.cast_nonneg _
    omega
  have hJK' : PCongr p (1 + padicValNat p (A - B))
      (((p * A).choose (p * B) : ℚ) / (A.choose B : ℚ)) 1 := by
    have : A * p = p * A := mul_comm _ _
    have : B * p = p * B := mul_comm _ _
    simpa [this, mul_comm A p, mul_comm B p] using pCongr_of_le hm hJK
  have h1I : IsPInt p (1 : ℚ) := isPInt_one p
  have hJKI : IsPInt p (((p * A).choose (p * B) : ℚ) / (A.choose B : ℚ)) :=
    isPInt_of_pCongr_one
      (add_nonneg (by norm_num : (0 : ℤ) ≤ 1) (Nat.cast_nonneg _)) hJK'
  convert pCongr_mul hJK' hprod hJKI h1I using 1
  ring

lemma choose_p_shift_pCongr {p A B r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hA : A ≠ 0) (hr : r < p) :
    PCongr p (1 + padicValNat p (A - B))
      ((p * A + r).choose (p * B + r) : ℚ) (A.choose B : ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hden : (A.choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos hBA).ne'
  have hrat := choose_p_shift_ratio_pCongr hp hp5 hBA hA hr
  have h := pCongr_mul_denom hden hrat
  refine pCongr_of_le ?_ h
  have : (0 : ℤ) ≤ padicValRat p (A.choose B : ℚ) := by
    rw [padicValRat.of_nat]; exact Nat.cast_nonneg _
  linarith

lemma choose_p_shift_cube_pCongr {p A B r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hA : A ≠ 0) (hr : r < p) :
    PCongr p (1 + padicValNat p (A - B))
      (((p * A + r).choose (p * B + r) : ℚ) ^ 3)
      ((A.choose B : ℚ) ^ 3) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact pCongr_pow_of 3 (choose_p_shift_pCongr hp hp5 hBA hA hr)
    (isPInt_nat p _) (isPInt_nat p _)

lemma sum_range_mul (p N : ℕ) (hp : 0 < p) (f : ℕ → ℚ) :
    ∑ q ∈ range (p * N), f q =
      ∑ t ∈ range N, ∑ r ∈ range p, f (p * t + r) := by
  have hbij :
      ∑ q ∈ range (p * N), f q =
        ∑ tr ∈ range N ×ˢ range p, f (p * tr.1 + tr.2) := by
    refine Finset.sum_nbij (fun q => (q / p, q % p)) ?_ ?_ ?_ ?_
    · intro q hq
      have hqlt : q < p * N := mem_range.mp hq
      exact mem_product.mpr ⟨mem_range.mpr (Nat.div_lt_of_lt_mul hqlt),
        mem_range.mpr (Nat.mod_lt q hp)⟩
    · intro q _ q' _ heq
      injection heq with hdiv hmod
      calc
        q = p * (q / p) + q % p := (Nat.div_add_mod q p).symm
        _ = p * (q' / p) + q' % p := by rw [hdiv, hmod]
        _ = q' := Nat.div_add_mod q' p
    · intro tr htr
      rcases mem_product.mp htr with ⟨ht, hr⟩
      have hrlt : tr.2 < p := mem_range.mp hr
      have ⟨hdiv, hmod⟩ := unalign_div_mod p tr.1 tr.2 hp hrlt
      refine ⟨p * tr.1 + tr.2, ?_, Prod.ext hdiv hmod⟩
      refine mem_range.mpr ?_
      have : p * tr.1 + tr.2 < p * tr.1 + p := Nat.add_lt_add_left hrlt _
      have : p * tr.1 + p = p * (tr.1 + 1) := by ring
      have hle : p * (tr.1 + 1) ≤ p * N :=
        Nat.mul_le_mul_left p (mem_range.mp ht)
      omega
    · intro q _
      simp [Nat.div_add_mod]
  rw [hbij, Finset.sum_product]

lemma padicValNat_mul_p {p N : ℕ} [Fact p.Prime] (hN : N ≠ 0) :
    padicValNat p (p * N) = padicValNat p N + 1 := by
  rw [padicValNat.mul (Fact.out : p.Prime).ne_zero hN,
      padicValNat.self (Fact.out : p.Prime).one_lt, add_comm]

lemma pCongr_zero_of_isPInt {p : ℕ} {x : ℚ} (h : IsPInt p x) :
    PCongr p 0 x 0 :=
  pCongr_zero_iff_isPInt.mpr h

/-- `v_p(∑_{q < N} C(N+q,q)³) ≥ v_p(N)`. -/
lemma sum_choose_cube_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ {N : ℕ}, 0 < N →
      PCongr p (padicValNat p N)
        (∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    by_cases hdvd : p ∣ N
    · obtain ⟨N', rfl⟩ := hdvd
      have hN' : 0 < N' := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        subst h0
        exact hN.ne' (by simp)
      have hN'lt : N' < p * N' := by
        have : 1 < p := hp.one_lt
        nlinarith
      have hA : N' ≠ 0 := hN'.ne'
      -- C((p N') + (p t + r), p t + r) = C(p(N'+t)+r, p t + r)
      have hterm : ∀ t ∈ range N', ∀ r ∈ range p,
          PCongr p (padicValNat p (p * N'))
            ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3)
            ((((N' + t).choose t : ℚ) ^ 3)) := by
        intro t ht r hr
        have hrlt : r < p := mem_range.mp hr
        have hBA : t ≤ N' + t := Nat.le_add_left _ _
        have hApos : N' + t ≠ 0 := (Nat.add_pos_left hN' t).ne'
        have hidx : p * N' + (p * t + r) = p * (N' + t) + r := by
          rw [Nat.mul_add, add_assoc]
        have hC := choose_p_shift_cube_pCongr (A := N' + t) (B := t) (r := r)
          hp hp5 hBA hApos hrlt
        have hAB : (N' + t) - t = N' := Nat.add_sub_cancel _ _
        rw [hAB] at hC
        have hv : (1 + padicValNat p N' : ℤ) = padicValNat p (p * N') := by
          rw [padicValNat_mul_p hA]; push_cast; ring
        rw [hidx]
        simpa [hv] using hC
      have hsum :
          PCongr p (padicValNat p (p * N'))
            (∑ t ∈ range N', ∑ r ∈ range p,
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
            (∑ t ∈ range N', ∑ r ∈ range p,
              (((N' + t).choose t : ℚ) ^ 3)) :=
        pCongr_sum (fun t ht => pCongr_sum (fun r hr => hterm t ht r hr))
      have hrhs :
          ∑ t ∈ range N', ∑ r ∈ range p, (((N' + t).choose t : ℚ) ^ 3) =
            (p : ℚ) * ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3) := by
        simp [sum_const, card_range, nsmul_eq_mul, ← mul_sum]
      have hlhs :
          ∑ q ∈ range (p * N'), (((p * N' + q).choose q : ℚ) ^ 3) =
            ∑ t ∈ range N', ∑ r ∈ range p,
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3) :=
        sum_range_mul p N' hp.pos _
      rw [hlhs]
      have hsum' := hsum
      rw [hrhs] at hsum'
      -- RHS = p * F(N') has val ≥ 1 + v(N') = v(p N')
      have hF := ih N' hN'lt hN'
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      have hFI : IsPInt p (∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) :=
        isPInt_sum fun _ _ => isPInt_pow (isPInt_nat p _) 3
      have hR : PCongr p (1 + padicValNat p N')
          ((p : ℚ) * ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 :=
        pCongr_mul_zero hp1 hF
      have hvN : (padicValNat p (p * N') : ℤ) = 1 + padicValNat p N' := by
        rw [padicValNat_mul_p hA]; push_cast; ring
      have hR' : PCongr p (padicValNat p (p * N'))
          ((p : ℚ) * ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        simpa [hvN] using hR
      exact pCongr_trans hsum' hR'
    · have hv0 : padicValNat p N = 0 :=
        padicValNat.eq_zero_of_not_dvd hdvd
      have hI : IsPInt p (∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3) :=
        isPInt_sum fun _ _ => isPInt_pow (isPInt_nat p _) 3
      simpa [hv0] using pCongr_zero_of_isPInt hI

lemma sum_range_cast (n : ℕ) :
    ∑ r ∈ range n, (r : ℚ) = (n : ℚ) * ((n - 1 : ℕ) : ℚ) / 2 := by
  have h := sum_range_id_mul_two n
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have : (∑ r ∈ range n, (r : ℚ)) * 2 =
      (n : ℚ) * ((n - 1 : ℕ) : ℚ) := by
    rw [← Nat.cast_sum, ← Nat.cast_two, ← Nat.cast_mul]
    exact_mod_cast h
  exact (eq_div_iff h2).mpr this

lemma sum_pt_add_r (p t : ℕ) :
    ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) =
      (p : ℚ) ^ 2 * t + (p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2 := by
  have : ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) =
      ∑ r ∈ range p, ((p : ℚ) * t + (r : ℚ)) := by
    refine sum_congr rfl fun r _ => by push_cast; rfl
  rw [this, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_range_cast]
  ring

/-- `v_p(∑_{q < N} q · C(N+q,q)³) ≥ v_p(N)`. -/
lemma sum_q_choose_cube_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ {N : ℕ}, 0 < N →
      PCongr p (padicValNat p N)
        (∑ q ∈ range N, (q : ℚ) * ((N + q).choose q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    by_cases hdvd : p ∣ N
    · obtain ⟨N', rfl⟩ := hdvd
      have hN' : 0 < N' := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        subst h0
        exact hN.ne' (by simp)
      have hN'lt : N' < p * N' := by
        have : 1 < p := hp.one_lt
        nlinarith
      have hA : N' ≠ 0 := hN'.ne'
      have hterm : ∀ t ∈ range N', ∀ r ∈ range p,
          PCongr p (padicValNat p (p * N'))
            (((p * t + r : ℕ) : ℚ) *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
            (((p * t + r : ℕ) : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) := by
        intro t ht r hr
        have hrlt : r < p := mem_range.mp hr
        have hBA : t ≤ N' + t := Nat.le_add_left _ _
        have hApos : N' + t ≠ 0 := (Nat.add_pos_left hN' t).ne'
        have hidx : p * N' + (p * t + r) = p * (N' + t) + r := by
          rw [Nat.mul_add, add_assoc]
        have hC := choose_p_shift_cube_pCongr (A := N' + t) (B := t) (r := r)
          hp hp5 hBA hApos hrlt
        have hAB : (N' + t) - t = N' := Nat.add_sub_cancel _ _
        rw [hAB] at hC
        have hv : (1 + padicValNat p N' : ℤ) = padicValNat p (p * N') := by
          rw [padicValNat_mul_p hA]; push_cast; ring
        have hC' : PCongr p (padicValNat p (p * N'))
            ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3)
            (((N' + t).choose t : ℚ) ^ 3) := by
          rw [hidx]
          simpa [hv] using hC
        have hprefI : IsPInt p ((p * t + r : ℕ) : ℚ) := isPInt_nat p _
        have hsmallI : IsPInt p (((N' + t).choose t : ℚ) ^ 3) :=
          isPInt_pow (isPInt_nat p _) 3
        exact pCongr_mul
          (pCongr_refl p (padicValNat p (p * N')) ((p * t + r : ℕ) : ℚ))
          hC' hprefI hsmallI
      have hsum :=
        pCongr_sum (s := range N')
          (fun t ht => pCongr_sum (s := range p)
            (fun r hr => hterm t ht r hr))
      have hlhs :
          ∑ q ∈ range (p * N'),
              (q : ℚ) * (((p * N' + q).choose q : ℚ) ^ 3) =
            ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) *
                ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3) := by
        simpa using sum_range_mul p N' hp.pos
          (fun q => (q : ℚ) * (((p * N' + q).choose q : ℚ) ^ 3))
      -- Inner sum over r: ∑_r (pt+r) C_small³ = (p² t + p(p-1)/2) C_small³
      have hrhs :
          ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) * (((N' + t).choose t : ℚ) ^ 3) =
            (p : ℚ) ^ 2 * ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
              ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
                ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3) := by
        have hinner : ∀ t,
            ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) * (((N' + t).choose t : ℚ) ^ 3) =
              ((p : ℚ) ^ 2 * (t : ℚ) + (p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
                (((N' + t).choose t : ℚ) ^ 3) := by
          intro t
          have hfactor :
              ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) * (((N' + t).choose t : ℚ) ^ 3) =
                (((N' + t).choose t : ℚ) ^ 3) *
                  ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) := by
            rw [Finset.mul_sum]
            refine sum_congr rfl fun r _ => mul_comm _ _
          rw [hfactor, sum_pt_add_r]
          ring
        rw [sum_congr rfl fun t _ => hinner t]
        have :
            ∑ t ∈ range N',
                ((p : ℚ) ^ 2 * (t : ℚ) + (p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
                  (((N' + t).choose t : ℚ) ^ 3) =
              ∑ t ∈ range N',
                  ((p : ℚ) ^ 2 * ((t : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) +
                    ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
                      (((N' + t).choose t : ℚ) ^ 3)) := by
          refine sum_congr rfl fun t _ => by ring
        rw [this, sum_add_distrib, ← mul_sum, ← mul_sum]
      rw [hlhs]
      have hsum' : PCongr p (padicValNat p (p * N'))
          (∑ t ∈ range N', ∑ r ∈ range p,
            ((p * t + r : ℕ) : ℚ) *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
          ((p : ℚ) ^ 2 * ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
            ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
              ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) := by
        rw [hrhs] at hsum
        exact hsum
      have hF := sum_choose_cube_val hp hp5 hN'
      have hD := ih N' hN'lt hN'
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      have hp2 : PCongr p 2 ((p : ℚ) ^ 2) 0 := by simpa using pCongr_p_pow (p := p) 2
      have hterm1 : PCongr p (2 + padicValNat p N')
          ((p : ℚ) ^ 2 * ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) 0 :=
        pCongr_mul_zero hp2 hD
      have h2inv : IsPInt p ((2 : ℚ)⁻¹) := isPInt_two_inv hp hp5
      have hp1' : PCongr p 1 ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) 0 := by
        have hrest : IsPInt p (((p - 1 : ℕ) : ℚ) * (2 : ℚ)⁻¹) :=
          isPInt_mul (isPInt_nat p _) h2inv
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using
          pCongr_mul_isPInt hp1 hrest
      have hterm2 : PCongr p (1 + padicValNat p N')
          (((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
            ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 :=
        pCongr_mul_zero hp1' hF
      have hvN : (padicValNat p (p * N') : ℤ) = 1 + padicValNat p N' := by
        rw [padicValNat_mul_p hA]; push_cast; ring
      have hle1 : (padicValNat p (p * N') : ℤ) ≤ 2 + padicValNat p N' := by
        rw [hvN]; linarith
      have hle2 : (padicValNat p (p * N') : ℤ) ≤ 1 + padicValNat p N' := by
        rw [hvN]
      have hR : PCongr p (padicValNat p (p * N'))
          ((p : ℚ) ^ 2 * ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
            ((p : ℚ) * ((p - 1 : ℕ) : ℚ) / 2) *
              ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        simpa using
          pCongr_add (pCongr_of_le hle1 hterm1) (pCongr_of_le hle2 hterm2)
      exact pCongr_trans hsum' hR
    · have hv0 : padicValNat p N = 0 :=
        padicValNat.eq_zero_of_not_dvd hdvd
      have hI : IsPInt p
          (∑ q ∈ range N, (q : ℚ) * ((N + q).choose q : ℚ) ^ 3) :=
        isPInt_sum fun _ _ =>
          isPInt_mul (isPInt_nat p _) (isPInt_pow (isPInt_nat p _) 3)
      simpa [hv0] using pCongr_zero_of_isPInt hI

lemma sum_N_add_two_q_choose_cube_val {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (padicValNat p N)
      (∑ q ∈ range N, ((N + 2 * q : ℕ) : ℚ) * ((N + q).choose q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA := sum_choose_cube_val (p := p) hp hp5 hN
  have hD := sum_q_choose_cube_val (p := p) hp hp5 hN
  have heq :
      ∑ q ∈ range N, ((N + 2 * q : ℕ) : ℚ) * ((N + q).choose q : ℚ) ^ 3 =
        (N : ℚ) * ∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3 +
          (2 : ℚ) * ∑ q ∈ range N, (q : ℚ) * ((N + q).choose q : ℚ) ^ 3 := by
    have hterm : ∀ q, ((N + 2 * q : ℕ) : ℚ) * ((N + q).choose q : ℚ) ^ 3 =
        (N : ℚ) * ((N + q).choose q : ℚ) ^ 3 +
          (2 : ℚ) * ((q : ℚ) * ((N + q).choose q : ℚ) ^ 3) := by
      intro q; push_cast; ring
    rw [sum_congr rfl fun q _ => hterm q, sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [heq]
  have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
  have hsumI : IsPInt p (∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3) :=
    isPInt_sum fun _ _ => isPInt_pow (isPInt_nat p _) 3
  have h1 : PCongr p (padicValNat p N)
      ((N : ℚ) * ∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3) 0 :=
    pCongr_mul_isPInt hN0 hsumI
  have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
  have h2' : PCongr p (padicValNat p N)
      ((2 : ℚ) * ∑ q ∈ range N, (q : ℚ) * ((N + q).choose q : ℚ) ^ 3) 0 := by
    simpa [mul_comm] using pCongr_mul_isPInt hD h2I
  simpa using pCongr_add h1 h2'

lemma rising_cube_identity {N q : ℕ} (hN : 0 < N) :
    ((N + q : ℕ) : ℚ) ^ 3 * (((N + q - 1).choose q : ℚ) ^ 3) =
      (N : ℚ) ^ 3 * ((N + q).choose q : ℚ) ^ 3 := by
  have h := rising_mul_identity (N := N) (q := q) hN
  have h3 := congrArg (fun x : ℚ => x ^ 3) h
  simpa [mul_pow] using h3

/-- The unaligned leading block `2 p³ H₂ ∑ M³ Cs³` has valuation `≥ 4+4v(N)`. -/
lemma unalign_H2_block_strong {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      ((2 : ℚ) * (p : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3)) *
        harmonicGen 2 (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hid :
      ∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) =
        (N : ℚ) ^ 3 * ∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3 := by
    have : ∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) =
        ∑ q ∈ range N, (N : ℚ) ^ 3 * ((N + q).choose q : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => rising_cube_identity hN
    rw [this, ← mul_sum]
  rw [hid]
  have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := pCongr_p_pow 3
  have hH2 : PCongr p 1 (harmonicGen 2 (p - 1)) 0 :=
    pCongr_zero_of_val (wolstenholme_two hp hp5)
  have hN3 : PCongr p (3 * padicValNat p N) ((N : ℚ) ^ 3) 0 := by
    have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
    simpa using pCongr_pow_zero (k := 3) hN0
  have hF := sum_choose_cube_val (p := p) hp hp5 hN
  have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
  have hmul := pCongr_mul_zero hp3 hH2
  have hmul' := pCongr_mul_zero hmul hN3
  have hmul'' := pCongr_mul_zero hmul' hF
  have hmul''' := pCongr_mul_isPInt hmul'' h2I
  have hle : (4 + 4 * padicValNat p N : ℤ) ≤
      3 + 1 + 3 * padicValNat p N + padicValNat p N := by omega
  have hmul0 : PCongr p (3 + 1 + 3 * padicValNat p N + padicValNat p N)
      ((2 : ℚ) * (p : ℚ) ^ 3 *
        ((N : ℚ) ^ 3 * ∑ q ∈ range N, ((N + q).choose q : ℚ) ^ 3) *
        harmonicGen 2 (p - 1)) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'''
  exact pCongr_of_le hle hmul0

/- ## Stronger unaligned Y-expansion -/

lemma choose_pM_t_pCongr_strong {p M t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (2 + 2 * padicValNat p M)
      (((p * M + t - 1).choose t : ℚ) - ((p : ℚ) * M / t)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have hpm : 1 ≤ p * M := Nat.mul_le_mul hp.pos hM
  rw [choose_pm_t_one_add htpos hpm]
  have hcast : (p * M : ℚ) / t = (p : ℚ) * M / t := by push_cast; rfl
  rw [hcast]
  set s := Icc 1 (t - 1)
  set x : ℕ → ℚ := fun j => (p : ℚ) * M / ((t : ℚ) - j)
  have hxeq :
      ∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) =
        ∏ j ∈ s, (1 + x j) := by
    refine prod_congr rfl fun j _ => by simp [s, x]
  have hα : (0 : ℤ) ≤ 1 + padicValNat p M :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hx : ∀ j ∈ s, PCongr p (1 + padicValNat p M) (x j) 0 := by
    intro j hj
    have ⟨hj1, hj2⟩ := mem_Icc.mp hj
    have htjN : t - j ∈ Icc 1 (p - 1) := by
      have : 1 ≤ t - j := by omega
      have : t - j ≤ p - 1 := by
        have := (mem_Icc.mp ht).2; omega
      exact mem_Icc.mpr ⟨by omega, this⟩
    have hcastj : (t : ℚ) - j = ((t - j : ℕ) : ℚ) :=
      (nat_cast_sub_eq (by omega)).symm
    have hpM : PCongr p (1 + padicValNat p M) ((p : ℚ) * M) 0 := by
      have hM0 : PCongr p (padicValNat p M) (M : ℚ) 0 := pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [add_comm] using pCongr_mul_zero hp1 hM0
    have hinv : IsPInt p (((t : ℚ) - j)⁻¹) := by
      rw [hcastj]; exact isPInt_inv_of_mem_Icc hp htjN
    simpa [x, div_eq_mul_inv, mul_assoc] using pCongr_mul_isPInt hpM hinv
  have hxI : ∀ j ∈ s, IsPInt p (x j) :=
    fun j hj => isPInt_of_pCongr hα (hx j hj)
  have hprod : PCongr p (1 + padicValNat p M)
      (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j))) 1 := by
    rw [hxeq]
    refine pCongr_prod_one_add_of (α := 1 + padicValNat p M)
      (β := 1 + padicValNat p M) (γ := 2 * (1 + padicValNat p M))
      (δ := 1 + padicValNat p M)
      hp hp5 hα hx hxI (pCongr_sum_zero hx) ?_ le_rfl ?_ ?_ ?_
    · refine pCongr_sum_zero ?_
      intro j hj
      simpa [pow_two, two_mul] using pCongr_mul_zero (hx j hj) (hx j hj)
    · nlinarith [hα]
    · nlinarith [hα]
    · nlinarith [hα]
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have ha : PCongr p (1 + padicValNat p M) ((p : ℚ) * M / t) 0 := by
    have hpM : PCongr p (1 + padicValNat p M) ((p : ℚ) * M) 0 := by
      have hM0 : PCongr p (padicValNat p M) (M : ℚ) 0 := pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [add_comm] using pCongr_mul_zero hp1 hM0
    have hinv : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
    simpa [div_eq_mul_inv] using pCongr_mul_isPInt hpM hinv
  have hdiff : PCongr p (1 + padicValNat p M)
      (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) - 1) 0 :=
    pCongr_sub_zero hprod
  have heq : ((p : ℚ) * M / t) *
        ∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) -
      (p : ℚ) * M / t =
      ((p : ℚ) * M / t) *
        (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) - 1) := by
    ring
  rw [heq]
  exact pCongr_of_le (by
      have : (2 + 2 * padicValNat p M : ℤ) ≤
          (1 + padicValNat p M) + (1 + padicValNat p M) := by omega
      exact this)
    (pCongr_mul_zero ha hdiff)

lemma pCongr_cube_diff_of {p : ℕ} [Fact p.Prime] {α : ℤ} {x a : ℚ}
    (hα : 0 ≤ α) (hxa : PCongr p (2 * α) (x - a) 0)
    (ha : PCongr p α a 0) (hx : PCongr p α x 0) :
    PCongr p (4 * α) (x ^ 3 - a ^ 3) 0 := by
  have hdiff : x ^ 3 - a ^ 3 = (x - a) * (x ^ 2 + x * a + a ^ 2) := by ring
  rw [hdiff]
  have hsq : PCongr p (2 * α) (x ^ 2 + x * a + a ^ 2) 0 := by
    have h1 : PCongr p (2 * α) (x ^ 2) 0 := by
      simpa [pow_two, two_mul] using pCongr_mul_zero hx hx
    have h2 : PCongr p (2 * α) (x * a) 0 := by
      simpa [two_mul] using pCongr_mul_zero hx ha
    have h3 : PCongr p (2 * α) (a ^ 2) 0 := by
      simpa [pow_two, two_mul] using pCongr_mul_zero ha ha
    simpa [add_assoc] using pCongr_add (pCongr_add h1 h2) h3
  have hmul := pCongr_mul_zero hxa hsq
  have : (4 * α : ℤ) = 2 * α + 2 * α := by ring
  simpa [this] using hmul

lemma unalign_Y3_pCongr_strong {p M t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (4 + 4 * padicValNat p M)
      ((((p * M + t - 1).choose t : ℚ) ^ 3) -
        (((p : ℚ) * M / t) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxa := choose_pM_t_pCongr_strong hp hp5 hM ht
  have ha : PCongr p (1 + padicValNat p M) ((p : ℚ) * M / t) 0 := by
    have hM0 : PCongr p (padicValNat p M) (M : ℚ) 0 := pCongr_coe_val
    have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
    have hpM := pCongr_mul_zero hp1 hM0
    have hinv : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
    simpa [div_eq_mul_inv, add_comm] using pCongr_mul_isPInt hpM hinv
  have hx : PCongr p (1 + padicValNat p M)
      ((p * M + t - 1).choose t : ℚ) 0 := by
    have : ((p * M + t - 1).choose t : ℚ) =
        (((p * M + t - 1).choose t : ℚ) - (p : ℚ) * M / t) +
          (p : ℚ) * M / t := by ring
    rw [this]
    have hxa' := pCongr_of_le (by
        have : (1 + padicValNat p M : ℤ) ≤ 2 + 2 * padicValNat p M := by omega
        exact this) hxa
    simpa using pCongr_add hxa' ha
  have h := pCongr_cube_diff_of (α := 1 + padicValNat p M)
    (add_nonneg (by norm_num) (Nat.cast_nonneg _))
    (by
      have : (2 * (1 + padicValNat p M) : ℤ) = 2 + 2 * padicValNat p M := by ring
      simpa [this] using hxa)
    ha hx
  have : (4 * (1 + padicValNat p M) : ℤ) = 4 + 4 * padicValNat p M := by ring
  simpa [this] using h

lemma unalign_X3_pCongr_strong {p M B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBM : B < M) :
    PCongr p (3 + padicValNat p M + padicValNat p B + padicValNat p (M - B))
      ((((p * M - 1).choose (p * B) : ℚ) ^ 3) -
        ((((M - 1).choose B : ℚ) ^ 3))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := choose_aligned_JK_strong (A := M) (B := B) hp hp5 hBM
  have h' : PCongr p (3 + padicValNat p M + padicValNat p B + padicValNat p (M - B))
      (((p * M - 1).choose (p * B) : ℚ) / ((M - 1).choose B : ℚ)) 1 := by
    have hidx1 : M * p = p * M := mul_comm _ _
    have hidx2 : B * p = p * B := mul_comm _ _
    simpa [hidx1, hidx2] using h
  have hden : ((M - 1).choose B : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.le_pred_of_lt hBM)).ne'
  have hX := pCongr_mul_denom hden h'
  have hpow := pCongr_pow_of 3 hX (isPInt_nat p _) (isPInt_nat p _)
  have hle : (3 + padicValNat p M + padicValNat p B + padicValNat p (M - B) : ℤ) ≤
      3 + padicValNat p M + padicValNat p B + padicValNat p (M - B) +
        padicValRat p ((M - 1).choose B : ℚ) := by
    have : (0 : ℤ) ≤ padicValRat p ((M - 1).choose B : ℚ) := by
      rw [padicValRat.of_nat]; exact Nat.cast_nonneg _
    linarith
  exact pCongr_sub_zero (pCongr_of_le hle hpow)

lemma choose_pB_t_pCongr_strong {p B t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (1 + padicValNat p B) ((p * B + t).choose t : ℚ) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  rw [choose_pB_t_one_add' htpos]
  set s := Icc 1 t
  set x : ℕ → ℚ := fun i => (p : ℚ) * B / i
  have hα : (0 : ℤ) ≤ 1 + padicValNat p B :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hx : ∀ i ∈ s, PCongr p (1 + padicValNat p B) (x i) 0 := by
    intro i hi
    have hiI : i ∈ Icc 1 (p - 1) := by
      have ⟨hi1, hi2⟩ := mem_Icc.mp hi
      exact mem_Icc.mpr ⟨hi1, le_trans hi2 (mem_Icc.mp ht).2⟩
    have hpB : PCongr p (1 + padicValNat p B) ((p : ℚ) * B) 0 := by
      have hB : PCongr p (padicValNat p B) (B : ℚ) 0 := pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [add_comm] using pCongr_mul_zero hp1 hB
    have hinv : IsPInt p ((i : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp hiI
    simpa [x, div_eq_mul_inv] using pCongr_mul_isPInt hpB hinv
  have hxI : ∀ i ∈ s, IsPInt p (x i) :=
    fun i hi => isPInt_of_pCongr hα (hx i hi)
  have hxeq : ∏ i ∈ Icc 1 t, (1 + (p * B : ℚ) / i) = ∏ i ∈ s, (1 + x i) := by
    refine prod_congr rfl fun i _ => by simp [x]
  rw [hxeq]
  refine pCongr_prod_one_add_of (α := 1 + padicValNat p B)
    (β := 1 + padicValNat p B) (γ := 2 * (1 + padicValNat p B))
    (δ := 1 + padicValNat p B)
    hp hp5 hα hx hxI (pCongr_sum_zero hx) ?_ le_rfl ?_ ?_ ?_
  · refine pCongr_sum_zero ?_
    intro i hi
    simpa [pow_two, two_mul] using pCongr_mul_zero (hx i hi) (hx i hi)
  · nlinarith [hα]
  · nlinarith [hα]
  · nlinarith [hα]

lemma unalign_Zinv3_pCongr_strong {p B t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (1 + padicValNat p B) ((((p * B + t).choose t : ℚ) ^ 3)⁻¹) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := choose_pB_t_pCongr_strong (B := B) hp hp5 ht
  have hZ0 : ((p * B + t).choose t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (Nat.le_add_left t (p * B))).ne'
  have hZI : IsPInt p ((p * B + t).choose t : ℚ) := isPInt_nat p _
  have hZ3 := pCongr_pow_of 3 hZ hZI (isPInt_one p)
  have hm : (1 : ℤ) ≤ 1 + padicValNat p B := by
    have : (0 : ℤ) ≤ padicValNat p B := Nat.cast_nonneg _
    linarith
  exact pCongr_inv_one hm hZ3 (pow_ne_zero 3 hZ0)

/- ## Product expansion keeping the linear term -/

lemma pCongr_prod_one_add_linear {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {x : ℕ → ℚ}
    {α : ℤ} (hp : p.Prime) (hp5 : 5 ≤ p) (hα : 0 ≤ α)
    (hx : ∀ j ∈ s, PCongr p α (x j) 0)
    (hxI : ∀ j ∈ s, IsPInt p (x j)) :
    PCongr p (2 * α)
      (∏ j ∈ s, (1 + x j) - 1 - ∑ j ∈ s, x j) 0 := by
  have hR : PCongr p (3 * α) (prodRemainder s x) 0 :=
    pCongr_prodRemainder_of hp hp5 hα hx hxI
  have hR' : PCongr p (2 * α) (prodRemainder s x) 0 :=
    pCongr_of_le (by nlinarith [hα]) hR
  have hsum : PCongr p α (∑ j ∈ s, x j) 0 := pCongr_sum_zero hx
  have hsum2 : PCongr p (2 * α) (∑ j ∈ s, x j ^ 2) 0 := by
    refine pCongr_sum_zero ?_
    intro j hj
    simpa [pow_two, two_mul] using pCongr_mul_zero (hx j hj) (hx j hj)
  have he2 : PCongr p (2 * α)
      (((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2) 0 := by
    have hsq : PCongr p (2 * α) ((∑ j ∈ s, x j) ^ 2) 0 := by
      simpa [pow_two, two_mul] using pCongr_mul_zero hsum hsum
    have hsub : PCongr p (2 * α) ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) 0 := by
      simpa using pCongr_sub hsq hsum2
    exact pCongr_div_two hp hp5 hsub
  have hdecomp : ∏ j ∈ s, (1 + x j) - 1 - ∑ j ∈ s, x j =
      prodRemainder s x + ((∑ j ∈ s, x j) ^ 2 - ∑ j ∈ s, x j ^ 2) / 2 := by
    unfold prodRemainder; ring
  rw [hdecomp]
  simpa using pCongr_add hR' he2


lemma choose_pM_t_linear {p M t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (2 + 2 * padicValNat p M)
      (∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) -
        1 - ((p : ℚ) * M) *
          ∑ j ∈ Icc 1 (t - 1), (1 : ℚ) / ((t : ℚ) - j)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := Icc 1 (t - 1)
  set x : ℕ → ℚ := fun j => (p : ℚ) * M / ((t : ℚ) - j)
  have hα : (0 : ℤ) ≤ 1 + padicValNat p M :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hx : ∀ j ∈ s, PCongr p (1 + padicValNat p M) (x j) 0 := by
    intro j hj
    have ⟨hj1, hj2⟩ := mem_Icc.mp hj
    have htjN : t - j ∈ Icc 1 (p - 1) := by
      have : 1 ≤ t - j := by omega
      have : t - j ≤ p - 1 := by
        have := (mem_Icc.mp ht).2; omega
      exact mem_Icc.mpr ⟨by omega, this⟩
    have hcastj : (t : ℚ) - j = ((t - j : ℕ) : ℚ) :=
      (nat_cast_sub_eq (by omega)).symm
    have hpM : PCongr p (1 + padicValNat p M) ((p : ℚ) * M) 0 := by
      have hM0 : PCongr p (padicValNat p M) (M : ℚ) 0 := pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [add_comm] using pCongr_mul_zero hp1 hM0
    have hinv : IsPInt p (((t : ℚ) - j)⁻¹) := by
      rw [hcastj]; exact isPInt_inv_of_mem_Icc hp htjN
    simpa [x, div_eq_mul_inv, mul_assoc] using pCongr_mul_isPInt hpM hinv
  have hxI : ∀ j ∈ s, IsPInt p (x j) :=
    fun j hj => isPInt_of_pCongr hα (hx j hj)
  have hlin := pCongr_prod_one_add_linear (s := s) (x := x) hp hp5 hα hx hxI
  have hxeq : ∏ j ∈ Icc 1 (t - 1), (1 + (p * M : ℚ) / ((t : ℚ) - j)) =
      ∏ j ∈ s, (1 + x j) := rfl
  have hsumx : ∑ j ∈ s, x j =
      ((p : ℚ) * M) * ∑ j ∈ Icc 1 (t - 1), (1 : ℚ) / ((t : ℚ) - j) := by
    have hxj : ∀ j, x j = ((p : ℚ) * M) * ((1 : ℚ) / ((t : ℚ) - j)) := by
      intro j; simp [x, div_eq_mul_inv, mul_assoc]
    simp only [hxj, ← mul_sum, s]
  have hmod : (2 * (1 + padicValNat p M) : ℤ) = 2 + 2 * padicValNat p M := by ring
  rw [hxeq, ← hsumx, ← hmod]
  exact hlin

lemma choose_pB_t_linear {p B t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (2 + 2 * padicValNat p B)
      (∏ i ∈ Icc 1 t, (1 + (p * B : ℚ) / i) -
        1 - ((p : ℚ) * B) * harmonicGen 1 t) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := Icc 1 t
  set x : ℕ → ℚ := fun i => (p : ℚ) * B / i
  have hα : (0 : ℤ) ≤ 1 + padicValNat p B :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hx : ∀ i ∈ s, PCongr p (1 + padicValNat p B) (x i) 0 := by
    intro i hi
    have hiI : i ∈ Icc 1 (p - 1) := by
      have ⟨hi1, hi2⟩ := mem_Icc.mp hi
      exact mem_Icc.mpr ⟨hi1, le_trans hi2 (mem_Icc.mp ht).2⟩
    have hpB : PCongr p (1 + padicValNat p B) ((p : ℚ) * B) 0 := by
      have hB : PCongr p (padicValNat p B) (B : ℚ) 0 := pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [add_comm] using pCongr_mul_zero hp1 hB
    have hinv : IsPInt p ((i : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp hiI
    simpa [x, div_eq_mul_inv] using pCongr_mul_isPInt hpB hinv
  have hxI : ∀ i ∈ s, IsPInt p (x i) :=
    fun i hi => isPInt_of_pCongr hα (hx i hi)
  have hlin := pCongr_prod_one_add_linear (s := s) (x := x) hp hp5 hα hx hxI
  have hxeq : ∏ i ∈ Icc 1 t, (1 + (p * B : ℚ) / i) = ∏ i ∈ s, (1 + x i) := rfl
  have hsumx : ∑ i ∈ s, x i = ((p : ℚ) * B) * harmonicGen 1 t := by
    have hxi : ∀ i, x i = ((p : ℚ) * B) * ((1 : ℚ) / (i : ℚ)) := by
      intro i; simp [x, div_eq_mul_inv, mul_assoc]
    simp only [hxi, ← mul_sum, s, harmonicGen_one_Icc]
  have hmod : (2 * (1 + padicValNat p B) : ℤ) = 2 + 2 * padicValNat p B := by ring
  rw [hxeq, ← hsumx, ← hmod]
  exact hlin



lemma sum_pt_add_r_sq (p t : ℕ) :
    ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 2 =
      (p : ℚ) ^ 3 * (t : ℚ) ^ 2 +
        (p : ℚ) ^ 2 * (t : ℚ) * ((p : ℚ) - 1) +
          (p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6 := by
  have hcast : ∀ r, ((p * t + r : ℕ) : ℚ) = (p : ℚ) * t + (r : ℚ) := by
    intro r; push_cast; rfl
  have : ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 2 =
      ∑ r ∈ range p, ((p : ℚ) * t + (r : ℚ)) ^ 2 :=
    sum_congr rfl fun r _ => by rw [hcast]
  rw [this]
  have hexp : ∀ r : ℕ, ((p : ℚ) * t + (r : ℚ)) ^ 2 =
      ((p : ℚ) * t) ^ 2 + 2 * ((p : ℚ) * t) * (r : ℚ) + (r : ℚ) ^ 2 := by
    intro r; ring
  rw [sum_congr rfl fun r _ => hexp r, sum_add_distrib, sum_add_distrib]
  have h0 : ∑ r ∈ range p, ((p : ℚ) * t) ^ 2 =
      (p : ℚ) * ((p : ℚ) * t) ^ 2 := by
    simp [sum_const, card_range, nsmul_eq_mul]
  have h1 : ∑ r ∈ range p, 2 * ((p : ℚ) * t) * (r : ℚ) =
      2 * ((p : ℚ) * t) * ∑ r ∈ range p, (r : ℚ) := by
    simp only [mul_assoc, ← mul_sum]
  rw [h0, h1, sum_range_rat, sum_range_rat_sq]
  ring

lemma sum_q_sq_choose_cube_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ {N : ℕ}, 0 < N →
      PCongr p (padicValNat p N)
        (∑ q ∈ range N, (q : ℚ) ^ 2 * ((N + q).choose q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    by_cases hdvd : p ∣ N
    · obtain ⟨N', rfl⟩ := hdvd
      have hN' : 0 < N' := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        subst h0
        exact hN.ne' (by simp)
      have hN'lt : N' < p * N' := by
        have : 1 < p := hp.one_lt
        nlinarith
      have hA : N' ≠ 0 := hN'.ne'
      have hvN : (padicValNat p (p * N') : ℤ) = 1 + padicValNat p N' := by
        rw [padicValNat_mul_p hA]; push_cast; ring
      have hterm : ∀ t ∈ range N', ∀ r ∈ range p,
          PCongr p (padicValNat p (p * N'))
            (((p * t + r : ℕ) : ℚ) ^ 2 *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
            (((p * t + r : ℕ) : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3)) := by
        intro t ht r hr
        have hrlt : r < p := mem_range.mp hr
        have hBA : t ≤ N' + t := Nat.le_add_left _ _
        have hApos : N' + t ≠ 0 := (Nat.add_pos_left hN' t).ne'
        have hidx : p * N' + (p * t + r) = p * (N' + t) + r := by
          rw [Nat.mul_add, add_assoc]
        have hC := choose_p_shift_cube_pCongr (A := N' + t) (B := t) (r := r)
          hp hp5 hBA hApos hrlt
        have hAB : (N' + t) - t = N' := Nat.add_sub_cancel _ _
        rw [hAB] at hC
        have hC' : PCongr p (padicValNat p (p * N'))
            ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3)
            (((N' + t).choose t : ℚ) ^ 3) := by
          rw [hidx]
          simpa [hvN] using hC
        have hprefI : IsPInt p (((p * t + r : ℕ) : ℚ) ^ 2) :=
          isPInt_pow (isPInt_nat p _) 2
        have hsmallI : IsPInt p (((N' + t).choose t : ℚ) ^ 3) :=
          isPInt_pow (isPInt_nat p _) 3
        exact pCongr_mul
          (pCongr_refl p (padicValNat p (p * N')) (((p * t + r : ℕ) : ℚ) ^ 2))
          hC' hprefI hsmallI
      have hsum :=
        pCongr_sum (s := range N')
          (fun t ht => pCongr_sum (s := range p)
            (fun r hr => hterm t ht r hr))
      have hlhs :
          ∑ q ∈ range (p * N'),
              (q : ℚ) ^ 2 * (((p * N' + q).choose q : ℚ) ^ 3) =
            ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) ^ 2 *
                ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3) := by
        simpa using sum_range_mul p N' hp.pos
          (fun q => (q : ℚ) ^ 2 * (((p * N' + q).choose q : ℚ) ^ 3))
      have hrhs :
          ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) =
            (p : ℚ) ^ 3 * ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) +
              (p : ℚ) ^ 2 * ((p : ℚ) - 1) *
                ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
              ((p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
                ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3) := by
        have hinner : ∀ t,
            ∑ r ∈ range p,
                ((p * t + r : ℕ) : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) =
              (((N' + t).choose t : ℚ) ^ 3) *
                ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 2 := by
          intro t
          rw [Finset.mul_sum]
          refine sum_congr rfl fun r _ => mul_comm _ _
        rw [sum_congr rfl fun t _ => hinner t]
        have htj : ∀ t : ℕ,
            (((N' + t).choose t : ℚ) ^ 3) *
                ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 2 =
              ((p : ℚ) ^ 3 * (t : ℚ) ^ 2 +
                (p : ℚ) ^ 2 * (t : ℚ) * ((p : ℚ) - 1) +
                (p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
                  (((N' + t).choose t : ℚ) ^ 3) := by
          intro t
          rw [sum_pt_add_r_sq]
          ring
        rw [sum_congr rfl fun t _ => htj t]
        have hsplit : ∀ t : ℕ,
            ((p : ℚ) ^ 3 * (t : ℚ) ^ 2 +
              (p : ℚ) ^ 2 * (t : ℚ) * ((p : ℚ) - 1) +
              (p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
                (((N' + t).choose t : ℚ) ^ 3) =
              (p : ℚ) ^ 3 * ((t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3)) +
                (p : ℚ) ^ 2 * ((p : ℚ) - 1) *
                  ((t : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) +
                ((p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
                  (((N' + t).choose t : ℚ) ^ 3) := by
          intro t; ring
        rw [sum_congr rfl fun t _ => hsplit t, sum_add_distrib, sum_add_distrib,
            ← mul_sum, ← mul_sum, ← mul_sum]
      rw [hlhs]
      have hsum' : PCongr p (padicValNat p (p * N'))
          (∑ t ∈ range N', ∑ r ∈ range p,
            ((p * t + r : ℕ) : ℚ) ^ 2 *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
          ((p : ℚ) ^ 3 * ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) +
            (p : ℚ) ^ 2 * ((p : ℚ) - 1) *
              ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
            ((p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
              ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) := by
        rw [hrhs] at hsum
        exact hsum
      have hF := sum_choose_cube_val hp hp5 hN'
      have hD := sum_q_choose_cube_val hp hp5 hN'
      have hSq := ih N' hN'lt hN'
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      have hp2 : PCongr p 2 ((p : ℚ) ^ 2) 0 := by simpa using pCongr_p_pow (p := p) 2
      have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := by simpa using pCongr_p_pow (p := p) 3
      have hterm1 : PCongr p (3 + padicValNat p N')
          ((p : ℚ) ^ 3 * ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3)) 0 :=
        pCongr_mul_zero hp3 hSq
      have hterm2 : PCongr p (2 + padicValNat p N')
          ((p : ℚ) ^ 2 * ((p : ℚ) - 1) *
            ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        have hpm1 : IsPInt p ((p : ℚ) - 1) :=
          isPInt_sub (isPInt_nat p _) (isPInt_one p)
        have hmul := pCongr_mul_zero hp2 hD
        simpa [mul_comm, mul_left_comm, mul_assoc] using pCongr_mul_isPInt hmul hpm1
      have hterm3 : PCongr p (1 + padicValNat p N')
          (((p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
            ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        have h6I : IsPInt p ((6 : ℚ)⁻¹) := isPInt_six_inv hp hp5
        have hrest : IsPInt p
            (((p : ℚ) - 1) * (2 * (p : ℚ) - 1) * (6 : ℚ)⁻¹) := by
          refine isPInt_mul (isPInt_mul ?_ ?_) h6I
          · exact isPInt_sub (isPInt_nat p _) (isPInt_one p)
          · exact isPInt_sub (isPInt_mul (isPInt_nat p 2) (isPInt_nat p _))
              (isPInt_one p)
        have hp1rest : PCongr p 1
            ((p : ℚ) * (((p : ℚ) - 1) * (2 * (p : ℚ) - 1) * (6 : ℚ)⁻¹)) 0 :=
          pCongr_mul_isPInt hp1 hrest
        have hmul' := pCongr_mul_zero hp1rest hF
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
      have hle1 : (padicValNat p (p * N') : ℤ) ≤ 3 + padicValNat p N' := by
        rw [hvN]; linarith
      have hle2 : (padicValNat p (p * N') : ℤ) ≤ 2 + padicValNat p N' := by
        rw [hvN]; linarith
      have hle3 : (padicValNat p (p * N') : ℤ) ≤ 1 + padicValNat p N' := by
        rw [hvN]
      have hR : PCongr p (padicValNat p (p * N'))
          ((p : ℚ) ^ 3 * ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) +
            (p : ℚ) ^ 2 * ((p : ℚ) - 1) *
              ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
            ((p : ℚ) * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) / 6) *
              ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        simpa [add_assoc] using
          pCongr_add (pCongr_add (pCongr_of_le hle1 hterm1) (pCongr_of_le hle2 hterm2))
            (pCongr_of_le hle3 hterm3)
      exact pCongr_trans hsum' hR
    · have hv0 : padicValNat p N = 0 :=
        padicValNat.eq_zero_of_not_dvd hdvd
      have hI : IsPInt p
          (∑ q ∈ range N, (q : ℚ) ^ 2 * ((N + q).choose q : ℚ) ^ 3) :=
        isPInt_sum fun _ _ =>
          isPInt_mul (isPInt_pow (isPInt_nat p _) 2) (isPInt_pow (isPInt_nat p _) 3)
      simpa [hv0] using pCongr_zero_of_isPInt hI

lemma sum_pt_add_r_cube (p t : ℕ) :
    ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 3 =
      (p : ℚ) ^ 4 * (t : ℚ) ^ 3 +
        (3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1) * (t : ℚ) ^ 2 +
          (1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) * (t : ℚ) +
            ((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2 := by
  have hcast : ∀ r : ℕ, ((p * t + r : ℕ) : ℚ) = (p : ℚ) * t + (r : ℚ) := by
    intro r; push_cast; rfl
  have : ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 3 =
      ∑ r ∈ range p, ((p : ℚ) * t + (r : ℚ)) ^ 3 :=
    sum_congr rfl fun r _ => by rw [hcast]
  rw [this]
  have hexp : ∀ r : ℕ, ((p : ℚ) * t + (r : ℚ)) ^ 3 =
      ((p : ℚ) * t) ^ 3 + 3 * ((p : ℚ) * t) ^ 2 * (r : ℚ) +
        3 * ((p : ℚ) * t) * (r : ℚ) ^ 2 + (r : ℚ) ^ 3 := by
    intro r; ring
  rw [sum_congr rfl fun r _ => hexp r]
  simp only [sum_add_distrib]
  have h0 : ∑ r ∈ range p, ((p : ℚ) * t) ^ 3 = (p : ℚ) * ((p : ℚ) * t) ^ 3 := by
    simp [sum_const, card_range, nsmul_eq_mul]
  have h1 : ∑ r ∈ range p, 3 * ((p : ℚ) * t) ^ 2 * (r : ℚ) =
      3 * ((p : ℚ) * t) ^ 2 * ∑ r ∈ range p, (r : ℚ) := by
    simp only [mul_assoc, ← mul_sum]
  have h2 : ∑ r ∈ range p, 3 * ((p : ℚ) * t) * (r : ℚ) ^ 2 =
      3 * ((p : ℚ) * t) * ∑ r ∈ range p, (r : ℚ) ^ 2 := by
    simp only [mul_assoc, ← mul_sum]
  rw [h0, h1, h2, sum_range_rat, sum_range_rat_sq, sum_range_rat_cube]
  ring



lemma sum_q_cube_choose_cube_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ {N : ℕ}, 0 < N →
      PCongr p (padicValNat p N)
        (∑ q ∈ range N, (q : ℚ) ^ 3 * ((N + q).choose q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    by_cases hdvd : p ∣ N
    · obtain ⟨N', rfl⟩ := hdvd
      have hN' : 0 < N' := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        subst h0
        exact hN.ne' (by simp)
      have hN'lt : N' < p * N' := by
        have : 1 < p := hp.one_lt
        nlinarith
      have hA : N' ≠ 0 := hN'.ne'
      have hvN : (padicValNat p (p * N') : ℤ) = 1 + padicValNat p N' := by
        rw [padicValNat_mul_p hA]; push_cast; ring
      have hterm : ∀ t ∈ range N', ∀ r ∈ range p,
          PCongr p (padicValNat p (p * N'))
            (((p * t + r : ℕ) : ℚ) ^ 3 *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
            (((p * t + r : ℕ) : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3)) := by
        intro t ht r hr
        have hrlt : r < p := mem_range.mp hr
        have hBA : t ≤ N' + t := Nat.le_add_left _ _
        have hApos : N' + t ≠ 0 := (Nat.add_pos_left hN' t).ne'
        have hidx : p * N' + (p * t + r) = p * (N' + t) + r := by
          rw [Nat.mul_add, add_assoc]
        have hC := choose_p_shift_cube_pCongr (A := N' + t) (B := t) (r := r)
          hp hp5 hBA hApos hrlt
        have hAB : (N' + t) - t = N' := Nat.add_sub_cancel _ _
        rw [hAB] at hC
        have hC' : PCongr p (padicValNat p (p * N'))
            ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3)
            (((N' + t).choose t : ℚ) ^ 3) := by
          rw [hidx]
          simpa [hvN] using hC
        exact pCongr_mul
          (pCongr_refl p (padicValNat p (p * N')) (((p * t + r : ℕ) : ℚ) ^ 3))
          hC' (isPInt_pow (isPInt_nat p _) 3) (isPInt_pow (isPInt_nat p _) 3)
      have hsum :=
        pCongr_sum (s := range N')
          (fun t ht => pCongr_sum (s := range p)
            (fun r hr => hterm t ht r hr))
      have hlhs :
          ∑ q ∈ range (p * N'),
              (q : ℚ) ^ 3 * (((p * N' + q).choose q : ℚ) ^ 3) =
            ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) ^ 3 *
                ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3) := by
        simpa using sum_range_mul p N' hp.pos
          (fun q => (q : ℚ) ^ 3 * (((p * N' + q).choose q : ℚ) ^ 3))
      have hrhs :
          ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3) =
            (p : ℚ) ^ 4 * ∑ t ∈ range N', (t : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3) +
              ((3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1)) *
                ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) +
              ((1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1)) *
                ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
              (((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
                ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3) := by
        have hinner : ∀ t : ℕ,
            ∑ r ∈ range p,
                ((p * t + r : ℕ) : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3) =
              (((N' + t).choose t : ℚ) ^ 3) *
                ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 3 := by
          intro t
          rw [Finset.mul_sum]
          refine sum_congr rfl fun r _ => mul_comm _ _
        rw [sum_congr rfl fun t _ => hinner t]
        have htj : ∀ t : ℕ,
            (((N' + t).choose t : ℚ) ^ 3) *
                ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ 3 =
              ((p : ℚ) ^ 4 * (t : ℚ) ^ 3 +
                (3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1) * (t : ℚ) ^ 2 +
                (1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) *
                  (t : ℚ) +
                ((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
                  (((N' + t).choose t : ℚ) ^ 3) := by
          intro t
          rw [sum_pt_add_r_cube]
          ring
        rw [sum_congr rfl fun t _ => htj t]
        have hsplit : ∀ t : ℕ,
            ((p : ℚ) ^ 4 * (t : ℚ) ^ 3 +
              (3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1) * (t : ℚ) ^ 2 +
              (1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) *
                (t : ℚ) +
              ((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
                (((N' + t).choose t : ℚ) ^ 3) =
              (p : ℚ) ^ 4 * ((t : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3)) +
                ((3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1)) *
                  ((t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3)) +
                ((1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1)) *
                  ((t : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) +
                (((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
                  (((N' + t).choose t : ℚ) ^ 3) := by
          intro t; ring
        rw [sum_congr rfl fun t _ => hsplit t]
        rw [sum_add_distrib, sum_add_distrib, sum_add_distrib,
            ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
      rw [hlhs]
      have hsum' : PCongr p (padicValNat p (p * N'))
          (∑ t ∈ range N', ∑ r ∈ range p,
            ((p * t + r : ℕ) : ℚ) ^ 3 *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
          ((p : ℚ) ^ 4 * ∑ t ∈ range N', (t : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3) +
            ((3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1)) *
              ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) +
            ((1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1)) *
              ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
            (((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
              ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) := by
        rw [hrhs] at hsum
        exact hsum
      have hF := sum_choose_cube_val hp hp5 hN'
      have hD := sum_q_choose_cube_val hp hp5 hN'
      have hSq := sum_q_sq_choose_cube_val hp hp5 hN'
      have hCu := ih N' hN'lt hN'
      have h2I : IsPInt p ((2 : ℚ)⁻¹) := isPInt_two_inv hp hp5
      have hp2 : PCongr p 2 ((p : ℚ) ^ 2) 0 := by simpa using pCongr_p_pow (p := p) 2
      have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := by simpa using pCongr_p_pow (p := p) 3
      have hp4 : PCongr p 4 ((p : ℚ) ^ 4) 0 := by simpa using pCongr_p_pow (p := p) 4
      have hterm1 : PCongr p (4 + padicValNat p N')
          ((p : ℚ) ^ 4 * ∑ t ∈ range N', (t : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3)) 0 :=
        pCongr_mul_zero hp4 hCu
      have hterm2 : PCongr p (3 + padicValNat p N')
          ((3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1) *
            ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        have hrest : IsPInt p
            ((3 : ℚ) * (2 : ℚ)⁻¹ * ((p : ℚ) - 1)) :=
          isPInt_mul (isPInt_mul (isPInt_nat p 3) h2I)
            (isPInt_sub (isPInt_nat p _) (isPInt_one p))
        have hmul := pCongr_mul_zero hp3 hSq
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          pCongr_mul_isPInt hmul hrest
      have hterm3 : PCongr p (2 + padicValNat p N')
          ((1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1) *
            ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        have hrest : IsPInt p
            ((2 : ℚ)⁻¹ * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1)) :=
          isPInt_mul (isPInt_mul h2I (isPInt_sub (isPInt_nat p _) (isPInt_one p)))
            (isPInt_sub (isPInt_mul (isPInt_nat p 2) (isPInt_nat p _)) (isPInt_one p))
        have hmul := pCongr_mul_zero hp2 hD
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          pCongr_mul_isPInt hmul hrest
      have hterm4 : PCongr p (2 + padicValNat p N')
          ((((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
            ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        have heq : ((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2 =
            (p : ℚ) ^ 2 * ((((p : ℚ) - 1) * (2 : ℚ)⁻¹) ^ 2) := by
          field_simp
        rw [heq]
        have hrest : IsPInt p ((((p : ℚ) - 1) * (2 : ℚ)⁻¹) ^ 2) :=
          isPInt_pow (isPInt_mul (isPInt_sub (isPInt_nat p _) (isPInt_one p)) h2I) 2
        have hmul := pCongr_mul_zero hp2 hF
        simpa [mul_comm, mul_left_comm, mul_assoc] using pCongr_mul_isPInt hmul hrest
      have hle1 : (padicValNat p (p * N') : ℤ) ≤ 4 + padicValNat p N' := by
        rw [hvN]; linarith
      have hle2 : (padicValNat p (p * N') : ℤ) ≤ 3 + padicValNat p N' := by
        rw [hvN]; linarith
      have hle3 : (padicValNat p (p * N') : ℤ) ≤ 2 + padicValNat p N' := by
        rw [hvN]; linarith
      have hR : PCongr p (padicValNat p (p * N'))
          ((p : ℚ) ^ 4 * ∑ t ∈ range N', (t : ℚ) ^ 3 * (((N' + t).choose t : ℚ) ^ 3) +
            ((3 : ℚ) / 2 * (p : ℚ) ^ 3 * ((p : ℚ) - 1)) *
              ∑ t ∈ range N', (t : ℚ) ^ 2 * (((N' + t).choose t : ℚ) ^ 3) +
            ((1 : ℚ) / 2 * (p : ℚ) ^ 2 * ((p : ℚ) - 1) * (2 * (p : ℚ) - 1)) *
              ∑ t ∈ range N', (t : ℚ) * (((N' + t).choose t : ℚ) ^ 3) +
            (((p : ℚ) * ((p : ℚ) - 1) / 2) ^ 2) *
              ∑ t ∈ range N', (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        simpa [add_assoc] using
          pCongr_add (pCongr_add (pCongr_add
            (pCongr_of_le hle1 hterm1) (pCongr_of_le hle2 hterm2))
            (pCongr_of_le hle3 hterm3))
            (pCongr_of_le hle3 hterm4)
      exact pCongr_trans hsum' hR
    · have hv0 : padicValNat p N = 0 :=
        padicValNat.eq_zero_of_not_dvd hdvd
      have hI : IsPInt p
          (∑ q ∈ range N, (q : ℚ) ^ 3 * ((N + q).choose q : ℚ) ^ 3) :=
        isPInt_sum fun _ _ =>
          isPInt_mul (isPInt_pow (isPInt_nat p _) 3) (isPInt_pow (isPInt_nat p _) 3)
      simpa [hv0] using pCongr_zero_of_isPInt hI

/- ## General polynomial moments of `C(N+q,q)³` -/

/-- Deficit in the moment valuation: `1` iff `(p-1) ∣ k` and `k ≠ 0`. -/
def momentDeficit (p k : ℕ) : ℕ :=
  if p - 1 ∣ k ∧ k ≠ 0 then 1 else 0

lemma momentDeficit_le_one (p k : ℕ) : momentDeficit p k ≤ 1 := by
  unfold momentDeficit; split_ifs <;> simp

lemma momentDeficit_zero (p : ℕ) : momentDeficit p 0 = 0 := by
  simp [momentDeficit]

/-- `∑_{r < p} r^k` is divisible by `p` unless `k > 0` and `(p-1) ∣ k`. -/
lemma sum_zmod_pow {p k : ℕ} [Fact p.Prime] (hk : k ≠ 0) (hnd : ¬ (p - 1) ∣ k) :
    ∑ x : ZMod p, x ^ k = 0 := by
  classical
  have hunits : ∑ u : (ZMod p)ˣ, ((u : ZMod p) ^ k) = 0 := by
    rw [FiniteField.sum_pow_units (ZMod p) k, if_neg]
    simpa [ZMod.card] using hnd
  have hx0 : ∀ x ∈ (univ : Finset (ZMod p)) \ {0}, x ≠ 0 := by
    intro x hx
    simp at hx
    exact hx
  have himg : ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ k =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p) ^ k) := by
    refine sum_bij (fun x hx => (isUnit_iff_ne_zero.mpr (hx0 x hx)).unit)
      (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro a ha b hb heq
      simpa using congrArg Units.val heq
    · intro u _
      refine ⟨(u : ZMod p), ?_, ?_⟩
      · simp [Units.ne_zero]
      · exact Units.ext (by simp)
    · intro x hx
      simp
  rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton,
    zero_pow hk, add_zero, himg, hunits]

lemma sum_range_zmod {p : ℕ} [Fact p.Prime] [AddCommMonoid α] (f : ZMod p → α) :
    ∑ r ∈ range p, f (r : ZMod p) = ∑ x : ZMod p, f x := by
  refine sum_bij (fun r _ => (r : ZMod p)) (fun _ _ => mem_univ _) ?_ ?_ ?_
  · intro a ha b hb heq
    have ha' : a < p := mem_range.mp ha
    have hb' : b < p := mem_range.mp hb
    have hcoe : (a : ZMod p) = (b : ZMod p) := heq
    have : (a : ZMod p).val = (b : ZMod p).val := by rw [hcoe]
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
  · intro x _
    refine ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  · intro r _; rfl

lemma sum_range_pow_dvd {p k : ℕ} (hp : p.Prime)
    (h : k = 0 ∨ ¬ (p - 1) ∣ k) :
    p ∣ ∑ r ∈ range p, r ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases h with hk0 | hnd
  · subst hk0
    simp [pow_zero, sum_const, card_range]
  · have hk : k ≠ 0 := fun h0 => by subst h0; simp at hnd
    rw [← ZMod.natCast_eq_zero_iff]
    have hcast : ((∑ r ∈ range p, r ^ k : ℕ) : ZMod p) =
        ∑ r ∈ range p, (r : ZMod p) ^ k := by
      push_cast; rfl
    rw [hcast, sum_range_zmod (fun x => x ^ k), sum_zmod_pow hk hnd]

/-- Valuation of `∑_{r < p} r^k`: at least `1` except when `(p-1) ∣ k` and `k ≠ 0`. -/
def powSumVal (p k : ℕ) : ℕ :=
  if k = 0 ∨ ¬ (p - 1) ∣ k then 1 else 0

lemma powSumVal_add_deficit (p k : ℕ) :
    powSumVal p k + momentDeficit p k = 1 := by
  unfold powSumVal momentDeficit
  by_cases hk0 : k = 0
  · subst hk0; simp
  · by_cases hd : p - 1 ∣ k
    · simp [hk0, hd]
    · simp [hk0, hd]

lemma sum_range_pow_pCongr {p k : ℕ} (hp : p.Prime) :
    PCongr p (powSumVal p k) (∑ r ∈ range p, (r : ℚ) ^ k) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : ∑ r ∈ range p, (r : ℚ) ^ k =
      ((∑ r ∈ range p, r ^ k : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    refine sum_congr rfl fun r _ => (Nat.cast_pow (α := ℚ) r k).symm
  rw [hcast]
  by_cases h : k = 0 ∨ ¬ (p - 1) ∣ k
  · have hdiv := sum_range_pow_dvd hp h
    have hval : powSumVal p k = 1 := by simp [powSumVal, h]
    rw [hval]
    rcases eq_or_ne (∑ r ∈ range p, r ^ k) 0 with hz | hz
    · simp [hz, pCongr_refl]
    · have : 1 ≤ padicValNat p (∑ r ∈ range p, r ^ k) :=
        (padicValNat_dvd_iff_le hz).mp (by simpa using hdiv)
      exact pCongr_nat_of_val hz this
  · have hval : powSumVal p k = 0 := by
      simp only [powSumVal, h, ite_false]
    rw [hval]
    exact pCongr_zero_of_isPInt (isPInt_nat p _)

lemma momentDeficit_one (p : ℕ) (hp5 : 5 ≤ p) : momentDeficit p 1 = 0 := by
  unfold momentDeficit
  have : ¬ (p - 1) ∣ 1 := by
    intro h
    have : p - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) h
    omega
  simp [this]

lemma moment_expand_val_le (p k j : ℕ) (hp5 : 5 ≤ p) :
    ((1 : ℤ) - momentDeficit p k : ℤ) ≤
      j + powSumVal p (k - j) - momentDeficit p j := by
  have hs : powSumVal p (k - j) + momentDeficit p (k - j) = 1 :=
    powSumVal_add_deficit p (k - j)
  have hmain : momentDeficit p j + momentDeficit p (k - j) ≤
      j + momentDeficit p k := by
    have hj : j = 0 ∨ j = 1 ∨ 2 ≤ j := by omega
    rcases hj with hj | hj | hj
    · subst hj; simp [momentDeficit_zero]
    · subst hj
      rw [momentDeficit_one p hp5, zero_add]
      exact Nat.le_trans (momentDeficit_le_one p (k - 1)) (Nat.le_add_right _ _)
    · have h1 : momentDeficit p j ≤ 1 := momentDeficit_le_one p j
      have h2 : momentDeficit p (k - j) ≤ 1 := momentDeficit_le_one p (k - j)
      omega
  have hsZ : (powSumVal p (k - j) : ℤ) + momentDeficit p (k - j) = 1 := by
    exact_mod_cast hs
  have hmainZ : (momentDeficit p j : ℤ) + momentDeficit p (k - j) ≤
      (j : ℤ) + momentDeficit p k := by exact_mod_cast hmain
  linarith

lemma sum_pt_add_r_pow (p t k : ℕ) :
    ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ k =
      ∑ j ∈ range (k + 1),
        (k.choose j : ℚ) * ((p : ℚ) ^ j) * ((t : ℚ) ^ j) *
          ∑ r ∈ range p, (r : ℚ) ^ (k - j) := by
  have hcast : ∀ r, ((p * t + r : ℕ) : ℚ) = (p : ℚ) * t + (r : ℚ) := by
    intro r; push_cast; rfl
  have : ∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ k =
      ∑ r ∈ range p, ((p : ℚ) * t + (r : ℚ)) ^ k :=
    sum_congr rfl fun r _ => by rw [hcast]
  rw [this]
  have hexp : ∀ r : ℕ,
      ((p : ℚ) * t + (r : ℚ)) ^ k =
        ∑ j ∈ range (k + 1),
          (k.choose j : ℚ) * ((p : ℚ) * t) ^ j * (r : ℚ) ^ (k - j) := by
    intro r
    simpa [add_pow, mul_comm, mul_left_comm, mul_assoc] using
      (add_pow ((p : ℚ) * t) (r : ℚ) k)
  rw [sum_congr rfl fun r _ => hexp r, sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have : ∑ r ∈ range p,
      (k.choose j : ℚ) * ((p : ℚ) * t) ^ j * (r : ℚ) ^ (k - j) =
      (k.choose j : ℚ) * ((p : ℚ) * t) ^ j *
        ∑ r ∈ range p, (r : ℚ) ^ (k - j) := by
    simp only [mul_assoc, ← mul_sum]
  rw [this]
  ring

/-- `v_p(∑_{q < N} q^k C(N+q,q)³) ≥ v_p(N) - δ_k`. -/
lemma sum_q_pow_choose_cube_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ {N : ℕ}, 0 < N → ∀ (k : ℕ),
      PCongr p ((padicValNat p N : ℤ) - momentDeficit p k)
        (∑ q ∈ range N, (q : ℚ) ^ k * ((N + q).choose q : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN k
    by_cases hdvd : p ∣ N
    · obtain ⟨N', rfl⟩ := hdvd
      have hN' : 0 < N' := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        subst h0
        exact hN.ne' (by simp)
      have hN'lt : N' < p * N' := by
        have : 1 < p := hp.one_lt
        nlinarith
      have hA : N' ≠ 0 := hN'.ne'
      have hvN : (padicValNat p (p * N') : ℤ) = 1 + padicValNat p N' := by
        rw [padicValNat_mul_p hA]; push_cast; ring
      -- Replace big binomials by small ones at precision `v(p N')`.
      have hterm : ∀ t ∈ range N', ∀ r ∈ range p,
          PCongr p (padicValNat p (p * N'))
            (((p * t + r : ℕ) : ℚ) ^ k *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
            (((p * t + r : ℕ) : ℚ) ^ k * (((N' + t).choose t : ℚ) ^ 3)) := by
        intro t ht r hr
        have hrlt : r < p := mem_range.mp hr
        have hBA : t ≤ N' + t := Nat.le_add_left _ _
        have hApos : N' + t ≠ 0 := (Nat.add_pos_left hN' t).ne'
        have hidx : p * N' + (p * t + r) = p * (N' + t) + r := by
          rw [Nat.mul_add, add_assoc]
        have hC := choose_p_shift_cube_pCongr (A := N' + t) (B := t) (r := r)
          hp hp5 hBA hApos hrlt
        have hAB : (N' + t) - t = N' := Nat.add_sub_cancel _ _
        rw [hAB] at hC
        have hv : (1 + padicValNat p N' : ℤ) = padicValNat p (p * N') := by
          rw [padicValNat_mul_p hA]; push_cast; ring
        have hC' : PCongr p (padicValNat p (p * N'))
            ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3)
            (((N' + t).choose t : ℚ) ^ 3) := by
          rw [hidx]
          simpa [hv] using hC
        have hprefI : IsPInt p (((p * t + r : ℕ) : ℚ) ^ k) :=
          isPInt_pow (isPInt_nat p _) k
        have hsmallI : IsPInt p (((N' + t).choose t : ℚ) ^ 3) :=
          isPInt_pow (isPInt_nat p _) 3
        exact pCongr_mul
          (pCongr_refl p (padicValNat p (p * N')) (((p * t + r : ℕ) : ℚ) ^ k))
          hC' hprefI hsmallI
      have hsum :=
        pCongr_sum (s := range N')
          (fun t ht => pCongr_sum (s := range p)
            (fun r hr => hterm t ht r hr))
      have hlhs :
          ∑ q ∈ range (p * N'),
              (q : ℚ) ^ k * (((p * N' + q).choose q : ℚ) ^ 3) =
            ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) ^ k *
                ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3) := by
        simpa using sum_range_mul p N' hp.pos
          (fun q => (q : ℚ) ^ k * (((p * N' + q).choose q : ℚ) ^ 3))
      have hrhs :
          ∑ t ∈ range N', ∑ r ∈ range p,
              ((p * t + r : ℕ) : ℚ) ^ k * (((N' + t).choose t : ℚ) ^ 3) =
            ∑ j ∈ range (k + 1),
              (k.choose j : ℚ) * (p : ℚ) ^ j *
                (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                  ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3) := by
        have hinner : ∀ t : ℕ,
            ∑ r ∈ range p,
                ((p * t + r : ℕ) : ℚ) ^ k * (((N' + t).choose t : ℚ) ^ 3) =
              (∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ k) *
                (((N' + t).choose t : ℚ) ^ 3) := by
          intro t
          rw [Finset.sum_mul]
        rw [sum_congr rfl fun t _ => hinner t]
        have : ∑ t ∈ range N',
            (∑ r ∈ range p, ((p * t + r : ℕ) : ℚ) ^ k) *
              (((N' + t).choose t : ℚ) ^ 3) =
            ∑ t ∈ range N',
              (∑ j ∈ range (k + 1),
                (k.choose j : ℚ) * (p : ℚ) ^ j * (t : ℚ) ^ j *
                  ∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                (((N' + t).choose t : ℚ) ^ 3) :=
          sum_congr rfl fun t _ => by rw [sum_pt_add_r_pow]
        rw [this]
        have hdistrib :
            ∑ t ∈ range N',
                (∑ j ∈ range (k + 1),
                  (k.choose j : ℚ) * (p : ℚ) ^ j * (t : ℚ) ^ j *
                    ∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                  (((N' + t).choose t : ℚ) ^ 3) =
              ∑ t ∈ range N', ∑ j ∈ range (k + 1),
                (k.choose j : ℚ) * (p : ℚ) ^ j *
                  (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                    ((t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) := by
          refine sum_congr rfl fun t _ => ?_
          rw [sum_mul]
          refine sum_congr rfl fun j _ => by ring
        rw [hdistrib, sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [← mul_sum]
      have hsum' : PCongr p (padicValNat p (p * N'))
          (∑ t ∈ range N', ∑ r ∈ range p,
            ((p * t + r : ℕ) : ℚ) ^ k *
              ((((p * N') + (p * t + r)).choose (p * t + r) : ℚ) ^ 3))
          (∑ j ∈ range (k + 1),
            (k.choose j : ℚ) * (p : ℚ) ^ j *
              (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) := by
        rw [hrhs] at hsum
        exact hsum
      -- Target precision is `v(pN') - δ_k ≤ v(pN')`.
      have hleTarget : ((padicValNat p (p * N') : ℤ) - momentDeficit p k) ≤
          padicValNat p (p * N') := by
        have : (0 : ℤ) ≤ momentDeficit p k := Nat.cast_nonneg _
        linarith
      have hsum0 : PCongr p ((padicValNat p (p * N') : ℤ) - momentDeficit p k)
          (∑ q ∈ range (p * N'),
            (q : ℚ) ^ k * (((p * N' + q).choose q : ℚ) ^ 3) -
          ∑ j ∈ range (k + 1),
            (k.choose j : ℚ) * (p : ℚ) ^ j *
              (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        rw [hlhs]
        exact pCongr_of_le hleTarget (pCongr_sub_zero hsum')
      -- Each j-term of the RHS vanishes at the target precision.
      have hR : PCongr p ((padicValNat p (p * N') : ℤ) - momentDeficit p k)
          (∑ j ∈ range (k + 1),
            (k.choose j : ℚ) * (p : ℚ) ^ j *
              (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
        refine pCongr_sum_zero ?_
        intro j hj
        have hmom := ih N' hN'lt hN' j
        have hpj : PCongr p j ((p : ℚ) ^ j) 0 := pCongr_p_pow j
        have hpows := sum_range_pow_pCongr (p := p) (k := k - j) hp
        have hbin : IsPInt p (k.choose j : ℚ) := isPInt_nat p _
        -- val ≥ j + powSumVal + (v(N') - δ_j)
        have hmul1 : PCongr p (j + powSumVal p (k - j) +
            ((padicValNat p N' : ℤ) - momentDeficit p j))
            ((p : ℚ) ^ j * (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
              ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
          have h1 := pCongr_mul_zero hpj hpows
          exact pCongr_mul_zero h1 hmom
        have hmul2 : PCongr p (j + powSumVal p (k - j) +
            ((padicValNat p N' : ℤ) - momentDeficit p j))
            ((k.choose j : ℚ) * (p : ℚ) ^ j *
              (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) 0 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            pCongr_mul_isPInt hmul1 hbin
        have hle : ((padicValNat p (p * N') : ℤ) - momentDeficit p k) ≤
            j + powSumVal p (k - j) +
              ((padicValNat p N' : ℤ) - momentDeficit p j) := by
          have hbound := moment_expand_val_le p k j hp5
          rw [hvN]
          linarith
        exact pCongr_of_le hle hmul2
      -- Combine replacement error with the expanded RHS.
      have heq :
          ∑ q ∈ range (p * N'),
              (q : ℚ) ^ k * (((p * N' + q).choose q : ℚ) ^ 3) =
            (∑ q ∈ range (p * N'),
                (q : ℚ) ^ k * (((p * N' + q).choose q : ℚ) ^ 3) -
              ∑ j ∈ range (k + 1),
                (k.choose j : ℚ) * (p : ℚ) ^ j *
                  (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                    ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3)) +
            ∑ j ∈ range (k + 1),
              (k.choose j : ℚ) * (p : ℚ) ^ j *
                (∑ r ∈ range p, (r : ℚ) ^ (k - j)) *
                  ∑ t ∈ range N', (t : ℚ) ^ j * (((N' + t).choose t : ℚ) ^ 3) := by
        ring
      rw [heq]
      simpa using pCongr_add hsum0 hR
    · have hv0 : padicValNat p N = 0 :=
        padicValNat.eq_zero_of_not_dvd hdvd
      have hI : IsPInt p
          (∑ q ∈ range N, (q : ℚ) ^ k * ((N + q).choose q : ℚ) ^ 3) :=
        isPInt_sum fun _ _ =>
          isPInt_mul (isPInt_pow (isPInt_nat p _) k) (isPInt_pow (isPInt_nat p _) 3)
      have h0 : PCongr p 0
          (∑ q ∈ range N, (q : ℚ) ^ k * ((N + q).choose q : ℚ) ^ 3) 0 :=
        pCongr_zero_of_isPInt hI
      have hle : ((padicValNat p N : ℤ) - momentDeficit p k) ≤ 0 := by
        rw [hv0]; simp
      exact pCongr_of_le hle h0

/- ## Algebraic factorisation of the unaligned product -/

lemma one_add_split (p N q t j : ℕ) (htj : (t : ℚ) - j ≠ 0)
    (hden : (t : ℚ) - j + (p : ℚ) * q ≠ 0) :
    (1 : ℚ) + (p : ℚ) * (N + q) / ((t : ℚ) - j) =
      (1 + (p : ℚ) * q / ((t : ℚ) - j)) *
        (1 + (p : ℚ) * N / ((t : ℚ) - j + (p : ℚ) * q)) := by
  field_simp [htj, hden]
  ring

lemma mem_Icc_pred {t j : ℕ} (ht : 1 ≤ t) (hj : j ∈ Icc 1 (t - 1)) :
    t - j ∈ Icc 1 (t - 1) := by
  have hj' : 1 ≤ j ∧ j ≤ t - 1 := Finset.mem_Icc.mp hj
  have hjle : j + 1 ≤ t := (Nat.le_sub_iff_add_le ht).mp hj'.2
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact Nat.le_sub_of_add_le (by simpa [add_comm] using hjle)
  · exact Nat.sub_le_sub_left hj'.1 t

lemma prod_reindex_sub {t : ℕ} (ht : 1 ≤ t) (f : ℕ → ℚ) :
    ∏ j ∈ Icc 1 (t - 1), f (t - j) = ∏ i ∈ Icc 1 (t - 1), f i := by
  refine prod_nbij (fun j => t - j) ?_ ?_ ?_ ?_
  · intro j hj
    exact mem_Icc_pred ht (by simpa using hj)
  · intro a ha b hb heq
    have ha' : 1 ≤ a ∧ a ≤ t - 1 := Finset.mem_Icc.mp (by simpa using ha)
    have hb' : 1 ≤ b ∧ b ≤ t - 1 := Finset.mem_Icc.mp (by simpa using hb)
    have ha1 : a + 1 ≤ t := (Nat.le_sub_iff_add_le ht).mp ha'.2
    have hb1 : b + 1 ≤ t := (Nat.le_sub_iff_add_le ht).mp hb'.2
    have hae : t - (t - a) = a := Nat.sub_sub_self (Nat.le_of_succ_le ha1)
    have hbe : t - (t - b) = b := Nat.sub_sub_self (Nat.le_of_succ_le hb1)
    have heq' : t - a = t - b := heq
    calc
      a = t - (t - a) := hae.symm
      _ = t - (t - b) := by rw [heq']
      _ = b := hbe
  · intro i hi
    have hi' := mem_Icc_pred ht (by simpa using hi)
    refine ⟨t - i, hi', ?_⟩
    have himem : 1 ≤ i ∧ i ≤ t - 1 := Finset.mem_Icc.mp (by simpa using hi)
    have : i + 1 ≤ t := (Nat.le_sub_iff_add_le ht).mp himem.2
    exact Nat.sub_sub_self (Nat.le_of_succ_le this)
  · intro _ _; rfl

/-- Binomial coefficients of `(-3)`: `c_ℓ = (-1)^ℓ C(ℓ+2,2)`. -/
def binomNegThree (ℓ : ℕ) : ℚ :=
  ((-1 : ℚ) ^ ℓ) * ((ℓ + 2).choose 2)

lemma binomNegThree_zero : binomNegThree 0 = 1 := by
  simp [binomNegThree]

lemma isPInt_binomNegThree {p : ℕ} [Fact p.Prime] (ℓ : ℕ) :
    IsPInt p (binomNegThree ℓ) :=
  isPInt_mul (isPInt_pow (isPInt_neg (isPInt_one p)) ℓ) (isPInt_nat p _)

def invCubePartial (x : ℚ) (M : ℕ) : ℚ :=
  ∑ ℓ ∈ range M, binomNegThree ℓ * x ^ ℓ

def invCubeQpoly (x : ℚ) (M : ℕ) : ℚ :=
  ((M + 2).choose 2 : ℚ) + (M : ℚ) * (M + 2 : ℕ) * x +
    ((M + 1).choose 2 : ℚ) * x ^ 2

lemma isPInt_invCubeQpoly {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : IsPInt p x) (M : ℕ) :
    IsPInt p (invCubeQpoly x M) :=
  isPInt_add (isPInt_add (isPInt_nat p _)
    (isPInt_mul (isPInt_mul (isPInt_nat p M) (isPInt_nat p (M + 2))) hx))
    (isPInt_mul (isPInt_nat p _) (isPInt_pow hx 2))

lemma choose_two_succ_add (n : ℕ) :
    ((n + 1).choose 2 : ℚ) = (n.choose 2 : ℚ) + n := by
  have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
  rw [choose_one_right] at h
  exact_mod_cast (h.trans (add_comm _ _))

lemma two_mul_choose_two (n : ℕ) :
    (2 : ℚ) * (n.choose 2 : ℚ) = (n : ℚ) * ((n - 1 : ℕ) : ℚ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hdiv : 2 ∣ n * (n - 1) := by
      have hn' : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
      rw [hn', mul_comm]
      exact even_iff_two_dvd.mp (Nat.even_mul_succ_self (n - 1))
    have h := Nat.choose_two_right n
    have hnat : n.choose 2 * 2 = n * (n - 1) := by
      rw [h, Nat.div_mul_cancel hdiv]
    have hcast : ((n.choose 2 * 2 : ℕ) : ℚ) = (n : ℚ) * ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_mul, mul_comm] using hcast

lemma choose_two_eq (n : ℕ) (hn : 0 < n) :
    (n.choose 2 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  have h := two_mul_choose_two n
  have hs : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [hs] at h
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr
  linarith

lemma invCubeQpoly_rec (x : ℚ) (M : ℕ) :
    ((M + 2).choose 2 : ℚ) * (1 + x) ^ 3 =
      invCubeQpoly x M + x * invCubeQpoly x (M + 1) := by
  have hC2 : ((M + 2).choose 2 : ℚ) =
      ((M : ℚ) + 2) * ((M : ℚ) + 1) / 2 := by
    have := choose_two_eq (M + 2) (by omega)
    simp only [Nat.cast_add] at this
    convert this using 1
    ring
  have hC1 : ((M + 1).choose 2 : ℚ) =
      ((M : ℚ) + 1) * (M : ℚ) / 2 := by
    have := choose_two_eq (M + 1) (by omega)
    simp only [Nat.cast_add] at this
    convert this using 1
    ring
  have hC3 : ((M + 3).choose 2 : ℚ) =
      ((M : ℚ) + 3) * ((M : ℚ) + 2) / 2 := by
    have := choose_two_eq (M + 3) (by omega)
    simp only [Nat.cast_add] at this
    convert this using 1
    ring
  unfold invCubeQpoly
  have hidx1 : ((M + 1) + 2).choose 2 = (M + 3).choose 2 := by
    simp [Nat.add_assoc]
  have hidx2 : ((M + 1) + 1).choose 2 = (M + 2).choose 2 := by
    simp [Nat.add_assoc]
  rw [hidx1, hidx2]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [hC2, hC1, hC3]
  ring

lemma inv_cube_mul_identity (x : ℚ) :
    ∀ M : ℕ, 0 < M →
      (1 + x) ^ 3 * invCubePartial x M - 1 =
        (-1 : ℚ) ^ (M - 1) * x ^ M * invCubeQpoly x M := by
  intro M
  induction M with
  | zero => intro h; exact (lt_irrefl _ h).elim
  | succ M ih =>
    intro _
    cases M with
    | zero =>
      have h0 : (0 + 2).choose 2 = 1 := by norm_num
      have h1 : (0 + 1).choose 2 = 0 := by norm_num
      simp [invCubePartial, binomNegThree, invCubeQpoly, h0, h1]
      ring
    | succ M =>
      have ih' := ih (Nat.succ_pos _)
      have hs : invCubePartial x (M + 2) =
          invCubePartial x (M + 1) + binomNegThree (M + 1) * x ^ (M + 1) := by
        simp [invCubePartial, sum_range_succ]
      have hc : binomNegThree (M + 1) =
          (-1 : ℚ) ^ (M + 1) * ((M + 3).choose 2 : ℚ) := by
        simp [binomNegThree, add_assoc]
      have hrec := invCubeQpoly_rec x (M + 1)
      have hneg : (-1 : ℚ) ^ (M + 1) = - ((-1 : ℚ) ^ M) := by
        rw [pow_succ]; ring
      have hpow' : (-1 : ℚ) ^ ((M + 1) - 1) = (-1 : ℚ) ^ M := by simp
      rw [hs]
      have hC : ((M + 3).choose 2 : ℚ) = ((M + 1 + 2).choose 2 : ℚ) := by
        simp [add_assoc]
      have hrec' : ((M + 1 + 2).choose 2 : ℚ) * (1 + x) ^ 3 =
          invCubeQpoly x (M + 1) + x * invCubeQpoly x (M + 2) := by
        simpa [add_assoc] using hrec
      have ihZ : (1 + x) ^ 3 * invCubePartial x (M + 1) - 1 =
          (-1 : ℚ) ^ M * x ^ (M + 1) * invCubeQpoly x (M + 1) := by
        simpa [hpow'] using ih'
      have : (1 + x) ^ 3 *
            (invCubePartial x (M + 1) + binomNegThree (M + 1) * x ^ (M + 1)) - 1 =
          (-1 : ℚ) ^ (M + 1) * x ^ (M + 2) * invCubeQpoly x (M + 2) := by
        rw [hc, hC, hneg]
        have hexpand :
            (1 + x) ^ 3 * (invCubePartial x (M + 1) +
              ((- ((-1 : ℚ) ^ M)) * ((M + 1 + 2).choose 2 : ℚ) * x ^ (M + 1))) - 1 =
            ((1 + x) ^ 3 * invCubePartial x (M + 1) - 1) +
              (- ((-1 : ℚ) ^ M)) * x ^ (M + 1) *
                (((M + 1 + 2).choose 2 : ℚ) * (1 + x) ^ 3) := by ring
        rw [hexpand, ihZ, hrec']
        ring
      simpa [Nat.add_sub_cancel] using this

lemma inv_cube_remainder (x : ℚ) (M : ℕ) (hM : 0 < M) (hx : 1 + x ≠ 0) :
    (1 + x)⁻¹ ^ 3 - invCubePartial x M =
      (-1 : ℚ) ^ M * x ^ M * invCubeQpoly x M / (1 + x) ^ 3 := by
  have hid := inv_cube_mul_identity x M hM
  have hpow : (1 + x)⁻¹ ^ 3 = ((1 + x) ^ 3)⁻¹ := by simp [inv_pow]
  have hne : (1 + x) ^ 3 ≠ 0 := pow_ne_zero 3 hx
  have hsign : (-1 : ℚ) ^ M = - ((-1 : ℚ) ^ (M - 1)) := by
    have hm : M - 1 + 1 = M := Nat.sub_add_cancel hM
    nth_rw 1 [← hm]
    rw [pow_succ]; ring
  calc
    (1 + x)⁻¹ ^ 3 - invCubePartial x M
        = ((1 + x) ^ 3)⁻¹ - invCubePartial x M := by rw [hpow]
      _ = (((1 + x) ^ 3)⁻¹ * (1 + x) ^ 3 - invCubePartial x M * (1 + x) ^ 3) /
            (1 + x) ^ 3 := by
          field_simp [hne]
      _ = (1 - invCubePartial x M * (1 + x) ^ 3) / (1 + x) ^ 3 := by
          field_simp [hne]
      _ = - ((1 + x) ^ 3 * invCubePartial x M - 1) / (1 + x) ^ 3 := by ring
      _ = - ((-1 : ℚ) ^ (M - 1) * x ^ M * invCubeQpoly x M) / (1 + x) ^ 3 := by
          rw [hid]
      _ = (-1 : ℚ) ^ M * x ^ M * invCubeQpoly x M / (1 + x) ^ 3 := by
          rw [hsign]; ring

lemma harmonicGen_Icc (m n : ℕ) :
    harmonicGen m n = ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ m := by
  rw [harmonicGen, ← range_map_add_one_eq_Icc, sum_map]
  simp [Nat.cast_add, Nat.cast_one]

lemma isPInt_invCubePartial {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : IsPInt p x) (M : ℕ) :
    IsPInt p (invCubePartial x M) :=
  isPInt_sum fun _ _ =>
    isPInt_mul (isPInt_binomNegThree _) (isPInt_pow hx _)

lemma one_add_pq_div_t_ne_zero (p q t : ℕ) (ht : 0 < t) :
    (1 : ℚ) + (p : ℚ) * q / t ≠ 0 := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have heq : (1 : ℚ) + (p : ℚ) * q / t = ((t + p * q : ℕ) : ℚ) / t := by
    have hcast : ((t + p * q : ℕ) : ℚ) = (t : ℚ) + (p : ℚ) * q := by
      push_cast; rfl
    rw [hcast]
    field_simp [ht0]
  rw [heq]
  exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.add_pos_left ht _).ne') ht0

lemma isPInt_inv_one_add_x {p q t : ℕ} (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    IsPInt p (((1 : ℚ) + (p : ℚ) * q / t)⁻¹) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have heq : ((1 : ℚ) + (p : ℚ) * q / t)⁻¹ =
      (t : ℚ) * ((p * q + t : ℕ) : ℚ)⁻¹ := by
    have hcast : (t : ℚ) + (p : ℚ) * q = ((p * q + t : ℕ) : ℚ) := by
      push_cast; ring
    field_simp [ht0]
    exact hcast.symm
  rw [heq]
  exact isPInt_mul (isPInt_nat p t) (isPInt_inv_pB_add_i (B := q) hp ht)

lemma inv_cube_remainder_pCongr {p : ℕ} [Fact p.Prime] {x : ℚ} {M : ℕ}
    (hM : 0 < M) (hx0 : 1 + x ≠ 0)
    (hx : PCongr p 1 x 0) (hxI : IsPInt p x)
    (hinv : IsPInt p ((1 + x)⁻¹)) :
    PCongr p M ((1 + x)⁻¹ ^ 3 - invCubePartial x M) 0 := by
  have hrem := inv_cube_remainder x M hM hx0
  rw [hrem]
  have hxM : PCongr p M (x ^ M) 0 := by
    simpa using pCongr_pow_zero (k := M) hx
  have hQ : IsPInt p (invCubeQpoly x M) := isPInt_invCubeQpoly hxI M
  have hsign : IsPInt p ((-1 : ℚ) ^ M) :=
    isPInt_pow (isPInt_neg (isPInt_one p)) M
  have hden : IsPInt p (((1 + x) ^ 3)⁻¹) := by
    simpa [inv_pow] using isPInt_pow hinv 3
  have heq : (-1 : ℚ) ^ M * x ^ M * invCubeQpoly x M / (1 + x) ^ 3 =
      ((-1 : ℚ) ^ M * invCubeQpoly x M * ((1 + x) ^ 3)⁻¹) * x ^ M := by
    field_simp
  rw [heq]
  have hrest : IsPInt p
      ((-1 : ℚ) ^ M * invCubeQpoly x M * ((1 + x) ^ 3)⁻¹) :=
    isPInt_mul (isPInt_mul hsign hQ) hden
  simpa [mul_comm] using pCongr_mul_isPInt hxM hrest

lemma unalign_den_cast (p q t j : ℕ) (hj : j ≤ t) :
    (t : ℚ) - j + (p : ℚ) * q = ((p * q + (t - j) : ℕ) : ℚ) := by
  rw [← nat_cast_sub_eq hj]
  push_cast
  ring

lemma unalign_den_ne (p q t j : ℕ) (ht : 1 ≤ t) (hj : j ∈ Icc 1 (t - 1)) :
    (t : ℚ) - j + (p : ℚ) * q ≠ 0 := by
  have hj' := mem_Icc.mp hj
  have hle : j ≤ t := le_trans hj'.2 (Nat.sub_le _ _)
  rw [unalign_den_cast p q t j hle]
  exact Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (by omega)).ne'

lemma unalign_tj_mem {p t j : ℕ} (ht : t ∈ Icc 1 (p - 1))
    (hj : j ∈ Icc 1 (t - 1)) : t - j ∈ Icc 1 (p - 1) := by
  have ht' := mem_Icc.mp ht
  have hj' := mem_Icc.mp hj
  refine mem_Icc.mpr ⟨by omega, by omega⟩

def unalignQ (p N q t : ℕ) : ℚ :=
  ∏ j ∈ Icc 1 (t - 1),
    (1 + (p : ℚ) * N / ((t : ℚ) - j + (p : ℚ) * q))

lemma unalignQ_pCongr {p N q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (1 + padicValNat p N) (unalignQ p N q t) 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := Icc 1 (t - 1)
  set x : ℕ → ℚ := fun j =>
    (p : ℚ) * N / ((t : ℚ) - j + (p : ℚ) * q)
  have hxeq : unalignQ p N q t = ∏ j ∈ s, (1 + x j) := rfl
  rw [hxeq]
  have hα : (0 : ℤ) ≤ 1 + padicValNat p N :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
  have hx : ∀ j ∈ s, PCongr p (1 + padicValNat p N) (x j) 0 := by
    intro j hj
    have hjI : j ∈ Icc 1 (t - 1) := by simpa [s] using hj
    have htj := unalign_tj_mem ht hjI
    have hle : j ≤ t := by
      have := (mem_Icc.mp hjI).2; omega
    have hcast := unalign_den_cast p q t j hle
    have hpN : PCongr p (1 + padicValNat p N) ((p : ℚ) * N) 0 := by
      have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
      have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
      simpa [add_comm] using pCongr_mul_zero hp1 hN0
    have hinv : IsPInt p (((t : ℚ) - j + (p : ℚ) * q)⁻¹) := by
      rw [hcast]
      exact isPInt_inv_pB_add_i (B := q) hp htj
    simpa [x, div_eq_mul_inv] using pCongr_mul_isPInt hpN hinv
  have hxI : ∀ j ∈ s, IsPInt p (x j) :=
    fun j hj => isPInt_of_pCongr hα (hx j hj)
  refine pCongr_prod_one_add_of (α := 1 + padicValNat p N)
    (β := 1 + padicValNat p N) (γ := 2 * (1 + padicValNat p N))
    (δ := 1 + padicValNat p N)
    hp hp5 hα hx hxI (pCongr_sum_zero hx) ?_ le_rfl ?_ ?_ ?_
  · refine pCongr_sum_zero ?_
    intro j hj
    simpa [pow_two, two_mul] using pCongr_mul_zero (hx j hj) (hx j hj)
  · nlinarith [hα]
  · nlinarith [hα]
  · nlinarith [hα]

lemma unalign_P_eq_ZQ (p N q t : ℕ) (ht : 1 ≤ t) :
    ∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) * (N + q) / ((t : ℚ) - j)) =
      (∏ j ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / ((t : ℚ) - j))) *
        unalignQ p N q t := by
  unfold unalignQ
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have htj : (t : ℚ) - j ≠ 0 := by
    have hj' := mem_Icc.mp hj
    have hlt : j < t := Nat.lt_of_le_pred ht hj'.2
    exact sub_ne_zero.mpr (Nat.cast_injective.ne hlt.ne).symm
  exact one_add_split p N q t j htj (unalign_den_ne p q t j ht hj)

lemma unalign_Z_prefix (p q t : ℕ) (ht : 1 ≤ t) :
    ∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / ((t : ℚ) - i)) =
      ∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / i) := by
  have hcast : ∀ i ∈ Icc 1 (t - 1),
      (t : ℚ) - i = ((t - i : ℕ) : ℚ) := by
    intro i hi
    have : i ≤ t := by have := (mem_Icc.mp hi).2; omega
    exact (nat_cast_sub_eq this).symm
  have h1 : ∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / ((t : ℚ) - i)) =
      ∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / ((t - i : ℕ) : ℚ)) :=
    prod_congr rfl fun i hi => by rw [hcast i hi]
  rw [h1]
  exact prod_reindex_sub ht (fun i => 1 + (p : ℚ) * q / i)

lemma unalign_Z_split (p q t : ℕ) (ht : 0 < t) :
    ∏ i ∈ Icc 1 t, (1 + (p : ℚ) * q / i) =
      (∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / i)) *
        (1 + (p : ℚ) * q / t) := by
  have hunion : Icc 1 t = Icc 1 (t - 1) ∪ {t} := by
    ext x; simp [mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 (t - 1)) ({t} : Finset ℕ) := by
    simp [disjoint_left]; omega
  rw [hunion, prod_union hdisj, prod_singleton]

lemma unalign_Ztm1_ne (p q t : ℕ) (ht : 0 < t) :
    ∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / i) ≠ 0 := by
  refine prod_ne_zero_iff.mpr ?_
  intro i hi
  have hi1 : 0 < i := (mem_Icc.mp hi).1
  exact one_add_pq_div_t_ne_zero p q i hi1

lemma unalign_Y_div_Z {p N q t : ℕ} (hp : p.Prime)
    (hN : 0 < N) (ht : t ∈ Icc 1 (p - 1)) :
    ((p * (N + q) + t - 1).choose t : ℚ) /
        ((p * q + t).choose t : ℚ) =
      ((p : ℚ) * (N + q) / t) * unalignQ p N q t /
        (1 + (p : ℚ) * q / t) := by
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht1 : 1 ≤ t := htpos
  have hpm : 1 ≤ p * (N + q) :=
    Nat.mul_le_mul hp.pos (Nat.add_pos_left hN q)
  have hY := choose_pm_t_one_add (M := N + q) (t := t) (p := p) htpos hpm
  have hZ := choose_pB_t_one_add' (B := q) (t := t) (p := p) htpos
  have hP := unalign_P_eq_ZQ p N q t ht1
  have hZpre := unalign_Z_prefix p q t ht1
  have hZsp := unalign_Z_split p q t htpos
  have hZtm1 : ∏ i ∈ Icc 1 (t - 1), (1 + (p : ℚ) * q / i) ≠ 0 :=
    unalign_Ztm1_ne p q t htpos
  have hx0 := one_add_pq_div_t_ne_zero p q t htpos
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have hcastM : ((N + q : ℕ) : ℚ) = (N : ℚ) + q := by push_cast; rfl
  rw [hY, hZ]
  simp only [hcastM]
  rw [hP, hZpre, hZsp]
  field_simp [hZtm1, hx0, ht0]

lemma unalign_C_eq {p N q t : ℕ} (hp : p.Prime)
    (hN : 0 < N) (_hq : q < N) (ht : t ∈ Icc 1 (p - 1)) :
    ((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) =
      ((p * (N + q) - 1).choose (p * q) : ℚ) *
        ((p : ℚ) * (N + q) / t) * unalignQ p N q t /
          (1 + (p : ℚ) * q / t) := by
  have hBM : q < N + q := Nat.lt_add_of_pos_left hN
  have hC := choose_unalign_eq (M := N + q) (B := q) (t := t) (p := p)
    hBM hp.pos
  have hYZ := unalign_Y_div_Z (p := p) (N := N) (q := q) (t := t) hp hN ht
  have hidx : p * N + (p * q + t) - 1 = p * (N + q) + t - 1 := by
    have : p * N + (p * q + t) = p * (N + q) + t := by
      rw [Nat.mul_add, add_assoc]
    omega
  rw [hidx, hC]
  have hmul : ((p * (N + q) - 1).choose (p * q) : ℚ) *
        ((p * (N + q) + t - 1).choose t : ℚ) /
        ((p * q + t).choose t : ℚ) =
      ((p * (N + q) - 1).choose (p * q) : ℚ) *
        (((p * (N + q) + t - 1).choose t : ℚ) /
          ((p * q + t).choose t : ℚ)) := by
    ring
  rw [hmul, hYZ]
  ring

lemma momentDeficit_succ_le (p ℓ : ℕ) (hp5 : 5 ≤ p) :
    (momentDeficit p (ℓ + 1) : ℤ) ≤ ℓ := by
  have hle := momentDeficit_le_one p (ℓ + 1)
  by_cases hδ : momentDeficit p (ℓ + 1) = 0
  · simp [hδ]
  · have h1 : momentDeficit p (ℓ + 1) = 1 := by omega
    have hcond : p - 1 ∣ (ℓ + 1) ∧ ℓ + 1 ≠ 0 := by
      unfold momentDeficit at h1
      split_ifs at h1 with hc
      · exact hc
    have : p - 1 ≤ ℓ + 1 := Nat.le_of_dvd (Nat.succ_pos _) hcond.1
    have : 4 ≤ ℓ + 1 := le_trans (by omega : 4 ≤ p - 1) this
    omega

lemma momentDeficit_self_le (p ℓ : ℕ) (hp5 : 5 ≤ p) (hℓ : 1 ≤ ℓ) :
    (momentDeficit p ℓ : ℤ) ≤ ℓ - 1 := by
  have hle := momentDeficit_le_one p ℓ
  by_cases hδ : momentDeficit p ℓ = 0
  · simp [hδ]; omega
  · have h1 : momentDeficit p ℓ = 1 := by omega
    have hcond : p - 1 ∣ ℓ ∧ ℓ ≠ 0 := by
      unfold momentDeficit at h1
      split_ifs at h1 with hc
      · exact hc
    have : p - 1 ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_ne_zero hcond.2) hcond.1
    have : 4 ≤ ℓ := le_trans (by omega : 4 ≤ p - 1) this
    omega

lemma unalign_x_pCongr {p q t : ℕ} (hp : p.Prime) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (1 + padicValNat p q) ((p : ℚ) * q / t) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : PCongr p (padicValNat p q) (q : ℚ) 0 := pCongr_coe_val
  have hp1 : PCongr p 1 (p : ℚ) 0 := by simpa using pCongr_p_pow (p := p) 1
  have hpq := pCongr_mul_zero hp1 hq
  have hinv : IsPInt p ((t : ℚ)⁻¹) := isPInt_inv_of_mem_Icc hp ht
  simpa [div_eq_mul_inv, add_comm] using pCongr_mul_isPInt hpq hinv

lemma unalign_Q3_sub_one {p N q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (1 + padicValNat p N) (unalignQ p N q t ^ 3 - 1) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ := unalignQ_pCongr (p := p) (N := N) (q := q) (t := t) hp hp5 ht
  have hα : (0 : ℤ) ≤ 1 + padicValNat p N :=
    add_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hQI : IsPInt p (unalignQ p N q t) := isPInt_of_pCongr_one hα hQ
  exact pCongr_pow_sub_one hQ hQI 3

lemma unalign_rho_cube {p N q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N)
      ((((p * (N + q) - 1).choose (p * q) : ℚ) /
          ((N + q - 1).choose q : ℚ)) ^ 3 - 1) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hρ := aligned_choose_pCongr_strong hp hp5 hN (q := q)
  have hμ : (0 : ℤ) ≤
      3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N := by
    have : (0 : ℤ) ≤ padicValNat p (N + q) := Nat.cast_nonneg _
    have : (0 : ℤ) ≤ padicValNat p q := Nat.cast_nonneg _
    have : (0 : ℤ) ≤ padicValNat p N := Nat.cast_nonneg _
    omega
  have hρI : IsPInt p
      (((p * (N + q) - 1).choose (p * q) : ℚ) /
        ((N + q - 1).choose q : ℚ)) := isPInt_of_pCongr_one hμ hρ
  exact pCongr_pow_sub_one hρ hρI 3

lemma cube_div_one_add (X a Q xx : ℚ) (hx : 1 + xx ≠ 0) :
    (X * a * Q / (1 + xx)) ^ 3 = X ^ 3 * a ^ 3 * Q ^ 3 / (1 + xx) ^ 3 := by
  field_simp [hx]

lemma cube_diff_factor (X a Q Cs xx : ℚ) :
    X ^ 3 * a ^ 3 * Q ^ 3 / (1 + xx) ^ 3 - Cs ^ 3 * a ^ 3 / (1 + xx) ^ 3 =
      a ^ 3 / (1 + xx) ^ 3 * (X ^ 3 * Q ^ 3 - Cs ^ 3) := by
  field_simp

lemma cube_Q_split (X Q Cs : ℚ) :
    X ^ 3 * Q ^ 3 - Cs ^ 3 =
      Cs ^ 3 * (Q ^ 3 - 1) + (X ^ 3 - Cs ^ 3) * Q ^ 3 := by
  ring

lemma pow_div_cube (p M t : ℚ) (ht0 : t ≠ 0) :
    (p * M / t) ^ 3 = p ^ 3 * M ^ 3 / t ^ 3 := by
  field_simp [ht0]

lemma XQ_piece1_id (a Q Cs M N Cr t p xx : ℚ)
    (ht0 : t ≠ 0) (_h1x3 : (1 + xx) ^ 3 ≠ 0)
    (hrising : M ^ 3 * Cs ^ 3 = N ^ 3 * Cr ^ 3)
    (ha3 : a ^ 3 = p ^ 3 * M ^ 3 / t ^ 3) :
    a ^ 3 / (1 + xx) ^ 3 * (Cs ^ 3 * (Q ^ 3 - 1)) =
      (p ^ 3 * N ^ 3 * Cr ^ 3 * (Q ^ 3 - 1)) / (t ^ 3 * (1 + xx) ^ 3) := by
  rw [ha3]
  have hre : p ^ 3 * M ^ 3 / t ^ 3 / (1 + xx) ^ 3 * (Cs ^ 3 * (Q ^ 3 - 1)) =
      p ^ 3 * (M ^ 3 * Cs ^ 3) * (Q ^ 3 - 1) / (t ^ 3 * (1 + xx) ^ 3) := by
    field_simp [ht0]
  rw [hre, hrising]
  ring

lemma rho_cube_id (X Cs : ℚ) (hCs0 : Cs ≠ 0) :
    X ^ 3 - Cs ^ 3 = Cs ^ 3 * ((X / Cs) ^ 3 - 1) := by
  field_simp [hCs0]

lemma XQ_piece2_id (X a Q Cs M N Cr t p xx : ℚ)
    (ht0 : t ≠ 0) (_h1x3 : (1 + xx) ^ 3 ≠ 0)
    (hrising : M ^ 3 * Cs ^ 3 = N ^ 3 * Cr ^ 3)
    (ha3 : a ^ 3 = p ^ 3 * M ^ 3 / t ^ 3)
    (hρeq : X ^ 3 - Cs ^ 3 = Cs ^ 3 * ((X / Cs) ^ 3 - 1)) :
    a ^ 3 / (1 + xx) ^ 3 * ((X ^ 3 - Cs ^ 3) * Q ^ 3) =
      (p ^ 3 * N ^ 3 * Cr ^ 3 * ((X / Cs) ^ 3 - 1) * Q ^ 3) /
        (t ^ 3 * (1 + xx) ^ 3) := by
  rw [ha3, hρeq]
  have hre : p ^ 3 * M ^ 3 / t ^ 3 / (1 + xx) ^ 3 *
        (Cs ^ 3 * ((X / Cs) ^ 3 - 1) * Q ^ 3) =
      p ^ 3 * (M ^ 3 * Cs ^ 3) * ((X / Cs) ^ 3 - 1) * Q ^ 3 /
        (t ^ 3 * (1 + xx) ^ 3) := by
    field_simp [ht0]
  rw [hre, hrising]
  ring

lemma unalign_XQ_error {p N q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hq : q < N) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (4 + 4 * padicValNat p N)
      (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
        ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
          (((N + q - 1).choose q : ℚ) ^ 3) *
            (((p : ℚ) * (N + q) / t) ^ 3) /
              ((1 + (p : ℚ) * q / t) ^ 3))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M := N + q
  set X : ℚ := ((p * M - 1).choose (p * q) : ℚ)
  set Cs : ℚ := ((M - 1).choose q : ℚ)
  set a : ℚ := (p : ℚ) * M / t
  set xx : ℚ := (p : ℚ) * q / t
  set Q : ℚ := unalignQ p N q t
  set Cr : ℚ := ((N + q).choose q : ℚ)
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have hx0 := one_add_pq_div_t_ne_zero p q t htpos
  have hC : ((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) =
      X * a * Q / (1 + xx) := by
    simpa [M, X, a, xx, Q] using unalign_C_eq hp hN hq ht
  have hCs0 : Cs ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_pos (by omega : q ≤ M - 1)).ne'
  have h1x3 : (1 + xx) ^ 3 ≠ 0 := pow_ne_zero 3 hx0
  have hC3 : ((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3 =
      X ^ 3 * a ^ 3 * Q ^ 3 / (1 + xx) ^ 3 := by
    rw [hC]; exact cube_div_one_add X a Q xx hx0
  have hdiff :
      ((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3 -
        Cs ^ 3 * a ^ 3 / (1 + xx) ^ 3 =
      a ^ 3 / (1 + xx) ^ 3 * (X ^ 3 * Q ^ 3 - Cs ^ 3) := by
    rw [hC3]; exact cube_diff_factor X a Q Cs xx
  have hrising : (M : ℚ) ^ 3 * Cs ^ 3 = (N : ℚ) ^ 3 * Cr ^ 3 := by
    simpa [M, Cs, Cr] using rising_cube_identity (N := N) (q := q) hN
  have ha3 : a ^ 3 = (p : ℚ) ^ 3 * (M : ℚ) ^ 3 / (t : ℚ) ^ 3 := by
    simpa [a] using pow_div_cube (p : ℚ) (M : ℚ) (t : ℚ) ht0
  have hρeq : X ^ 3 - Cs ^ 3 = Cs ^ 3 * ((X / Cs) ^ 3 - 1) :=
    rho_cube_id X Cs hCs0
  have hprefI : IsPInt p ((p * N + 2 * (p * q + t) : ℕ) : ℚ) :=
    isPInt_nat p _
  have hinvx : IsPInt p ((1 + xx)⁻¹) := by
    simpa [xx] using isPInt_inv_one_add_x (p := p) (q := q) (t := t) hp ht
  have hinvx3 : IsPInt p (((1 + xx) ^ 3)⁻¹) := by
    simpa [inv_pow] using isPInt_pow hinvx 3
  have htinv3 : IsPInt p (((t : ℚ) ^ 3)⁻¹) := by
    simpa [inv_pow] using isPInt_pow (isPInt_inv_of_mem_Icc hp ht) 3
  have hQ3m := unalign_Q3_sub_one (p := p) (N := N) (q := q) (t := t) hp hp5 ht
  have hρ3 := unalign_rho_cube (p := p) (N := N) (q := q) hp hp5 hN
  have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := pCongr_p_pow 3
  have hN3 : PCongr p (3 * padicValNat p N) ((N : ℚ) ^ 3) 0 := by
    have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
    simpa using pCongr_pow_zero (k := 3) hN0
  have hCrI : IsPInt p (Cr ^ 3) := isPInt_pow (isPInt_nat p _) 3
  have hQI : IsPInt p Q :=
    isPInt_of_pCongr_one (add_nonneg (by norm_num) (Nat.cast_nonneg _))
      (unalignQ_pCongr (p := p) (N := N) (q := q) (t := t) hp hp5 ht)
  have hQ3I : IsPInt p (Q ^ 3) := isPInt_pow hQI 3
  have hdenI : IsPInt p (((t : ℚ) ^ 3 * (1 + xx) ^ 3)⁻¹) := by
    rw [mul_inv]; exact isPInt_mul htinv3 hinvx3
  have h1 : PCongr p (4 + 4 * padicValNat p N)
      (a ^ 3 / (1 + xx) ^ 3 * (Cs ^ 3 * (Q ^ 3 - 1))) 0 := by
    rw [XQ_piece1_id a Q Cs (M : ℚ) (N : ℚ) Cr (t : ℚ) (p : ℚ) xx
      ht0 h1x3 hrising ha3]
    have hmul1 := pCongr_mul_zero hp3 hN3
    have hmul2 := pCongr_mul_zero hmul1 hQ3m
    have hmul3 := pCongr_mul_isPInt hmul2 hCrI
    have hfin := pCongr_mul_isPInt hmul3 hdenI
    have hle : (4 + 4 * padicValNat p N : ℤ) ≤
        3 + 3 * padicValNat p N + (1 + padicValNat p N) := by omega
    refine pCongr_of_le hle ?_
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfin
  have h2 : PCongr p (4 + 4 * padicValNat p N)
      (a ^ 3 / (1 + xx) ^ 3 * ((X ^ 3 - Cs ^ 3) * Q ^ 3)) 0 := by
    rw [XQ_piece2_id X a Q Cs (M : ℚ) (N : ℚ) Cr (t : ℚ) (p : ℚ) xx
      ht0 h1x3 hrising ha3 hρeq]
    have hmul1 := pCongr_mul_zero hp3 hN3
    have hmul2 := pCongr_mul_zero hmul1 hρ3
    have hmul3 := pCongr_mul_isPInt hmul2 hCrI
    have hmul4 := pCongr_mul_isPInt hmul3 hQ3I
    have hfin := pCongr_mul_isPInt hmul4 hdenI
    have hle : (4 + 4 * padicValNat p N : ℤ) ≤
        3 + 3 * padicValNat p N +
          (3 + padicValNat p (N + q) + padicValNat p q + padicValNat p N) := by
      have : (0 : ℤ) ≤ padicValNat p (N + q) := Nat.cast_nonneg _
      have : (0 : ℤ) ≤ padicValNat p q := Nat.cast_nonneg _
      omega
    refine pCongr_of_le hle ?_
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, M] using hfin
  have hinner : PCongr p (4 + 4 * padicValNat p N)
      (a ^ 3 / (1 + xx) ^ 3 * (X ^ 3 * Q ^ 3 - Cs ^ 3)) 0 := by
    rw [cube_Q_split X Q Cs, mul_add]
    simpa using pCongr_add h1 h2
  have hbody : PCongr p (4 + 4 * padicValNat p N)
      ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
        Cs ^ 3 * a ^ 3 / (1 + xx) ^ 3) 0 := by
    rw [hdiff]; exact hinner
  have hgoal := pCongr_mul_isPInt hbody hprefI
  simpa [mul_comm, Cs, a, xx, M] using hgoal

lemma unalign_XQ_sum {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
            (((N + q - 1).choose q : ℚ) ^ 3) *
              (((p : ℚ) * (N + q) / t) ^ 3) /
                ((1 + (p : ℚ) * q / t) ^ 3))) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pCongr_sum_zero ?_
  intro q hq
  refine pCongr_sum_zero ?_
  intro t ht
  exact unalign_XQ_error hp hp5 hN (mem_range.mp hq) ht

lemma invCubePartial_decomp (x : ℚ) (L : ℕ) (hL : 0 < L) :
    invCubePartial x L =
      1 + ∑ ℓ ∈ Icc 1 (L - 1), binomNegThree ℓ * x ^ ℓ := by
  have hrange : range L = {0} ∪ Icc 1 (L - 1) := by
    ext n; simp [mem_range, mem_Icc]; omega
  have hdisj : Disjoint ({0} : Finset ℕ) (Icc 1 (L - 1)) := by
    simp [disjoint_left]
  simp only [invCubePartial]
  rw [hrange, sum_union hdisj, sum_singleton, binomNegThree_zero, one_mul, pow_zero]

lemma two_t_monomial_eq (p N q t ℓ : ℕ) (ht : 0 < t) :
    (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
      (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
      ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
    (2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
      (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3) / (t : ℚ) ^ (ℓ + 2) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have hx : ((p : ℚ) * q / t) ^ ℓ =
      (p : ℚ) ^ ℓ * (q : ℚ) ^ ℓ / (t : ℚ) ^ ℓ := by
    rw [div_pow, mul_pow]
  rw [hx]
  have hden : (t : ℚ) ^ (ℓ + 3) ≠ 0 := pow_ne_zero _ ht0
  apply (mul_right_inj' hden).mp
  field_simp [ht0]
  ring

lemma prefN_monomial_eq (p N q t ℓ : ℕ) (ht : 0 < t) :
    (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
      (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
      ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
    binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
      ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
        (((N + q).choose q : ℚ) ^ 3) / (t : ℚ) ^ (ℓ + 3) := by
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have hx : ((p : ℚ) * q / t) ^ ℓ =
      (p : ℚ) ^ ℓ * (q : ℚ) ^ ℓ / (t : ℚ) ^ ℓ := by
    rw [div_pow, mul_pow]
  rw [hx]
  have hden : (t : ℚ) ^ (ℓ + 4) ≠ 0 := pow_ne_zero _ ht0
  apply (mul_right_inj' hden).mp
  field_simp [ht0]
  ring

lemma sum_two_t_monomial {p N ℓ : ℕ} (hp : p.Prime) (hN : 0 < N) :
    ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
        (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
        ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
    (2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
      (∑ q ∈ range N, (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3)) *
      harmonicGen (ℓ + 2) (p - 1) := by
  have hterm := fun q t (ht : t ∈ Icc 1 (p - 1)) =>
    two_t_monomial_eq p N q t ℓ (mem_Icc.mp ht).1
  have h1 : ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
        (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
        ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
    ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      (2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
        (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3) / (t : ℚ) ^ (ℓ + 2) :=
    sum_congr rfl fun q _ => sum_congr rfl fun t ht => hterm q t ht
  rw [h1, sum_comm]
  have h2 : ∑ t ∈ Icc 1 (p - 1), ∑ q ∈ range N,
      (2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
        (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3) / (t : ℚ) ^ (ℓ + 2) =
    ∑ t ∈ Icc 1 (p - 1),
      ((2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
        (∑ q ∈ range N, (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3))) *
          ((t : ℚ) ^ (ℓ + 2))⁻¹ := by
    refine sum_congr rfl fun t ht => ?_
    have ht0 : (t : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
    have hfactor : ∀ q : ℕ,
        (2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
          (q : ℚ) ^ ℓ * ((((N + q).choose q : ℚ) ^ 3)) / (t : ℚ) ^ (ℓ + 2) =
        ((2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
          ((t : ℚ) ^ (ℓ + 2))⁻¹) *
        ((q : ℚ) ^ ℓ * ((((N + q).choose q : ℚ) ^ 3))) := by
      intro q; field_simp [ht0]
    simp only [hfactor, ← mul_sum]
    ring
  rw [h2, ← mul_sum, harmonicGen_Icc]
  simp only [div_eq_mul_inv]
  ring

lemma sum_prefN_monomial {p N ℓ : ℕ} (hp : p.Prime) (hN : 0 < N) :
    ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
        (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
        ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
    binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
      (∑ q ∈ range N, ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
        (((N + q).choose q : ℚ) ^ 3)) *
      harmonicGen (ℓ + 3) (p - 1) := by
  have hterm := fun q t (ht : t ∈ Icc 1 (p - 1)) =>
    prefN_monomial_eq p N q t ℓ (mem_Icc.mp ht).1
  have h1 : ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
        (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
        ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
    ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
          (((N + q).choose q : ℚ) ^ 3) / (t : ℚ) ^ (ℓ + 3) :=
    sum_congr rfl fun q _ => sum_congr rfl fun t ht => hterm q t ht
  rw [h1, sum_comm]
  have h2 : ∑ t ∈ Icc 1 (p - 1), ∑ q ∈ range N,
      binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
          (((N + q).choose q : ℚ) ^ 3) / (t : ℚ) ^ (ℓ + 3) =
    ∑ t ∈ Icc 1 (p - 1),
      (binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
          (((N + q).choose q : ℚ) ^ 3))) * ((t : ℚ) ^ (ℓ + 3))⁻¹ := by
    refine sum_congr rfl fun t ht => ?_
    have ht0 : (t : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
    have hfactor : ∀ q : ℕ,
        binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
          ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
            ((((N + q).choose q : ℚ) ^ 3)) / (t : ℚ) ^ (ℓ + 3) =
        (binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
          ((t : ℚ) ^ (ℓ + 3))⁻¹) *
        (((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
          ((((N + q).choose q : ℚ) ^ 3))) := by
      intro q; field_simp [ht0]
    simp only [hfactor, ← mul_sum]
    ring
  rw [h2, ← mul_sum, harmonicGen_Icc]
  simp only [div_eq_mul_inv]
  ring

lemma two_t_moment_pCongr {p N ℓ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hℓ : 1 ≤ ℓ) :
    PCongr p (4 + 4 * padicValNat p N)
      ((2 : ℚ) * binomNegThree ℓ * (p : ℚ) ^ (3 + ℓ) * (N : ℚ) ^ 3 *
        (∑ q ∈ range N, (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3)) *
        harmonicGen (ℓ + 2) (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpL : PCongr p (3 + ℓ) ((p : ℚ) ^ (3 + ℓ)) 0 := pCongr_p_pow (3 + ℓ)
  have hN3 : PCongr p (3 * padicValNat p N) ((N : ℚ) ^ 3) 0 := by
    have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
    simpa using pCongr_pow_zero (k := 3) hN0
  have hmom := sum_q_pow_choose_cube_val hp hp5 hN ℓ
  have hcI : IsPInt p (binomNegThree ℓ) := isPInt_binomNegThree ℓ
  have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
  have hHI : IsPInt p (harmonicGen (ℓ + 2) (p - 1)) :=
    harmonicGen_isPInt hp (ℓ + 2) (p - 1) (Nat.sub_lt hp.pos (by omega))
  have hmul1 := pCongr_mul_zero hpL hN3
  have hmul2 := pCongr_mul_zero hmul1 hmom
  have hmul3 := pCongr_mul_isPInt hmul2 hcI
  have hmul4 := pCongr_mul_isPInt hmul3 h2I
  have hmul5 := pCongr_mul_isPInt hmul4 hHI
  have hle : (4 + 4 * padicValNat p N : ℤ) ≤
      (3 + ℓ) + 3 * padicValNat p N +
        ((padicValNat p N : ℤ) - momentDeficit p ℓ) := by
    have hδ := momentDeficit_self_le p ℓ hp5 hℓ
    omega
  refine pCongr_of_le hle ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul5

lemma prefN_q_pow_split (N ℓ : ℕ) :
    ∑ q ∈ range N, ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
        (((N + q).choose q : ℚ) ^ 3) =
      (N : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3) +
        (2 : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ (ℓ + 1) *
          (((N + q).choose q : ℚ) ^ 3) := by
  have hterm : ∀ q, ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
        (((N + q).choose q : ℚ) ^ 3) =
      (N : ℚ) * ((q : ℚ) ^ ℓ * (((N + q).choose q : ℚ) ^ 3)) +
        (2 : ℚ) * ((q : ℚ) ^ (ℓ + 1) * (((N + q).choose q : ℚ) ^ 3)) := by
    intro q; push_cast; ring
  rw [sum_congr rfl fun q _ => hterm q, sum_add_distrib, ← mul_sum, ← mul_sum]

lemma prefN_moment_pCongr {p N ℓ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + 2 * q : ℕ) : ℚ) * (q : ℚ) ^ ℓ *
          (((N + q).choose q : ℚ) ^ 3)) *
        harmonicGen (ℓ + 3) (p - 1)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [prefN_q_pow_split]
  have hpL : PCongr p (4 + ℓ) ((p : ℚ) ^ (4 + ℓ)) 0 := pCongr_p_pow (4 + ℓ)
  have hN3 : PCongr p (3 * padicValNat p N) ((N : ℚ) ^ 3) 0 := by
    have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
    simpa using pCongr_pow_zero (k := 3) hN0
  have hmomℓ := sum_q_pow_choose_cube_val hp hp5 hN ℓ
  have hmomℓ1 := sum_q_pow_choose_cube_val hp hp5 hN (ℓ + 1)
  have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
  have hcI : IsPInt p (binomNegThree ℓ) := isPInt_binomNegThree ℓ
  have h2I : IsPInt p (2 : ℚ) := isPInt_nat p 2
  have hHI : IsPInt p (harmonicGen (ℓ + 3) (p - 1)) :=
    harmonicGen_isPInt hp (ℓ + 3) (p - 1) (Nat.sub_lt hp.pos (by omega))
  have hA : PCongr p (4 + 4 * padicValNat p N)
      (binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        ((N : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ ℓ *
          (((N + q).choose q : ℚ) ^ 3)) *
        harmonicGen (ℓ + 3) (p - 1)) 0 := by
    have hmul1 := pCongr_mul_zero hpL hN3
    have hmul2 := pCongr_mul_zero hmul1 hN0
    have hmul3 := pCongr_mul_zero hmul2 hmomℓ
    have hmul4 := pCongr_mul_isPInt hmul3 hcI
    have hmul5 := pCongr_mul_isPInt hmul4 hHI
    have hle : (4 + 4 * padicValNat p N : ℤ) ≤
        (4 + ℓ) + 3 * padicValNat p N + padicValNat p N +
          ((padicValNat p N : ℤ) - momentDeficit p ℓ) := by
      have hδ : (momentDeficit p ℓ : ℤ) ≤ ℓ := by
        have := momentDeficit_le_one p ℓ
        by_cases hℓ0 : ℓ = 0
        · subst hℓ0; simp [momentDeficit_zero]
        · omega
      omega
    refine pCongr_of_le hle ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul5
  have hB : PCongr p (4 + 4 * padicValNat p N)
      (binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        ((2 : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ (ℓ + 1) *
          (((N + q).choose q : ℚ) ^ 3)) *
        harmonicGen (ℓ + 3) (p - 1)) 0 := by
    have hmul1 := pCongr_mul_zero hpL hN3
    have hmul2 := pCongr_mul_zero hmul1 hmomℓ1
    have hmul3 := pCongr_mul_isPInt hmul2 hcI
    have hmul4 := pCongr_mul_isPInt hmul3 h2I
    have hmul5 := pCongr_mul_isPInt hmul4 hHI
    have hle : (4 + 4 * padicValNat p N : ℤ) ≤
        (4 + ℓ) + 3 * padicValNat p N +
          ((padicValNat p N : ℤ) - momentDeficit p (ℓ + 1)) := by
      have hδ := momentDeficit_succ_le p ℓ hp5
      omega
    refine pCongr_of_le hle ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul5
  have heq :
      binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
        ((N : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ ℓ *
            (((N + q).choose q : ℚ) ^ 3) +
          (2 : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ (ℓ + 1) *
            (((N + q).choose q : ℚ) ^ 3)) *
        harmonicGen (ℓ + 3) (p - 1) =
      binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
          ((N : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ ℓ *
            (((N + q).choose q : ℚ) ^ 3)) *
          harmonicGen (ℓ + 3) (p - 1) +
      binomNegThree ℓ * (p : ℚ) ^ (4 + ℓ) * (N : ℚ) ^ 3 *
          ((2 : ℚ) * ∑ q ∈ range N, (q : ℚ) ^ (ℓ + 1) *
            (((N + q).choose q : ℚ) ^ 3)) *
          harmonicGen (ℓ + 3) (p - 1) := by
    ring
  rw [heq]
  simpa using pCongr_add hA hB

lemma invCubePartial_sub_one (x : ℚ) (L : ℕ) (hL : 0 < L) :
    invCubePartial x L - 1 =
      ∑ ℓ ∈ Icc 1 (L - 1), binomNegThree ℓ * x ^ ℓ := by
  rw [invCubePartial_decomp x L hL]
  ring

lemma main_diff_factor (pref a Cs xx t p M N Cr N2q : ℚ)
    (ht0 : t ≠ 0) (hx0 : 1 + xx ≠ 0)
    (ha3 : a ^ 3 = p ^ 3 * M ^ 3 / t ^ 3)
    (hrising : M ^ 3 * Cs ^ 3 = N ^ 3 * Cr ^ 3)
    (hpref : pref = p * N2q + 2 * t) :
    pref * Cs ^ 3 * a ^ 3 / (1 + xx) ^ 3 - 2 * p ^ 3 * M ^ 3 * Cs ^ 3 / t ^ 2 =
      p ^ 3 * N ^ 3 * Cr ^ 3 / t ^ 3 *
        (2 * t * ((1 + xx)⁻¹ ^ 3 - 1) + p * N2q * (1 + xx)⁻¹ ^ 3) := by
  rw [ha3, hpref]
  have h1x3 : (1 + xx) ^ 3 ≠ 0 := pow_ne_zero 3 hx0
  have hinv : (1 + xx)⁻¹ ^ 3 = ((1 + xx) ^ 3)⁻¹ := by simp [inv_pow]
  rw [hinv]
  have hre :
      (p * N2q + 2 * t) * Cs ^ 3 * (p ^ 3 * M ^ 3 / t ^ 3) / (1 + xx) ^ 3 -
        2 * p ^ 3 * M ^ 3 * Cs ^ 3 / t ^ 2 =
      p ^ 3 * (M ^ 3 * Cs ^ 3) / t ^ 3 *
        (2 * t * (((1 + xx) ^ 3)⁻¹ - 1) + p * N2q * ((1 + xx) ^ 3)⁻¹) := by
    field_simp [ht0, h1x3]
    ring
  rw [hre, hrising]
  ring

lemma unalign_two_t_rem {p N q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (4 + 4 * padicValNat p N)
      ((2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
        (((N + q).choose q : ℚ) ^ 3) *
        (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
          invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
          (t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have hx0 := one_add_pq_div_t_ne_zero p q t htpos
  have hL : 0 < padicValNat p N + 1 := Nat.succ_pos _
  set xx : ℚ := (p : ℚ) * q / t
  have hx : PCongr p 1 xx 0 :=
    pCongr_of_le (by
      have : (0 : ℤ) ≤ padicValNat p q := Nat.cast_nonneg _
      omega) (unalign_x_pCongr (p := p) (q := q) (t := t) hp ht)
  have hxI : IsPInt p xx :=
    isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) hx
  have hinv : IsPInt p ((1 + xx)⁻¹) := by
    simpa [xx] using isPInt_inv_one_add_x (p := p) (q := q) (t := t) hp ht
  have hrem := inv_cube_remainder_pCongr (p := p) (x := xx)
    (M := padicValNat p N + 1) hL hx0 hx hxI hinv
  have hp3 : PCongr p 3 ((p : ℚ) ^ 3) 0 := pCongr_p_pow 3
  have hN3 : PCongr p (3 * padicValNat p N) ((N : ℚ) ^ 3) 0 := by
    have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
    simpa using pCongr_pow_zero (k := 3) hN0
  have hrest : IsPInt p
      ((2 : ℚ) * t * (((N + q).choose q : ℚ) ^ 3) * ((t : ℚ) ^ 3)⁻¹) := by
    refine isPInt_mul (isPInt_mul (isPInt_mul (isPInt_nat p 2) (isPInt_nat p t))
      (isPInt_pow (isPInt_nat p _) 3)) ?_
    simpa [inv_pow] using isPInt_pow (isPInt_inv_of_mem_Icc hp ht) 3
  have hmul1 := pCongr_mul_zero hp3 hN3
  have hmul2 := pCongr_mul_zero hmul1 hrem
  have hfin := pCongr_mul_isPInt hmul2 hrest
  have hle : (4 + 4 * padicValNat p N : ℤ) ≤
      3 + 3 * padicValNat p N + (padicValNat p N + 1) := by omega
  refine pCongr_of_le hle ?_
  simpa [xx, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfin

lemma unalign_prefN_rem {p N q t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (ht : t ∈ Icc 1 (p - 1)) :
    PCongr p (4 + 4 * padicValNat p N)
      ((p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
        (((N + q).choose q : ℚ) ^ 3) *
        (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
          invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
          (t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have hx0 := one_add_pq_div_t_ne_zero p q t htpos
  have hL : 0 < padicValNat p N + 1 := Nat.succ_pos _
  set xx : ℚ := (p : ℚ) * q / t
  have hx : PCongr p 1 xx 0 :=
    pCongr_of_le (by
      have : (0 : ℤ) ≤ padicValNat p q := Nat.cast_nonneg _
      omega) (unalign_x_pCongr (p := p) (q := q) (t := t) hp ht)
  have hxI : IsPInt p xx :=
    isPInt_of_pCongr (by norm_num : (0 : ℤ) ≤ 1) hx
  have hinv : IsPInt p ((1 + xx)⁻¹) := by
    simpa [xx] using isPInt_inv_one_add_x (p := p) (q := q) (t := t) hp ht
  have hrem := inv_cube_remainder_pCongr (p := p) (x := xx)
    (M := padicValNat p N + 1) hL hx0 hx hxI hinv
  have hp4 : PCongr p 4 ((p : ℚ) ^ 4) 0 := pCongr_p_pow 4
  have hN3 : PCongr p (3 * padicValNat p N) ((N : ℚ) ^ 3) 0 := by
    have hN0 : PCongr p (padicValNat p N) (N : ℚ) 0 := pCongr_coe_val
    simpa using pCongr_pow_zero (k := 3) hN0
  have hrest : IsPInt p
      (((N + 2 * q : ℕ) : ℚ) * (((N + q).choose q : ℚ) ^ 3) *
        ((t : ℚ) ^ 3)⁻¹) := by
    refine isPInt_mul (isPInt_mul (isPInt_nat p _) (isPInt_pow (isPInt_nat p _) 3)) ?_
    simpa [inv_pow] using isPInt_pow (isPInt_inv_of_mem_Icc hp ht) 3
  have hmul1 := pCongr_mul_zero hp4 hN3
  have hmul2 := pCongr_mul_zero hmul1 hrem
  have hfin := pCongr_mul_isPInt hmul2 hrest
  have hle : (4 + 4 * padicValNat p N : ℤ) ≤
      4 + 3 * padicValNat p N + (padicValNat p N + 1) := by omega
  refine pCongr_of_le hle ?_
  convert hfin using 1
  simp [xx, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  ring

lemma unalign_two_t_part_sum {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) - 1) /
            (t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set L := padicValNat p N + 1
  have hL : 0 < L := Nat.succ_pos _
  have hdecomp : ∀ q t,
      invCubePartial ((p : ℚ) * q / t) L - 1 =
        ∑ ℓ ∈ Icc 1 (L - 1),
          binomNegThree ℓ * ((p : ℚ) * q / t) ^ ℓ :=
    fun q t => invCubePartial_sub_one _ L hL
  have hswap :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (invCubePartial ((p : ℚ) * q / t) L - 1) / (t : ℚ) ^ 3 =
      ∑ ℓ ∈ Icc 1 (L - 1),
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
            ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 := by
    have h1 : ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (invCubePartial ((p : ℚ) * q / t) L - 1) / (t : ℚ) ^ 3 =
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (∑ ℓ ∈ Icc 1 (L - 1),
            binomNegThree ℓ * ((p : ℚ) * q / t) ^ ℓ) / (t : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => sum_congr rfl fun t _ => by
        rw [hdecomp]
    rw [h1]
    have h2 : ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (∑ ℓ ∈ Icc 1 (L - 1),
            binomNegThree ℓ * ((p : ℚ) * q / t) ^ ℓ) / (t : ℚ) ^ 3 =
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1), ∑ ℓ ∈ Icc 1 (L - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
          ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => sum_congr rfl fun t _ => by
        simp only [mul_sum, sum_div]
        refine sum_congr rfl fun ℓ _ => by ring
    rw [h2]
    have h3 :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1), ∑ ℓ ∈ Icc 1 (L - 1),
          (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
            ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
        ∑ q ∈ range N, ∑ ℓ ∈ Icc 1 (L - 1), ∑ t ∈ Icc 1 (p - 1),
          (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
            ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => sum_comm
    rw [h3]
    exact sum_comm
  rw [hswap]
  refine pCongr_sum_zero ?_
  intro ℓ hℓ
  have hℓ1 : 1 ≤ ℓ := (mem_Icc.mp hℓ).1
  have heq := sum_two_t_monomial (p := p) (N := N) (ℓ := ℓ) hp hN
  rw [heq]
  exact two_t_moment_pCongr hp hp5 hN hℓ1

lemma unalign_two_t_rem_sum {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
            invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
            (t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pCongr_sum_zero ?_
  intro q hq
  refine pCongr_sum_zero ?_
  intro t ht
  exact unalign_two_t_rem hp hp5 hN ht

lemma unalign_prefN_part_sum {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) /
            (t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set L := padicValNat p N + 1
  have hdecomp : ∀ q t,
      invCubePartial ((p : ℚ) * q / t) L =
        ∑ ℓ ∈ range L, binomNegThree ℓ * ((p : ℚ) * q / t) ^ ℓ :=
    fun q t => rfl
  have hswap :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          invCubePartial ((p : ℚ) * q / t) L / (t : ℚ) ^ 3 =
      ∑ ℓ ∈ range L,
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
            ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 := by
    have h1 : ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          invCubePartial ((p : ℚ) * q / t) L / (t : ℚ) ^ 3 =
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (∑ ℓ ∈ range L, binomNegThree ℓ * ((p : ℚ) * q / t) ^ ℓ) /
            (t : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => sum_congr rfl fun t _ => by rw [hdecomp]
    rw [h1]
    have h2 : ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (∑ ℓ ∈ range L, binomNegThree ℓ * ((p : ℚ) * q / t) ^ ℓ) /
            (t : ℚ) ^ 3 =
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1), ∑ ℓ ∈ range L,
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
          ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => sum_congr rfl fun t _ => by
        simp only [mul_sum, sum_div]
        refine sum_congr rfl fun ℓ _ => by ring
    rw [h2]
    have h3 :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1), ∑ ℓ ∈ range L,
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
            ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 =
        ∑ q ∈ range N, ∑ ℓ ∈ range L, ∑ t ∈ Icc 1 (p - 1),
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) * binomNegThree ℓ *
            ((p : ℚ) * q / t) ^ ℓ / (t : ℚ) ^ 3 :=
      sum_congr rfl fun q _ => sum_comm
    rw [h3]
    exact sum_comm
  rw [hswap]
  refine pCongr_sum_zero ?_
  intro ℓ hℓ
  have heq := sum_prefN_monomial (p := p) (N := N) (ℓ := ℓ) hp hN
  rw [heq]
  exact prefN_moment_pCongr hp hp5 hN

lemma unalign_prefN_rem_sum {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
            invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
            (t : ℚ) ^ 3) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pCongr_sum_zero ?_
  intro q hq
  refine pCongr_sum_zero ?_
  intro t ht
  exact unalign_prefN_rem hp hp5 hN ht




lemma four_split (P N Cr t N2q xx part : ℚ) (ht0 : t ≠ 0) :
    P ^ 3 * N ^ 3 * Cr ^ 3 / t ^ 3 *
      (2 * t * ((1 + xx)⁻¹ ^ 3 - 1) + P * N2q * (1 + xx)⁻¹ ^ 3) =
    (2 * t * P ^ 3 * N ^ 3 * Cr ^ 3 *
      (part - 1) / t ^ 3) +
    (2 * t * P ^ 3 * N ^ 3 * Cr ^ 3 *
      ((1 + xx)⁻¹ ^ 3 - part) / t ^ 3) +
    (P * N2q * P ^ 3 * N ^ 3 * Cr ^ 3 *
      part / t ^ 3) +
    (P * N2q * P ^ 3 * N ^ 3 * Cr ^ 3 *
      ((1 + xx)⁻¹ ^ 3 - part) / t ^ 3) := by
  field_simp [ht0]
  ring

lemma unalign_main_term_split {p N q t : ℕ} (hN : 0 < N)
    (ht : t ∈ Icc 1 (p - 1)) :
    ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
        (((N + q - 1).choose q : ℚ) ^ 3) *
        (((p : ℚ) * (N + q) / t) ^ 3) /
          ((1 + (p : ℚ) * q / t) ^ 3) -
      (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
        (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
    (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
      (((N + q).choose q : ℚ) ^ 3) *
      (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) - 1) /
        (t : ℚ) ^ 3 +
    (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
      (((N + q).choose q : ℚ) ^ 3) *
      (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
        invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
        (t : ℚ) ^ 3 +
    (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
      (((N + q).choose q : ℚ) ^ 3) *
      invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) /
        (t : ℚ) ^ 3 +
    (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
      (((N + q).choose q : ℚ) ^ 3) *
      (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
        invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
        (t : ℚ) ^ 3 := by
  have htpos : 0 < t := (mem_Icc.mp ht).1
  have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htpos.ne'
  have hx0 := one_add_pq_div_t_ne_zero p q t htpos
  have hpref : ((p * N + 2 * (p * q + t) : ℕ) : ℚ) =
      (p : ℚ) * (N + 2 * q : ℕ) + 2 * (t : ℚ) := by
    push_cast; ring
  have ha3 : ((p : ℚ) * (N + q) / t) ^ 3 =
      (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 / (t : ℚ) ^ 3 := by
    have : (p : ℚ) * (N + q) / t = (p : ℚ) * ((N + q : ℕ) : ℚ) / t := by
      push_cast; rfl
    rw [this]
    exact pow_div_cube (p : ℚ) ((N + q : ℕ) : ℚ) (t : ℚ) ht0
  have hrising : ((N + q : ℕ) : ℚ) ^ 3 * (((N + q - 1).choose q : ℚ) ^ 3) =
      (N : ℚ) ^ 3 * (((N + q).choose q : ℚ) ^ 3) :=
    rising_cube_identity (N := N) (q := q) hN
  have hmd := main_diff_factor
    (((p * N + 2 * (p * q + t) : ℕ) : ℚ))
    ((p : ℚ) * (N + q) / t)
    (((N + q - 1).choose q : ℚ))
    ((p : ℚ) * q / t)
    (t : ℚ) (p : ℚ) ((N + q : ℕ) : ℚ) (N : ℚ)
    (((N + q).choose q : ℚ))
    ((N + 2 * q : ℕ) : ℚ)
    ht0 hx0 ha3 hrising hpref
  have h4 := four_split (p : ℚ) (N : ℚ)
    (((N + q).choose q : ℚ)) (t : ℚ)
    ((N + 2 * q : ℕ) : ℚ)
    ((p : ℚ) * q / t)
    (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1))
    ht0
  exact hmd.trans h4

lemma unalign_H2_sum_eq (p N : ℕ) :
    ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
      (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
        (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
    (2 : ℚ) * (p : ℚ) ^ 3 *
      (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
        (((N + q - 1).choose q : ℚ) ^ 3)) *
      harmonicGen 2 (p - 1) := by
  have hswap :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
      ∑ t ∈ Icc 1 (p - 1), ∑ q ∈ range N,
        (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 := by
    rw [sum_comm]
  rw [hswap]
  have : ∑ t ∈ Icc 1 (p - 1), ∑ q ∈ range N,
      (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
        (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
      ∑ t ∈ Icc 1 (p - 1),
        ((2 : ℚ) * (p : ℚ) ^ 3 *
          (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3))) * ((t : ℚ) ^ 2)⁻¹ := by
    refine sum_congr rfl fun t ht => ?_
    have ht0 : (t : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp ht).1)
    have hfactor :
        ∀ q, (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2 =
          ((2 : ℚ) * (p : ℚ) ^ 3 * ((t : ℚ) ^ 2)⁻¹) *
            (((N + q : ℕ) : ℚ) ^ 3 * (((N + q - 1).choose q : ℚ) ^ 3)) := by
      intro q; field_simp [ht0]
    simp only [hfactor, ← mul_sum]
    ring
  rw [this, ← mul_sum, harmonicGen_two_Icc]
  simp only [div_eq_mul_inv]
  ring

lemma unalign_main_sum {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            (((N + q - 1).choose q : ℚ) ^ 3) *
            (((p : ℚ) * (N + q) / t) ^ 3) /
              ((1 + (p : ℚ) * q / t) ^ 3) -
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hterm :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            (((N + q - 1).choose q : ℚ) ^ 3) *
            (((p : ℚ) * (N + q) / t) ^ 3) /
              ((1 + (p : ℚ) * q / t) ^ 3) -
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) =
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) - 1) /
            (t : ℚ) ^ 3) +
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
            invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
            (t : ℚ) ^ 3) +
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) /
            (t : ℚ) ^ 3) +
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
          (((N + q).choose q : ℚ) ^ 3) *
          (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
            invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
            (t : ℚ) ^ 3) := by
    have h1 :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
              (((N + q - 1).choose q : ℚ) ^ 3) *
              (((p : ℚ) * (N + q) / t) ^ 3) /
                ((1 + (p : ℚ) * q / t) ^ 3) -
            (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
              (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) =
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          ((2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) - 1) /
              (t : ℚ) ^ 3 +
          (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
              invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
              (t : ℚ) ^ 3 +
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) /
              (t : ℚ) ^ 3 +
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
              invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
              (t : ℚ) ^ 3) :=
      sum_congr rfl fun q _ => sum_congr rfl fun t ht =>
        unalign_main_term_split hN ht
    rw [h1]
    have h2 :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          ((2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) - 1) /
              (t : ℚ) ^ 3 +
          (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
              invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
              (t : ℚ) ^ 3 +
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) /
              (t : ℚ) ^ 3 +
          (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
            (((N + q).choose q : ℚ) ^ 3) *
            (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
              invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
              (t : ℚ) ^ 3) =
        ∑ q ∈ range N,
          ((∑ t ∈ Icc 1 (p - 1),
            (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
              (((N + q).choose q : ℚ) ^ 3) *
              (invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) - 1) /
                (t : ℚ) ^ 3) +
          (∑ t ∈ Icc 1 (p - 1),
            (2 : ℚ) * t * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
              (((N + q).choose q : ℚ) ^ 3) *
              (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
                invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
                (t : ℚ) ^ 3) +
          (∑ t ∈ Icc 1 (p - 1),
            (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
              (((N + q).choose q : ℚ) ^ 3) *
              invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1) /
                (t : ℚ) ^ 3) +
          (∑ t ∈ Icc 1 (p - 1),
            (p : ℚ) * (N + 2 * q : ℕ) * (p : ℚ) ^ 3 * (N : ℚ) ^ 3 *
              (((N + q).choose q : ℚ) ^ 3) *
              (((1 + (p : ℚ) * q / t)⁻¹ ^ 3) -
                invCubePartial ((p : ℚ) * q / t) (padicValNat p N + 1)) /
                (t : ℚ) ^ 3)) :=
      sum_congr rfl fun q _ => by simp [sum_add_distrib]
    rw [h2]
    simp [sum_add_distrib]
  rw [hterm]
  have hA := unalign_two_t_part_sum hp hp5 hN
  have hB := unalign_two_t_rem_sum hp hp5 hN
  have hC := unalign_prefN_part_sum hp hp5 hN
  have hD := unalign_prefN_rem_sum hp hp5 hN
  simpa using pCongr_add (pCongr_add (pCongr_add hA hB) hC) hD

lemma unalign_sum_pCongr_strong {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [unalign_sum_bilinear hp hN]
  have hXQ := unalign_XQ_sum hp hp5 hN
  have hmain := unalign_main_sum hp hp5 hN
  have hH2 := unalign_H2_block_strong hp hp5 hN
  have hHeq := unalign_H2_sum_eq (p := p) (N := N)
  have hdecomp :
      ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) =
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
          ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
            (((N + q - 1).choose q : ℚ) ^ 3) *
              (((p : ℚ) * (N + q) / t) ^ 3) /
                ((1 + (p : ℚ) * q / t) ^ 3))) +
      (∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
        (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            (((N + q - 1).choose q : ℚ) ^ 3) *
            (((p : ℚ) * (N + q) / t) ^ 3) /
              ((1 + (p : ℚ) * q / t) ^ 3) -
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2)) +
      ((2 : ℚ) * (p : ℚ) ^ 3 *
        (∑ q ∈ range N, ((N + q : ℕ) : ℚ) ^ 3 *
          (((N + q - 1).choose q : ℚ) ^ 3)) *
        harmonicGen 2 (p - 1)) := by
    rw [← hHeq]
    have h1 :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            (((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) =
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
              (((N + q - 1).choose q : ℚ) ^ 3) *
                (((p : ℚ) * (N + q) / t) ^ 3) /
                  ((1 + (p : ℚ) * q / t) ^ 3)) +
          (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
              (((N + q - 1).choose q : ℚ) ^ 3) *
              (((p : ℚ) * (N + q) / t) ^ 3) /
                ((1 + (p : ℚ) * q / t) ^ 3) -
            (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
              (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) +
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) :=
      sum_congr rfl fun q _ => sum_congr rfl fun t _ => by ring
    rw [h1]
    have h2 :
        ∑ q ∈ range N, ∑ t ∈ Icc 1 (p - 1),
          (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
            ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
              (((N + q - 1).choose q : ℚ) ^ 3) *
                (((p : ℚ) * (N + q) / t) ^ 3) /
                  ((1 + (p : ℚ) * q / t) ^ 3)) +
          (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
              (((N + q - 1).choose q : ℚ) ^ 3) *
              (((p : ℚ) * (N + q) / t) ^ 3) /
                ((1 + (p : ℚ) * q / t) ^ 3) -
            (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
              (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) +
          (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
            (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2) =
        ∑ q ∈ range N,
          ((∑ t ∈ Icc 1 (p - 1),
            ((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
              ((((p * N + (p * q + t) - 1).choose (p * q + t) : ℚ) ^ 3) -
                (((N + q - 1).choose q : ℚ) ^ 3) *
                  (((p : ℚ) * (N + q) / t) ^ 3) /
                    ((1 + (p : ℚ) * q / t) ^ 3))) +
          (∑ t ∈ Icc 1 (p - 1),
            (((p * N + 2 * (p * q + t) : ℕ) : ℚ) *
                (((N + q - 1).choose q : ℚ) ^ 3) *
                (((p : ℚ) * (N + q) / t) ^ 3) /
                  ((1 + (p : ℚ) * q / t) ^ 3) -
              (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
                (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2)) +
          (∑ t ∈ Icc 1 (p - 1),
            (2 : ℚ) * (p : ℚ) ^ 3 * ((N + q : ℕ) : ℚ) ^ 3 *
              (((N + q - 1).choose q : ℚ) ^ 3) / (t : ℚ) ^ 2)) :=
      sum_congr rfl fun q _ => by simp [sum_add_distrib]
    rw [h2]
    simp [sum_add_distrib]
  rw [hdecomp]
  simpa using pCongr_add (pCongr_add hXQ hmain) hH2

lemma Ssum_pN_strong {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hN : 0 < N) :
    PCongr p (4 + 4 * padicValNat p N)
      ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Ssum_split_aligned hp hN]
  have hal := aligned_sum_pCongr_strong hp hp5 hN
  have hun := unalign_sum_pCongr_strong hp hp5 hN
  have heq :
      (∑ q ∈ range (N + 1),
          ((p * N + 2 * (p * q) : ℕ) : ℚ) *
            (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3)) +
        (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
          ((p * N + 2 * k : ℕ) : ℚ) *
            (((p * N + k - 1).choose k : ℚ) ^ 3)) -
        (p : ℚ) * Ssum N =
      (∑ q ∈ range (N + 1),
          ((p * N + 2 * (p * q) : ℕ) : ℚ) *
            (((p * N + p * q - 1).choose (p * q) : ℚ) ^ 3) -
        (p : ℚ) * Ssum N) +
      (∑ k ∈ (range (p * N + 1)).filter (fun k => ¬ p ∣ k),
        ((p * N + 2 * k : ℕ) : ℚ) *
          (((p * N + k - 1).choose k : ℚ) ^ 3)) := by
    ring
  rw [heq]
  have hal0 := pCongr_sub_zero hal
  simpa using pCongr_add hal0 hun

lemma a_supercongruence {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N := n * p ^ (r - 1) with hNdef
  have hN : 0 < N := Nat.mul_pos hn (pow_pos hp.pos _)
  have hmul : n * p ^ r = p * N := by
    rw [hNdef]
    nth_rw 1 [← Nat.sub_add_cancel hr]
    rw [pow_succ]
    ring
  have hv : padicValNat p N = padicValNat p n + (r - 1) :=
    padicValNat_mul_p_pow (p := p) (n := n) (r := r - 1) hn.ne'
  have hS : PCongr p (4 + 4 * padicValNat p N)
      ((Ssum (p * N) : ℚ) - (p : ℚ) * Ssum N) 0 :=
    Ssum_pN_strong hp hp5 hN
  have ha : PCongr p (3 + 3 * padicValNat p N) (a (p * N) : ℚ) (a N) := by
    refine pCongr_a_of_Ssum (m := 3 + 3 * padicValNat p N) hp hN ?_
    have hm : ((3 + 3 * padicValNat p N) + 1 + padicValNat p N : ℤ) =
        (4 + 4 * padicValNat p N : ℤ) := by
      push_cast; ring
    simpa [hm] using hS
  have hleN : 3 * r ≤ 3 + 3 * padicValNat p N := by
    rw [hv]
    calc
      3 * r = 3 * (r - 1 + 1) := by rw [Nat.sub_add_cancel hr]
      _ = 3 * (r - 1) + 3 := by ring
      _ ≤ 3 * (padicValNat p n + (r - 1)) + 3 := by
        gcongr; exact Nat.le_add_left _ _
      _ = 3 + 3 * (padicValNat p n + (r - 1)) := by ring
  have hle : ((3 * r : ℕ) : ℤ) ≤ 3 + 3 * padicValNat p N :=
    Nat.cast_le.mpr hleN
  have ha' : PCongr p (3 * r) (a (p * N) : ℚ) (a N) :=
    pCongr_of_le hle ha
  rw [hNdef] at ha'
  rw [← hmul] at ha'
  exact pCongr_nat_modEq hp ha'

theorem foo {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
  a_supercongruence hp hp5 hn hr




