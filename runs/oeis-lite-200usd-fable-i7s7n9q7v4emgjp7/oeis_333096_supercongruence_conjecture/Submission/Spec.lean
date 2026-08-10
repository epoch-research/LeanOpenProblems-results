import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int

-- Generalized binomial coefficient $\binom{r}{k}$ for $r \in \mathbb{Z}, k \in \mathbb{N}$.
-- We use the definition $\binom{r}{k} = \frac{\prod_{i=0}^{k-1} (r-i)}{k!}$ and rely on
-- the known property that this division results in an integer.
def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

-- Helper definition for the generalized coefficient formula.
/--
The $k$-th power series coefficient of $c(x)^r$: $\frac{r}{r+k}\binom{r+2k-1}{k}$.
This expression is known to be an integer for all $r \in \mathbb{Z}$.
-/
def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    -- The division is exact because the coefficient is an integer.
    -- We rely on integer division to compute the result.
    (r * num_choose) / denominator

/--
The generalized sequence $a_m(n)$ is the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{m \cdot n}$ evaluated at $x=1$.
$$a_m(n) = \sum_{k=0}^n [x^k] c(x)^{m n}$$
-/
def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator

section HelperS01

/-! # S01: Generalized integer binomial coefficients `ich` and their API. -/

namespace A333096

open Finset Polynomial

/-- Generalized binomial coefficient over ℤ. -/
noncomputable def ich (r : ℤ) (k : ℕ) : ℤ := Ring.choose r k

@[simp] lemma ich_zero (r : ℤ) : ich r 0 = 1 := Ring.choose_zero_right r

lemma ich_pascal (r : ℤ) (k : ℕ) : ich (r + 1) (k + 1) = ich r k + ich r (k + 1) :=
  Ring.choose_succ_succ r k

@[simp] lemma ich_natCast (n k : ℕ) : ich (n : ℤ) k = n.choose k :=
  Ring.choose_natCast n k

@[simp] lemma ich_zero_left (k : ℕ) : ich 0 k = if k = 0 then 1 else 0 :=
  Ring.choose_zero_ite ℤ k

lemma ich_one_right (r : ℤ) : ich r 1 = r := Ring.choose_one_right r

/-- `k! * ich r k = r(r-1)⋯(r-k+1)`. -/
lemma factorial_mul_ich (r : ℤ) (k : ℕ) :
    (k.factorial : ℤ) * ich r k = (descPochhammer ℤ k).eval r := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) r k
  rw [← Polynomial.eval_eq_smeval] at h
  rw [h, nsmul_eq_mul]
  rfl

lemma prod_range_eq_factorial_mul_ich (r : ℤ) (k : ℕ) :
    (∏ i ∈ Finset.range k, (r - (i : ℤ))) = (k.factorial : ℤ) * ich r k := by
  rw [factorial_mul_ich, descPochhammer_eval_eq_prod_range]

/-- Ratio identity: `(k+1) * ich r (k+1) = (r - k) * ich r k`. -/
lemma ich_ratio (r : ℤ) (k : ℕ) :
    ((k : ℤ) + 1) * ich r (k + 1) = (r - k) * ich r k := by
  have hne : (k.factorial : ℤ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  apply mul_left_cancel₀ hne
  have h1 := factorial_mul_ich r (k + 1)
  have h2 := factorial_mul_ich r k
  have h3 : descPochhammer ℤ (k + 1) = descPochhammer ℤ k * (X - (k : ℤ[X])) :=
    descPochhammer_succ_right (R := ℤ) k
  have h4 : (descPochhammer ℤ (k+1)).eval r
      = (descPochhammer ℤ k).eval r * (r - k) := by
    rw [h3]; simp
  have h5 : ((k+1).factorial : ℤ) = (k + 1 : ℤ) * (k.factorial : ℤ) := by
    push_cast [Nat.factorial_succ]; ring
  calc (k.factorial : ℤ) * (((k:ℤ) + 1) * ich r (k + 1))
      = ((k+1).factorial : ℤ) * ich r (k+1) := by rw [h5]; ring
    _ = (descPochhammer ℤ k).eval r * (r - k) := by rw [h1, h4]
    _ = (r - k) * ((k.factorial : ℤ) * ich r k) := by rw [h2]; ring
    _ = (k.factorial : ℤ) * ((r - (k:ℤ)) * ich r k) := by ring

/-- Absorption: `(k+1) * ich r (k+1) = r * ich (r-1) k`. -/
lemma ich_absorb (r : ℤ) (k : ℕ) :
    ((k : ℤ) + 1) * ich r (k + 1) = r * ich (r - 1) k := by
  have hne : (k.factorial : ℤ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  apply mul_left_cancel₀ hne
  have h1 := factorial_mul_ich r (k + 1)
  have h2 := factorial_mul_ich (r - 1) k
  have h3 : descPochhammer ℤ (k + 1) = X * (descPochhammer ℤ k).comp (X - 1) :=
    descPochhammer_succ_left (R := ℤ) k
  have h4 : (descPochhammer ℤ (k+1)).eval r
      = r * (descPochhammer ℤ k).eval (r - 1) := by
    rw [h3]; simp
  have h5 : ((k+1).factorial : ℤ) = (k + 1 : ℤ) * (k.factorial : ℤ) := by
    push_cast [Nat.factorial_succ]; ring
  calc (k.factorial : ℤ) * (((k:ℤ) + 1) * ich r (k + 1))
      = ((k+1).factorial : ℤ) * ich r (k+1) := by rw [h5]; ring
    _ = r * (descPochhammer ℤ k).eval (r - 1) := by rw [h1, h4]
    _ = r * ((k.factorial : ℤ) * ich (r-1) k) := by rw [h2]
    _ = (k.factorial : ℤ) * (r * ich (r-1) k) := by ring

/-- Reflection: `ich (-r) n = (-1)^n * ich (r + n - 1) n`. -/
lemma ich_neg (r : ℤ) (n : ℕ) : ich (-r) n = (-1 : ℤ) ^ n * ich (r + n - 1) n := by
  show Ring.choose (-r) n = (-1 : ℤ) ^ n * Ring.choose (r + n - 1) n
  have h := Ring.choose_neg (R := ℤ) r n
  rw [h, Int.negOnePow_def, Units.smul_def, zsmul_eq_mul]
  have hcast : (((-1 : ℤˣ) ^ (n : ℤ) : ℤˣ) : ℤ) = (-1 : ℤ) ^ n := by
    rw [zpow_natCast]
    push_cast
    ring
  rw [hcast]
  push_cast
  ring

/-- `mch A j = binom(A + j - 1, j)`, the "multichoose". -/
noncomputable def mch (A : ℤ) (j : ℕ) : ℤ := ich (A + j - 1) j

@[simp] lemma mch_zero (A : ℤ) : mch A 0 = 1 := by simp [mch]

lemma mch_eq_neg_pow_mul_ich (A : ℤ) (j : ℕ) : mch A j = (-1 : ℤ) ^ j * ich (-A) j := by
  rw [ich_neg A j, mch, ← mul_assoc, ← mul_pow]
  simp

lemma ich_neg_eq_neg_pow_mul_mch (A : ℤ) (j : ℕ) : ich (-A) j = (-1 : ℤ) ^ j * mch A j := by
  rw [mch_eq_neg_pow_mul_ich, ← mul_assoc, ← mul_pow]
  simp

lemma mch_pascal (A : ℤ) (j : ℕ) : mch (A + 1) (j + 1) = mch (A + 1) j + mch A (j + 1) := by
  unfold mch
  have e1 : A + 1 + ((j + 1 : ℕ) : ℤ) - 1 = (A + (j:ℤ)) + 1 := by push_cast; ring
  have e2 : A + 1 + (j:ℤ) - 1 = A + (j:ℤ) := by ring
  have e3 : A + ((j + 1 : ℕ) : ℤ) - 1 = A + (j:ℤ) := by push_cast; ring
  rw [e1, e2, e3, ich_pascal]

/-- Hockey stick: `∑_{j ≤ s} mch A j = mch (A+1) s`. -/
lemma mch_hockey (A : ℤ) (s : ℕ) : ∑ j ∈ Finset.range (s + 1), mch A j = mch (A + 1) s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, ← mch_pascal]

/-- `mch` of a positive integer is a `Nat.choose`. -/
lemma mch_natCast (B : ℕ) (hB : 1 ≤ B) (j : ℕ) : mch (B : ℤ) j = ((B - 1 + j).choose j : ℤ) := by
  unfold mch
  have : (B : ℤ) + j - 1 = ((B - 1 + j : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hB]; ring
  rw [this, ich_natCast]

lemma ich_neg_natCast (B : ℕ) (hB : 1 ≤ B) (j : ℕ) :
    ich (-(B : ℤ)) j = (-1:ℤ)^j * ((B - 1 + j).choose j : ℤ) := by
  rw [ich_neg_eq_neg_pow_mul_mch, mch_natCast B hB]

/-- For `0 ≤ n < k`, `ich n k = 0`. -/
lemma ich_natCast_eq_zero {n k : ℕ} (h : n < k) : ich (n : ℤ) k = 0 := by
  rw [ich_natCast]
  simp [Nat.choose_eq_zero_of_lt h]

end A333096

end HelperS01

section HelperS02

/-! # S02: `POge p n x`: the p-adic valuation of the rational `x` is at least `n`. -/

set_option linter.unusedSectionVars false

namespace A333096

open Finset

/-- `POge p n x` means `v_p(x) ≥ n` (with `x = 0` allowed). -/
def POge (p : ℕ) (n : ℤ) (x : ℚ) : Prop :=
  ∃ a b : ℤ, ¬((p:ℤ) ∣ b) ∧ x * (b:ℚ) = (p:ℚ) ^ n * (a:ℚ)

/-- `EOrd p e d`: the integer `d` has p-adic valuation exactly `e`. -/
def EOrd (p : ℕ) (e : ℕ) (d : ℤ) : Prop :=
  (p:ℤ)^e ∣ d ∧ ¬((p:ℤ)^(e+1) ∣ d)

variable {p : ℕ} (hp : p.Prime)

section basic
include hp

lemma pQ_ne_zero : (p:ℚ) ≠ 0 := by
  exact_mod_cast hp.ne_zero

lemma not_dvd_one : ¬((p:ℤ) ∣ (1:ℤ)) := by
  intro h
  have := Int.eq_one_of_dvd_one (by norm_num) h
  have h2 := hp.two_le
  omega

lemma POge_zero (n : ℤ) : POge p n 0 := by
  exact ⟨0, 1, not_dvd_one hp, by simp⟩

lemma POge_of_dvd {t : ℕ} {z : ℤ} (h : (p:ℤ)^t ∣ z) : POge p (t:ℤ) (z:ℚ) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, 1, not_dvd_one hp, ?_⟩
  rw [ha]
  push_cast
  rw [zpow_natCast]
  ring

lemma POge_int (z : ℤ) : POge p 0 (z:ℚ) := POge_of_dvd hp (t := 0) (by simp)

lemma POge_pow (t : ℤ) : POge p t ((p:ℚ)^t) := by
  exact ⟨1, 1, not_dvd_one hp, by simp⟩

lemma POge_mul {m n : ℤ} {x y : ℚ} (hx : POge p m x) (hy : POge p n y) :
    POge p (m + n) (x * y) := by
  obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
  obtain ⟨a₂, b₂, hb₂, e₂⟩ := hy
  refine ⟨a₁ * a₂, b₁ * b₂, ?_, ?_⟩
  · intro h
    rcases (Int.Prime.dvd_mul' (by exact_mod_cast hp) h) with h1 | h1
    exacts [hb₁ h1, hb₂ h1]
  · push_cast
    rw [zpow_add₀ (pQ_ne_zero hp)]
    calc x * y * ((b₁:ℚ) * b₂) = (x * b₁) * (y * b₂) := by ring
      _ = ((p:ℚ)^m * a₁) * ((p:ℚ)^n * a₂) := by rw [e₁, e₂]
      _ = (p:ℚ)^m * (p:ℚ)^n * (a₁ * a₂) := by ring

lemma POge_add {n : ℤ} {x y : ℚ} (hx : POge p n x) (hy : POge p n y) :
    POge p n (x + y) := by
  obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
  obtain ⟨a₂, b₂, hb₂, e₂⟩ := hy
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, ?_, ?_⟩
  · intro h
    rcases (Int.Prime.dvd_mul' (by exact_mod_cast hp) h) with h1 | h1
    exacts [hb₁ h1, hb₂ h1]
  · push_cast
    calc (x + y) * ((b₁:ℚ) * b₂) = (x * b₁) * b₂ + (y * b₂) * b₁ := by ring
      _ = ((p:ℚ)^n * a₁) * b₂ + ((p:ℚ)^n * a₂) * b₁ := by rw [e₁, e₂]
      _ = (p:ℚ)^n * ((a₁:ℚ) * b₂ + (a₂:ℚ) * b₁) := by ring

lemma POge_neg {n : ℤ} {x : ℚ} (hx : POge p n x) : POge p n (-x) := by
  obtain ⟨a, b, hb, e⟩ := hx
  exact ⟨-a, b, hb, by push_cast; rw [neg_mul, e]; ring⟩

lemma POge_mono {m n : ℤ} {x : ℚ} (hmn : m ≤ n) (hx : POge p n x) : POge p m x := by
  obtain ⟨a, b, hb, e⟩ := hx
  refine ⟨(p:ℤ)^((n - m).toNat) * a, b, hb, ?_⟩
  rw [e]
  push_cast
  rw [← zpow_natCast (p:ℚ) ((n-m).toNat), Int.toNat_of_nonneg (by omega), ← mul_assoc,
    ← zpow_add₀ (pQ_ne_zero hp)]
  congr 2
  omega

lemma POge_sum {n : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, POge p n (f i)) : POge p n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using POge_zero hp n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact POge_add hp (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma POge_max {m n : ℤ} {x : ℚ} (hm : POge p m x) (hn : POge p n x) :
    POge p (max m n) x := by
  rcases le_total m n with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- Division by an integer of exact valuation `e`. -/
lemma POge_div {n : ℤ} {x : ℚ} {e : ℕ} {d : ℤ} (hx : POge p n x) (hd : EOrd p e d) :
    POge p (n - e) (x / (d:ℚ)) := by
  obtain ⟨a, b, hb, hxe⟩ := hx
  obtain ⟨⟨d', hd'⟩, hnd⟩ := hd
  have hpd' : ¬ ((p:ℤ) ∣ d') := by
    intro ⟨d'', hd''⟩
    exact hnd ⟨d'', by rw [hd', hd'']; ring⟩
  have hd0 : (d:ℚ) ≠ 0 := by
    intro h
    have : d = 0 := by exact_mod_cast h
    apply hnd
    simp [this]
  refine ⟨a, b * d', ?_, ?_⟩
  · intro h
    rcases (Int.Prime.dvd_mul' (by exact_mod_cast hp) h) with h1 | h1
    exacts [hb h1, hpd' h1]
  · have hpe : ((p:ℚ)^e : ℚ) ≠ 0 := pow_ne_zero _ (pQ_ne_zero hp)
    have hdq : (d:ℚ) = (p:ℚ)^e * (d':ℚ) := by
      rw [hd']; push_cast; ring
    have hd'0 : (d':ℚ) ≠ 0 := by
      intro h
      apply hd0
      rw [hdq, h, mul_zero]
    have h2 : (d':ℚ) / (d:ℚ) = ((p:ℚ)^(e:ℕ))⁻¹ := by
      rw [hdq]
      field_simp
    have h1 : x / (d:ℚ) * ((b:ℚ) * (d':ℚ)) = (x * (b:ℚ)) * ((d':ℚ) / (d:ℚ)) := by
      ring
    push_cast
    rw [h1, hxe, h2, zpow_sub₀ (pQ_ne_zero hp), zpow_natCast]
    ring

/-- Extraction: a `POge` bound on an integer yields divisibility. -/
lemma dvd_of_POge {t : ℕ} {D : ℤ} (h : POge p (t:ℤ) ((D:ℤ):ℚ)) : (p:ℤ)^t ∣ D := by
  obtain ⟨a, b, hb, e⟩ := h
  rw [zpow_natCast] at e
  have e' : ((D * b : ℤ) : ℚ) = (((p:ℤ)^t * a : ℤ) : ℚ) := by
    push_cast
    exact_mod_cast e
  have eZ : D * b = (p:ℤ)^t * a := by exact_mod_cast e'
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime ((p:ℤ)^t) b :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpp).mpr hb)
  exact hcop.dvd_of_dvd_mul_right ⟨a, eZ⟩

end basic

section eord

lemma EOrd_mul {e f : ℕ} {x y : ℤ} (hp : p.Prime) (hx : EOrd p e x) (hy : EOrd p f y) :
    EOrd p (e + f) (x * y) := by
  obtain ⟨⟨x', hx'⟩, hnx⟩ := hx
  obtain ⟨⟨y', hy'⟩, hny⟩ := hy
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpx' : ¬ ((p:ℤ) ∣ x') := fun ⟨u, hu⟩ => hnx ⟨u, by rw [hx', hu]; ring⟩
  have hpy' : ¬ ((p:ℤ) ∣ y') := fun ⟨u, hu⟩ => hny ⟨u, by rw [hy', hu]; ring⟩
  constructor
  · exact ⟨x' * y', by rw [hx', hy']; ring⟩
  · intro ⟨u, hu⟩
    have h1 : (p:ℤ)^(e+f) * (x' * y') = (p:ℤ)^(e+f) * ((p:ℤ) * u) := by
      calc (p:ℤ)^(e+f) * (x' * y') = x * y := by rw [hx', hy']; ring
        _ = (p:ℤ)^(e+f+1) * u := hu
        _ = (p:ℤ)^(e+f) * ((p:ℤ) * u) := by ring
    have h2 : x' * y' = (p:ℤ) * u := by
      have hpef : ((p:ℤ)^(e+f)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      exact mul_left_cancel₀ hpef h1
    rcases hpp.dvd_mul.mp ⟨u, h2⟩ with h | h
    exacts [hpx' h, hpy' h]

lemma EOrd_one (hp : p.Prime) : EOrd p 0 1 := by
  refine ⟨by simp, ?_⟩
  rw [pow_one]
  exact not_dvd_one hp

lemma EOrd_prod {ι : Type*} (hp : p.Prime) (s : Finset ι) (e : ι → ℕ) (x : ι → ℤ)
    (h : ∀ i ∈ s, EOrd p (e i) (x i)) :
    EOrd p (∑ i ∈ s, e i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using EOrd_one hp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact EOrd_mul hp (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma EOrd_padicValNat (hp : p.Prime) {s : ℕ} (hs : s ≠ 0) :
    EOrd p (padicValNat p s) (s : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · exact_mod_cast Int.natCast_dvd_natCast.mpr pow_padicValNat_dvd
  · intro h
    have h' : p ^ (padicValNat p s + 1) ∣ s := by exact_mod_cast h
    exact pow_succ_padicValNat_not_dvd hs h'

end eord

end A333096

end HelperS02

section HelperS03

/-! # S03: Legendre and Kummer valuation facts; D1, D2 wrappers. -/

set_option linter.unusedSectionVars false

namespace A333096

open Finset Nat

variable {p : ℕ} (hp : p.Prime)
include hp

/-! ## Legendre-type bounds -/

/-- `(p-1) * ν(a!) ≤ a - 1` (trivially true for `a = 0`). -/
lemma legendre_bound (a : ℕ) : (p - 1) * padicValNat p a.factorial ≤ a - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) (by omega : a ≠ 0)
    omega

lemma four_mul_nu_factorial_le (hp5 : 5 ≤ p) (c : ℕ) :
    4 * padicValNat p c.factorial ≤ c - 1 := by
  have h := legendre_bound hp c
  have h4 : 4 ≤ p - 1 := by omega
  calc 4 * padicValNat p c.factorial ≤ (p - 1) * padicValNat p c.factorial :=
        Nat.mul_le_mul_right _ h4
    _ ≤ c - 1 := h

/-- `ν(a!) ≤ i - 1` when `a + 2 ≤ i * (p - 1)`. -/
lemma nu_factorial_le {i a : ℕ} (hi : 1 ≤ i) (h : a + 2 ≤ i * (p - 1)) :
    padicValNat p a.factorial + 1 ≤ i := by
  have hleg := legendre_bound hp a
  by_contra hcon
  push_neg at hcon
  have h2 : i * (p - 1) ≤ padicValNat p a.factorial * (p - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_comm (padicValNat p a.factorial) (p - 1)] at h2
  omega

lemma nu_factorial_eq_zero {c : ℕ} (h : c < p) : padicValNat p c.factorial = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  have := hp.dvd_factorial.mp hd
  omega

/-- valuation of `t ≤ A` is at most `log p A`. -/
lemma nu_le_log {t A : ℕ} (ht : 1 ≤ t) (hA : t ≤ A) : padicValNat p t ≤ Nat.log p A := by
  have h1 : p ^ padicValNat p t ≤ t := Nat.le_of_dvd ht pow_padicValNat_dvd
  exact (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mpr (h1.trans hA)

lemma nu_lt_of_lt_pow {t v : ℕ} (ht : 1 ≤ t) (h : t < p ^ v) : padicValNat p t < v := by
  have h1 : p ^ padicValNat p t ≤ t := Nat.le_of_dvd ht pow_padicValNat_dvd
  have : p ^ padicValNat p t < p ^ v := lt_of_le_of_lt h1 h
  exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp this

lemma two_v_add_one_lt {v : ℕ} (hp5 : 5 ≤ p) (hv : 1 ≤ v) : 2 * v + 1 < p ^ v := by
  induction v with
  | zero => omega
  | succ v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv'
    · simpa using by omega
    · have h1 := ih hv'
      have h2 : p ^ v * 1 ≤ p ^ v * (p - 1) := by
        apply Nat.mul_le_mul_left
        omega
      have h3 : p ^ (v + 1) = p ^ v * (p - 1) + p ^ v := by
        have : p ^ (v+1) = p ^ v * p := by ring
        rw [this]
        have hpp : p ^ v * p = p ^ v * (p - 1) + p ^ v * 1 := by
          rw [← Nat.mul_add]
          congr 1
          omega
        omega
      omega

/-! ## Kummer lower bounds -/

/-- Kummer bound (N2): if `p^v ∣ B`, `B ≥ 1`, `K ≥ 1` then
`ν(choose (B + K - 1) K) ≥ v - ν(K)` (in the safe form). -/
lemma kummer_N2 {v B K : ℕ} (hB : p ^ v ∣ B) (hB1 : 1 ≤ B) (hK : 1 ≤ K) :
    v ≤ padicValNat p ((B + K - 1).choose K) + min v (padicValNat p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set νK := padicValNat p K with hνK
  rcases le_or_gt v νK with hcase | hcase
  · omega
  -- now νK < v; show ν(choose) ≥ v - νK
  have hBK : B + K - 1 = (B - 1) + K := by omega
  set b := Nat.log p ((B - 1) + K) + 1 with hb
  have hchoose := padicValNat_choose' (p := p) (n := B - 1) (k := K) (b := b)
    (by omega)
  have hsub : Finset.Ico (νK + 1) (v + 1) ⊆
      {i ∈ Finset.Ico 1 b | p ^ i ≤ K % p ^ i + (B - 1) % p ^ i} := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have hiv : i ≤ v := by omega
    have hpiB : p ^ i ∣ B := dvd_trans (pow_dvd_pow p hiv) hB
    have hpi1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.pos
    have hpile : p ^ i ≤ B := Nat.le_of_dvd (by omega) hpiB
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · -- i < b
      have : p ^ i ≤ (B - 1) + K := by omega
      have := (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mpr this
      omega
    · -- carry condition
      have hKmod : 1 ≤ K % p ^ i := by
        rcases Nat.eq_zero_or_pos (K % p ^ i) with h0 | h1
        · exfalso
          have hdvd : p ^ i ∣ K := Nat.dvd_iff_mod_eq_zero.mpr h0
          have : i ≤ νK := by
            rw [hνK]
            exact (padicValNat_dvd_iff_le (by omega)).mp hdvd
          omega
        · exact h1
      have hBmod : (B - 1) % p ^ i = p ^ i - 1 := by
        obtain ⟨m, hm⟩ := hpiB
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with rfl | h
          · omega
          · exact h
        have e : p ^ i * m = p ^ i * (m - 1) + p ^ i := by
          have hm' : m = (m - 1) + 1 := by omega
          calc p ^ i * m = p ^ i * ((m - 1) + 1) := by rw [← hm']
            _ = p ^ i * (m - 1) + p ^ i := by ring
        have hBrw : B - 1 = (p ^ i - 1) + p ^ i * (m - 1) := by omega
        rw [hBrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
  have hcard : v - νK ≤ padicValNat p ((B + K - 1).choose K) := by
    rw [hBK, hchoose]
    calc v - νK = #(Finset.Ico (νK + 1) (v + 1)) := by
          rw [Nat.card_Ico]; omega
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-- Kummer bound (N1): if `p^v ∣ B`, `1 ≤ K ≤ B` then `ν(choose B K) ≥ v - ν(K)`. -/
lemma kummer_N1 {v B K : ℕ} (hB : p ^ v ∣ B) (hK : 1 ≤ K) (hKB : K ≤ B) :
    v ≤ padicValNat p (B.choose K) + min v (padicValNat p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set νK := padicValNat p K with hνK
  rcases le_or_gt v νK with hcase | hcase
  · omega
  -- νK < v. First: K < B (else ν K ≥ v).
  have hKltB : K < B := by
    rcases Nat.lt_or_ge K B with h | h
    · exact h
    · exfalso
      have : K = B := by omega
      subst this
      have : v ≤ νK := by
        rw [hνK]
        exact (padicValNat_dvd_iff_le (by omega)).mp hB
      omega
  set b := Nat.log p B + 1 with hb
  have hchoose := padicValNat_choose (p := p) (n := B) (k := K) (b := b) hKB (by omega)
  have hsub : Finset.Ico (νK + 1) (v + 1) ⊆
      {i ∈ Finset.Ico 1 b | p ^ i ≤ K % p ^ i + (B - K) % p ^ i} := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have hiv : i ≤ v := by omega
    have hpiB : p ^ i ∣ B := dvd_trans (pow_dvd_pow p hiv) hB
    have hpi1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.pos
    have hpile : p ^ i ≤ B := Nat.le_of_dvd (by omega) hpiB
    rw [Finset.mem_filter, Finset.mem_Ico]
    have hKmod : 1 ≤ K % p ^ i := by
      rcases Nat.eq_zero_or_pos (K % p ^ i) with h0 | h1
      · exfalso
        have hdvd : p ^ i ∣ K := Nat.dvd_iff_mod_eq_zero.mpr h0
        have : i ≤ νK := by
          rw [hνK]
          exact (padicValNat_dvd_iff_le (by omega)).mp hdvd
        omega
      · exact h1
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have := (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mpr hpile
      omega
    · -- carry condition: (B - K) % p^i = p^i - K % p^i
      obtain ⟨m, hm⟩ := hpiB
      have hq : K = p ^ i * (K / p ^ i) + K % p ^ i := (Nat.div_add_mod K (p ^ i)).symm
      set κ := K % p ^ i with hκ
      set q := K / p ^ i with hq'
      have hκlt : κ < p ^ i := Nat.mod_lt _ (by omega)
      have hmq : q + 1 ≤ m := by
        by_contra hcon
        push_neg at hcon
        -- m ≤ q so B ≤ p^i q ≤ K - κ < K
        have h1 : B ≤ p ^ i * q := by
          rw [hm]
          exact Nat.mul_le_mul_left _ (by omega)
        have h2 : p ^ i * q ≤ K := by omega
        omega
      have e1 : p ^ i * m = p ^ i * (m - q - 1) + p ^ i * q + p ^ i := by
        have e3 : m = (m - q - 1) + q + 1 := by omega
        calc p ^ i * m = p ^ i * ((m - q - 1) + q + 1) := by rw [← e3]
          _ = p ^ i * (m - q - 1) + p ^ i * q + p ^ i := by ring
      have hBK : B - K = (p ^ i - κ) + p ^ i * (m - q - 1) := by omega
      have : (B - K) % p ^ i = p ^ i - κ := by
        rw [hBK, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
  have hcard : v - νK ≤ padicValNat p (B.choose K) := by
    rw [hchoose]
    calc v - νK = #(Finset.Ico (νK + 1) (v + 1)) := by
          rw [Nat.card_Ico]; omega
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-! ## POge wrappers (D2, D1) -/

/-- D2: `v_p(ich (-S) K) ≥ v - min v ν(K)` when `p^v ∣ S`, `K ≥ 1`. -/
lemma D2 {v K : ℕ} {S : ℤ} (hS : (p:ℤ)^v ∣ S) (hK : 1 ≤ K) :
    POge p ((v:ℤ) - min v (padicValNat p K)) ((ich (-S) K : ℤ) : ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases lt_trichotomy S 0 with hneg | hzero | hpos
  · -- S < 0 : ich (-S) K = choose B K with B = (-S).toNat ≥ 1
    set B := (-S).toNat with hB
    have hSB : -S = (B : ℤ) := by
      rw [hB, Int.toNat_of_nonneg (by omega)]
    have hpvB : p ^ v ∣ B := by
      have h1 : (p:ℤ)^v ∣ (B:ℤ) := by
        rw [← hSB]
        exact Dvd.dvd.neg_right hS
      exact_mod_cast h1
    have hichB : ich (-S) K = ((B.choose K : ℕ) : ℤ) := by
      rw [hSB, ich_natCast]
    rcases Nat.lt_or_ge B K with hlt | hge
    · -- choose = 0
      rw [hichB, Nat.choose_eq_zero_of_lt hlt]
      simpa using POge_zero hp _
    · have hkum := kummer_N1 hp hpvB hK hge
      have hle : v - min v (padicValNat p K) ≤ padicValNat p (B.choose K) := by omega
      have hdvd : p ^ (v - min v (padicValNat p K)) ∣ B.choose K :=
        dvd_trans (pow_dvd_pow p hle) pow_padicValNat_dvd
      have hdvd' : (p:ℤ) ^ (v - min v (padicValNat p K)) ∣ (B.choose K : ℤ) := by
        exact_mod_cast hdvd
      have := POge_of_dvd hp hdvd'
      rw [hichB]
      have harith : ((v - min v (padicValNat p K) : ℕ) : ℤ)
          = (v:ℤ) - min v (padicValNat p K) := by
        have : min v (padicValNat p K) ≤ v := Nat.min_le_left _ _
        push_cast [Nat.cast_sub this]
        omega
      rwa [harith] at this
  · -- S = 0: ich 0 K = 0
    subst hzero
    have hK0 : K ≠ 0 := by omega
    rw [show (-(0:ℤ)) = 0 by ring, ich_zero_left, if_neg hK0]
    simpa using POge_zero hp _
  · -- S > 0: ich (-S) K = ± choose (S + K - 1) K
    set B := S.toNat with hB
    have hSB : S = (B : ℤ) := by
      rw [hB, Int.toNat_of_nonneg (by omega)]
    have hB1 : 1 ≤ B := by omega
    have hpvB : p ^ v ∣ B := by
      have h1 : (p:ℤ)^v ∣ (B:ℤ) := by rw [← hSB]; exact hS
      exact_mod_cast h1
    have hich : ich (-S) K = (-1:ℤ)^K * ((B - 1 + K).choose K : ℤ) := by
      rw [hSB]
      exact ich_neg_natCast B hB1 K
    have hBK : B - 1 + K = B + K - 1 := by omega
    have hkum := kummer_N2 hp hpvB hB1 hK
    have hle : v - min v (padicValNat p K) ≤ padicValNat p ((B + K - 1).choose K) := by omega
    have hdvd : p ^ (v - min v (padicValNat p K)) ∣ (B + K - 1).choose K :=
      dvd_trans (pow_dvd_pow p hle) pow_padicValNat_dvd
    have hdvd' : (p:ℤ) ^ (v - min v (padicValNat p K)) ∣ ((B - 1 + K).choose K : ℤ) := by
      rw [hBK]
      exact_mod_cast hdvd
    have h1 := POge_of_dvd hp hdvd'
    have h2 := POge_int hp ((-1:ℤ)^K)
    have h3 := POge_mul hp h2 h1
    rw [zero_add] at h3
    have harith : ((v - min v (padicValNat p K) : ℕ) : ℤ)
        = (v:ℤ) - min v (padicValNat p K) := by
      have : min v (padicValNat p K) ≤ v := Nat.min_le_left _ _
      push_cast [Nat.cast_sub this]
      omega
    rw [harith] at h3
    rw [hich]
    push_cast at h3 ⊢
    exact h3

/-- D1: `v_p(ich (-m₀) i) ≥ v - min v ν(i)` when `p^v ∣ m₀`, `i ≥ 1`. -/
lemma D1 {v i : ℕ} {m₀ : ℤ} (hm : (p:ℤ)^v ∣ m₀) (hi : 1 ≤ i) :
    POge p ((v:ℤ) - min v (padicValNat p i)) ((ich (-m₀) i : ℤ) : ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- i * ich (-m₀) i = (-m₀) * ich (-m₀ - 1) (i-1)
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have habs := ich_absorb (-m₀) k
  -- POge of the numerator
  have h1 : POge p (v:ℤ) ((-m₀ : ℤ) : ℚ) := by
    exact POge_of_dvd hp (Dvd.dvd.neg_right hm)
  have h2 := POge_int hp (ich (-m₀ - 1) k)
  have h3 := POge_mul hp h1 h2
  rw [add_zero] at h3
  have h4 : POge p ((v:ℤ) - padicValNat p (k+1))
      ((((-m₀ : ℤ) : ℚ) * (ich (-m₀ - 1) k : ℤ)) / ((k+1 : ℕ) : ℤ)) := by
    have hE : EOrd p (padicValNat p (k+1)) ((k+1 : ℕ) : ℤ) :=
      EOrd_padicValNat hp (by omega)
    exact POge_div hp h3 hE
  have heq : ((ich (-m₀) (k+1) : ℤ) : ℚ)
      = (((-m₀ : ℤ) : ℚ) * (ich (-m₀ - 1) k : ℤ)) / ((k+1 : ℕ) : ℤ) := by
    rw [eq_div_iff (by push_cast; positivity)]
    have hQ : (((k:ℤ) + 1) * ich (-m₀) (k+1) : ℤ) = ((-m₀ * ich (-m₀ - 1) k : ℤ)) := habs
    have := congrArg (fun z : ℤ => (z : ℚ)) hQ
    push_cast at this ⊢
    linarith
  have h5 : POge p ((v:ℤ) - padicValNat p (k+1)) ((ich (-m₀) (k+1) : ℤ) : ℚ) := by
    rwa [heq]
  have h6 := POge_int hp (ich (-m₀) (k+1))
  have h7 := POge_max hp h5 h6
  have : max ((v:ℤ) - padicValNat p (k+1)) 0 = (v:ℤ) - min v (padicValNat p (k+1)) := by
    rcases le_total (v:ℕ) (padicValNat p (k+1)) with h | h
    · rw [min_eq_left h]
      have : (v:ℤ) - padicValNat p (k+1) ≤ 0 := by
        have := Int.ofNat_le.mpr h
        omega
      omega
    · rw [min_eq_right h]
      have : (0:ℤ) ≤ (v:ℤ) - padicValNat p (k+1) := by
        have := Int.ofNat_le.mpr h
        omega
      omega
  rwa [this] at h7

/-- Exact valuation of `N - s` when `p^v ∣ N` and `ν(s) < v`. -/
lemma EOrd_sub_of_dvd {v : ℕ} {N : ℤ} (hN : (p:ℤ)^v ∣ N) {s : ℕ} (hs : 1 ≤ s)
    (hsv : padicValNat p s < v) : EOrd p (padicValNat p s) (N - s) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set e := padicValNat p s with he
  have h1 : (p:ℤ)^e ∣ (s:ℤ) := by
    exact_mod_cast Int.natCast_dvd_natCast.mpr pow_padicValNat_dvd
  have h2 : (p:ℤ)^e ∣ N := dvd_trans (pow_dvd_pow _ (by omega)) hN
  constructor
  · exact _root_.dvd_sub h2 h1
  · intro hcon
    have h3 : (p:ℤ)^(e+1) ∣ N := dvd_trans (pow_dvd_pow _ (by omega)) hN
    have h4 : (p:ℤ)^(e+1) ∣ (s:ℤ) := by
      have := _root_.dvd_sub h3 hcon
      simpa using this
    have h5 : p^(e+1) ∣ s := by exact_mod_cast h4
    exact pow_succ_padicValNat_not_dvd (by omega) h5

end A333096

end HelperS03

section HelperS04

/-! # S04: Stirling numbers (2nd kind), W-identity, A_c = 0. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset Polynomial

/-! ## Stirling numbers of the second kind -/

def S2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | c + 1, j + 1 => (j + 1) * S2 c (j + 1) + S2 c j

@[simp] lemma S2_zero_zero : S2 0 0 = 1 := rfl
@[simp] lemma S2_zero_succ (j : ℕ) : S2 0 (j + 1) = 0 := rfl
@[simp] lemma S2_succ_zero (c : ℕ) : S2 (c + 1) 0 = 0 := rfl
lemma S2_succ_succ (c j : ℕ) : S2 (c + 1) (j + 1) = (j + 1) * S2 c (j + 1) + S2 c j := rfl

lemma S2_eq_zero_of_lt : ∀ {c j : ℕ}, c < j → S2 c j = 0 := by
  intro c
  induction c with
  | zero =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rfl
  | succ c ih =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [S2_succ_succ, ih (by omega), ih (by omega)]
    ring

/-- `K^c = ∑_t S2(c,t) t! C(K,t)` in ℤ. -/
lemma pow_eq_sum_S2 (K c : ℕ) :
    ((K : ℤ))^c
      = ∑ t ∈ Finset.range (c + 1), (S2 c t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hstep : ∀ t : ℕ,
        (K:ℤ) * ((S2 c t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ))
          = (S2 c t : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ)
            + (t:ℤ) * ((S2 c t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ)) := by
      intro t
      have hratio : ((t:ℤ) + 1) * ich (K:ℤ) (t + 1) = ((K:ℤ) - t) * ich (K:ℤ) t :=
        ich_ratio (K:ℤ) t
      rw [ich_natCast, ich_natCast] at hratio
      have hfac : ((t+1).factorial : ℤ) = ((t:ℤ) + 1) * (t.factorial : ℤ) := by
        push_cast [Nat.factorial_succ]
        ring
      rw [hfac]
      linear_combination (-(S2 c t : ℤ) * (t.factorial : ℤ)) * hratio
    have hmain : (K:ℤ)^(c+1)
        = (∑ t ∈ Finset.range (c + 1),
            (S2 c t : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ))
          + ∑ t ∈ Finset.range (c + 1),
            (t:ℤ) * ((S2 c t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ)) := by
      calc (K:ℤ)^(c+1) = (K:ℤ) * (K:ℤ)^c := by ring
        _ = ∑ t ∈ Finset.range (c + 1),
              (K:ℤ) * ((S2 c t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ)) := by
            rw [ih, Finset.mul_sum]
        _ = _ := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun t _ => hstep t
    -- second sum: shift index
    have hshift : (∑ t ∈ Finset.range (c + 1),
          (t:ℤ) * ((S2 c t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ)))
        = ∑ t ∈ Finset.range c,
            ((t:ℤ)+1) * ((S2 c (t+1) : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ)) := by
      rw [Finset.sum_range_succ' (fun t => (t:ℤ) * ((S2 c t : ℤ) * (t.factorial : ℤ)
        * (K.choose t : ℤ))) c]
      push_cast
      ring
    -- RHS: expand
    have hRHS : (∑ t ∈ Finset.range (c + 2), (S2 (c+1) t : ℤ) * (t.factorial : ℤ) * (K.choose t : ℤ))
        = ∑ t ∈ Finset.range (c + 1),
            (S2 (c+1) (t+1) : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ) := by
      rw [Finset.sum_range_succ' (fun t => (S2 (c+1) t : ℤ) * (t.factorial : ℤ)
        * (K.choose t : ℤ)) (c+1)]
      simp
    rw [hRHS]
    have hsplit : ∀ t : ℕ, (S2 (c+1) (t+1) : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ)
        = ((t:ℤ)+1) * ((S2 c (t+1) : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ))
          + (S2 c t : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ) := by
      intro t
      rw [S2_succ_succ]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_add_distrib, hmain, hshift]
    have hA' : ∑ t ∈ Finset.range (c + 1),
          ((t:ℤ)+1) * ((S2 c (t+1) : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ))
        = ∑ t ∈ Finset.range c,
          ((t:ℤ)+1) * ((S2 c (t+1) : ℤ) * ((t+1).factorial : ℤ) * (K.choose (t+1) : ℤ)) := by
      rw [Finset.sum_range_succ,
        show S2 c (c+1) = 0 from S2_eq_zero_of_lt (by omega)]
      push_cast
      ring
    rw [hA']
    ring

/-- Alternating double-choose sum. -/
lemma alt_sum_choose_choose (j t : ℕ) :
    ∑ K ∈ Finset.range (j + 1), (j.choose K : ℤ) * (K.choose t : ℤ) * (-1)^K
      = if t = j then (-1:ℤ)^j else 0 := by
  rcases Nat.lt_or_ge j t with hjt | htj
  · -- t > j : all terms vanish
    rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro K hK
    rw [Finset.mem_range] at hK
    have : K.choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this]
    push_cast
    ring
  · -- t ≤ j
    have hzero : ∀ K ∈ Finset.range t, (j.choose K : ℤ) * (K.choose t : ℤ) * (-1)^K = 0 := by
      intro K hK
      rw [Finset.mem_range] at hK
      rw [Nat.choose_eq_zero_of_lt hK]
      push_cast
      ring
    have hsplit : ∑ K ∈ Finset.range (j + 1), (j.choose K : ℤ) * (K.choose t : ℤ) * (-1)^K
        = ∑ K ∈ Ico t (j + 1), (j.choose K : ℤ) * (K.choose t : ℤ) * (-1)^K := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le t) (by omega)]
      rw [← Finset.range_eq_Ico]
      rw [Finset.sum_eq_zero hzero, zero_add]
    rw [hsplit, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ r < j + 1 - t,
        ((j.choose (t + r) : ℤ) * ((t + r).choose t : ℤ) * (-1)^(t + r))
          = (j.choose t : ℤ) * ((-1:ℤ)^t) * (((j - t).choose r : ℤ) * (-1)^r) := by
      intro r hr
      have hmul := Nat.choose_mul (n := j) (k := t + r) (s := t) (by omega)
      have h1 : (t + r) - t = r := by omega
      rw [h1] at hmul
      have : (j.choose (t+r) : ℤ) * ((t+r).choose t : ℤ)
          = (j.choose t : ℤ) * ((j - t).choose r : ℤ) := by exact_mod_cast hmul
      calc (j.choose (t + r) : ℤ) * ((t + r).choose t : ℤ) * (-1)^(t + r)
          = ((j.choose (t+r) : ℤ) * ((t+r).choose t : ℤ)) * ((-1:ℤ)^t * (-1)^r) := by
            rw [pow_add]
        _ = ((j.choose t : ℤ) * ((j - t).choose r : ℤ)) * ((-1:ℤ)^t * (-1)^r) := by rw [this]
        _ = _ := by ring
    have hjt1 : j + 1 - t = (j - t) + 1 := by omega
    rw [Finset.sum_congr rfl (fun r hr => hterm r (Finset.mem_range.mp hr))]
    rw [← Finset.mul_sum, hjt1]
    have halt : ∑ r ∈ Finset.range ((j - t) + 1), ((j - t).choose r : ℤ) * (-1)^r
        = if j - t = 0 then 1 else 0 := by
      have := Int.alternating_sum_range_choose (n := j - t)
      rw [← this]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [halt]
    rcases Nat.eq_or_lt_of_le htj with heq | hlt
    · rw [if_pos (by omega), if_pos heq]
      subst heq
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      ring

/-- W-identity: `∑_K C(j,K)(-1)^K K^c = (-1)^j j! S2(c,j)`. -/
lemma W_identity (c j : ℕ) :
    ∑ K ∈ Finset.range (j + 1), (j.choose K : ℤ) * (-1)^K * (K:ℤ)^c
      = (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) := by
  have hexp : ∑ K ∈ Finset.range (j + 1), (j.choose K : ℤ) * (-1)^K * (K:ℤ)^c
      = ∑ K ∈ Finset.range (j + 1), ∑ t ∈ Finset.range (c + 1),
          (S2 c t : ℤ) * (t.factorial : ℤ)
            * ((j.choose K : ℤ) * (K.choose t : ℤ) * (-1)^K) := by
    apply Finset.sum_congr rfl
    intro K _
    rw [pow_eq_sum_S2 K c, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hexp, Finset.sum_comm]
  have hinner : ∀ t ∈ Finset.range (c + 1),
      ∑ K ∈ Finset.range (j + 1), (S2 c t : ℤ) * (t.factorial : ℤ)
          * ((j.choose K : ℤ) * (K.choose t : ℤ) * (-1)^K)
        = if t = j then (S2 c t : ℤ) * (t.factorial : ℤ) * (-1:ℤ)^j else 0 := by
    intro t _
    rw [← Finset.mul_sum, alt_sum_choose_choose j t]
    split_ifs with h
    · ring
    · ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range (c+1)) j
    (fun t => (S2 c t : ℤ) * (t.factorial : ℤ) * (-1:ℤ)^j)]
  split_ifs with h
  · ring
  · rw [Finset.mem_range, not_lt] at h
    rw [S2_eq_zero_of_lt (by omega)]
    push_cast
    ring

/-- `A_c := ∑_{j=1}^{c} (-1)^(j-1) (j-1)! S2(c,j)` (shifted index). -/
def Ac (c : ℕ) : ℤ := ∑ j ∈ Finset.range c, (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c (j+1) : ℤ)

lemma Ac_eq_zero {c : ℕ} (hc : 2 ≤ c) : Ac c = 0 := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hc' : 1 ≤ c' := by omega
  unfold Ac
  have hsplit : ∀ j : ℕ, (-1:ℤ)^j * (j.factorial : ℤ) * (S2 (c'+1) (j+1) : ℤ)
      = (-1:ℤ)^j * ((j+1).factorial : ℤ) * (S2 c' (j+1) : ℤ)
        + (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c' j : ℤ) := by
    intro j
    rw [S2_succ_succ]
    push_cast [Nat.factorial_succ]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  -- first sum: last term vanishes
  have h1 : ∑ j ∈ Finset.range (c'+1), (-1:ℤ)^j * ((j+1).factorial : ℤ) * (S2 c' (j+1) : ℤ)
      = ∑ j ∈ Finset.range c', (-1:ℤ)^j * ((j+1).factorial : ℤ) * (S2 c' (j+1) : ℤ) := by
    rw [Finset.sum_range_succ]
    rw [S2_eq_zero_of_lt (by omega)]
    push_cast
    ring
  -- second sum: first term vanishes, shift
  have h2 : ∑ j ∈ Finset.range (c'+1), (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c' j : ℤ)
      = ∑ j ∈ Finset.range c', (-1:ℤ)^(j+1) * ((j+1).factorial : ℤ) * (S2 c' (j+1) : ℤ) := by
    rw [Finset.sum_range_succ' (fun j => (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c' j : ℤ)) c']
    have hz : (S2 c' 0 : ℤ) = 0 := by
      obtain ⟨c'', rfl⟩ : ∃ c'', c' = c'' + 1 := ⟨c' - 1, by omega⟩
      rfl
    rw [hz]
    ring_nf
  rw [h1, h2, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  ring

end A333096

end HelperS04

section HelperS05

/-! # S05: signed Stirling numbers of the first kind, valuation bounds, `Uc`, `F`. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset Polynomial

/-- Signed Stirling numbers of the first kind: coefficients of the falling factorial. -/
noncomputable def s1 (a c : ℕ) : ℤ := (descPochhammer ℤ a).coeff c

@[simp] lemma s1_zero (c : ℕ) : s1 0 c = if c = 0 then 1 else 0 := by
  unfold s1
  rw [descPochhammer_zero, Polynomial.coeff_one]

lemma s1_succ_succ (a c : ℕ) : s1 (a + 1) (c + 1) = s1 a c - (a:ℤ) * s1 a (c + 1) := by
  unfold s1
  rw [descPochhammer_succ_right,
    show ((a : ℤ[X])) = Polynomial.C (a:ℤ) by simp,
    Polynomial.coeff_mul_X_sub_C]
  ring

lemma s1_succ_zero (a : ℕ) : s1 (a + 1) 0 = 0 := by
  unfold s1
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact descPochhammer_ne_zero_eval_zero (R := ℤ) (n := a + 1) (Nat.succ_ne_zero a)

lemma s1_eq_zero_of_lt {a c : ℕ} (h : a < c) : s1 a c = 0 := by
  unfold s1
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [descPochhammer_natDegree]
  exact h

@[simp] lemma s1_self (a : ℕ) : s1 a a = 1 := by
  unfold s1
  have hm : (descPochhammer ℤ a).Monic := monic_descPochhammer ℤ a
  have := hm.coeff_natDegree
  rwa [descPochhammer_natDegree] at this

lemma s1_one_right (a : ℕ) : s1 (a + 1) 1 = (-1:ℤ)^a * (a.factorial : ℤ) := by
  induction a with
  | zero =>
    unfold s1
    simp
  | succ a ih =>
    rw [s1_succ_succ, s1_succ_zero, ih]
    push_cast [Nat.factorial_succ]
    ring

/-- Core inductive valuation bound for Stirling-1 coefficients:
`v_p(s1 a c) ≥ ν((a-1)!) - min(ν((a-1)!), (c-1)·L)` provided all `t ≤ A` have `ν(t) ≤ L`. -/
lemma s1_val_bound {p : ℕ} (hp : p.Prime) {L A : ℕ}
    (hL : ∀ t, 1 ≤ t → t ≤ A → padicValNat p t ≤ L) :
    ∀ a, a ≤ A + 1 → ∀ c,
      (p:ℤ) ^ (padicValNat p (a-1).factorial
          - min (padicValNat p (a-1).factorial) ((c-1) * L)) ∣ s1 a c := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro a
  induction a with
  | zero =>
    intro _ c
    simp only [Nat.zero_sub, Nat.factorial_zero, padicValNat.one, Nat.zero_min,
      Nat.sub_zero, pow_zero]
    exact one_dvd _
  | succ a ih =>
    intro ha c
    have hsimp : (a + 1) - 1 = a := by omega
    rw [hsimp]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · -- c = 0 : s1 (a+1) 0 = 0
      rw [s1_succ_zero]
      exact dvd_zero _
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha1
    · -- a = 0 : s1 1 (c'+1) ∈ {0,1}, exponent = 0
      simp only [Nat.factorial_zero, padicValNat.one, Nat.zero_min, Nat.sub_zero, pow_zero]
      exact one_dvd _
    -- a ≥ 1
    have hνa : padicValNat p a ≤ L := hL a ha1 (by omega)
    have hfact : padicValNat p a.factorial
        = padicValNat p (a-1).factorial + padicValNat p a := by
      have h1 : a.factorial = a * (a-1).factorial := by
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        simp [Nat.factorial_succ]
      rw [h1, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      ring
    rw [s1_succ_succ]
    set X := padicValNat p (a-1).factorial with hX
    set y := padicValNat p a with hy
    -- target exponent
    set ε := (X + y) - min (X + y) (c' * L) with hε
    have hεgoal : padicValNat p a.factorial - min (padicValNat p a.factorial) ((c'+1-1) * L)
        = ε := by
      rw [hfact]
      simp only [hε, Nat.add_sub_cancel]
    rw [hεgoal]
    apply _root_.dvd_sub
    · -- term 1 : s1 a c'
      rcases Nat.eq_zero_or_pos c' with rfl | hc'
      · -- s1 a 0 = 0 (a ≥ 1)
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        rw [s1_succ_zero]
        exact dvd_zero _
      · have hI1 : ε ≤ X - min X ((c'-1) * L) := by
          have hprod : c' * L = (c'-1) * L + L := by
            obtain ⟨c'', rfl⟩ : ∃ c'', c' = c'' + 1 := ⟨c' - 1, by omega⟩
            simp [Nat.succ_mul]
          omega
        exact dvd_trans (pow_dvd_pow _ hI1) (ih (by omega) c')
    · -- term 2 : a * s1 a (c'+1)
      have hI2 : ε ≤ y + (X - min X (c' * L)) := by omega
      have hdvd_a : (p:ℤ)^y ∣ (a:ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.mpr (pow_padicValNat_dvd (p := p) (n := a))
      have hdvd_s : (p:ℤ)^(X - min X ((c'+1-1) * L)) ∣ s1 a (c'+1) := ih (by omega) (c'+1)
      have hsimp2 : c' + 1 - 1 = c' := by omega
      rw [hsimp2] at hdvd_s
      calc (p:ℤ)^ε ∣ (p:ℤ)^(y + (X - min X (c' * L))) := pow_dvd_pow _ hI2
        _ = (p:ℤ)^y * (p:ℤ)^(X - min X (c' * L)) := by rw [pow_add]
        _ ∣ (a:ℤ) * s1 a (c'+1) := mul_dvd_mul hdvd_a hdvd_s

/-! ## `Uc` and `F` -/

/-- `U_c(π) = ∑_a (-1)^a π_a s1(a,c) / a!`. -/
noncomputable def Uc (π : Polynomial ℤ) (c : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (π.natDegree + 1),
    ((-1:ℤ)^a * π.coeff a * s1 a c : ℤ) / ((a.factorial : ℤ) : ℚ)

/-- `F(π, M) = ∑_a (-1)^a π_a C(M,a)`. -/
noncomputable def Fp (π : Polynomial ℤ) (M : ℕ) : ℤ :=
  ∑ a ∈ Finset.range (π.natDegree + 1), (-1:ℤ)^a * π.coeff a * (M.choose a : ℤ)

lemma Fp_ext (π : Polynomial ℤ) (M : ℕ) {n : ℕ} (hn : π.natDegree ≤ n) :
    Fp π M = ∑ a ∈ Finset.range (n + 1), (-1:ℤ)^a * π.coeff a * (M.choose a : ℤ) := by
  unfold Fp
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at *
    omega
  · intro x _ hx
    rw [Finset.mem_range, not_lt] at hx
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    ring

lemma Uc_ext (π : Polynomial ℤ) (c : ℕ) {n : ℕ} (hn : π.natDegree ≤ n) :
    Uc π c = ∑ a ∈ Finset.range (n + 1),
      ((-1:ℤ)^a * π.coeff a * s1 a c : ℤ) / ((a.factorial : ℤ) : ℚ) := by
  unfold Uc
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at *
    omega
  · intro x _ hx
    rw [Finset.mem_range, not_lt] at hx
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    push_cast
    ring

lemma Uc_eq_zero_of_gt (π : Polynomial ℤ) {c : ℕ} (hc : π.natDegree < c) : Uc π c = 0 := by
  unfold Uc
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finset.mem_range] at ha
  rw [s1_eq_zero_of_lt (by omega)]
  push_cast
  ring

/-- Expansion of a binomial in powers: `C(M,a) = ∑_c s1(a,c) M^c / a!` over ℚ. -/
lemma choose_eq_sum_s1 (M a : ℕ) :
    ((M.choose a : ℤ) : ℚ)
      = (∑ c ∈ Finset.range (a + 1), (s1 a c : ℚ) * ((M:ℚ))^c) / ((a.factorial : ℤ) : ℚ) := by
  have h1 : ((a.factorial : ℤ)) * ich (M:ℤ) a = (descPochhammer ℤ a).eval (M:ℤ) :=
    factorial_mul_ich (M:ℤ) a
  rw [ich_natCast] at h1
  have h2 : (descPochhammer ℤ a).eval (M:ℤ)
      = ∑ c ∈ Finset.range (a + 1), s1 a c * (M:ℤ)^c := by
    have := Polynomial.eval_eq_sum_range (p := descPochhammer ℤ a) (x := (M:ℤ))
    rw [descPochhammer_natDegree] at this
    exact this
  rw [h2] at h1
  have hfacne : ((a.factorial : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℚ)).mpr a.factorial_ne_zero
  rw [eq_div_iff hfacne]
  have := congrArg (fun z : ℤ => (z : ℚ)) h1
  push_cast at this ⊢
  linarith [this]

/-- `F(π,M) = ∑_c U_c(π) M^c` over ℚ. -/
lemma Fp_eq_sum_Uc (π : Polynomial ℤ) (M : ℕ) :
    ((Fp π M : ℤ) : ℚ) = ∑ c ∈ Finset.range (π.natDegree + 1), Uc π c * ((M:ℚ))^c := by
  set D := π.natDegree with hD
  unfold Fp
  push_cast
  have hterm : ∀ a ∈ Finset.range (D + 1),
      ((-1:ℚ))^a * (π.coeff a : ℚ) * ((M.choose a : ℕ) : ℚ)
        = ∑ c ∈ Finset.range (D + 1),
            ((-1:ℤ)^a * π.coeff a * s1 a c : ℤ) / ((a.factorial : ℤ) : ℚ) * ((M:ℚ))^c := by
    intro a ha
    rw [Finset.mem_range] at ha
    have h1 : ((M.choose a : ℕ) : ℚ)
        = (∑ c ∈ Finset.range (a + 1), (s1 a c : ℚ) * ((M:ℚ))^c) / ((a.factorial : ℤ) : ℚ) := by
      exact_mod_cast choose_eq_sum_s1 M a
    rw [h1]
    have h2 : (∑ c ∈ Finset.range (a + 1), (s1 a c : ℚ) * ((M:ℚ))^c)
        = ∑ c ∈ Finset.range (D + 1), (s1 a c : ℚ) * ((M:ℚ))^c := by
      apply Finset.sum_subset
      · intro x hx
        rw [Finset.mem_range] at *
        omega
      · intro x _ hx
        rw [Finset.mem_range, not_lt] at hx
        rw [s1_eq_zero_of_lt (by omega)]
        push_cast
        ring
    rw [h2, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Uc_ext π c (le_refl D), Finset.sum_mul]

/-! ## U bounds -/

section Ubounds

variable {p : ℕ} (hp : p.Prime)
include hp

/-- (U-a): `v_p(U_c π) ≥ -(i-1)` when `deg π + 2 ≤ i(p-1)`. -/
lemma U_bound_a {π : Polynomial ℤ} {i : ℕ} (hi : 1 ≤ i)
    (hdeg : π.natDegree + 2 ≤ i * (p - 1)) (c : ℕ) :
    POge p (-((i:ℤ) - 1)) (Uc π c) := by
  apply POge_sum hp
  intro a ha
  rw [Finset.mem_range] at ha
  have hnum := POge_int hp ((-1:ℤ)^a * π.coeff a * s1 a c)
  have hE : EOrd p (padicValNat p a.factorial) ((a.factorial : ℕ) : ℤ) :=
    EOrd_padicValNat hp a.factorial_ne_zero
  have hdiv := POge_div hp hnum hE
  rw [zero_sub] at hdiv
  apply POge_mono hp _ hdiv
  have hν : padicValNat p a.factorial + 1 ≤ i := nu_factorial_le hp hi (by omega)
  have : (padicValNat p a.factorial : ℤ) ≤ (i:ℤ) - 1 := by exact_mod_cast by omega
  omega

/-- (U-1): `v_p(U_c π) ≥ 0` when `deg π + 3 ≤ p`. -/
lemma U_bound_one {π : Polynomial ℤ} (hdeg : π.natDegree + 3 ≤ p) (c : ℕ) :
    POge p 0 (Uc π c) := by
  apply POge_sum hp
  intro a ha
  rw [Finset.mem_range] at ha
  have hnum := POge_int hp ((-1:ℤ)^a * π.coeff a * s1 a c)
  have hE : EOrd p (padicValNat p a.factorial) ((a.factorial : ℕ) : ℤ) :=
    EOrd_padicValNat hp a.factorial_ne_zero
  have hdiv := POge_div hp hnum hE
  rw [zero_sub] at hdiv
  have hν : padicValNat p a.factorial = 0 := nu_factorial_eq_zero hp (by omega)
  rw [hν] at hdiv
  simpa using hdiv

/-- (U-b): `v_p(U_c π) ≥ -c·L` when `deg π ≤ D` and all `1 ≤ t ≤ D` have `ν(t) ≤ L`. -/
lemma U_bound_b {π : Polynomial ℤ} {D L c : ℕ} (hc : 1 ≤ c)
    (hdeg : π.natDegree ≤ D)
    (hL : ∀ t, 1 ≤ t → t ≤ D → padicValNat p t ≤ L) :
    POge p (-((c:ℤ) * L)) (Uc π c) := by
  apply POge_sum hp
  intro a ha
  rw [Finset.mem_range] at ha
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · -- a = 0 : s1 0 c = 0 for c ≥ 1
    have hz : s1 0 c = 0 := by
      rw [s1_zero, if_neg (by omega : ¬ c = 0)]
    rw [hz]
    simp only [mul_zero, Int.cast_zero, zero_div]
    exact POge_zero hp _
  -- a ≥ 1
  have hsdvd := s1_val_bound hp hL a (by omega) c
  have hnum1 := POge_int hp ((-1:ℤ)^a * π.coeff a)
  have hnum2 := POge_of_dvd hp hsdvd
  have hnum := POge_mul hp hnum1 hnum2
  rw [zero_add] at hnum
  have hE : EOrd p (padicValNat p a.factorial) ((a.factorial : ℕ) : ℤ) :=
    EOrd_padicValNat hp a.factorial_ne_zero
  have hdiv := POge_div hp hnum hE
  have heqterm : (((-1:ℤ)^a * π.coeff a * s1 a c : ℤ) : ℚ) / ((a.factorial : ℤ) : ℚ)
      = ((((-1:ℤ)^a * π.coeff a : ℤ) : ℚ) * ((s1 a c : ℤ) : ℚ)) / ((a.factorial : ℤ) : ℚ) := by
    push_cast
    ring
  rw [heqterm]
  apply POge_mono hp _ hdiv
  -- arithmetic: exponent bound
  have hνa : padicValNat p a ≤ L := hL a ha1 (by omega)
  have hfact : padicValNat p a.factorial
      = padicValNat p (a-1).factorial + padicValNat p a := by
    have h1 : a.factorial = a * (a-1).factorial := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      simp [Nat.factorial_succ]
    haveI : Fact p.Prime := ⟨hp⟩
    rw [h1, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    ring
  have hprod : c * L = (c-1) * L + L := by
    obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
    simp [Nat.succ_mul]
  set X := padicValNat p (a-1).factorial
  set y := padicValNat p a
  have hcast : ((X - min X ((c-1) * L) : ℕ) : ℤ) - ((X + y : ℕ) : ℤ)
      ≥ -((c:ℤ) * L) := by
    have h1 : min X ((c-1)*L) ≤ (c-1)*L := Nat.min_le_right _ _
    have h2 : min X ((c-1)*L) ≤ X := Nat.min_le_left _ _
    push_cast
    have : ((c:ℤ)) * L = ((c*L : ℕ) : ℤ) := by push_cast; ring
    rw [this]
    push_cast
    omega
  rw [hfact]
  exact hcast

/-- (U-small): sharp bound for small degrees `D < p²`. -/
lemma U_bound_small {π : Polynomial ℤ} {D F c : ℕ} (hc : 1 ≤ c)
    (hdeg : π.natDegree ≤ D) (hD2 : D < p^2)
    (hF : padicValNat p (D - 1).factorial ≤ F) :
    POge p (-(1 + min (F:ℤ) ((c:ℤ) - 1))) (Uc π c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : ∀ t, 1 ≤ t → t ≤ D → padicValNat p t ≤ 1 := by
    intro t ht htD
    have := nu_lt_of_lt_pow hp ht (v := 2) (by omega)
    omega
  apply POge_sum hp
  intro a ha
  rw [Finset.mem_range] at ha
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · have hz : s1 0 c = 0 := by
      rw [s1_zero, if_neg (by omega : ¬ c = 0)]
    rw [hz]
    simp only [mul_zero, Int.cast_zero, zero_div]
    exact POge_zero hp _
  have hsdvd := s1_val_bound hp hL a (by omega) c
  have hnum1 := POge_int hp ((-1:ℤ)^a * π.coeff a)
  have hnum2 := POge_of_dvd hp hsdvd
  have hnum := POge_mul hp hnum1 hnum2
  rw [zero_add] at hnum
  have hE : EOrd p (padicValNat p a.factorial) ((a.factorial : ℕ) : ℤ) :=
    EOrd_padicValNat hp a.factorial_ne_zero
  have hdiv := POge_div hp hnum hE
  have heqterm : (((-1:ℤ)^a * π.coeff a * s1 a c : ℤ) : ℚ) / ((a.factorial : ℤ) : ℚ)
      = ((((-1:ℤ)^a * π.coeff a : ℤ) : ℚ) * ((s1 a c : ℤ) : ℚ)) / ((a.factorial : ℤ) : ℚ) := by
    push_cast
    ring
  rw [heqterm]
  apply POge_mono hp _ hdiv
  -- exponent arithmetic
  have hνa : padicValNat p a ≤ 1 := hL a ha1 (by omega)
  have hfact : padicValNat p a.factorial
      = padicValNat p (a-1).factorial + padicValNat p a := by
    have h1 : a.factorial = a * (a-1).factorial := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      simp [Nat.factorial_succ]
    rw [h1, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    ring
  have hXF : padicValNat p (a-1).factorial ≤ F := by
    have hdvdf : (a-1).factorial ∣ (D-1).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    have h2 : p ^ padicValNat p (a-1).factorial ∣ (D-1).factorial :=
      dvd_trans pow_padicValNat_dvd hdvdf
    have h3 := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero (D-1))).mp h2
    omega
  set X := padicValNat p (a-1).factorial
  set y := padicValNat p a
  rw [hfact]
  have h1 : min X ((c-1)*1) ≤ (c-1) := by
    have := Nat.min_le_right X ((c-1)*1)
    omega
  have h2 : min X ((c-1)*1) ≤ X := Nat.min_le_left _ _
  have h3 : min X ((c-1)*1) ≤ F := le_trans h2 hXF
  push_cast
  omega

end Ubounds

end A333096

end HelperS05

section HelperS06

/-! # S06: power series infrastructure: explicit units, coefficients of `(1-X)^z`,
truncation lemma for `U^(-A)` modulo `Z^(N+1)`. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset PowerSeries

section GenericRing

variable {R : Type} [CommRing R]

/-- The geometric series `∑ X^n`. -/
noncomputable def gs : R⟦X⟧ := PowerSeries.mk fun _ => 1

@[simp] lemma coeff_gs (n : ℕ) : (coeff n (gs : R⟦X⟧) : R) = 1 := coeff_mk n _

lemma one_sub_X_mul_gs : ((1 - X) * gs : R⟦X⟧) = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : coeff 0 ((1 - X) * gs : R⟦X⟧) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_one, constantCoeff_X]
      have : constantCoeff (gs : R⟦X⟧) = 1 := rfl
      rw [this]
      ring
    rw [h0, coeff_one, if_pos rfl]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sub_mul, one_mul, map_sub, coeff_one, if_neg (by omega)]
    have h1 : coeff (m+1) ((X : R⟦X⟧) * gs) = coeff m gs := by
      have h2 := coeff_X_pow_mul (gs : R⟦X⟧) 1 m
      rw [pow_one] at h2
      exact h2
    rw [h1]
    simp [gs]

/-- The unit `1 - X` with explicit geometric inverse. -/
noncomputable def us : (R⟦X⟧)ˣ :=
  ⟨1 - X, gs, one_sub_X_mul_gs, by rw [mul_comm]; exact one_sub_X_mul_gs⟩

@[simp] lemma us_val : ((us : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 - X := rfl
@[simp] lemma us_inv_val : (((us⁻¹ : (R⟦X⟧)ˣ)) : R⟦X⟧) = (gs : R⟦X⟧) := rfl

/-- Unit from a power series with constant coefficient 1. -/
noncomputable def unitOf (f : R⟦X⟧) (h : constantCoeff f = 1) : (R⟦X⟧)ˣ :=
  ⟨f, PowerSeries.invOfUnit f 1,
    PowerSeries.mul_invOfUnit f 1 (by simpa using h),
    by rw [mul_comm]; exact PowerSeries.mul_invOfUnit f 1 (by simpa using h)⟩

@[simp] lemma unitOf_val (f : R⟦X⟧) (h : constantCoeff f = 1) :
    ((unitOf f h : (R⟦X⟧)ˣ) : R⟦X⟧) = f := rfl

/-- Coefficients of `(1-X)^m`. -/
lemma coeff_one_sub_X_pow (m n : ℕ) :
    coeff n (((1 - X : R⟦X⟧))^m) = (-1:R)^n * (m.choose n : R) := by
  have hexp : ((1 - X : R⟦X⟧))^m = ∑ k ∈ Finset.range (m+1), (m.choose k : R⟦X⟧) * (-1:R⟦X⟧)^k * X^k := by
    have h := add_pow (-X : R⟦X⟧) 1 m
    have h2 : ((-X : R⟦X⟧) + 1)^m = (1 - X : R⟦X⟧)^m := by ring
    rw [← h2, h]
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_pow (X : R⟦X⟧) k, one_pow]
    ring
  rw [hexp, map_sum]
  have hterm : ∀ k ∈ Finset.range (m+1),
      coeff n ((m.choose k : R⟦X⟧) * (-1:R⟦X⟧)^k * X^k)
        = if n = k then (-1:R)^n * (m.choose n : R) else 0 := by
    intro k _
    have hc : ((m.choose k : R⟦X⟧) * (-1:R⟦X⟧)^k * X^k)
        = ((m.choose k : R) * (-1:R)^k) • (X^k : R⟦X⟧) := by
      rw [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
    rw [hc, map_smul, smul_eq_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases h : n = k
    · rw [if_pos h, if_pos h, h]
      ring
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (Finset.range (m+1)) n
    (fun _ => (-1:R)^n * (m.choose n : R))]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    push_cast
    ring

end GenericRing

section IntSeries

/-- Multiplication by the geometric series sums initial coefficients. -/
lemma coeff_mul_gs {R : Type} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    coeff n (f * gs) = ∑ a ∈ Finset.range (n+1), coeff a f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro a _
  simp [gs]

/-- Coefficients of `gs^m` for `m ≥ 1`. -/
lemma coeff_gs_pow (m : ℕ) (hm : 1 ≤ m) :
    ∀ n : ℕ, coeff n ((gs : ℤ⟦X⟧)^m) = ((m - 1 + n).choose n : ℤ) := by
  induction m with
  | zero => omega
  | succ m ih =>
    intro n
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · rw [pow_one]
      simp [gs, Nat.choose_self]
    · rw [pow_succ, coeff_mul_gs]
      have hterm : ∀ a ∈ Finset.range (n+1), coeff a ((gs : ℤ⟦X⟧)^m) = mch (m : ℤ) a := by
        intro a _
        rw [ih hm' a, mch_natCast m hm']
      rw [Finset.sum_congr rfl hterm, mch_hockey (m : ℤ) n]
      have hcast : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, mch_natCast (m+1) (by omega)]

/-- Coefficient of integer powers of the unit `1 - X` over ℤ. -/
lemma coeff_us_zpow (z : ℤ) (n : ℕ) :
    coeff n (((us ^ z : (ℤ⟦X⟧)ˣ)) : ℤ⟦X⟧) = (-1:ℤ)^n * ich z n := by
  cases z with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    have h1 : ((us ^ m : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = ((1 - X : ℤ⟦X⟧))^m := by
      rw [Units.val_pow_eq_pow_val, us_val]
    rw [h1, coeff_one_sub_X_pow, ich_natCast]
  | negSucc m =>
    rw [zpow_negSucc]
    have h1 : (((us ^ (m+1) : (ℤ⟦X⟧)ˣ)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = ((gs : ℤ⟦X⟧))^(m+1) := by
      rw [← inv_pow, Units.val_pow_eq_pow_val, us_inv_val]
    rw [h1, coeff_gs_pow (m+1) (by omega) n]
    have h2 : (Int.negSucc m) = -((m+1 : ℕ) : ℤ) := by
      simp [Int.negSucc_eq]
    rw [h2, ich_neg_eq_neg_pow_mul_mch, mch_natCast (m+1) (by omega), ← mul_assoc,
      ← mul_pow]
    simp

end IntSeries

section Trunc

variable {R : Type} [CommRing R]

@[simp] lemma mch_zero_left (j : ℕ) : mch (0 : ℤ) j = if j = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [if_neg (by omega)]
    unfold mch
    have h : (0:ℤ) + j - 1 = ((j - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hj]
      ring
    rw [h, ich_natCast, Nat.choose_eq_zero_of_lt (by omega)]
    rfl

/-- Core telescoping step: `(∑ mch(A+1,s) z^s)(1-z) = ∑ mch(A,s) z^s` when `z^(N+1) = 0`. -/
lemma telescope_core {Q : Type} [CommRing Q] {z : Q} {N : ℕ} (hz : z^(N+1) = 0) (A : ℤ) :
    (∑ s ∈ Finset.range (N+1), (mch (A+1) s : ℤ) • z^s) * (1 - z)
      = ∑ s ∈ Finset.range (N+1), (mch A s : ℤ) • z^s := by
  have hexpand : (∑ s ∈ Finset.range (N+1), (mch (A+1) s : ℤ) • z^s) * (1 - z)
      = (∑ s ∈ Finset.range (N+1), (mch (A+1) s : ℤ) • z^s)
        - ∑ s ∈ Finset.range (N+1), (mch (A+1) s : ℤ) • z^(s+1) := by
    rw [mul_sub, mul_one, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    rw [smul_mul_assoc, pow_succ]
  rw [hexpand]
  -- second sum: drop the last (vanishing) term
  have h2 : ∑ s ∈ Finset.range (N+1), (mch (A+1) s : ℤ) • z^(s+1)
      = ∑ s ∈ Finset.range N, (mch (A+1) s : ℤ) • z^(s+1) := by
    rw [Finset.sum_range_succ, hz, smul_zero, add_zero]
  -- first sum: peel off s = 0
  have h1 : ∑ s ∈ Finset.range (N+1), (mch (A+1) s : ℤ) • z^s
      = (∑ s ∈ Finset.range N, (mch (A+1) (s+1) : ℤ) • z^(s+1)) + (mch (A+1) 0 : ℤ) • z^0 := by
    rw [Finset.sum_range_succ' (fun s => (mch (A+1) s : ℤ) • z^s) N]
  have h3 : ∑ s ∈ Finset.range (N+1), (mch A s : ℤ) • z^s
      = (∑ s ∈ Finset.range N, (mch A (s+1) : ℤ) • z^(s+1)) + (mch A 0 : ℤ) • z^0 := by
    rw [Finset.sum_range_succ' (fun s => (mch A s : ℤ) • z^s) N]
  rw [h1, h2, h3]
  have hpascal : ∀ s : ℕ, (mch (A+1) (s+1) : ℤ) • z^(s+1) - (mch (A+1) s : ℤ) • z^(s+1)
      = (mch A (s+1) : ℤ) • z^(s+1) := by
    intro s
    rw [← sub_smul]
    congr 1
    have := mch_pascal A s
    omega
  simp only [mch_zero]
  rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => hpascal s

/-- Truncation: `U^(-A) ≡ ∑_{j≤N} mch(A,j) Z^j  mod Z^(N+1)` for `U = 1 - Z`. -/
theorem trunc_unit_zpow (Z : R⟦X⟧) (U : (R⟦X⟧)ˣ)
    (hU : (U : R⟦X⟧) = 1 - Z) (A : ℤ) (N : ℕ) :
    Z^(N+1) ∣ ((U ^ (-A) : (R⟦X⟧)ˣ) : R⟦X⟧)
      - ∑ j ∈ Finset.range (N+1), (mch A j : ℤ) • Z^j := by
  set I : Ideal R⟦X⟧ := Ideal.span {Z^(N+1)} with hI
  rw [← Ideal.mem_span_singleton (α := R⟦X⟧), ← hI, ← Ideal.Quotient.eq_zero_iff_mem]
  set ffi : R⟦X⟧ →+* R⟦X⟧ ⧸ I := Ideal.Quotient.mk I with hffi
  set z : R⟦X⟧ ⧸ I := ffi Z with hzdef
  have hz : z^(N+1) = 0 := by
    rw [hzdef, ← map_pow, hffi, Ideal.Quotient.eq_zero_iff_mem, hI]
    exact Ideal.subset_span rfl
  set V : (R⟦X⟧ ⧸ I)ˣ := Units.map (ffi : R⟦X⟧ →+* R⟦X⟧ ⧸ I).toMonoidHom U with hV
  have hVval : (V : R⟦X⟧ ⧸ I) = 1 - z := by
    rw [hV, Units.coe_map, hffi]
    show ffi (U : R⟦X⟧) = 1 - z
    rw [hU, map_sub, map_one, hzdef]
  have hunit : IsUnit ((1 : R⟦X⟧ ⧸ I) - z) := by
    rw [← hVval]
    exact Units.isUnit V
  have hzpow : ∀ B : ℤ, ((V ^ B : (R⟦X⟧ ⧸ I)ˣ) : R⟦X⟧ ⧸ I)
      = ffi ((U ^ B : (R⟦X⟧)ˣ) : R⟦X⟧) := by
    intro B
    rw [hV, ← map_zpow (Units.map (ffi : R⟦X⟧ →+* R⟦X⟧ ⧸ I).toMonoidHom) U B,
      Units.coe_map]
    rfl
  have hMain : ∀ B : ℤ, ((V ^ (-B) : (R⟦X⟧ ⧸ I)ˣ) : R⟦X⟧ ⧸ I)
      = ∑ j ∈ Finset.range (N+1), (mch B j : ℤ) • z^j := by
    intro B
    induction B using Int.induction_on with
    | zero =>
      simp only [neg_zero, zpow_zero, Units.val_one]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        rw [mch_zero_left, if_neg hj]
        simp
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    | succ B ih =>
      -- up-step
      have h1 : ((V ^ (-((B:ℤ)+1)) : (R⟦X⟧ ⧸ I)ˣ) : R⟦X⟧ ⧸ I) * (1 - z)
          = ((V ^ (-(B:ℤ)) : (R⟦X⟧ ⧸ I)ˣ) : R⟦X⟧ ⧸ I) := by
        rw [← hVval, ← Units.val_mul, ← zpow_add_one V (-((B:ℤ)+1))]
        congr 2
        ring
      have h2 : ((V ^ (-((B:ℤ)+1)) : (R⟦X⟧ ⧸ I)ˣ) : R⟦X⟧ ⧸ I) * (1 - z)
          = (∑ s ∈ Finset.range (N+1), (mch ((B:ℤ)+1) s : ℤ) • z^s) * (1 - z) := by
        rw [h1, ih, ← telescope_core hz (B:ℤ)]
      exact hunit.mul_right_cancel h2
    | pred B ih =>
      -- down-step
      have hexp : (-(-(B:ℤ) - 1)) = (-(-(B:ℤ))) + 1 := by ring
      rw [hexp, zpow_add_one V, Units.val_mul, ih, hVval]
      have := telescope_core hz (-(B:ℤ)-1)
      rw [show (-(B:ℤ)-1) + 1 = -(B:ℤ) by ring] at this
      exact this
  rw [map_sub, sub_eq_zero, ← hzpow (-A), hMain A, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [zsmul_eq_mul, zsmul_eq_mul, map_mul, map_pow, ← hzdef, map_intCast]

end Trunc

/-- Coefficient extraction: if `X^q ∣ Z` and `M < q(N+1)` then any multiple of
`Z^(N+1)` has vanishing `M`-th coefficient. -/
lemma coeff_eq_zero_of_dvd {R : Type} [CommRing R] {Z f : R⟦X⟧} {q M N : ℕ}
    (hq : (X : R⟦X⟧)^q ∣ Z) (hdvd : Z^(N+1) ∣ f) (hM : M < q * (N+1)) :
    coeff M f = 0 := by
  have h1 : ((X : R⟦X⟧)^q)^(N+1) ∣ Z^(N+1) := pow_dvd_pow_of_dvd hq (N+1)
  have h2 : (X : R⟦X⟧)^(q*(N+1)) ∣ f := by
    rw [pow_mul]
    exact dvd_trans h1 hdvd
  exact (PowerSeries.X_pow_dvd_iff.mp h2) M hM

/-- Main workhorse: coefficient expansion of `U^(-A) * W` modulo high powers of `Z`. -/
theorem coeff_unit_zpow_expand {R : Type} [CommRing R] (Z W : R⟦X⟧) (U : (R⟦X⟧)ˣ)
    (hU : (U : R⟦X⟧) = 1 - Z) (A : ℤ) {q M N : ℕ}
    (hq : (X : R⟦X⟧)^q ∣ Z) (hM : M < q * (N+1)) :
    coeff M (((U ^ (-A) : (R⟦X⟧)ˣ) : R⟦X⟧) * W)
      = ∑ j ∈ Finset.range (N+1), (mch A j : ℤ) • coeff M (Z^j * W) := by
  obtain ⟨g, hg⟩ := trunc_unit_zpow Z U hU A N
  have hf : ((U ^ (-A) : (R⟦X⟧)ˣ) : R⟦X⟧) * W
      = (∑ j ∈ Finset.range (N+1), (mch A j : ℤ) • Z^j) * W + Z^(N+1) * (g * W) := by
    have heq : ((U ^ (-A) : (R⟦X⟧)ˣ) : R⟦X⟧)
        = (∑ j ∈ Finset.range (N+1), (mch A j : ℤ) • Z^j) + Z^(N+1) * g := by
      rw [← sub_eq_iff_eq_add']
      exact hg
    rw [heq]
    ring
  rw [hf, map_add, coeff_eq_zero_of_dvd hq (Dvd.intro _ rfl) hM, add_zero,
    Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, map_zsmul]

end A333096

end HelperS06

section HelperS07

/-! # S07: the series `G`, the coefficients `β(S,N)`, and `B(R,N) = β(R+N,N)`. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset PowerSeries

/-- `uval z = (1-X)^z` as a power series (via the unit `us`). -/
noncomputable def uval (z : ℤ) : ℤ⟦X⟧ := ((us ^ z : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)

lemma uval_add (a b : ℤ) : uval (a + b) = uval a * uval b := by
  unfold uval
  rw [zpow_add, Units.val_mul]

lemma coeff_uval (z : ℤ) (n : ℕ) : coeff n (uval z) = (-1:ℤ)^n * ich z n :=
  coeff_us_zpow z n

lemma uval_one : uval 1 = 1 - X := by
  unfold uval
  rw [zpow_one, us_val]

lemma uval_zero : uval 0 = 1 := by
  unfold uval
  rw [zpow_zero, Units.val_one]

lemma uval_natCast (t : ℕ) : uval (t : ℤ) = (1 - X : ℤ⟦X⟧)^t := by
  unfold uval
  rw [zpow_natCast, Units.val_pow_eq_pow_val, us_val]

lemma uval_neg_one : uval (-1) = gs := by
  unfold uval
  rw [zpow_neg_one, us_inv_val]

lemma uval_mul_uval_neg (z : ℤ) : uval z * uval (-z) = 1 := by
  rw [← uval_add]
  simp [uval_zero]

/-- The series `Q = 1 - X + X²`. -/
noncomputable def Qs : ℤ⟦X⟧ := 1 - X + X^2

lemma constantCoeff_Qs : constantCoeff (Qs : ℤ⟦X⟧) = 1 := by
  unfold Qs
  rw [map_add, map_sub, map_one, constantCoeff_X, map_pow, constantCoeff_X]
  ring

/-- The unit with value `Q`. -/
noncomputable def uQ : (ℤ⟦X⟧)ˣ := unitOf Qs constantCoeff_Qs

/-- The inverse `1/Q` as a series. -/
noncomputable def Qinv : ℤ⟦X⟧ := ((uQ⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)

lemma Qinv_mul_Qs : Qinv * Qs = 1 := by
  unfold Qinv
  have h : ((uQ⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * ((uQ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = 1 := by
    rw [← Units.val_mul]
    simp
  exact h

lemma Qs_mul_Qinv : Qs * Qinv = 1 := by
  rw [mul_comm]
  exact Qinv_mul_Qs

/-- The series `G = (1-2X) / ((1-X) Q)`. -/
noncomputable def Gs : ℤ⟦X⟧ := (1 - 2*X : ℤ⟦X⟧) * Qinv * gs

lemma Gs_mul : Gs * (1 - X) * Qs = 1 - 2*X := by
  unfold Gs
  have h1 : (1 - 2*X : ℤ⟦X⟧) * Qinv * gs * (1 - X) * Qs
      = (1 - 2*X) * (Qinv * Qs) * ((1 - X) * gs) := by ring
  rw [h1, Qinv_mul_Qs, one_sub_X_mul_gs, mul_one, mul_one]

/-- `β(S, N) = [X^N] ((1-X)^{-S} G)`. -/
noncomputable def bet (S : ℤ) (N : ℕ) : ℤ := coeff N (Gs * uval (-S))

/-- The polynomial coefficients `P_k(R)`. -/
noncomputable def Pk (R : ℤ) : ℕ → ℤ
  | 0 => 1
  | (k+1) => ich (R + 2*(k+1) - 1) (k+1) - ich (R + 2*(k+1) - 1) k

/-- `B(R,N) = ∑_{k≤N} P_k(R)`. -/
noncomputable def Bsum (R : ℤ) (N : ℕ) : ℤ := ∑ k ∈ Finset.range (N+1), Pk R k

lemma coeff_one_sub_two_X_mul (f : ℤ⟦X⟧) (n : ℕ) :
    coeff (n+1) ((1 - 2*X : ℤ⟦X⟧) * f) = coeff (n+1) f - 2 * coeff n f := by
  have h : ((1 - 2*X : ℤ⟦X⟧)) * f = f - 2*(X * f) := by ring
  rw [h, map_sub]
  have h3 : (2*(X * f) : ℤ⟦X⟧) = (2:ℤ) • (X * f) := by
    rw [zsmul_eq_mul]
    norm_num
  rw [h3, map_smul, smul_eq_mul, coeff_succ_X_mul]

lemma coeff_zero_one_sub_two_X_mul (f : ℤ⟦X⟧) :
    coeff 0 ((1 - 2*X : ℤ⟦X⟧) * f) = coeff 0 f := by
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_one, map_mul,
    constantCoeff_X, coeff_zero_eq_constantCoeff_apply]
  ring

/-- Step B1: `P_k(R) = [X^k]((1-2X)(1-X)^{-(R+k+1)})`. -/
lemma Pk_eq_coeff (R : ℤ) (k : ℕ) :
    Pk R k = coeff k ((1 - 2*X : ℤ⟦X⟧) * uval (-(R + k + 1))) := by
  rcases k with _ | k'
  · rw [coeff_zero_one_sub_two_X_mul, coeff_uval]
    rw [ich_zero]
    simp [Pk]
  · set A : ℤ := R + ((k' + 1 : ℕ) : ℤ) + 1 with hA
    rw [coeff_one_sub_two_X_mul, coeff_uval, coeff_uval]
    rw [ich_neg_eq_neg_pow_mul_mch, ich_neg_eq_neg_pow_mul_mch]
    have e1 : (-1:ℤ)^(k'+1) * ((-1:ℤ)^(k'+1) * mch A (k'+1)) = mch A (k'+1) := by
      rw [← mul_assoc, ← mul_pow]
      simp
    have e2 : (2:ℤ) * ((-1:ℤ)^k' * ((-1:ℤ)^k' * mch A k')) = 2 * mch A k' := by
      rw [← mul_assoc ((-1:ℤ)^k'), ← mul_pow]
      simp
    rw [e1]
    rw [show (2:ℤ) * ((-1:ℤ)^k' * ((-1:ℤ)^k' * mch A k')) = 2 * mch A k' from e2]
    -- Now: Pk R (k'+1) = mch A (k'+1) - 2 mch A k'
    unfold mch
    have e3 : A + ((k'+1 : ℕ) : ℤ) - 1 = (R + 2*(k':ℤ) + 1) + 1 := by
      rw [hA]
      push_cast
      ring
    have e4 : A + (k':ℤ) - 1 = R + 2*(k':ℤ) + 1 := by
      rw [hA]
      push_cast
      ring
    rw [e3, e4, ich_pascal]
    show Pk R (k'+1) = _
    unfold Pk
    have e5 : R + 2*((k':ℤ)+1) - 1 = R + 2*(k':ℤ) + 1 := by push_cast; ring
    push_cast
    rw [e5]
    ring

/-- Step B2/B3: `B(R, N) = β(R+N, N)`. -/
theorem Bsum_eq_bet (R : ℤ) (N : ℕ) : Bsum R N = bet (R + N) N := by
  set Y : ℤ⟦X⟧ := X * uval 1 with hY
  have hQY : Qs = 1 - Y := by
    rw [hY, uval_one]
    unfold Qs
    ring
  have hgeom : (∑ t ∈ Finset.range (N+1), Y^t) * Qs = 1 - Y^(N+1) := by
    rw [hQY]
    exact geom_sum_mul_neg Y (N+1)
  have hinv : Qinv = (∑ t ∈ Finset.range (N+1), Y^t) + Y^(N+1) * Qinv := by
    have h1 : ((∑ t ∈ Finset.range (N+1), Y^t) + Y^(N+1) * Qinv) * Qs = 1 := by
      rw [add_mul, hgeom, mul_assoc, Qinv_mul_Qs, mul_one]
      ring
    calc Qinv = 1 * Qinv := by ring
      _ = (((∑ t ∈ Finset.range (N+1), Y^t) + Y^(N+1) * Qinv) * Qs) * Qinv := by rw [h1]
      _ = ((∑ t ∈ Finset.range (N+1), Y^t) + Y^(N+1) * Qinv) * (Qs * Qinv) := by ring
      _ = _ := by rw [Qs_mul_Qinv, mul_one]
  unfold bet
  have hsplit : Gs * uval (-(R + N))
      = (1 - 2*X : ℤ⟦X⟧) * uval (-(R + N + 1)) * Qinv := by
    unfold Gs
    have h2 : uval (-(R + N + 1)) = uval (-(R+N)) * uval (-1) := by
      rw [← uval_add]
      congr 1
      ring
    rw [h2, uval_neg_one]
    ring
  rw [hsplit, hinv, mul_add, map_add]
  have hvanish : coeff N ((1 - 2*X : ℤ⟦X⟧) * uval (-(R + N + 1))
      * (Y^(N+1) * Qinv)) = 0 := by
    have hXdvd : (X : ℤ⟦X⟧)^(N+1) ∣ (1 - 2*X : ℤ⟦X⟧) * uval (-(R + N + 1))
        * (Y^(N+1) * Qinv) := by
      have h5 : (Y^(N+1) : ℤ⟦X⟧) = X^(N+1) * (uval 1)^(N+1) := by
        rw [hY, mul_pow]
      exact ⟨(uval 1)^(N+1) * ((1 - 2*X : ℤ⟦X⟧) * uval (-(R + N + 1))) * Qinv,
        by rw [h5]; ring⟩
    exact (PowerSeries.X_pow_dvd_iff.mp hXdvd) N (by omega)
  rw [hvanish, add_zero, Finset.mul_sum, map_sum]
  have hterm : ∀ t ∈ Finset.range (N+1),
      coeff N ((1 - 2*X : ℤ⟦X⟧) * uval (-(R + N + 1)) * Y^t)
        = Pk R (N - t) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hYt : (Y^t : ℤ⟦X⟧) = X^t * uval (t : ℤ) := by
      rw [hY, uval_one, uval_natCast, mul_pow]
    have hexps : uval (-(R + N + 1)) * uval (t:ℤ)
        = uval (-(R + ((N - t : ℕ) : ℤ) + 1)) := by
      rw [← uval_add]
      congr 1
      have hc : ((N - t : ℕ) : ℤ) = (N : ℤ) - t := by
        rw [Nat.cast_sub (by omega)]
      rw [hc]
      ring
    have hcomb : (1 - 2*X : ℤ⟦X⟧) * uval (-(R + N + 1)) * Y^t
        = X^t * ((1 - 2*X : ℤ⟦X⟧) * uval (-(R + ((N - t : ℕ) : ℤ) + 1))) := by
      rw [hYt, ← hexps]
      ring
    rw [hcomb]
    have hcoeff := coeff_X_pow_mul
      ((1 - 2*X : ℤ⟦X⟧) * uval (-(R + ((N - t : ℕ) : ℤ) + 1))) t (N - t)
    rw [show N - t + t = N by omega] at hcoeff
    rw [hcoeff, ← Pk_eq_coeff]
  rw [Finset.sum_congr rfl hterm]
  unfold Bsum
  rw [← Finset.sum_range_reflect (fun k => Pk R k) (N+1)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  congr 1

end A333096

end HelperS07

section HelperS08

/-! # S08: `a_gen m n = Bsum (m*n) n + (m = -1 correction)`. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset

/-- `generalized_choose_int` agrees with `ich`. -/
lemma gci_eq_ich (r : ℤ) (k : ℕ) : generalized_choose_int r k = ich r k := by
  unfold generalized_choose_int
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · rw [if_neg (by omega : k ≠ 0), prod_range_eq_factorial_mul_ich]
    exact Int.mul_ediv_cancel_left _ (by exact_mod_cast k.factorial_ne_zero)

/-- Absorption: `R * ich (R+2k-1) k = (R+k) * Pk R k`. -/
lemma absorb_Pk (R : ℤ) (k : ℕ) :
    R * ich (R + 2 * (k : ℤ) - 1) k = (R + (k : ℤ)) * Pk R k := by
  cases k with
  | zero => simp [Pk]
  | succ k =>
    have harg : R + 2 * ((k + 1 : ℕ) : ℤ) - 1 = R + 2 * (k : ℤ) + 1 := by
      push_cast; ring
    rw [Pk]
    have h := ich_ratio (R + 2 * (k : ℤ) + 1) k
    push_cast
    push_cast at harg
    rw [harg]
    linear_combination -h

/-- If `r + k ≠ 0` then `generalized_catalan_coefficient r k = Pk r k`. -/
lemma gcc_eq (r : ℤ) (k : ℕ) (h : r + (k : ℤ) ≠ 0) :
    generalized_catalan_coefficient r k = Pk r k := by
  unfold generalized_catalan_coefficient
  cases k with
  | zero => simp [Pk]
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)]
    show (r * generalized_choose_int (r + 2 * ((k+1:ℕ) : ℤ) - 1) (k+1)) / (r + ((k+1:ℕ):ℤ))
      = Pk r (k+1)
    rw [gci_eq_ich, absorb_Pk r (k+1)]
    exact Int.mul_ediv_cancel_left _ h

/-- If `r + k = 0` and `k ≠ 0` then `generalized_catalan_coefficient r k = 0`. -/
lemma gcc_eq_zero (r : ℤ) (k : ℕ) (hk : k ≠ 0) (h : r + (k : ℤ) = 0) :
    generalized_catalan_coefficient r k = 0 := by
  unfold generalized_catalan_coefficient
  rw [if_neg hk]
  show (r * generalized_choose_int (r + 2 * (k : ℤ) - 1) k) / (r + (k:ℤ)) = 0
  rw [gci_eq_ich, absorb_Pk r k, h, zero_mul, Int.zero_ediv]

/-- `Pk (-k) k = -1` for `k ≥ 1`. -/
lemma Pk_neg_self (k : ℕ) (hk : 1 ≤ k) : Pk (-(k : ℤ)) k = -1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Pk]
  have harg : -(((k'+1:ℕ)) : ℤ) + 2 * ((k'+1:ℕ) : ℤ) - 1 = ((k' : ℕ) : ℤ) := by
    push_cast; ring
  push_cast
  push_cast at harg
  rw [harg, ich_natCast_eq_zero (Nat.lt_succ_self k'), ich_natCast, Nat.choose_self]
  norm_num

/-- Main lemma of module A: `a_gen m n = Bsum (m n) n` plus a correction at `m = -1`. -/
lemma a_gen_eq_Bsum (m : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    a_gen m n = Bsum (m * n) n + (if m = -1 then 1 else 0) := by
  unfold a_gen Bsum
  rw [if_neg (by omega : n ≠ 0)]
  have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  by_cases hm : m = -1
  · subst hm
    rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : ∀ k ∈ Finset.range n, generalized_catalan_coefficient (-1 * (n:ℤ)) k
        = Pk (-1 * (n:ℤ)) k := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp [generalized_catalan_coefficient, Pk]
      · apply gcc_eq
        have hkn : k < n := mem_range.mp hk
        have : (k : ℤ) < (n : ℤ) := by exact_mod_cast hkn
        intro hcon; omega
    rw [Finset.sum_congr rfl h1]
    have h2 : generalized_catalan_coefficient (-1 * (n:ℤ)) n = 0 := by
      apply gcc_eq_zero _ _ (by omega)
      ring
    have h3 : Pk (-1 * (n:ℤ)) n = -1 := by
      rw [neg_one_mul]; exact Pk_neg_self n hn
    rw [h2, h3]; ring
  · rw [if_neg hm, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp [generalized_catalan_coefficient, Pk]
    · apply gcc_eq
      have hkn : k ≤ n := by have := mem_range.mp hk; omega
      have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast h0
      have hknZ : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
      intro hcon
      rcases le_or_gt 0 m with hm0 | hm0
      · nlinarith
      · have hm2 : m ≤ -2 := by omega
        nlinarith

/-- Difference form: the `m = -1` corrections cancel. -/
lemma a_gen_sub (m : ℤ) (n₁ n₂ : ℕ) (h1 : 1 ≤ n₁) (h2 : 1 ≤ n₂) :
    a_gen m n₁ - a_gen m n₂ = Bsum (m * n₁) n₁ - Bsum (m * n₂) n₂ := by
  rw [a_gen_eq_Bsum m n₁ h1, a_gen_eq_Bsum m n₂ h2]; ring

/-- Difference in terms of `bet`. -/
lemma a_gen_sub_eq_bet (m : ℤ) (n₁ n₂ : ℕ) (h1 : 1 ≤ n₁) (h2 : 1 ≤ n₂) :
    a_gen m n₁ - a_gen m n₂
      = bet (m * n₁ + n₁) n₁ - bet (m * n₂ + n₂) n₂ := by
  rw [a_gen_sub m n₁ n₂ h1 h2, Bsum_eq_bet, Bsum_eq_bet]

end A333096

end HelperS08

section HelperS09

/-! # S09: the period-6 sequence `G6`, the series `Es`, and the Cartier fixed-point
computation `coeff (p*j) (Δ^j * Gs) = Gcoef j`. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset PowerSeries

/-! ## The period-6 sequence -/

/-- Period-6 sequence `2, 1, -1, -2, -1, 1, ...`; `G6 a = ω^a + ω̄^a` morally. -/
def G6 (n : ℕ) : ℤ :=
  if n % 6 = 0 then 2
  else if n % 6 = 1 then 1
  else if n % 6 = 2 then -1
  else if n % 6 = 3 then -2
  else if n % 6 = 4 then -1
  else 1

lemma G6_zero : G6 0 = 2 := rfl

lemma G6_rec (n : ℕ) : G6 (n + 2) = G6 (n + 1) - G6 n := by
  unfold G6
  have h1 : (n + 1) % 6 = (n % 6 + 1) % 6 := by omega
  have h2 : (n + 2) % 6 = (n % 6 + 2) % 6 := by omega
  rw [h1, h2]
  have h : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  set r := n % 6 with hr
  clear_value r
  interval_cases r <;> decide

/-- `Gcoef a = G6 a - 1`: the coefficients of `Gs`. -/
def Gcoef (n : ℕ) : ℤ := G6 n - 1

/-! ## The series `Es = (2-X)/Q` and `Gs = Es - gs` -/

/-- The series with coefficients `G6`. -/
noncomputable def Es : ℤ⟦X⟧ := PowerSeries.mk fun a => G6 a

@[simp] lemma coeff_Es (a : ℕ) : coeff a Es = G6 a := coeff_mk a _

lemma coeff_two_sub_X (n : ℕ) :
    coeff n (2 - X : ℤ⟦X⟧) = if n = 0 then 2 else if n = 1 then -1 else 0 := by
  have h2 : (2 : ℤ⟦X⟧) = PowerSeries.C (R := ℤ) 2 := (map_ofNat _ 2).symm
  rw [map_sub, h2, coeff_C, coeff_X]
  rcases n with _ | _ | n <;> simp

lemma Es_mul_Qs : Es * Qs = 2 - X := by
  have hE : Es * Qs = Es - X * Es + X^2 * Es := by
    unfold Qs; ring
  ext n
  rw [hE, map_add, map_sub, coeff_two_sub_X]
  rcases n with _ | _ | n
  · rw [if_pos rfl]
    have h1 : coeff 0 (X * Es : ℤ⟦X⟧) = 0 := by
      rw [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]
    have h2 : coeff 0 (X^2 * Es : ℤ⟦X⟧) = 0 := by
      rw [coeff_zero_eq_constantCoeff, map_mul, map_pow, constantCoeff_X]
      ring
    rw [h1, h2, coeff_Es]
    decide
  · simp only [show (0:ℕ)+1 = 1 from rfl]
    norm_num only
    have h1 : coeff 1 (X * Es : ℤ⟦X⟧) = coeff 0 Es := coeff_succ_X_mul 0 Es
    have h2 : coeff 1 (X^2 * Es : ℤ⟦X⟧) = 0 := by
      have hX : (X^2 * Es : ℤ⟦X⟧) = X * (X * Es) := by ring
      rw [hX]
      have h3 : coeff 1 (X * (X * Es) : ℤ⟦X⟧) = coeff 0 (X * Es : ℤ⟦X⟧) :=
        coeff_succ_X_mul 0 (X * Es)
      rw [h3, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]
    rw [h1, h2, coeff_Es, coeff_Es]
    decide
  · simp only [show ∀ m : ℕ, m+1+1 = m+2 from fun m => rfl]
    rw [if_neg (by omega), if_neg (by omega)]
    have h1 : coeff (n+2) (X * Es : ℤ⟦X⟧) = coeff (n+1) Es := coeff_succ_X_mul (n+1) Es
    have h2 : coeff (n+2) (X^2 * Es : ℤ⟦X⟧) = coeff n Es := coeff_X_pow_mul Es 2 n
    rw [h1, h2, coeff_Es, coeff_Es, coeff_Es]
    have := G6_rec n
    omega

lemma one_sub_X_mul_Qs_ne_zero : ((1 - X) * Qs : ℤ⟦X⟧) ≠ 0 := by
  intro h0
  have := congrArg constantCoeff h0
  rw [map_mul, constantCoeff_Qs, map_zero, map_sub, map_one, constantCoeff_X] at this
  norm_num at this

lemma Gs_eq : Gs = Es - gs := by
  apply mul_right_cancel₀ one_sub_X_mul_Qs_ne_zero
  have hL : Gs * ((1 - X) * Qs) = 1 - 2*X := by
    rw [← mul_assoc]; exact Gs_mul
  have hR : (Es - gs) * ((1 - X) * Qs) = 1 - 2*X := by
    have hexp : (Es - gs) * ((1 - X) * Qs) = (Es * Qs) * (1 - X) - ((1 - X) * gs) * Qs := by
      ring
    rw [hexp, Es_mul_Qs, one_sub_X_mul_gs, one_mul]
    unfold Qs
    ring
  rw [hL, hR]

lemma coeff_Gs (a : ℕ) : coeff a Gs = Gcoef a := by
  rw [Gs_eq, map_sub, coeff_Es, coeff_gs]
  rfl

/-! ## The parametrized alternating-sum induction (`Tsum`) -/

/-- `Tsum M r = ∑_a (-1)^(M+a) C(M,a) G6(a+r)`. -/
def Tsum (M r : ℕ) : ℤ :=
  ∑ a ∈ Finset.range (M+1), (-1 : ℤ)^(M+a) * (M.choose a : ℤ) * G6 (a + r)

lemma Tsum_zero (r : ℕ) : Tsum 0 r = G6 r := by
  simp [Tsum]

lemma Tsum_succ (M r : ℕ) : Tsum (M+1) r = Tsum M (r+1) - Tsum M r := by
  have hstep1 : Tsum (M+1) r
      = (∑ b ∈ Finset.range (M+1),
          ((-1 : ℤ)^(M+b) * (M.choose b : ℤ) * G6 (b + (r+1))
            + (-1 : ℤ)^(M+b) * (M.choose (b+1) : ℤ) * G6 (b + 1 + r)))
        + (-1 : ℤ)^(M+1) * G6 r := by
    unfold Tsum
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro b _
      beta_reduce
      have hc : (((M+1).choose (b+1) : ℕ) : ℤ)
          = (M.choose b : ℤ) + (M.choose (b+1) : ℤ) := by
        rw [Nat.choose_succ_succ]
        push_cast
        ring
      have hsign : (-1 : ℤ)^(M+1+(b+1)) = (-1 : ℤ)^(M+b) := by
        rw [show M+1+(b+1) = (M+b)+2 by ring, pow_add]
        norm_num
      rw [hc, hsign]
      have hidx : b + 1 + r = b + (r + 1) := by ring
      rw [hidx]
      ring
    · simp
  have hstep2 : ∑ b ∈ Finset.range (M+1), (-1 : ℤ)^(M+b) * (M.choose (b+1) : ℤ) * G6 (b + 1 + r)
      = -Tsum M r + (-1 : ℤ)^M * G6 r := by
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hTs : Tsum M r
        = (∑ b ∈ Finset.range M, (-1 : ℤ)^(M+(b+1)) * (M.choose (b+1) : ℤ) * G6 (b + 1 + r))
          + (-1 : ℤ)^(M+0) * (M.choose 0 : ℤ) * G6 (0 + r) := by
      unfold Tsum
      rw [Finset.sum_range_succ']
    have hsum : (∑ b ∈ Finset.range M, (-1 : ℤ)^(M+b) * (M.choose (b+1) : ℤ) * G6 (b + 1 + r))
        + (∑ b ∈ Finset.range M, (-1 : ℤ)^(M+(b+1)) * (M.choose (b+1) : ℤ) * G6 (b + 1 + r))
        = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro b _
      have hneg : (-1 : ℤ)^(M+(b+1)) = -((-1 : ℤ)^(M+b)) := by
        rw [show M+(b+1) = (M+b)+1 by ring, pow_succ]
        ring
      rw [hneg]
      ring
    have hc : (-1 : ℤ)^(M+0) * (M.choose 0 : ℤ) * G6 (0 + r) = (-1 : ℤ)^M * G6 r := by
      simp
    rw [hc] at hTs
    linarith [hTs, hsum]
  rw [hstep1, Finset.sum_add_distrib, hstep2]
  have hfold : ∑ b ∈ Finset.range (M+1), (-1 : ℤ)^(M+b) * (M.choose b : ℤ) * G6 (b + (r+1))
      = Tsum M (r+1) := rfl
  rw [hfold]
  have hsign : (-1 : ℤ)^(M+1) = -((-1 : ℤ)^M) := by
    rw [pow_succ]; ring
  rw [hsign]
  ring

lemma Tsum_eq (M : ℕ) : ∀ r, Tsum M r = G6 (2*M + r) := by
  induction M with
  | zero =>
    intro r
    rw [Tsum_zero]
    norm_num
  | succ M ih =>
    intro r
    rw [Tsum_succ, ih, ih]
    have h1 : 2*M + (r+1) = (2*M + r) + 1 := by ring
    have h2 : 2*(M+1) + r = (2*M + r) + 2 := by ring
    rw [h1, h2, G6_rec]

/-! ## The binomial-sum induction (`Ksum`) -/

/-- `Ksum j r = ∑_K C(j,K) G6(2K+r)`. -/
def Ksum (j r : ℕ) : ℤ :=
  ∑ K ∈ Finset.range (j+1), (j.choose K : ℤ) * G6 (2*K + r)

lemma Ksum_zero (r : ℕ) : Ksum 0 r = G6 r := by
  simp [Ksum]

lemma Ksum_succ (j r : ℕ) : Ksum (j+1) r = Ksum j r + Ksum j (r+2) := by
  have hstep1 : Ksum (j+1) r
      = (∑ b ∈ Finset.range (j+1),
          ((j.choose b : ℤ) * G6 (2*b + (r+2)) + (j.choose (b+1) : ℤ) * G6 (2*(b+1) + r)))
        + G6 r := by
    unfold Ksum
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro b _
      beta_reduce
      have hc : (((j+1).choose (b+1) : ℕ) : ℤ)
          = (j.choose b : ℤ) + (j.choose (b+1) : ℤ) := by
        rw [Nat.choose_succ_succ]
        push_cast
        ring
      rw [hc]
      have hidx : 2*(b+1) + r = 2*b + (r+2) := by ring
      rw [hidx]
      ring
    · simp
  have hstep2 : ∑ b ∈ Finset.range (j+1), (j.choose (b+1) : ℤ) * G6 (2*(b+1) + r)
      = Ksum j r - G6 r := by
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    have hKs : Ksum j r
        = (∑ b ∈ Finset.range j, (j.choose (b+1) : ℤ) * G6 (2*(b+1) + r))
          + (j.choose 0 : ℤ) * G6 (2*0 + r) := by
      unfold Ksum
      rw [Finset.sum_range_succ']
    rw [hKs]
    simp
  rw [hstep1, Finset.sum_add_distrib, hstep2]
  have hfold : ∑ b ∈ Finset.range (j+1), (j.choose b : ℤ) * G6 (2*b + (r+2)) = Ksum j (r+2) := rfl
  rw [hfold]
  ring

lemma Ksum_eq (j : ℕ) : ∀ r, Ksum j r = G6 (j + r) := by
  induction j with
  | zero =>
    intro r
    rw [Ksum_zero]
    norm_num
  | succ j ih =>
    intro r
    rw [Ksum_succ, ih, ih]
    have h1 : j + (r+2) = (j + r) + 2 := by ring
    have h2 : (j+1) + r = (j + r) + 1 := by ring
    rw [h1, h2, G6_rec]
    ring

/-! ## Coefficient extraction lemmas for Cartier -/

/-- `[X^M] ((1-X)^M · Es) = G6 (2M)`. -/
lemma coeff_pow_mul_Es (M : ℕ) :
    coeff M ((1 - X : ℤ⟦X⟧)^M * Es) = G6 (2*M) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ k ∈ Finset.range (M+1),
      coeff k ((1 - X : ℤ⟦X⟧)^M) * coeff (M - k) Es
        = (-1 : ℤ)^(M+(M-k)) * (M.choose (M-k) : ℤ) * G6 ((M - k) + 0) := by
    intro k hk
    have hkM : k ≤ M := by
      have := Finset.mem_range.mp hk; omega
    rw [coeff_one_sub_X_pow, coeff_Es]
    have hsign : (-1 : ℤ)^k = (-1 : ℤ)^(M+(M-k)) := by
      rw [show M+(M-k) = k + 2*(M-k) by omega, pow_add, pow_mul]
      norm_num
    have hch : (M.choose k : ℤ) = (M.choose (M-k) : ℤ) := by
      rw [Nat.choose_symm hkM]
    rw [hsign, hch, add_zero]
  rw [Finset.sum_congr rfl hterm]
  have hR := Finset.sum_range_reflect
    (fun t => (-1 : ℤ)^(M+t) * (M.choose t : ℤ) * G6 (t + 0)) (M+1)
  simp only [Nat.add_sub_cancel] at hR
  rw [hR]
  have hfold : ∑ t ∈ Finset.range (M+1), (-1 : ℤ)^(M+t) * (M.choose t : ℤ) * G6 (t + 0)
      = Tsum M 0 := rfl
  rw [hfold, Tsum_eq M 0]
  norm_num

/-- `[X^M] ((1-X)^M · gs) = 0` for `M ≥ 1`. -/
lemma coeff_pow_mul_gs (M : ℕ) (hM : 1 ≤ M) :
    coeff M ((1 - X : ℤ⟦X⟧)^M * gs) = 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have h : ((1 - X : ℤ⟦X⟧))^(M'+1) * gs = (1 - X)^(M') * ((1 - X) * gs) := by
    ring
  rw [h, one_sub_X_mul_gs, mul_one, coeff_one_sub_X_pow]
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  ring

/-- Reduction of `G6 (2M)` modulo 3. -/
lemma G6_two_mul_mod3 (M : ℕ) : G6 (2*M) = if M % 3 = 0 then 2 else -1 := by
  unfold G6
  have h : (2*M) % 6 = 2 * (M % 3) := by omega
  rw [h]
  have h3 : M % 3 < 3 := Nat.mod_lt _ (by norm_num)
  set r := M % 3 with hr
  clear_value r
  interval_cases r <;> decide

lemma G6_two_mul_p_mul {p : ℕ} (hp3 : ¬ 3 ∣ p) (K : ℕ) : G6 (2*(p*K)) = G6 (2*K) := by
  rw [G6_two_mul_mod3, G6_two_mul_mod3]
  have h3 : Nat.Prime 3 := by norm_num
  have hiff : 3 ∣ p*K ↔ 3 ∣ K := by
    rw [h3.dvd_mul]
    simp [hp3]
  have h1 : (p*K) % 3 = 0 ↔ K % 3 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    exact hiff
  by_cases hK : K % 3 = 0
  · rw [if_pos (h1.mpr hK), if_pos hK]
  · rw [if_neg (fun hc => hK (h1.mp hc)), if_neg hK]

/-! ## The Δ-power expansion lemma -/

/-- Expansion of `coeff (p·j) (Δ^j · f)` where `Δ = X^p + (1-X)^p`. -/
lemma expand_delta (p j : ℕ) (f : ℤ⟦X⟧) :
    coeff (p*j) ((((X : ℤ⟦X⟧)^p + (1 - X)^p))^j * f)
      = ∑ K ∈ Finset.range (j+1), (j.choose K : ℤ) * coeff (p*K) ((1 - X : ℤ⟦X⟧)^(p*K) * f) := by
  rw [add_pow, Finset.sum_mul, map_sum]
  have hterm : ∀ K ∈ Finset.range (j+1),
      coeff (p*j) (((X : ℤ⟦X⟧)^p)^K * ((1 - X)^p)^(j-K) * ((j.choose K : ℕ) : ℤ⟦X⟧) * f)
        = (j.choose (j-K) : ℤ) * coeff (p*(j-K)) ((1 - X : ℤ⟦X⟧)^(p*(j-K)) * f) := by
    intro K hK
    have hKj : K ≤ j := by
      have := Finset.mem_range.mp hK; omega
    have hres : ((X : ℤ⟦X⟧)^p)^K * ((1 - X)^p)^(j-K) * ((j.choose K : ℕ) : ℤ⟦X⟧) * f
        = ((j.choose K : ℤ)) • ((X : ℤ⟦X⟧)^(p*K) * ((1 - X)^(p*(j-K)) * f)) := by
      rw [← pow_mul, ← pow_mul, zsmul_eq_mul]
      push_cast
      ring
    rw [hres, map_zsmul]
    have hidx : p*j = p*(j-K) + p*K := by
      have hj : j = (j - K) + K := by omega
      calc p*j = p*((j-K) + K) := by rw [← hj]
        _ = p*(j-K) + p*K := by ring
    rw [hidx, coeff_X_pow_mul, smul_eq_mul]
    have hch : (j.choose K : ℤ) = (j.choose (j-K) : ℤ) := by
      rw [Nat.choose_symm hKj]
    rw [hch]
  rw [Finset.sum_congr rfl hterm]
  have hR := Finset.sum_range_reflect
    (fun t => (j.choose t : ℤ) * coeff (p*t) ((1 - X : ℤ⟦X⟧)^(p*t) * f)) (j+1)
  simp only [Nat.add_sub_cancel] at hR
  exact hR

/-! ## The Cartier fixed-point theorem -/

theorem cartier_fixed {p : ℕ} (hp1 : 1 ≤ p) (hp3 : ¬ 3 ∣ p) (j : ℕ) :
    coeff (p*j) ((((X : ℤ⟦X⟧)^p + (1 - X)^p))^j * Gs) = Gcoef j := by
  rw [expand_delta]
  have hterm : ∀ K ∈ Finset.range (j+1),
      (j.choose K : ℤ) * coeff (p*K) ((1 - X : ℤ⟦X⟧)^(p*K) * Gs)
        = (j.choose K : ℤ) * G6 (2*K + 0) - (if K = 0 then (j.choose K : ℤ) else 0) := by
    intro K hK
    rw [Gs_eq, mul_sub, map_sub, coeff_pow_mul_Es (p*K), G6_two_mul_p_mul hp3, add_zero]
    rcases Nat.eq_zero_or_pos K with rfl | hKpos
    · rw [if_pos rfl]
      have hc0 : coeff (p*0) ((1 - X : ℤ⟦X⟧)^(p*0) * gs) = 1 := by
        rw [Nat.mul_zero, pow_zero, one_mul]
        simp [gs]
      rw [hc0]
      ring
    · rw [coeff_pow_mul_gs (p*K) (Nat.mul_pos hp1 hKpos), if_neg (by omega)]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have h1 : ∑ K ∈ Finset.range (j+1), (j.choose K : ℤ) * G6 (2*K + 0) = G6 j := by
    have hf : ∑ K ∈ Finset.range (j+1), (j.choose K : ℤ) * G6 (2*K + 0) = Ksum j 0 := rfl
    have hj0 : j + 0 = j := by omega
    rw [hf, Ksum_eq j 0, hj0]
  have h2 : ∑ K ∈ Finset.range (j+1), (if K = 0 then (j.choose K : ℤ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.range (j+1)) 0 (fun K => (j.choose K : ℤ))]
    simp
  rw [h1, h2]
  rfl

end A333096

end HelperS09

section HelperS10

/-! # S10: the polynomial `h = (Δ-1)/p`, its factorization `h = (1-X)·Q·η`,
and the polynomials `ψ = η(1-2X)`, `π_i = ψ·h^(i-1)`. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset Polynomial
open scoped PowerSeries

/-- `Δ = X^p + (1-X)^p` as a polynomial. -/
noncomputable def Dpoly (p : ℕ) : ℤ[X] := X^p + (1 - X)^p

/-- `Q = X² - X + 1` as a polynomial. -/
noncomputable def Qpoly : ℤ[X] := X^2 - X + 1

/-- `h = (Δ - 1)/p` with explicit integer coefficients. -/
noncomputable def hpoly (p : ℕ) : ℤ[X] :=
  ∑ n ∈ Finset.Ioo 0 p, Polynomial.C ((-1:ℤ)^n * ((p.choose n) / p : ℕ)) * X^n

/-- Coefficients of `(1-X)^m` as a polynomial. -/
lemma poly_coeff_one_sub_X_pow (m n : ℕ) :
    ((1 - X : ℤ[X])^m).coeff n = (-1:ℤ)^n * (m.choose n : ℤ) := by
  have hcoe : (((1 - X : ℤ[X])^m : ℤ[X]) : ℤ⟦X⟧) = (1 - PowerSeries.X : ℤ⟦X⟧)^m := by
    rw [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
  have h := congrArg (PowerSeries.coeff n) hcoe
  rw [Polynomial.coeff_coe] at h
  rw [h, coeff_one_sub_X_pow]

lemma hpoly_coeff (p n : ℕ) :
    (hpoly p).coeff n
      = if 0 < n ∧ n < p then (-1:ℤ)^n * (((p.choose n) / p : ℕ) : ℤ) else 0 := by
  unfold hpoly
  rw [Polynomial.finset_sum_coeff]
  have hterm : ∀ k ∈ Finset.Ioo 0 p,
      (Polynomial.C ((-1:ℤ)^k * ((p.choose k) / p : ℕ)) * X^k).coeff n
        = if k = n then (-1:ℤ)^n * (((p.choose n) / p : ℕ) : ℤ) else 0 := by
    intro k _
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · rfl
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.Ioo 0 p) n (fun _ => (-1:ℤ)^n * (((p.choose n) / p : ℕ) : ℤ))]
  simp only [Finset.mem_Ioo]

/-- The key identity: `p · h = Δ - 1`. -/
lemma p_mul_hpoly {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ[X]) * hpoly p = Dpoly p - 1 := by
  apply Polynomial.ext
  intro n
  have hcast : ((p:ℕ) : ℤ[X]) = Polynomial.C (p : ℤ) := by
    rw [Polynomial.C_eq_natCast]
  rw [hcast, Polynomial.coeff_C_mul, hpoly_coeff]
  unfold Dpoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    poly_coeff_one_sub_X_pow, Polynomial.coeff_one]
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_neg (by omega : ¬(0 < 0 ∧ 0 < p)), if_neg (by omega : ¬(0 = p)), if_pos rfl]
    simp
  · by_cases hnp : n < p
    · rw [if_pos ⟨by omega, hnp⟩, if_neg (by omega : ¬(n = p)), if_neg hn0]
      have hdvd : p ∣ p.choose n := hp.dvd_choose_self hn0 hnp
      have hmc : ((p.choose n / p : ℕ) : ℤ) * (p : ℤ) = (p.choose n : ℤ) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      calc (p:ℤ) * ((-1:ℤ)^n * ((p.choose n / p : ℕ) : ℤ))
          = (-1:ℤ)^n * (((p.choose n / p : ℕ) : ℤ) * (p:ℤ)) := by ring
        _ = (-1:ℤ)^n * (p.choose n : ℤ) := by rw [hmc]
        _ = 0 + (-1:ℤ)^n * (p.choose n : ℤ) - 0 := by ring
    · by_cases hnep : n = p
      · rw [if_neg (by omega : ¬(0 < n ∧ n < p)), if_pos hnep, if_neg hn0, hnep,
          Nat.choose_self]
        have hodd : Odd p := hp.odd_of_ne_two (by omega)
        rw [hodd.neg_one_pow]
        ring
      · rw [if_neg (by omega), if_neg (fun h => hnep h), if_neg hn0]
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        push_cast
        ring

lemma hpoly_natDegree_le (p : ℕ) : (hpoly p).natDegree ≤ p - 1 := by
  unfold hpoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ p - 1 := by
    have := Finset.mem_Ioo.mp hk; omega
  calc (Polynomial.C ((-1:ℤ)^k * ((p.choose k) / p : ℕ)) * X^k).natDegree
      ≤ (X^k : ℤ[X]).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = k := Polynomial.natDegree_X_pow k
    _ ≤ p - 1 := hk'

lemma hpoly_coeff_zero (p : ℕ) : (hpoly p).coeff 0 = 0 := by
  rw [hpoly_coeff]
  simp

lemma hpoly_coeff_one {p : ℕ} (hp : p.Prime) : (hpoly p).coeff 1 = -1 := by
  rw [hpoly_coeff]
  have h2 : 2 ≤ p := hp.two_le
  rw [if_pos ⟨by omega, by omega⟩, Nat.choose_one_right, Nat.div_self (by omega : 0 < p)]
  norm_num

lemma hpoly_ne_zero {p : ℕ} (hp : p.Prime) : hpoly p ≠ 0 := by
  intro h
  have h1 := hpoly_coeff_one hp
  rw [h, Polynomial.coeff_zero] at h1
  norm_num at h1

/-! ## `Q` divides `Δ - 1` -/

lemma Qpoly_monic : (Qpoly).Monic := by
  have hdeg : Polynomial.degree (1 - X : ℤ[X]) < 2 := by
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    rw [Polynomial.degree_one, Polynomial.degree_X]
    decide
  have h := Polynomial.monic_X_pow_add (n := 2) hdeg
  have heq : (X^2 + (1 - X) : ℤ[X]) = Qpoly := by
    unfold Qpoly; ring
  rwa [heq] at h

lemma Q_dvd_X6 : Qpoly ∣ (X^6 - 1 : ℤ[X]) :=
  ⟨(X^3 - 1) * (X + 1), by unfold Qpoly; ring⟩

lemma Q_dvd_Y6 : Qpoly ∣ ((1-X)^6 - 1 : ℤ[X]) :=
  ⟨((1-X)^3 - 1) * (2 - X), by unfold Qpoly; ring⟩

lemma Q_dvd_five : Qpoly ∣ (X^5 + (1-X)^5 - 1 : ℤ[X]) :=
  ⟨5 * X * (X - 1), by unfold Qpoly; ring⟩

lemma Q_dvd_pow_six_t (f : ℤ[X]) (hf : Qpoly ∣ f^6 - 1) (t : ℕ) :
    Qpoly ∣ (f^6)^t - 1 := by
  have h := sub_dvd_pow_sub_pow (f^6) 1 t
  rw [one_pow] at h
  exact dvd_trans hf h

lemma Qpoly_dvd_delta {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Qpoly ∣ (Dpoly p - 1) := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 3) hp).mp h
    omega
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3
  have hm : p % 6 = 1 ∨ p % 6 = 5 := by omega
  set t := p / 6 with ht
  rcases hm with h | h
  · have hpt : p = 6*t + 1 := by omega
    have d1 : Qpoly ∣ (X^p - X : ℤ[X]) := by
      have heq : (X^p - X : ℤ[X]) = ((X^6)^t - 1) * X := by
        have hx : (X : ℤ[X])^(6*t+1) = (X^6)^t * X := by
          rw [pow_add, pow_mul, pow_one]
        rw [hpt, hx]; ring
      rw [heq]
      exact Dvd.dvd.mul_right (Q_dvd_pow_six_t _ Q_dvd_X6 t) X
    have d2 : Qpoly ∣ ((1-X)^p - (1-X) : ℤ[X]) := by
      have heq : ((1-X)^p - (1-X) : ℤ[X]) = (((1-X)^6)^t - 1) * (1-X) := by
        have hx : ((1-X) : ℤ[X])^(6*t+1) = ((1-X)^6)^t * (1-X) := by
          rw [pow_add, pow_mul, pow_one]
        rw [hpt, hx]; ring
      rw [heq]
      exact Dvd.dvd.mul_right (Q_dvd_pow_six_t _ Q_dvd_Y6 t) _
    have hsum : (Dpoly p - 1 : ℤ[X]) = (X^p - X) + ((1-X)^p - (1-X)) := by
      unfold Dpoly; ring
    rw [hsum]
    exact dvd_add d1 d2
  · have hpt : p = 6*t + 5 := by omega
    have d1 : Qpoly ∣ (X^p - X^5 : ℤ[X]) := by
      have heq : (X^p - X^5 : ℤ[X]) = ((X^6)^t - 1) * X^5 := by
        have hx : (X : ℤ[X])^(6*t+5) = (X^6)^t * X^5 := by
          rw [pow_add, pow_mul]
        rw [hpt, hx]; ring
      rw [heq]
      exact Dvd.dvd.mul_right (Q_dvd_pow_six_t _ Q_dvd_X6 t) _
    have d2 : Qpoly ∣ ((1-X)^p - (1-X)^5 : ℤ[X]) := by
      have heq : ((1-X)^p - (1-X)^5 : ℤ[X]) = (((1-X)^6)^t - 1) * (1-X)^5 := by
        have hx : ((1-X) : ℤ[X])^(6*t+5) = ((1-X)^6)^t * (1-X)^5 := by
          rw [pow_add, pow_mul]
        rw [hpt, hx]; ring
      rw [heq]
      exact Dvd.dvd.mul_right (Q_dvd_pow_six_t _ Q_dvd_Y6 t) _
    have hsum : (Dpoly p - 1 : ℤ[X])
        = (X^p - X^5) + ((1-X)^p - (1-X)^5) + (X^5 + (1-X)^5 - 1) := by
      unfold Dpoly; ring
    rw [hsum]
    exact dvd_add (dvd_add d1 d2) Q_dvd_five

lemma Qpoly_dvd_hpoly {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : Qpoly ∣ hpoly p := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd Qpoly_monic]
  have hd : (Dpoly p - 1) %ₘ Qpoly = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd Qpoly_monic).mpr (Qpoly_dvd_delta hp hp5)
  have hph : ((p:ℤ) • hpoly p) %ₘ Qpoly = (p:ℤ) • (hpoly p %ₘ Qpoly) :=
    Polynomial.smul_modByMonic _ _
  have hcast : ((p:ℤ) • hpoly p) = (p : ℤ[X]) * hpoly p := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.C_eq_natCast]
  rw [hcast, p_mul_hpoly hp hp5, hd] at hph
  have hz := hph.symm
  rw [smul_eq_zero] at hz
  rcases hz with h | h
  · exfalso
    have : (p:ℤ) ≠ 0 := by
      have := hp.two_le; omega
    exact this h
  · exact h

/-! ## The factorization `h = (1-X) Q η` -/

/-- `g = h /ₘ Q`. -/
noncomputable def gQ (p : ℕ) : ℤ[X] := hpoly p /ₘ Qpoly

lemma h_eq_Q_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hpoly p = Qpoly * gQ p := by
  have h := Polynomial.modByMonic_add_div (hpoly p) Qpoly_monic
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd Qpoly_monic).mpr (Qpoly_dvd_hpoly hp hp5),
    zero_add] at h
  exact h.symm

lemma hpoly_eval_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : (hpoly p).eval 1 = 0 := by
  have h := congrArg (Polynomial.eval 1) (p_mul_hpoly hp hp5)
  have hD : (Dpoly p).eval 1 = 1 := by
    unfold Dpoly
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
    rw [one_pow, sub_self, zero_pow (by omega : p ≠ 0)]
    ring
  rw [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_sub, hD,
    Polynomial.eval_one, sub_self] at h
  have hpne : (p:ℤ) ≠ 0 := by
    have := hp.two_le; omega
  exact (mul_eq_zero.mp h).resolve_left hpne

lemma gQ_eval_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : (gQ p).eval 1 = 0 := by
  have h := congrArg (Polynomial.eval 1) (h_eq_Q_mul hp hp5)
  have hQ1 : (Qpoly).eval 1 = 1 := by
    unfold Qpoly
    simp
  rw [hpoly_eval_one hp hp5, Polynomial.eval_mul, hQ1, one_mul] at h
  exact h.symm

/-- `η` with `h = (1-X) Q η`. -/
noncomputable def etaP (p : ℕ) : ℤ[X] := -(gQ p /ₘ (X - Polynomial.C 1))

lemma gQ_eq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    gQ p = (X - Polynomial.C 1) * (gQ p /ₘ (X - Polynomial.C 1)) := by
  have hdvd : (X - Polynomial.C 1) ∣ gQ p :=
    Polynomial.dvd_iff_isRoot.mpr (gQ_eval_one hp hp5)
  have h := Polynomial.modByMonic_add_div (gQ p) (Polynomial.monic_X_sub_C (1:ℤ))
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C (1:ℤ))).mpr hdvd,
    zero_add] at h
  exact h.symm

/-- The factorization `h = (1-X)·Q·η`. -/
lemma h_factor {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hpoly p = (1 - X) * Qpoly * etaP p := by
  rw [h_eq_Q_mul hp hp5, gQ_eq hp hp5]
  unfold etaP
  rw [Polynomial.C_1]
  ring

lemma etaP_eval_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : (etaP p).eval 0 = 0 := by
  have h := congrArg (Polynomial.eval 0) (h_factor hp hp5)
  have h0 : (hpoly p).eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hpoly_coeff_zero p
  have hQ0 : Qpoly.eval 0 = 1 := by
    unfold Qpoly; simp
  rw [h0, Polynomial.eval_mul, Polynomial.eval_mul, hQ0, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, sub_zero, one_mul, one_mul] at h
  exact h.symm

lemma etaP_coeff_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : (etaP p).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact etaP_eval_zero hp hp5

/-! ## `ψ` and `π_i` -/

/-- `ψ = η (1 - 2X)`. -/
noncomputable def psiP (p : ℕ) : ℤ[X] := etaP p * (1 - 2*X)

/-- `π_i = ψ h^(i-1)`. -/
noncomputable def piP (p i : ℕ) : ℤ[X] := psiP p * (hpoly p)^(i-1)

/-- `h` as a power series. -/
noncomputable def hser (p : ℕ) : ℤ⟦X⟧ := (hpoly p : ℤ⟦X⟧)

lemma coe_Qpoly : ((Qpoly : ℤ[X]) : ℤ⟦X⟧) = Qs := by
  unfold Qpoly
  rw [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X,
    Polynomial.coe_one]
  unfold Qs
  ring

lemma coe_one_sub_X : ((1 - X : ℤ[X]) : ℤ⟦X⟧) = 1 - PowerSeries.X := by
  rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]

lemma coe_two : ((2 : ℤ[X]) : ℤ⟦X⟧) = 2 := by
  have h := map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℤ)) 2
  rwa [Polynomial.coeToPowerSeries.ringHom_apply] at h

lemma coe_one_sub_two_X : ((1 - 2*X : ℤ[X]) : ℤ⟦X⟧) = 1 - 2*PowerSeries.X := by
  rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, coe_two, Polynomial.coe_X]

/-- `h·G = ψ` as power series. -/
lemma hser_mul_Gs {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hser p * Gs = ((psiP p : ℤ[X]) : ℤ⟦X⟧) := by
  unfold hser psiP
  rw [h_factor hp hp5]
  simp only [Polynomial.coe_mul]
  rw [coe_one_sub_X, coe_Qpoly, coe_one_sub_two_X]
  linear_combination ((etaP p : ℤ[X]) : ℤ⟦X⟧) * Gs_mul

/-- `π_i = h^i·G` as power series, for `i ≥ 1`. -/
lemma piP_series {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) (hi : 1 ≤ i) :
    ((piP p i : ℤ[X]) : ℤ⟦X⟧) = (hser p)^i * Gs := by
  unfold piP
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i-1, by omega⟩
  rw [Polynomial.coe_mul, Polynomial.coe_pow]
  simp only [Nat.add_sub_cancel]
  rw [← hser_mul_Gs hp hp5]
  unfold hser
  ring

/-! ## Degree bounds -/

lemma natDegree_one_sub_X_mul_Q : ((1 - X) * Qpoly : ℤ[X]).natDegree = 3 := by
  have h : ((1-X) * Qpoly : ℤ[X]) = -(X^3) + 2*X^2 - 2*X + 1 := by
    unfold Qpoly; ring
  rw [h]
  compute_degree!

lemma etaP_natDegree_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (etaP p).natDegree ≤ p - 4 := by
  by_cases hη : etaP p = 0
  · rw [hη]; simp
  · have hfac := h_factor hp hp5
    have hne : ((1-X)*Qpoly : ℤ[X]) ≠ 0 := by
      intro h0
      have h3 := natDegree_one_sub_X_mul_Q
      rw [h0] at h3
      simp at h3
    have hdeg : (hpoly p).natDegree = 3 + (etaP p).natDegree := by
      rw [hfac, Polynomial.natDegree_mul hne hη, natDegree_one_sub_X_mul_Q]
    have hle := hpoly_natDegree_le p
    omega

lemma psiP_natDegree_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (psiP p).natDegree ≤ p - 3 := by
  unfold psiP
  apply le_trans (Polynomial.natDegree_mul_le)
  have h1 : (1 - 2*X : ℤ[X]).natDegree ≤ 1 := by
    compute_degree
  have h2 := etaP_natDegree_le hp hp5
  omega

lemma piP_natDegree_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) (hi : 1 ≤ i) :
    (piP p i).natDegree ≤ i*(p-1) - 2 := by
  unfold piP
  apply le_trans (Polynomial.natDegree_mul_le)
  have h1 := psiP_natDegree_le hp hp5
  have h2 : ((hpoly p)^(i-1)).natDegree ≤ (i-1)*(p-1) := by
    apply le_trans (Polynomial.natDegree_pow_le)
    exact Nat.mul_le_mul_left _ (hpoly_natDegree_le p)
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i-1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2 ⊢
  have hexp : (i'+1)*(p-1) = i'*(p-1) + (p-1) := by ring
  omega

lemma piP_coeff_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) :
    (piP p i).coeff 0 = 0 := by
  unfold piP psiP
  rw [Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero, etaP_coeff_zero hp hp5]
  ring

/-! ## Series form of `Δ` -/

lemma delta_coe (p : ℕ) :
    ((Dpoly p : ℤ[X]) : ℤ⟦X⟧) = (PowerSeries.X : ℤ⟦X⟧)^p + (1 - PowerSeries.X)^p := by
  unfold Dpoly
  rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_pow, Polynomial.coe_X,
    coe_one_sub_X]

lemma delta_ser {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((Dpoly p : ℤ[X]) : ℤ⟦X⟧) = 1 + (p : ℤ⟦X⟧) * hser p := by
  have h := congrArg (fun f : ℤ[X] => (f : ℤ⟦X⟧)) (p_mul_hpoly hp hp5)
  simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one] at h
  have hcast : (((p:ℕ) : ℤ[X]) : ℤ⟦X⟧) = ((p:ℕ) : ℤ⟦X⟧) := by
    have := map_natCast (Polynomial.coeToPowerSeries.ringHom (R := ℤ)) p
    rwa [Polynomial.coeToPowerSeries.ringHom_apply] at this
  rw [hcast] at h
  unfold hser
  linear_combination -h

lemma hser_coeff_zero (p : ℕ) : PowerSeries.coeff 0 (hser p) = 0 := by
  unfold hser
  rw [Polynomial.coeff_coe]
  exact hpoly_coeff_zero p

end A333096

end HelperS10

section HelperS11

/-! # S11: antisymmetry and the vanishing `U₁(π_i) = 0` (step C6). -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset Polynomial
open scoped PowerSeries

/-! ## Antiderivative and the antisymmetric-sum lemma over ℚ -/

/-- Formal antiderivative (without constant) of a rational polynomial. -/
noncomputable def antider (q : ℚ[X]) : ℚ[X] :=
  ∑ b ∈ Finset.range (q.natDegree + 1), Polynomial.C (q.coeff b / ((b : ℚ)+1)) * X^(b+1)

lemma antider_coeff (q : ℚ[X]) (n : ℕ) :
    (antider q).coeff (n+1) = q.coeff n / ((n : ℚ)+1) := by
  unfold antider
  rw [Polynomial.finset_sum_coeff]
  have hterm : ∀ b ∈ Finset.range (q.natDegree+1),
      (Polynomial.C (q.coeff b / ((b : ℚ)+1)) * X^(b+1)).coeff (n+1)
        = if b = n then q.coeff n / ((n : ℚ)+1) else 0 := by
    intro b _
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    by_cases h : b = n
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (by omega), if_neg h]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.range (q.natDegree+1)) n (fun _ => q.coeff n / ((n : ℚ)+1))]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_div]

lemma antider_coeff_zero (q : ℚ[X]) : (antider q).coeff 0 = 0 := by
  unfold antider
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro b _
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, if_neg (by omega)]

lemma antider_natDegree_le (q : ℚ[X]) : (antider q).natDegree ≤ q.natDegree + 1 := by
  unfold antider
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b hb
  have hb' : b ≤ q.natDegree := by
    have := Finset.mem_range.mp hb; omega
  calc (Polynomial.C (q.coeff b / ((b : ℚ)+1)) * X^(b+1)).natDegree
      ≤ (X^(b+1) : ℚ[X]).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = b+1 := Polynomial.natDegree_X_pow (b+1)
    _ ≤ q.natDegree + 1 := by omega

lemma derivative_antider (q : ℚ[X]) : Polynomial.derivative (antider q) = q := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_derivative, antider_coeff]
  have hne : ((n : ℚ)+1) ≠ 0 := by positivity
  field_simp

/-- The antisymmetric-sum lemma: if `q(1-X) = -q(X)` then `∑ q_b/(b+1) = 0`. -/
lemma antisym_sum (q : ℚ[X]) (hq : q.comp (1 - X) = -q) (n : ℕ) (hn : q.natDegree ≤ n) :
    ∑ b ∈ Finset.range (n+1), q.coeff b / ((b : ℚ)+1) = 0 := by
  set r := antider q with hrdef
  have hD : Polynomial.derivative (r.comp (1 - X) - r) = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_comp_one_sub_X, derivative_antider,
      hq]
    ring
  have hC := Polynomial.eq_C_of_derivative_eq_zero hD
  have h0 := congrArg (Polynomial.eval 0) hC
  have h1 := congrArg (Polynomial.eval 1) hC
  rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_C] at h0 h1
  have hev0 : Polynomial.eval 0 (1 - X : ℚ[X]) = 1 := by simp
  have hev1 : Polynomial.eval 1 (1 - X : ℚ[X]) = 0 := by simp
  rw [hev0] at h0
  rw [hev1] at h1
  have hr0 : r.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact antider_coeff_zero q
  have hr1 : r.eval 1 = 0 := by
    rw [hr0] at h0 h1
    -- h0 : r.eval 1 - 0 = c ; h1 : 0 - r.eval 1 = c
    have := h0.trans h1.symm
    linarith
  -- expand r.eval 1 as a coefficient sum
  have hdeg_r : r.natDegree < n + 2 := by
    have h1 := antider_natDegree_le q
    rw [← hrdef] at h1
    omega
  have heval : r.eval 1 = ∑ b ∈ Finset.range (n+2), r.coeff b := by
    rw [Polynomial.eval_eq_sum_range' hdeg_r]
    apply Finset.sum_congr rfl
    intro b _
    rw [one_pow, mul_one]
  rw [Finset.sum_range_succ'] at heval
  rw [antider_coeff_zero, add_zero] at heval
  have hterm : ∀ b ∈ Finset.range (n+1), (r.coeff (b+1) : ℚ) = q.coeff b / ((b : ℚ)+1) := by
    intro b _
    exact antider_coeff q b
  rw [Finset.sum_congr rfl hterm] at heval
  rw [← heval, hr1]

/-! ## The involution `σ : f ↦ f∘(1-X)` and antisymmetry of `π_i/X` -/

lemma sigma_Q : Qpoly.comp (1 - X) = Qpoly := by
  unfold Qpoly
  rw [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.one_comp]
  ring

lemma one_sub_X_comp : ((1 - X : ℤ[X])).comp (1 - X) = X := by
  rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
  ring

lemma sigma_h {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (hpoly p).comp (1 - X) = hpoly p := by
  have h2 : (Dpoly p - 1 : ℤ[X]).comp (1 - X) = Dpoly p - 1 := by
    unfold Dpoly
    rw [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.pow_comp, Polynomial.pow_comp,
      Polynomial.X_comp, one_sub_X_comp, Polynomial.one_comp]
    ring
  have h3 := congrArg (fun f : ℤ[X] => f.comp (1 - X)) (p_mul_hpoly hp hp5)
  simp only [Polynomial.mul_comp, Polynomial.natCast_comp] at h3
  rw [h2, ← p_mul_hpoly hp hp5] at h3
  have hpne : ((p:ℕ) : ℤ[X]) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  exact mul_left_cancel₀ hpne h3

lemma sigma_eta {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    X * ((etaP p).comp (1 - X)) = (1 - X) * etaP p := by
  have h1 := sigma_h hp hp5
  nth_rewrite 1 [h_factor hp hp5] at h1
  rw [h_factor hp hp5] at h1
  rw [Polynomial.mul_comp, Polynomial.mul_comp, sigma_Q, one_sub_X_comp] at h1
  -- h1 : X * Qpoly * (η∘σ) = (1-X) * Qpoly * η
  apply mul_right_cancel₀ (Qpoly_monic.ne_zero)
  linear_combination h1

lemma sigma_pi {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) :
    X * ((piP p i).comp (1 - X)) = -((1 - X) * piP p i) := by
  unfold piP psiP
  rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.pow_comp, sigma_h hp hp5]
  have hc : (1 - 2*X : ℤ[X]).comp (1 - X) = -(1 - 2*X) := by
    have h2 : (1 - 2*X : ℤ[X]) = 1 - X - X := by ring
    rw [h2, Polynomial.sub_comp, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
    ring
  rw [hc]
  have hse := sigma_eta hp hp5
  linear_combination (-(1 - 2*X) * (hpoly p)^(i-1)) * hse

lemma X_mul_one_sub_X_ne_zero : (X * (1 - X) : ℤ[X]) ≠ 0 := by
  apply mul_ne_zero Polynomial.X_ne_zero
  intro h0
  have := congrArg (Polynomial.eval 0) h0
  simp at this

lemma sigma_g {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) :
    ((piP p i).divX).comp (1 - X) = -(piP p i).divX := by
  set g := (piP p i).divX with hg
  have hXg : X * g = piP p i := by
    have h := Polynomial.X_mul_divX_add (piP p i)
    rw [piP_coeff_zero hp hp5 i, map_zero, add_zero] at h
    exact h
  have hpi := sigma_pi hp hp5 i
  rw [← hXg] at hpi
  rw [Polynomial.mul_comp, Polynomial.X_comp] at hpi
  -- hpi : X * ((1-X) * g∘σ) = -((1-X) * (X*g))
  have hfac : (X * (1 - X) : ℤ[X]) * (g.comp (1-X)) = (X * (1-X)) * (-g) := by
    linear_combination hpi
  exact mul_left_cancel₀ X_mul_one_sub_X_ne_zero hfac

/-! ## `U₁(π_i) = 0` -/

theorem Uc_pi_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) :
    Uc (piP p i) 1 = 0 := by
  set π := piP p i with hπ
  set g := π.divX with hgdef
  set n := π.natDegree with hn
  -- the mapped polynomial over ℚ is antisymmetric
  set qq := g.map (Int.castRingHom ℚ) with hqq
  have hcompq : qq.comp (1 - X) = -qq := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (sigma_g hp hp5 i)
    rw [Polynomial.map_comp, Polynomial.map_neg] at h
    rw [hqq]
    have hmap1 : ((1 - X : ℤ[X]).map (Int.castRingHom ℚ)) = (1 - X : ℚ[X]) := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
    rw [← hmap1]
    exact h
  have hdegq : qq.natDegree ≤ n := by
    apply le_trans (Polynomial.natDegree_map_le)
    rw [hgdef, hn]
    exact Polynomial.natDegree_divX_le
  have hanti := antisym_sum qq hcompq n hdegq
  have hqcoeff : ∀ b, qq.coeff b = ((g.coeff b : ℤ) : ℚ) := by
    intro b
    rw [hqq, Polynomial.coeff_map]
    rfl
  -- now compute Uc π 1
  unfold Uc
  rw [← hn, Finset.sum_range_succ']
  have hzero : ((-1:ℤ)^0 * π.coeff 0 * s1 0 1 : ℤ) / ((Nat.factorial 0 : ℤ) : ℚ) = 0 := by
    rw [s1_zero]
    norm_num
  rw [hzero, add_zero]
  have hterm : ∀ b ∈ Finset.range n,
      ((-1:ℤ)^(b+1) * π.coeff (b+1) * s1 (b+1) 1 : ℤ) / (((b+1).factorial : ℤ) : ℚ)
        = -(qq.coeff b / ((b : ℚ)+1)) := by
    intro b _
    rw [s1_one_right b, hqcoeff b]
    have hgb : g.coeff b = π.coeff (b+1) := Polynomial.coeff_divX
    rw [hgb]
    have hfact : (((b+1).factorial : ℤ) : ℚ) = ((b : ℚ)+1) * ((b.factorial : ℤ) : ℚ) := by
      push_cast [Nat.factorial_succ]
      ring
    have hb1 : ((b : ℚ)+1) ≠ 0 := by positivity
    have hbf : ((b.factorial : ℤ) : ℚ) ≠ 0 := by
      have := b.factorial_ne_zero
      exact_mod_cast Nat.cast_ne_zero.mpr this
    rw [hfact]
    push_cast
    have hsign : ((-1:ℚ))^(b+1) * ((-1:ℚ))^b = -1 := by
      rw [← pow_add]
      have hodd : Odd (b + 1 + b) := ⟨b, by ring⟩
      exact hodd.neg_one_pow
    have hsq : ((-1:ℚ))^(b*2) = 1 := by
      rw [mul_comm b 2, pow_mul]
      norm_num
    field_simp
    linear_combination ((π.coeff (b+1) : ℚ) * (b.factorial : ℚ)) * hsign
      + ((π.coeff (b+1) : ℚ) * (b.factorial : ℚ) - (π.coeff (b+1) : ℚ)) * hsq
  rw [Finset.sum_congr rfl hterm]
  -- ∑_{b ∈ Finset.range n} -(qq_b/(b+1)) and hanti : ∑_{b ∈ Finset.range (n+1)} qq_b/(b+1) = 0
  have hlast : qq.coeff n / ((n : ℚ)+1) = 0 := by
    have hgn : g.coeff n = 0 := by
      have : π.coeff (n+1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hgdef, Polynomial.coeff_divX, this]
    rw [hqcoeff n, hgn]
    norm_num
  rw [Finset.sum_range_succ, hlast, add_zero] at hanti
  -- hanti : ∑_{b ∈ Finset.range n} qq_b/(b+1) = 0
  rw [Finset.sum_neg_distrib, hanti, neg_zero]

end A333096

end HelperS11

section HelperS12

/-! # S12: series expansions: `β(pS,pN)`, `𝒢_j`, `C_{ij}` (steps C1–C5 of the blueprint). -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace A333096

open Finset PowerSeries
open scoped Polynomial

/-! ## Units built from `Δ` -/

/-- `Δ` as a power series (defined via `1 + p·h` so that unit-ness is unconditional). -/
noncomputable def D1ser (p : ℕ) : ℤ⟦X⟧ := 1 + (p : ℤ⟦X⟧) * hser p

lemma constantCoeff_D1ser (p : ℕ) : constantCoeff (D1ser p) = 1 := by
  unfold D1ser
  rw [map_add, map_one, map_mul]
  have h0 : constantCoeff (hser p) = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    exact hser_coeff_zero p
  rw [h0, mul_zero, add_zero]

/-- `Δ` as a unit of `ℤ⟦X⟧`. -/
noncomputable def uD (p : ℕ) : (ℤ⟦X⟧)ˣ := unitOf (D1ser p) (constantCoeff_D1ser p)

lemma uD_val (p : ℕ) : ((uD p : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = D1ser p := unitOf_val _ _

/-- `Δ` as a series (the polynomial coercion). -/
noncomputable def Dser (p : ℕ) : ℤ⟦X⟧ := ((Dpoly p : ℤ[X]) : ℤ⟦X⟧)

lemma uD_val' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((uD p : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = Dser p := by
  rw [uD_val]
  unfold Dser
  rw [delta_ser hp hp5]
  rfl

/-- The complementary unit `u₃ = Δ⁻¹ (1-X)^p`. -/
noncomputable def u3 (p : ℕ) : (ℤ⟦X⟧)ˣ := (uD p)⁻¹ * us^(p:ℕ)

lemma us_pow_split (p : ℕ) : ((us : (ℤ⟦X⟧)ˣ))^(p:ℕ) = uD p * u3 p := by
  unfold u3
  rw [mul_inv_cancel_left]

lemma u3_val {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((u3 p : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)
      = 1 - (X : ℤ⟦X⟧)^p * (((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) := by
  unfold u3
  rw [Units.val_mul, Units.val_pow_eq_pow_val, us_val]
  have hD : ((1 - X : ℤ⟦X⟧))^p = Dser p - X^p := by
    unfold Dser
    rw [delta_coe]
    ring
  rw [hD, mul_sub]
  have h1 : (((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * Dser p = 1 := by
    rw [← uD_val' hp hp5, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1]
  ring

/-! ## The inner coefficients -/

/-- `𝒢_j = [X^{pj}] (G · Δ^{j-m₀})`. -/
noncomputable def GG (p : ℕ) (m₀ : ℤ) (j : ℕ) : ℤ :=
  coeff (p*j) (Gs * (((uD p)^((j:ℤ) - m₀) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))

/-- `C_{ij} = [X^{pj}] (Δ^j h^i G)`. -/
noncomputable def Cij (p i j : ℕ) : ℤ :=
  coeff (p*j) ((Dser p)^j * ((hser p)^i * Gs))

lemma neg_one_pow_mul_self (i : ℕ) : (-1:ℤ)^i * (-1:ℤ)^i = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨i, rfl⟩

/-! ## Step 1: the outer expansion of `β(pS, pN)` -/

theorem bet_pS_pN {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (S : ℤ) (N : ℕ) :
    bet (p*S) (p*N) = ∑ j ∈ Finset.range (N+1), mch S (N-j) * GG p (S + N) j := by
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  unfold bet
  -- rewrite `uval (-(p*S))` as `↑((us^p)^(-S))`
  have h1 : uval (-((p:ℤ)*S)) = ((((us : (ℤ⟦X⟧)ˣ)^(p:ℕ))^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) := by
    unfold uval
    congr 1
    rw [← zpow_natCast (us : (ℤ⟦X⟧)ˣ) p, ← zpow_mul]
    congr 1
    ring
  rw [h1, us_pow_split, mul_zpow, Units.val_mul]
  have h2 : Gs * ((((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * (((u3 p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))
      = (((u3 p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * (Gs * (((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)) := by
    ring
  rw [h2]
  have hexp := coeff_unit_zpow_expand
    ((X : ℤ⟦X⟧)^p * (((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))
    (Gs * (((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))
    (u3 p) (u3_val hp hp5) S
    (q := p) (M := p*N) (N := N)
    (dvd_mul_right _ _)
    (by
      have : p*N < p*N + p := by omega
      calc p*N < p*N + p := this
        _ = p*(N+1) := by ring)
  rw [hexp]
  -- simplify each term
  have hterm : ∀ j ∈ Finset.range (N+1),
      (mch S j : ℤ) • coeff (p*N)
          (((X : ℤ⟦X⟧)^p * (((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))^j
            * (Gs * (((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)))
        = mch S j * GG p (S + N) (N - j) := by
    intro j hj
    have hjN : j ≤ N := by
      have := Finset.mem_range.mp hj; omega
    have hpow : (((X : ℤ⟦X⟧)^p * (((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))^j
          * (Gs * (((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)))
        = (X : ℤ⟦X⟧)^(p*j) * ((((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)^j
            * (((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * Gs) := by
      rw [mul_pow, ← pow_mul]
      ring
    rw [hpow]
    have hidx : p*N = p*(N-j) + p*j := by
      have : N = (N - j) + j := by omega
      calc p*N = p*((N-j) + j) := by rw [← this]
        _ = p*(N-j) + p*j := by ring
    rw [hidx, coeff_X_pow_mul]
    have hcomb : ((((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)^j * (((uD p)^(-S) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * Gs)
        = Gs * (((uD p)^(((N-j : ℕ):ℤ) - (S + N)) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) := by
      have hz : (((uD p)⁻¹ : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)^j = (((uD p)^(-(j:ℤ)) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) := by
        rw [← Units.val_pow_eq_pow_val]
        congr 1
        rw [zpow_neg, zpow_natCast, inv_pow]
      rw [hz, ← Units.val_mul, ← zpow_add]
      have harg : -(j:ℤ) + -S = ((N-j : ℕ):ℤ) - (S + N) := by
        have hc : ((N-j : ℕ):ℤ) = (N:ℤ) - (j:ℤ) := by
          rw [Nat.cast_sub hjN]
        rw [hc]
        ring
      rw [harg]
      ring
    rw [hcomb, smul_eq_mul]
    rfl
  rw [Finset.sum_congr rfl hterm]
  -- reflect the sum
  have hterm2 : ∀ j ∈ Finset.range (N+1),
      mch S j * GG p (S + N) (N - j)
        = mch S (N - (N - j)) * GG p (S + N) (N - j) := by
    intro j hj
    have hjN : j ≤ N := by
      have := Finset.mem_range.mp hj; omega
    rw [show N - (N - j) = j by omega]
  rw [Finset.sum_congr rfl hterm2]
  have hR := Finset.sum_range_reflect
    (fun t => mch S (N - t) * GG p (S + N) t) (N+1)
  simp only [Nat.add_sub_cancel] at hR
  exact hR

/-! ## Step 2: the expansion of `𝒢_j` -/

theorem GG_eq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m₀ : ℤ) (N j : ℕ) (hj : j ≤ N) :
    GG p m₀ j = Gcoef j
      + ∑ i ∈ Icc 1 (p*N), ich (-m₀) i * (p:ℤ)^i * Cij p i j := by
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  have hp3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 3) hp).mp h
    omega
  unfold GG
  have hsplit : (uD p)^((j:ℤ) - m₀) = (uD p)^((j:ℤ)) * (uD p)^(-m₀) := by
    rw [← zpow_add, sub_eq_add_neg]
  rw [hsplit, Units.val_mul]
  have hj1 : (((uD p)^((j:ℤ)) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = (Dser p)^j := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, uD_val' hp hp5]
  rw [hj1]
  have h2 : Gs * ((Dser p)^j * (((uD p)^(-m₀) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧))
      = (((uD p)^(-m₀) : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) * ((Dser p)^j * Gs) := by
    ring
  rw [h2]
  have hU : ((uD p : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = 1 - (-((p:ℤ⟦X⟧) * hser p)) := by
    rw [uD_val]
    unfold D1ser
    ring
  have hXdvd : (X : ℤ⟦X⟧)^1 ∣ -((p:ℤ⟦X⟧) * hser p) := by
    rw [pow_one, dvd_neg]
    apply Dvd.dvd.mul_left
    rw [PowerSeries.X_dvd_iff, ← coeff_zero_eq_constantCoeff]
    exact hser_coeff_zero p
  have hexp := coeff_unit_zpow_expand
    (-((p:ℤ⟦X⟧) * hser p)) ((Dser p)^j * Gs) (uD p) hU m₀
    (q := 1) (M := p*j) (N := p*N)
    hXdvd
    (by
      have : p*j ≤ p*N := Nat.mul_le_mul_left p hj
      omega)
  rw [hexp]
  -- peel the `i = 0` term
  rw [Finset.sum_range_succ']
  have hzero : (mch m₀ 0 : ℤ) • coeff (p*j) ((-((p:ℤ⟦X⟧) * hser p))^0 * ((Dser p)^j * Gs))
      = Gcoef j := by
    rw [mch_zero, pow_zero, one_mul, one_smul]
    unfold Dser
    rw [delta_coe]
    exact cartier_fixed hp1 hp3 j
  rw [hzero]
  have hterm : ∀ i ∈ Finset.range (p*N),
      (mch m₀ (i+1) : ℤ) • coeff (p*j)
          ((-((p:ℤ⟦X⟧) * hser p))^(i+1) * ((Dser p)^j * Gs))
        = ich (-m₀) (i+1) * (p:ℤ)^(i+1) * Cij p (i+1) j := by
    intro i _
    have hpow : ((-((p:ℤ⟦X⟧) * hser p))^(i+1) * ((Dser p)^j * Gs))
        = ((-1:ℤ)^(i+1) * (p:ℤ)^(i+1)) • ((Dser p)^j * ((hser p)^(i+1) * Gs)) := by
      rw [zsmul_eq_mul]
      push_cast
      rw [neg_pow, mul_pow]
      ring
    rw [hpow, map_zsmul]
    unfold Cij
    simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_id]
    rw [mch_eq_neg_pow_mul_ich]
    linear_combination (ich (-m₀) (i+1) * (p:ℤ)^(i+1)
      * coeff (p*j) ((Dser p)^j * ((hser p)^(i+1) * Gs))) * (neg_one_pow_mul_self (i+1))
  rw [Finset.sum_congr rfl hterm]
  -- convert Finset.range to Icc
  have hIcc : ∑ i ∈ Icc 1 (p*N), ich (-m₀) i * (p:ℤ)^i * Cij p i j
      = ∑ i ∈ Finset.range (p*N), ich (-m₀) (i+1) * (p:ℤ)^(i+1) * Cij p (i+1) j := by
    have hset : Finset.Icc 1 (p*N) = Finset.Ico 1 (p*N+1) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have h1 : p*N + 1 - 1 = p*N := by omega
    rw [h1]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 1 + i = i + 1 by ring]
  rw [hIcc]
  ring

/-! ## Step 3: the expansion of `β(S, N)` -/

theorem bet_base (S : ℤ) (N : ℕ) :
    bet S N = ∑ j ∈ Finset.range (N+1), mch S (N-j) * Gcoef j := by
  unfold bet
  have h2 : Gs * uval (-S) = uval (-S) * Gs := by ring
  rw [h2]
  unfold uval
  have hexp := coeff_unit_zpow_expand
    (X : ℤ⟦X⟧) Gs us (by rw [us_val]) S
    (q := 1) (M := N) (N := N)
    (by rw [pow_one])
    (by omega)
  rw [hexp]
  have hterm : ∀ j ∈ Finset.range (N+1),
      (mch S j : ℤ) • coeff N ((X:ℤ⟦X⟧)^j * Gs) = mch S j * Gcoef (N - j) := by
    intro j hj
    have hjN : j ≤ N := by
      have := Finset.mem_range.mp hj; omega
    have hidx : N = (N - j) + j := by omega
    rw [hidx, coeff_X_pow_mul, coeff_Gs, smul_eq_mul]
    rw [show (N - j) + j - j = N - j by omega]
  rw [Finset.sum_congr rfl hterm]
  have hterm2 : ∀ j ∈ Finset.range (N+1),
      mch S j * Gcoef (N - j) = mch S (N - (N - j)) * Gcoef (N - j) := by
    intro j hj
    have hjN : j ≤ N := by
      have := Finset.mem_range.mp hj; omega
    rw [show N - (N - j) = j by omega]
  rw [Finset.sum_congr rfl hterm2]
  have hR := Finset.sum_range_reflect
    (fun t => mch S (N - t) * Gcoef t) (N+1)
  simp only [Nat.add_sub_cancel] at hR
  exact hR

/-! ## Step 4: `C_{ij}` via `F` -/

lemma Fp_eq_range (π : Polynomial ℤ) (M : ℕ) :
    Fp π M = ∑ a ∈ Finset.range (M+1), (-1:ℤ)^a * π.coeff a * (M.choose a : ℤ) := by
  rcases le_or_gt π.natDegree M with h | h
  · rw [Fp_ext π M h]
  · rw [Fp_ext π M (le_refl _)]
    symm
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at *
      omega
    · intro x _ hx
      rw [Finset.mem_range, not_lt] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      push_cast
      ring

/-- `[X^M] ((1-X)^M · π) = (-1)^M F(π; M)`. -/
lemma coeff_pow_mul_poly (π : Polynomial ℤ) (M : ℕ) :
    coeff M ((1 - X : ℤ⟦X⟧)^M * (π : ℤ⟦X⟧)) = (-1:ℤ)^M * Fp π M := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ k ∈ Finset.range (M+1),
      coeff k ((1 - X : ℤ⟦X⟧)^M) * coeff (M - k) (π : ℤ⟦X⟧)
        = (-1:ℤ)^(M + (M-k)) * (π.coeff (M-k) * (M.choose (M-k) : ℤ)) := by
    intro k hk
    have hkM : k ≤ M := by
      have := Finset.mem_range.mp hk; omega
    rw [coeff_one_sub_X_pow, Polynomial.coeff_coe]
    have hsign : (-1:ℤ)^k = (-1:ℤ)^(M + (M-k)) := by
      rw [show M + (M-k) = k + 2*(M-k) by omega, pow_add, pow_mul]
      norm_num
    have hch : (M.choose k : ℤ) = (M.choose (M-k) : ℤ) := by
      rw [Nat.choose_symm hkM]
    rw [hsign, hch]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hR := Finset.sum_range_reflect
    (fun t => (-1:ℤ)^(M + t) * (π.coeff t * (M.choose t : ℤ))) (M+1)
  simp only [Nat.add_sub_cancel] at hR
  rw [hR]
  rw [Fp_eq_range π M, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_add]
  ring

/-- Step C5: `C_{ij} = ∑_K C(j,K) (-1)^K F(π_i; pK)`. -/
theorem Cij_eq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i j : ℕ) (hi : 1 ≤ i) :
    Cij p i j = ∑ K ∈ Finset.range (j+1),
      (j.choose K : ℤ) * ((-1:ℤ)^K * Fp (piP p i) (p*K)) := by
  unfold Cij
  rw [← piP_series hp hp5 i hi]
  unfold Dser
  rw [delta_coe, expand_delta]
  apply Finset.sum_congr rfl
  intro K _
  rw [coeff_pow_mul_poly]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsign : (-1:ℤ)^(p*K) = (-1:ℤ)^K := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [hsign]

end A333096

end HelperS12

section HelperS13

/-! # S13: the master identity (step C7). -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace A333096

open Finset PowerSeries
open scoped Polynomial

/-- `Ξ_c(S,N) = ∑_{j=1}^{min(c,N)} (-1)^j j! S₂(c,j) C(S+N-1-j, N-j)`. -/
noncomputable def Xi (c : ℕ) (S : ℤ) (N : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 (min c N), (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) * mch S (N-j)

lemma Xi_eq_range {c : ℕ} (hc : 1 ≤ c) (S : ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), (-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) * mch S (N-j)
      = Xi c S N := by
  unfold Xi
  symm
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  · intro x hx hnx
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hnx
    have hcase : x = 0 ∨ (min c N < x) := by omega
    rcases hcase with rfl | hgt
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c-1, by omega⟩
      rw [S2_succ_zero]
      push_cast
      ring
    · have hcx : c < x := by omega
      rw [S2_eq_zero_of_lt hcx]
      push_cast
      ring

lemma Uc_pi_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) :
    Uc (piP p i) 0 = 0 := by
  unfold Uc
  apply Finset.sum_eq_zero
  intro a _
  rcases a with _ | a'
  · rw [piP_coeff_zero hp hp5]
    norm_num
  · rw [s1_succ_zero, mul_zero, Int.cast_zero, zero_div]

/-- Cast of the `W`-identity to ℚ. -/
lemma W_identity_rat (c j : ℕ) :
    ∑ K ∈ Finset.range (j + 1), (j.choose K : ℚ) * (-1:ℚ)^K * (K:ℚ)^c
      = (-1:ℚ)^j * (j.factorial : ℚ) * (S2 c j : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (W_identity c j)
  push_cast at h
  push_cast
  exact h

/-- `C_{ij}` in ℚ via `U_c` and Stirling numbers. -/
lemma Cij_rat {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (i j : ℕ) (hi : 1 ≤ i) :
    ((Cij p i j : ℤ) : ℚ)
      = ∑ c ∈ Finset.range ((piP p i).natDegree + 1),
          Uc (piP p i) c * (p:ℚ)^c
            * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) : ℤ) : ℚ) := by
  rw [Cij_eq hp hp5 i j hi]
  push_cast
  have hstep : ∀ K ∈ Finset.range (j+1),
      (j.choose K : ℚ) * ((-1:ℚ)^K * ((Fp (piP p i) (p*K) : ℤ) : ℚ))
        = ∑ c ∈ Finset.range ((piP p i).natDegree + 1),
            (j.choose K : ℚ) * (-1:ℚ)^K * (Uc (piP p i) c * ((p:ℚ)^c * (K:ℚ)^c)) := by
    intro K _
    rw [Fp_eq_sum_Uc (piP p i) (p*K), Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    have hcast : (((p*K : ℕ)) : ℚ)^c = (p:ℚ)^c * (K:ℚ)^c := by
      push_cast
      rw [mul_pow]
    rw [hcast]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← W_identity_rat c j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  ring

/-- Uniform-Finset.range version of `Cij_rat`. -/
lemma Cij_rat' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {i N : ℕ} (j : ℕ)
    (hi : 1 ≤ i) (hiN : i ≤ p*N) :
    ((Cij p i j : ℤ) : ℚ)
      = ∑ c ∈ Finset.range (p*N*(p-1) + 1),
          Uc (piP p i) c * (p:ℚ)^c
            * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) : ℤ) : ℚ) := by
  rw [Cij_rat hp hp5 i j hi]
  apply Finset.sum_subset
  · intro c hc
    rw [Finset.mem_range] at *
    have h1 := piP_natDegree_le hp hp5 i hi
    have h2 : i * (p-1) ≤ p*N*(p-1) := Nat.mul_le_mul_right _ hiN
    omega
  · intro c _ hc
    rw [Finset.mem_range, not_lt] at hc
    rw [Uc_eq_zero_of_gt (piP p i) (by omega)]
    ring

/-- **The master identity** (step C7): for `N ≥ 1`, `S ∈ ℤ`, `p ≥ 5` prime,
`β(pS, pN) - β(S, N) = ∑_{i,c} binom(-m₀, i) p^{i+c} U_c(π_i) Ξ_c(S,N)`. -/
theorem master_identity {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (S : ℤ) (N : ℕ) :
    ((bet ((p:ℤ)*S) (p*N) - bet S N : ℤ) : ℚ)
      = ∑ i ∈ Icc 1 (p*N), ∑ c ∈ Icc 2 (p*N*(p-1)),
          ((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^(i+c) * Uc (piP p i) c
            * ((Xi c S N : ℤ) : ℚ) := by
  -- Step A (in ℤ): difference as a double sum over j, i
  have hA : bet ((p:ℤ)*S) (p*N) - bet S N
      = ∑ j ∈ Finset.range (N+1), mch S (N-j)
          * (∑ i ∈ Icc 1 (p*N), ich (-(S+(N:ℤ))) i * (p:ℤ)^i * Cij p i j) := by
    rw [bet_pS_pN hp hp5 S N, bet_base S N, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N := by
      have := Finset.mem_range.mp hj; omega
    rw [GG_eq hp hp5 (S+(N:ℤ)) N j hjN]
    ring
  -- cast to ℚ
  have hB : ((bet ((p:ℤ)*S) (p*N) - bet S N : ℤ) : ℚ)
      = ∑ j ∈ Finset.range (N+1), ((mch S (N-j) : ℤ) : ℚ)
          * (∑ i ∈ Icc 1 (p*N),
              ((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^i * ((Cij p i j : ℤ) : ℚ)) := by
    rw [hA]
    push_cast
    rfl
  rw [hB]
  -- Step B: substitute `Cij_rat'` and flatten
  have hC : ∀ j ∈ Finset.range (N+1), ((mch S (N-j) : ℤ) : ℚ)
          * (∑ i ∈ Icc 1 (p*N),
              ((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^i * ((Cij p i j : ℤ) : ℚ))
      = ∑ i ∈ Icc 1 (p*N), ∑ c ∈ Finset.range (p*N*(p-1) + 1),
          ((mch S (N-j) : ℤ) : ℚ) * (((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^i
            * (Uc (piP p i) c * (p:ℚ)^c
                * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) : ℤ) : ℚ))) := by
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Cij_rat' hp hp5 j hi.1 hi.2]
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl hC]
  -- Fubini: bring the j-sum inside
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Finset.sum_comm]
  -- restrict the c-Finset.range to `Icc 2 CD`
  have hD : ∑ c ∈ Icc 2 (p*N*(p-1)), (∑ j ∈ Finset.range (N+1),
        ((mch S (N-j) : ℤ) : ℚ) * (((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^i
          * (Uc (piP p i) c * (p:ℚ)^c
              * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) : ℤ) : ℚ))))
      = ∑ c ∈ Finset.range (p*N*(p-1) + 1), (∑ j ∈ Finset.range (N+1),
        ((mch S (N-j) : ℤ) : ℚ) * (((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^i
          * (Uc (piP p i) c * (p:ℚ)^c
              * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) : ℤ) : ℚ)))) := by
    apply Finset.sum_subset
    · intro c hc
      rw [Finset.mem_Icc] at hc
      rw [Finset.mem_range]
      omega
    · intro c hc hnc
      rw [Finset.mem_range] at hc
      rw [Finset.mem_Icc] at hnc
      have hc01 : c = 0 ∨ c = 1 := by omega
      apply Finset.sum_eq_zero
      intro j _
      rcases hc01 with rfl | rfl
      · rw [Uc_pi_zero hp hp5 i]
        ring
      · rw [Uc_pi_one hp hp5 i]
        ring
  rw [← hD]
  -- final per-(i,c) simplification
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_Icc] at hc
  have hstep : ∀ j ∈ Finset.range (N+1),
      ((mch S (N-j) : ℤ) : ℚ) * (((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^i
          * (Uc (piP p i) c * (p:ℚ)^c
              * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) : ℤ) : ℚ)))
        = (((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^(i+c) * Uc (piP p i) c)
            * (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) * mch S (N-j) : ℤ) : ℚ) := by
    intro j _
    push_cast
    rw [pow_add]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hXi : ∑ j ∈ Finset.range (N+1),
      (((-1:ℤ)^j * (j.factorial : ℤ) * (S2 c j : ℤ) * mch S (N-j) : ℤ) : ℚ)
        = ((Xi c S N : ℤ) : ℚ) := by
    rw [← Int.cast_sum]
    congr 1
    exact Xi_eq_range (by omega) S N
  rw [hXi]

end A333096

end HelperS13

section HelperS14

/-! # S14: Module D — valuation bounds for `Xi` (D3–D5). -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset

/-! ## The auxiliary polynomial-value functions -/

/-- `P1 Y m = ∏_{s=1}^{m} (Y - s)`. -/
noncomputable def P1 (Y : ℤ) (m : ℕ) : ℤ := ∏ s ∈ Ioc 0 m, (Y - (s:ℤ))

/-- `Aprod X c d = ∏_{e=0}^{d-1} (X - c + e)`. -/
noncomputable def Aprod (X : ℤ) (c d : ℕ) : ℤ := ∏ e ∈ Finset.range d, (X - (c:ℤ) + (e:ℤ))

/-- `f_c(X,Y) = ∑_{j=1}^{c} (-1)^{c-j} j! S₂(c,j) ∏_{t=j+1}^c (X-t) ∏_{s=1}^{j-1} (Y-s)`. -/
noncomputable def fpoly (c : ℕ) (X Y : ℤ) : ℤ :=
  ∑ j ∈ Icc 1 c,
    (-1:ℤ)^(c-j) * (j.factorial:ℤ) * (S2 c j :ℤ) * Aprod X c (c-j) * P1 Y (j-1)

/-! ## The climbing identity -/

/-- Iterated ratio identity: climbing the binomial index from `K` to `K + d`. -/
lemma climb (S : ℤ) (K : ℕ) (d : ℕ) :
    ich (-S) (K + d) * ∏ e ∈ Finset.range d, ((K:ℤ) + 1 + (e:ℤ))
      = (-1:ℤ)^d * (∏ e ∈ Finset.range d, (S + (K:ℤ) + (e:ℤ))) * ich (-S) K := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [prod_range_succ, prod_range_succ]
    have hr := ich_ratio (-S) (K + d)
    push_cast at hr
    have hidx : K + (d+1) = (K + d) + 1 := by omega
    rw [hidx]
    linear_combination
      (∏ e ∈ Finset.range d, ((K:ℤ) + 1 + (e:ℤ))) * hr + (-(S + (K:ℤ) + (d:ℤ))) * ih

/-! ## D3: the Xi product identity -/

lemma Xi_mul {c N : ℕ} (hc : 1 ≤ c) (hcN : c ≤ N) (S : ℤ) :
    Xi c S N * P1 (N:ℤ) (c-1)
      = (-1:ℤ)^N * ich (-S) (N-c) * fpoly c (S + (N:ℤ)) (N:ℤ) := by
  unfold Xi fpoly
  rw [min_eq_left hcN, sum_mul, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  -- split P1 (c-1) into P1 (j-1) times the ascending product
  have hsplit : P1 (N:ℤ) (c-1)
      = P1 (N:ℤ) (j-1) * ∏ e ∈ Finset.range (c-j), (((N-c:ℕ):ℤ) + 1 + (e:ℤ)) := by
    unfold P1
    rw [← prod_Ioc_consecutive _ (Nat.zero_le (j-1)) (show j-1 ≤ c-1 by omega)]
    congr 1
    rw [show Ioc (j-1) (c-1) = Ico j c from by
          ext t; simp only [mem_Ioc, mem_Ico]; omega,
        prod_Ico_eq_prod_range, ← prod_range_reflect]
    refine prod_congr rfl fun e he => ?_
    rw [mem_range] at he
    omega
  have hclimb := climb S (N-c) (c-j)
  rw [show (N-c) + (c-j) = N - j from by omega] at hclimb
  have hA : Aprod (S + (N:ℤ)) c (c-j)
      = ∏ e ∈ Finset.range (c-j), (S + ((N-c:ℕ):ℤ) + (e:ℤ)) := by
    unfold Aprod
    refine prod_congr rfl fun e he => ?_
    omega
  have hsign : (-1:ℤ)^j * (-1:ℤ)^(N-j) = (-1:ℤ)^N := by
    rw [← pow_add]; congr 1; omega
  rw [mch_eq_neg_pow_mul_ich, hsplit, hA]
  linear_combination
    ((-1:ℤ)^j * (j.factorial:ℤ) * (S2 c j:ℤ) * (-1:ℤ)^(N-j) * P1 (N:ℤ) (j-1)) * hclimb
    + ((-1:ℤ)^(c-j) * (j.factorial:ℤ) * (S2 c j:ℤ)
        * (∏ e ∈ Finset.range (c-j), (S + ((N-c:ℕ):ℤ) + (e:ℤ))) * P1 (N:ℤ) (j-1)
        * ich (-S) (N-c)) * hsign

/-! ## D4: the constant term vanishes -/

lemma Aprod_zero (c : ℕ) : ∀ d : ℕ, d ≤ c →
    Aprod 0 c d = (-1:ℤ)^d * (c.descFactorial d : ℤ) := by
  intro d
  induction d with
  | zero => intro _; simp [Aprod]
  | succ d ih =>
    intro hdc
    unfold Aprod at ih ⊢
    rw [prod_range_succ, ih (by omega), Nat.descFactorial_succ]
    push_cast [Nat.cast_sub (show d ≤ c by omega)]
    ring

lemma P1_zero : ∀ m : ℕ, P1 0 m = (-1:ℤ)^m * (m.factorial : ℤ) := by
  intro m
  induction m with
  | zero => simp [P1]
  | succ m ih =>
    unfold P1 at ih ⊢
    rw [prod_Ioc_succ_top (Nat.zero_le _), ih, Nat.factorial_succ]
    push_cast
    ring

lemma fpoly_zero {c : ℕ} (hc : 2 ≤ c) : fpoly c 0 0 = 0 := by
  unfold fpoly
  have h1 : ∀ j ∈ Icc 1 c,
      (-1:ℤ)^(c-j) * (j.factorial:ℤ) * (S2 c j:ℤ) * Aprod 0 c (c-j) * P1 0 (j-1)
        = (c.factorial:ℤ) * ((-1:ℤ)^(j-1) * ((j-1).factorial:ℤ) * (S2 c j:ℤ)) := by
    intro j hj
    rw [mem_Icc] at hj
    rw [Aprod_zero c (c-j) (by omega), P1_zero]
    have hfd : (j.factorial:ℤ) * (c.descFactorial (c-j) : ℤ) = (c.factorial:ℤ) := by
      have h := Nat.factorial_mul_descFactorial (show c-j ≤ c by omega)
      rw [show c - (c-j) = j from by omega] at h
      exact_mod_cast h
    have hsq : (-1:ℤ)^(c-j) * (-1:ℤ)^(c-j) = 1 := neg_one_pow_mul_self _
    linear_combination
      ((S2 c j:ℤ) * (-1:ℤ)^(j-1) * ((j-1).factorial:ℤ) * (c.descFactorial (c-j):ℤ)
        * (j.factorial:ℤ)) * hsq
      + ((-1:ℤ)^(j-1) * ((j-1).factorial:ℤ) * (S2 c j:ℤ)) * hfd
  rw [sum_congr rfl h1, ← mul_sum]
  have h2 : ∑ j ∈ Icc 1 c, (-1:ℤ)^(j-1) * ((j-1).factorial:ℤ) * (S2 c j:ℤ) = Ac c := by
    rw [show Icc 1 c = Ico 1 (c+1) from by
          ext t; simp only [mem_Icc, mem_Ico]; omega,
        Finset.sum_Ico_eq_sum_range]
    unfold Ac
    rw [show c + 1 - 1 = c from rfl]
    refine sum_congr rfl fun t ht => ?_
    rw [show 1 + t - 1 = t from by omega, show 1 + t = t + 1 from by omega]
  rw [h2, Ac_eq_zero hc, mul_zero]

/-! ## p-adic lemmas -/

section PrimeSection

variable {p : ℕ} (hp : p.Prime)
include hp

lemma EOrd_unique {e f : ℕ} {d : ℤ} (he : EOrd p e d) (hf : EOrd p f d) : e = f := by
  by_contra hne
  rcases Nat.lt_or_ge e f with h | h
  · exact he.2 (dvd_trans (pow_dvd_pow _ (by omega)) hf.1)
  · exact hf.2 (dvd_trans (pow_dvd_pow _ (by omega)) he.1)

lemma nu_fact_sum (m : ℕ) :
    padicValNat p m.factorial = ∑ s ∈ Ioc 0 m, padicValNat p s := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction m with
  | zero => simp [Nat.factorial]
  | succ m ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ← ih, Nat.factorial_succ,
        padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    omega

/-- Exact order of `P1 (N:ℤ) (c-1)` when `p^v ∣ N` and `c - 1 < p^v`. -/
lemma EOrd_P1 {v c : ℕ} {N : ℕ} (hN : (p:ℤ)^v ∣ (N:ℤ)) (hcp : c - 1 < p^v) :
    EOrd p (padicValNat p (c-1).factorial) (P1 (N:ℤ) (c-1)) := by
  rw [nu_fact_sum hp]
  refine EOrd_prod hp _ _ _ (fun s hs => ?_)
  rw [mem_Ioc] at hs
  exact EOrd_sub_of_dvd hp hN hs.1 (nu_lt_of_lt_pow hp hs.1 (by omega))

/-- D4 wrapper: `p^v` divides `fpoly c m₀ N` when `p^v ∣ m₀`, `p^v ∣ N`, `c ≥ 2`. -/
lemma fpoly_dvd {v c : ℕ} {m₀ : ℤ} {N : ℕ} (hm : (p:ℤ)^v ∣ m₀) (hN : p^v ∣ N)
    (hc : 2 ≤ c) : (p:ℤ)^v ∣ fpoly c m₀ (N:ℤ) := by
  have hnz : p ^ v ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hm0 : ((m₀ : ℤ) : ZMod (p^v)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm
  have hN0 : ((N : ℕ) : ZMod (p^v)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hN
  have key : ((fpoly c m₀ (N:ℤ) : ℤ) : ZMod (p^v)) = ((fpoly c 0 (0:ℤ) : ℤ) : ZMod (p^v)) := by
    unfold fpoly Aprod P1
    push_cast
    rw [hm0, hN0]
  rw [fpoly_zero hc] at key
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using key)
  have hcast : ((p^v : ℕ) : ℤ) = (p:ℤ)^v := by push_cast; ring
  rwa [hcast] at h

/-! ## D5: the main Xi bound -/

lemma Xi_bound (hp5 : 5 ≤ p) {v c N : ℕ} {S : ℤ}
    (hc2 : 2 ≤ c) (hpv : c < p^v) (hS : (p:ℤ)^v ∣ S) (hN : p^v ∣ N)
    (hN1 : 1 ≤ N) :
    POge p (2*(v:ℤ) - (padicValNat p c.factorial : ℤ)) ((Xi c S N : ℤ) : ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpN : p^v ≤ N := Nat.le_of_dvd (by omega) hN
  have hcN : c < N := lt_of_lt_of_le hpv hpN
  have hNZ : (p:ℤ)^v ∣ (N:ℤ) := by exact_mod_cast Int.natCast_dvd_natCast.mpr hN
  -- ν(N-c) = ν(c)
  have hE1 : EOrd p (padicValNat p c) ((N:ℤ) - (c:ℤ)) :=
    EOrd_sub_of_dvd hp hNZ (by omega) (nu_lt_of_lt_pow hp (by omega) hpv)
  have hE2 : EOrd p (padicValNat p (N - c)) ((N:ℤ) - (c:ℤ)) := by
    rw [show (N:ℤ) - (c:ℤ) = ((N - c : ℕ) : ℤ) from by omega]
    exact EOrd_padicValNat hp (by omega)
  have hnu : padicValNat p (N - c) = padicValNat p c := EOrd_unique hp hE2 hE1
  -- D2 for the binomial factor
  have hich := D2 hp hS (show 1 ≤ N - c by omega)
  rw [hnu, min_eq_right (le_of_lt (nu_lt_of_lt_pow hp (show 1 ≤ c by omega) hpv))] at hich
  -- fpoly divisibility
  have hf : POge p (v:ℤ) ((fpoly c (S + (N:ℤ)) (N:ℤ) : ℤ) : ℚ) :=
    POge_of_dvd hp (fpoly_dvd hp (dvd_add hS hNZ) hN hc2)
  have hsgn : POge p 0 ((((-1:ℤ)^N : ℤ) : ℚ)) := POge_int hp _
  have hprod := POge_mul hp (POge_mul hp hsgn hich) hf
  -- Exact order of P1
  have hP1 : EOrd p (padicValNat p (c-1).factorial) (P1 (N:ℤ) (c-1)) :=
    EOrd_P1 hp hNZ (by omega)
  have hdiv := POge_div hp hprod hP1
  have hP1ne : P1 (N:ℤ) (c-1) ≠ 0 := fun h => hP1.2 (by rw [h]; exact dvd_zero _)
  -- rewrite Xi as the quotient
  have hXi := Xi_mul (show 1 ≤ c by omega) (le_of_lt hcN) S
  have hx : ((Xi c S N : ℤ) : ℚ)
      = (((-1:ℤ)^N : ℤ):ℚ) * ((ich (-S) (N-c) : ℤ):ℚ)
          * ((fpoly c (S + (N:ℤ)) (N:ℤ) : ℤ):ℚ) / ((P1 (N:ℤ) (c-1) : ℤ):ℚ) := by
    have hq : ((P1 (N:ℤ) (c-1) : ℤ):ℚ) ≠ 0 := by exact_mod_cast hP1ne
    rw [eq_div_iff hq]
    have := congrArg (fun z : ℤ => (z : ℚ)) hXi
    push_cast at this ⊢
    linarith [this]
  rw [hx]
  -- exponent bookkeeping
  have hfact : padicValNat p c.factorial
      = padicValNat p c + padicValNat p (c-1).factorial := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
  refine POge_mono hp ?_ hdiv
  omega

end PrimeSection

end A333096

end HelperS14

section HelperS15

/-! # S15: Module E — assembly of the valuation bounds; Theorem C2. -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace A333096

open Finset

/-! ## Numeric helper lemmas -/

lemma pow_lin {v : ℕ} (hv : 1 ≤ v) : 3*v + 2 ≤ 5^v := by
  induction v with
  | zero => omega
  | succ v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv1
    · norm_num
    · have h := ih hv1
      rw [pow_succ]
      omega

lemma powB2a {m : ℕ} (hm : 1 ≤ m) : 16*m + 39 ≤ 12 * 5^m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · norm_num
    · have h := ih hm1
      rw [pow_succ]
      omega

lemma powB2b {L : ℕ} (hL : 2 ≤ L) : 16*L^2 + 44*L + 24 ≤ 12 * 5^L := by
  induction L with
  | zero => omega
  | succ L ih =>
    rcases Nat.lt_or_ge L 2 with hL1 | hL1
    · interval_cases L
      · omega
      · norm_num
    · have h := ih hL1
      have h1 : (L+1)^2 = L^2 + 2*L + 1 := by ring
      have h2 : (5:ℕ)^(L+1) = 5^L * 5 := pow_succ 5 L
      rw [h1, h2]
      omega

section PrimeSection

variable {p : ℕ} (hp : p.Prime)
include hp

/-- The per-term valuation bound: every term of the master identity has
`p`-adic valuation at least `3(1+v)`. -/
lemma term_bound (hp5 : 5 ≤ p) {v : ℕ} {S : ℤ} {N : ℕ}
    (hS : (p:ℤ)^v ∣ S) (hN : p^v ∣ N) (hN1 : 1 ≤ N)
    {i c : ℕ} (hi : 1 ≤ i) (hc : 2 ≤ c) :
    POge p ((3*(1+v) : ℕ):ℤ)
      (((ich (-(S+(N:ℤ))) i : ℤ) : ℚ) * (p:ℚ)^(i+c) * Uc (piP p i) c
        * ((Xi c S N : ℤ) : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNZ : (p:ℤ)^v ∣ (N:ℤ) := by exact_mod_cast Int.natCast_dvd_natCast.mpr hN
  have hm₀ : (p:ℤ)^v ∣ (S + (N:ℤ)) := dvd_add hS hNZ
  -- the binomial factor
  have hich := D1 hp hm₀ hi
  -- the power factor
  have hpow : POge p ((i:ℤ)+(c:ℤ)) ((p:ℚ)^(i+c)) := by
    have h := POge_of_dvd hp (dvd_refl ((p:ℤ)^(i+c)))
    push_cast at h
    exact h
  -- degree facts
  have hd := piP_natDegree_le hp hp5 i hi
  have h4 : 1*(p-1) ≤ i*(p-1) := Nat.mul_le_mul_right _ hi
  have hdeg2 : (piP p i).natDegree + 2 ≤ i*(p-1) := by omega
  -- ν(c!) bound
  have hnf4 : 4 * padicValNat p c.factorial ≤ c - 1 := four_mul_nu_factorial_le hp hp5 c
  rcases Nat.lt_or_ge c (p^v) with hcpv | hcpv
  · -- ### Case B : c < p^v  (so v ≥ 1)
    have hv1 : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with rfl | h
      · rw [pow_zero] at hcpv; omega
      · exact h
    have hXi := Xi_bound hp hp5 hc hcpv hS hN hN1
    rcases Nat.lt_or_ge c (2 + min v (padicValNat p i) + padicValNat p c.factorial)
      with hcm | hcm
    · -- #### Case B2 : c < 2 + m + ν(c!) — use U-b
      have h3c : 3*c ≤ 3 + 4*(min v (padicValNat p i)) := by omega
      have hm1 : 1 ≤ min v (padicValNat p i) := by omega
      have he1 : 1 ≤ padicValNat p i := by omega
      have hipe : p^(padicValNat p i) ≤ i := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
      have hpe5 : 5^(padicValNat p i) ≤ p^(padicValNat p i) :=
        Nat.pow_le_pow_left (by omega) _
      have hU := U_bound_b hp (show 1 ≤ c by omega) hd
        (fun t ht1 ht2 => nu_le_log hp ht1 ht2)
      have hcomb := POge_mul hp (POge_mul hp (POge_mul hp hich hpow) hU) hXi
      refine POge_mono hp ?_ hcomb
      -- need: 3(1+v) ≤ (v-m) + (i+c) - cΛ + (2v - ν(c!))
      have key : 3 + min v (padicValNat p i)
          + c * Nat.log p (i*(p-1)-2) + padicValNat p c.factorial ≤ i + c := by
        rcases Nat.lt_or_ge (Nat.log p (i*(p-1)-2)) 2 with hL | hL
        · -- Λ ≤ 1
          have h5m : 16*(min v (padicValNat p i)) + 39
              ≤ 12 * 5^(min v (padicValNat p i)) := powB2a hm1
          have h5me : 5^(min v (padicValNat p i)) ≤ 5^(padicValNat p i) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have hcL : c * Nat.log p (i*(p-1)-2) ≤ c*1 :=
            Nat.mul_le_mul_left c (by omega)
          omega
        · -- Λ ≥ 2
          have hip : p ≤ i := by
            calc p = p^1 := (pow_one p).symm
            _ ≤ p^(padicValNat p i) := Nat.pow_le_pow_right (by omega) he1
            _ ≤ i := hipe
          have h20 : 5*4 ≤ i*(p-1) := Nat.mul_le_mul (by omega) (by omega)
          have heL : padicValNat p i ≤ Nat.log p i := nu_le_log hp (by omega) (le_refl i)
          have hiub : i < p^(Nat.log p i + 1) := Nat.lt_pow_succ_log_self hp.one_lt i
          have hΛL : Nat.log p (i*(p-1)-2) ≤ Nat.log p i + 1 := by
            have h1 : i*(p-1) - 2 < p^(Nat.log p i + 2) := by
              have h2 : i*(p-1) < p^(Nat.log p i + 1) * p := by
                calc i*(p-1) < i*p := mul_lt_mul_of_pos_left (by omega) (by omega)
                _ ≤ p^(Nat.log p i + 1) * p := Nat.mul_le_mul_right _ (le_of_lt hiub)
              rw [show Nat.log p i + 2 = (Nat.log p i + 1) + 1 from rfl, pow_succ]
              omega
            have := Nat.log_lt_of_lt_pow (show i*(p-1)-2 ≠ 0 by omega) h1
            omega
          have hpLi : p^(Nat.log p i) ≤ i := Nat.pow_log_le_self p (by omega)
          have h5L : 5^(Nat.log p i) ≤ p^(Nat.log p i) := Nat.pow_le_pow_left (by omega) _
          rcases Nat.lt_or_ge (Nat.log p i) 2 with hL2 | hL2
          · -- L = 1, Λ = 2, c = 2, ν(c!) = 0, i ≥ p+2
            have hΛ2 : Nat.log p (i*(p-1)-2) = 2 := by omega
            have hpow2 : p^2 ≤ i*(p-1)-2 := by
              calc p^2 ≤ p^(Nat.log p (i*(p-1)-2)) :=
                    Nat.pow_le_pow_right (by omega) hL
              _ ≤ i*(p-1)-2 := Nat.pow_log_le_self p (by omega)
            have hip2 : p + 2 ≤ i := by
              by_contra hcon
              push_neg at hcon
              have h1 : i*(p-1) ≤ (p+1)*(p-1) := Nat.mul_le_mul_right _ (by omega)
              have h2 : (p+1)*(p-1) + 1 = p*p := by
                obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p-1, by omega⟩
                simp only [Nat.add_sub_cancel]
                ring
              rw [pow_two] at hpow2
              omega
            have hc2 : c ≤ 2 := by omega
            have hcΛ4 : c * Nat.log p (i*(p-1)-2) ≤ 4 := by
              calc c * Nat.log p (i*(p-1)-2) = c * 2 := by rw [hΛ2]
              _ ≤ 4 := by omega
            omega
          · -- L ≥ 2 : the exponential estimate
            have hnum := powB2b hL2
            have hcΛle : c * Nat.log p (i*(p-1)-2) ≤ c*(Nat.log p i + 1) :=
              Nat.mul_le_mul_left c hΛL
            have hprod : 3*(c*(Nat.log p i + 1))
                ≤ (3 + 4*Nat.log p i)*(Nat.log p i + 1) := by
              rw [← mul_assoc]
              exact Nat.mul_le_mul_right _ (by omega)
            have hexp : (3 + 4*Nat.log p i)*(Nat.log p i + 1)
                = 4*(Nat.log p i)^2 + 7*(Nat.log p i) + 3 := by ring
            omega
      have hcast : (c:ℤ) * (Nat.log p (i*(p-1)-2) : ℤ)
          = ((c * Nat.log p (i*(p-1)-2) : ℕ) : ℤ) := by
        push_cast
        ring
      omega
    · -- #### Case B1 : c ≥ 2 + m + ν(c!) — use U-a
      have hU := U_bound_a hp hi hdeg2 c
      have hcomb := POge_mul hp (POge_mul hp (POge_mul hp hich hpow) hU) hXi
      refine POge_mono hp ?_ hcomb
      omega
  · -- ### Case A : c ≥ p^v — use U-a and the trivial Xi bound
    have hU := U_bound_a hp hi hdeg2 c
    have hXi0 : POge p 0 ((Xi c S N : ℤ) : ℚ) := POge_int hp _
    have hcomb := POge_mul hp (POge_mul hp (POge_mul hp hich hpow) hU) hXi0
    refine POge_mono hp ?_ hcomb
    have hpv32 : 3*v + 2 ≤ p^v ∨ v = 0 := by
      rcases Nat.eq_zero_or_pos v with h | h
      · right; exact h
      · left; exact le_trans (pow_lin h) (Nat.pow_le_pow_left (by omega) v)
    have hpv0 : v = 0 → p^v = 1 := fun h => by rw [h, pow_zero]
    omega

/-- **Theorem C2**: the key supercongruence for `bet`. -/
theorem C2 (hp5 : 5 ≤ p) {v : ℕ} {S : ℤ} {N : ℕ}
    (hS : (p:ℤ)^v ∣ S) (hN : p^v ∣ N) (hN1 : 1 ≤ N) :
    (p:ℤ)^(3*(1+v)) ∣ (bet ((p:ℤ)*S) (p*N) - bet S N) := by
  apply dvd_of_POge hp
  rw [master_identity hp hp5 S N]
  refine POge_sum hp _ _ fun i hi => POge_sum hp _ _ fun c hc => ?_
  rw [mem_Icc] at hi hc
  exact term_bound hp hp5 hS hN hN1 hi.1 hc.1

end PrimeSection

end A333096

end HelperS15

open A333096

/--
Conjecture on OEIS A333096:
More generally, for each integer $m$, we conjecture that the sequence
$a_m(n) := \text{the } n\text{-th order Taylor polynomial of } c(x)^{m \cdot n} \text{ evaluated at } x = 1$
satisfies the supercongruences $a_m(n \cdot p^k) \equiv a_m(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have hN2 : 1 ≤ n * p ^ (k-1) := by
    have h1 : 1 ≤ p ^ (k-1) := Nat.one_le_pow _ _ hp.pos
    have := Nat.mul_le_mul hn h1
    omega
  have hpN : p * (n * p^(k-1)) = n * p^k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hN1 : 1 ≤ n * p ^ k := by
    rw [← hpN]
    have := Nat.mul_le_mul hp.pos hN2
    omega
  have hdiff := a_gen_sub_eq_bet m (n*p^k) (n*p^(k-1)) hN1 hN2
  rw [show n*p^k = p*(n*p^(k-1)) from hpN.symm] at hdiff ⊢
  have hSid : m * ((p*(n*p^(k-1)):ℕ):ℤ) + ((p*(n*p^(k-1)):ℕ):ℤ)
      = (p:ℤ) * (m*((n*p^(k-1):ℕ):ℤ)+((n*p^(k-1):ℕ):ℤ)) := by
    push_cast
    ring
  rw [hSid] at hdiff
  -- divisibility hypotheses for C2
  have hNdvd : p^(k-1) ∣ n * p^(k-1) := dvd_mul_left _ _
  have hS : (p:ℤ)^(k-1) ∣ m*((n*p^(k-1):ℕ):ℤ)+((n*p^(k-1):ℕ):ℤ) := by
    have hdvd : (p:ℤ)^(k-1) ∣ ((n*p^(k-1):ℕ):ℤ) := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr hNdvd
    exact dvd_add (Dvd.dvd.mul_left hdvd m) hdvd
  have hC2 := C2 hp hp5 hS hNdvd hN2
  rw [← hdiff, show 3*(1+(k-1)) = 3*k from by omega] at hC2
  -- convert divisibility into the congruence
  have hfin : ((p:ℤ) ^ (3*k)) ∣ a_gen m (n*p^(k-1)) - a_gen m (p*(n*p^(k-1))) := by
    rw [show a_gen m (n*p^(k-1)) - a_gen m (p*(n*p^(k-1)))
        = -(a_gen m (p*(n*p^(k-1))) - a_gen m (n*p^(k-1))) from by ring]
    exact dvd_neg.mpr hC2
  exact Int.modEq_iff_dvd.mpr hfin
