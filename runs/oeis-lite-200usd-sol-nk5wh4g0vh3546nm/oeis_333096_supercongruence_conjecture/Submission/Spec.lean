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

-- Development component: Generic.lean
open Nat Finset BigOperators Int

private def fallInt (X : ℕ) (d : ℕ) : ℤ :=
  ∏ i ∈ Finset.range d, ((X : ℤ) - i)

private lemma fallInt_eq (X d : ℕ) :
    fallInt X d = (d.factorial : ℤ) * (X.choose d : ℤ) := by
  rw [fallInt, ← Ring.choose_natCast (R := ℤ), ← nsmul_eq_mul,
    ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.eval_eq_smeval]
  exact (descPochhammer_eval_eq_prod_range d (X : ℤ)).symm

private lemma fallInt_succ (X d : ℕ) :
    fallInt X (d + 1) = (X : ℤ) * ∏ i ∈ Finset.range d, ((X : ℤ) - (i + 1 : ℕ)) := by
  simp only [fallInt, Finset.prod_range_succ', Nat.cast_zero, sub_zero]
  ring


private lemma fallInt_tail_modEq (X Y d : ℕ) :
    (∏ i ∈ Finset.range d, ((X : ℤ) - (i + 1 : ℕ))) ≡
      (∏ i ∈ Finset.range d, ((Y : ℤ) - (i + 1 : ℕ))) [ZMOD ((Y : ℤ) - X)] := by
  apply Int.ModEq.prod
  intro i hi
  apply Int.ModEq.sub
  · exact Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  · rfl

private lemma factorial_choose_det_factor (X Y d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ∃ z : ℤ,
      (d.factorial : ℤ) * e.factorial *
          ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) =
        (X : ℤ) * Y * ((Y : ℤ) - X) * z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  let UX : ℤ := ∏ i ∈ Finset.range d, ((X : ℤ) - (i + 1 : ℕ))
  let UY : ℤ := ∏ i ∈ Finset.range d, ((Y : ℤ) - (i + 1 : ℕ))
  let VX : ℤ := ∏ i ∈ Finset.range e, ((X : ℤ) - (i + 1 : ℕ))
  let VY : ℤ := ∏ i ∈ Finset.range e, ((Y : ℤ) - (i + 1 : ℕ))
  have hU : UX ≡ UY [ZMOD ((Y : ℤ) - X)] := fallInt_tail_modEq X Y d
  have hV : VX ≡ VY [ZMOD ((Y : ℤ) - X)] := fallInt_tail_modEq X Y e
  have hdiv : ((Y : ℤ) - X) ∣ UX * VY - VX * UY := by
    have h := hV.mul hU.symm
    rw [Int.modEq_iff_dvd] at h
    simpa [mul_comm] using h
  obtain ⟨z, hz⟩ := hdiv
  use z
  rw [show ((d + 1).factorial : ℤ) * (e + 1).factorial *
      ((X.choose (d + 1) : ℤ) * Y.choose (e + 1) -
       X.choose (e + 1) * Y.choose (d + 1)) =
      (((d + 1).factorial : ℤ) * X.choose (d + 1)) *
        (((e + 1).factorial : ℤ) * Y.choose (e + 1)) -
      (((e + 1).factorial : ℤ) * X.choose (e + 1)) *
        (((d + 1).factorial : ℤ) * Y.choose (d + 1)) by ring]
  rw [← fallInt_eq, ← fallInt_eq, ← fallInt_eq, ← fallInt_eq,
    fallInt_succ, fallInt_succ, fallInt_succ, fallInt_succ]
  dsimp [UX, UY, VX, VY] at hz ⊢
  linear_combination (X : ℤ) * Y * hz

private lemma factorial_vals_add_three_le {p d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) :
    padicValNat p d.factorial + padicValNat p e.factorial + 3 ≤ d + e := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpd := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.ne_of_gt hd)
  have hpe := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.ne_of_gt he)
  have hp4 : 4 ≤ p - 1 := by omega
  have hd4 : 4 * padicValNat p d.factorial < d :=
    (Nat.mul_le_mul_right (padicValNat p d.factorial) hp4).trans_lt hpd
  have he4 : 4 * padicValNat p e.factorial < e :=
    (Nat.mul_le_mul_right (padicValNat p e.factorial) hp4).trans_lt hpe
  rcases lt_or_gt_of_ne hne with hde | hed <;> omega

lemma factorial_choose_det_level_dvd {p lev X Y d e : ℕ}
    (hX : p ^ lev ∣ X) (hY : p ^ lev ∣ Y) (hd : 0 < d) (he : 0 < e) :
    ((p : ℤ) ^ (3 * lev)) ∣
      (d.factorial : ℤ) * e.factorial *
        ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) := by
  obtain ⟨z, hz⟩ := factorial_choose_det_factor X Y d e hd he
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  have hxyz : ((p : ℤ) ^ (3 * lev)) ∣ (X : ℤ) * Y * ((Y : ℤ) - X) := by
    use (x : ℤ) * y * ((y : ℤ) - x)
    push_cast at hx hy ⊢
    rw [hx, hy]
    push_cast
    ring
  rw [hz]
  exact dvd_mul_of_dvd_left hxyz z


lemma factorial_choose_det_of_product_dvd {p L X Y d e : ℕ}
    (hprod : ((p : ℤ)^L) ∣ (X : ℤ) * Y * ((Y : ℤ)-X))
    (hd : 0 < d) (he : 0 < e) :
    ((p : ℤ)^L) ∣ (d.factorial : ℤ) * e.factorial *
      ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) := by
  obtain ⟨z,hz⟩ := factorial_choose_det_factor X Y d e hd he
  rw [hz]
  exact dvd_mul_of_dvd_left hprod z


lemma paired_choose_term_dvd {p lev X Y d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : p ^ lev ∣ X) (hY : p ^ lev ∣ Y) (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) :
    ((p : ℤ) ^ (3 * (lev + 1))) ∣
      (p : ℤ) ^ (d + e) *
        ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) := by
  letI : Fact p.Prime := ⟨hp⟩
  let det : ℤ := (X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d
  by_cases hdet : det = 0
  · simp [det, hdet]
  have hfac := factorial_choose_det_factor X Y d e hd he
  obtain ⟨z, hz⟩ := hfac
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  have hxyz : ((p : ℤ) ^ (3 * lev)) ∣ (X : ℤ) * Y * ((Y : ℤ) - X) := by
    use (x : ℤ) * y * ((y : ℤ) - x)
    push_cast at hx hy ⊢
    rw [hx, hy]
    push_cast
    ring
  have hprod : ((p : ℤ) ^ (3 * lev)) ∣
      (d.factorial : ℤ) * e.factorial * det := by
    rw [hz]
    exact dvd_mul_of_dvd_left hxyz z
  have hvalprod : 3 * lev ≤ padicValInt p ((d.factorial : ℤ) * e.factorial * det) :=
    (padicValInt_dvd_iff (3 * lev) _).mp hprod |>.resolve_left (by
      exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) hdet)
  have hvalsplit : padicValInt p ((d.factorial : ℤ) * e.factorial * det) =
      padicValNat p d.factorial + padicValNat p e.factorial + padicValInt p det := by
    rw [padicValInt.mul (mul_ne_zero (by positivity) (by positivity)) hdet,
      padicValInt.mul (by positivity) (by positivity), padicValInt.of_nat, padicValInt.of_nat]
  have hvfac := factorial_vals_add_three_le hp hp5 hd he hne
  have hgoalval : 3 * (lev + 1) ≤
      padicValInt p ((p : ℤ) ^ (d + e) * det) := by
    rw [padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hdet]
    change padicValNat p (p ^ (d + e)) + padicValInt p det ≥ 3 * (lev + 1)
    rw [padicValNat.prime_pow]
    rw [hvalsplit] at hvalprod
    omega
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr hgoalval)

-- Development component: CorePositive.lean
open Nat Finset BigOperators Int Polynomial

namespace Core

abbrev ZPoly := Polynomial ℤ

noncomputable def cyclo3 : ZPoly := X ^ 2 + X + 1

def PMod (a b : ZPoly) : Prop := cyclo3 ∣ a - b

lemma pmod_refl (a : ZPoly) : PMod a a := by simp [PMod]
lemma pmod_symm {a b : ZPoly} (h : PMod a b) : PMod b a := by
  obtain ⟨q, hq⟩ := h
  use -q
  dsimp [PMod] at hq ⊢
  linear_combination -hq

lemma pmod_neg {a b : ZPoly} (h : PMod a b) : PMod (-a) (-b) := by
  obtain ⟨q, hq⟩ := h
  use -q
  dsimp [PMod] at hq ⊢
  linear_combination -hq
lemma pmod_trans {a b c : ZPoly} (h₁ : PMod a b) (h₂ : PMod b c) : PMod a c := by
  rw [PMod] at *
  convert dvd_add h₁ h₂ using 1 <;> ring
lemma pmod_add {a b c d : ZPoly} (h₁ : PMod a b) (h₂ : PMod c d) : PMod (a+c) (b+d) := by
  rw [PMod] at *
  convert dvd_add h₁ h₂ using 1 <;> ring
lemma pmod_mul {a b c d : ZPoly} (h₁ : PMod a b) (h₂ : PMod c d) : PMod (a*c) (b*d) := by
  rw [PMod] at *
  have h := dvd_add (dvd_mul_of_dvd_right h₁ c) (dvd_mul_of_dvd_left h₂ b)
  convert h using 1 <;> ring
lemma pmod_pow {a b : ZPoly} (h : PMod a b) (n : ℕ) : PMod (a^n) (b^n) := by
  induction n with
  | zero => exact pmod_refl _
  | succ n ih => simpa [pow_succ] using pmod_mul ih h

lemma one_add_X_pmod : PMod (1 + X) (-X^2) := by
  use 1
  dsimp [PMod, cyclo3]
  ring

lemma X_cube_pmod : PMod (X^3) 1 := by
  use X - 1
  dsimp [PMod, cyclo3]
  ring

lemma X_pow_pmod_mod3 (n : ℕ) : PMod (X^n) (X^(n%3)) := by
  have h := pmod_pow X_cube_pmod (n / 3)
  have hn : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm.trans (by omega)
  have hm := pmod_mul h (pmod_refl (X^(n%3)))
  convert hm using 1
  · rw [← pow_mul, ← pow_add, ← hn]
  · simp only [one_pow, one_mul]

lemma prime_mod_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : p % 3 = 1 ∨ p % 3 = 2 := by
  have hlt := Nat.mod_lt p (by omega : 0 < 3)
  have hn0 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.dvd_prime hp).mp hd
    omega
  omega

lemma frob_numerator_dvd_cyclo3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    cyclo3 ∣ (1 + X)^p - (1 + X^p) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpow := pmod_pow one_add_X_pmod p
  have hneg : (-X^2 : ZPoly)^p = -(X^(2*p)) := by
    obtain ⟨t, rfl⟩ := hodd
    simp [pow_succ, pow_mul]
  rw [hneg] at hpow
  rcases prime_mod_three hp hp5 with hpmod | hpmod
  · have hx := X_pow_pmod_mod3 (2*p)
    have h2 : (2*p)%3 = 2 := by omega
    rw [h2] at hx
    norm_num at hx
    have hx' := X_pow_pmod_mod3 p
    rw [hpmod] at hx'
    norm_num at hx'
    have hleft : PMod ((1+X)^p) (-X^2) :=
      pmod_trans hpow (pmod_neg hx)
    have hrhs : PMod (1 + X^p) (-X^2) :=
      pmod_trans (pmod_add (pmod_refl 1) hx') one_add_X_pmod
    exact pmod_trans hleft (pmod_symm hrhs)
  · have hx := X_pow_pmod_mod3 (2*p)
    have h2 : (2*p)%3 = 1 := by omega
    rw [h2] at hx
    norm_num at hx
    have hx' := X_pow_pmod_mod3 p
    rw [hpmod] at hx'
    norm_num at hx'
    have hone : PMod (1 + X^2) (-X) := by
      use 1
      dsimp [PMod, cyclo3]
      ring
    have hrhs : PMod (1 + X^p) (-X) :=
      pmod_trans (pmod_add (pmod_refl 1) hx') hone
    have hleft : PMod ((1+X)^p) (-X) :=
      pmod_trans hpow (pmod_neg hx)
    exact pmod_trans hleft (pmod_symm hrhs)


noncomputable def frobError (p : ℕ) : ZPoly :=
  ∑ i ∈ Finset.Ioo 0 p, C ((p.choose i / p : ℕ) : ℤ) * X ^ i

lemma coeff_frobError (p n : ℕ) :
    (frobError p).coeff n =
      if 0 < n ∧ n < p then ((p.choose n / p : ℕ) : ℤ) else 0 := by
  classical
  simp [frobError]

lemma frob_decomposition {p : ℕ} (hp : p.Prime) :
    (1 + X : ZPoly)^p = 1 + X^p + C (p : ℤ) * frobError p := by
  ext n
  rw [coeff_one_add_X_pow]
  rw [coeff_add, coeff_add, coeff_one, coeff_X_pow, coeff_C_mul, coeff_frobError]
  by_cases hn0 : n = 0
  · subst n; simp [hp.ne_zero, Ne.symm hp.ne_zero]
  by_cases hnp : n = p
  · subst n; simp [hp.ne_zero, Ne.symm hp.ne_zero]
  by_cases hlt : n < p
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hd : p ∣ p.choose n := hp.dvd_choose_self hn0 hlt
    simp only [hnpos, hlt, and_self, if_true, hn0, hnp, if_false, zero_add,
      Int.natCast_ediv]
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  · have hpn : p < n := by omega
    have hchoose : p.choose n = 0 := Nat.choose_eq_zero_of_lt hpn
    simp [hchoose, hn0, hnp, hlt]

lemma frobError_dvd_cyclo3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    cyclo3 ∣ frobError p := by
  have hmonic : cyclo3.Monic := by
    dsimp [cyclo3]
    monicity <;> norm_num
  have hnum := frob_numerator_dvd_cyclo3 hp hp5
  have heq : (1 + X : ZPoly)^p - (1 + X^p) = C (p : ℤ) * frobError p := by
    rw [frob_decomposition hp]
    ring
  rw [heq] at hnum
  have hrem : (p : ℤ) • (frobError p %ₘ cyclo3) = 0 := by
    rw [← Polynomial.smul_modByMonic]
    rw [← C_mul']
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hnum
  have hrem0 : frobError p %ₘ cyclo3 = 0 := by
    ext n
    have hn := congr_arg (fun f : ZPoly => f.coeff n) hrem
    simp only [coeff_smul, coeff_zero] at hn ⊢
    exact (mul_eq_zero.mp hn).resolve_left (by exact_mod_cast hp.ne_zero)
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mp hrem0


def qCoeff (n : ℕ) : ℤ :=
  if n = 0 then 1 else if 3 ∣ n then 2 else -1

noncomputable def Qseries : PowerSeries ℤ := PowerSeries.mk qCoeff

lemma qCoeff_mul_prime {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    qCoeff (p * n) = qCoeff n := by
  by_cases hn : n = 0
  · subst n; simp [qCoeff]
  have hp0 : p ≠ 0 := hp.ne_zero
  simp only [qCoeff, mul_eq_zero, hp0, hn, or_self, if_false]
  have hp3 : ¬3 ∣ p := by
    intro h
    have := (Nat.dvd_prime hp).mp h
    omega
  simp [Nat.prime_three.dvd_mul, hp3]

lemma qCoeff_recurrence (n : ℕ) :
    qCoeff n + (if 1 ≤ n then qCoeff (n-1) else 0) +
      (if 2 ≤ n then qCoeff (n-2) else 0) =
      if n = 0 then 1 else if n = 2 then -1 else 0 := by
  by_cases h0 : n = 0
  · subst n; norm_num [qCoeff]
  by_cases h1 : n = 1
  · subst n; norm_num [qCoeff]
  by_cases h2 : n = 2
  · subst n; norm_num [qCoeff]
  have hn3 : 3 ≤ n := by omega
  have hm : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have := Nat.mod_lt n (by omega : 0 < 3)
    omega
  rcases hm with hm | hm | hm <;>
    simp [qCoeff, h0, h2, hn3, show 1 ≤ n by omega,
      Nat.dvd_iff_mod_eq_zero, hm] <;> omega

lemma cyclo3_mul_Qseries :
    (cyclo3 : PowerSeries ℤ) * Qseries = 1 - PowerSeries.X^2 := by
  ext n
  rw [show (cyclo3 : PowerSeries ℤ) =
    (PowerSeries.X^2 + PowerSeries.X + 1) by simp [cyclo3]]

  change PowerSeries.coeff n
      ((PowerSeries.X^2 + PowerSeries.X + 1) * Qseries) = _
  rw [add_mul, add_mul]
  have hx : PowerSeries.coeff n (PowerSeries.X * Qseries) =
      if 1 ≤ n then qCoeff (n-1) else 0 := by
    simpa only [pow_one, Qseries, PowerSeries.coeff_mk] using
      PowerSeries.coeff_X_pow_mul' Qseries 1 n
  have hx2 : PowerSeries.coeff n (PowerSeries.X^2 * Qseries) =
      if 2 ≤ n then qCoeff (n-2) else 0 := by
    simpa only [Qseries, PowerSeries.coeff_mk] using
      PowerSeries.coeff_X_pow_mul' Qseries 2 n
  rw [map_add, map_add, hx2, hx]
  simp only [one_mul, Qseries, PowerSeries.coeff_mk, map_sub, map_one,
    PowerSeries.coeff_X_pow]
  rw [show ((if 2 ≤ n then qCoeff (n-2) else 0) +
      (if 1 ≤ n then qCoeff (n-1) else 0)) + qCoeff n =
      qCoeff n + (if 1 ≤ n then qCoeff (n-1) else 0) +
        (if 2 ≤ n then qCoeff (n-2) else 0) by ring]
  rw [qCoeff_recurrence]
  split_ifs <;> norm_num <;> omega


noncomputable def frobQuot (p : ℕ) : ZPoly := frobError p /ₘ cyclo3

lemma frobError_eq_mul_quot' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    frobError p = cyclo3 * frobQuot p := by
  have hmonic : cyclo3.Monic := by
    dsimp [cyclo3]; monicity <;> norm_num
  calc
    frobError p = frobError p %ₘ cyclo3 + cyclo3 * (frobError p /ₘ cyclo3) :=
      (Polynomial.modByMonic_add_div (frobError p) hmonic).symm
    _ = cyclo3 * frobQuot p := by
      rw [(Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr
        (frobError_dvd_cyclo3 hp hp5), zero_add]
      rfl

lemma natDegree_frobError_le (p : ℕ) : (frobError p).natDegree ≤ p - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_frobError]
  simp only [ite_eq_right_iff]
  intro h
  omega

private lemma natDegree_cyclo3 : cyclo3.natDegree = 2 := by
  dsimp [cyclo3]
  compute_degree <;> norm_num

private lemma natDegree_frobQuot_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (frobQuot p).natDegree ≤ p - 3 := by
  have heq := frobError_eq_mul_quot' hp hp5
  have hq0 : frobQuot p ≠ 0 := by
    intro h
    rw [h, mul_zero] at heq
    have hc := congr_arg (fun f : ZPoly => f.coeff 1) heq
    change (frobError p).coeff 1 = 0 at hc
    rw [coeff_frobError] at hc
    norm_num [hp.one_lt, hp.ne_zero] at hc
  have hmonic : cyclo3.Monic := by
    dsimp [cyclo3]; monicity <;> norm_num
  have hdeg := Polynomial.natDegree_mul hmonic.ne_zero hq0
  rw [natDegree_cyclo3] at hdeg
  have hle := natDegree_frobError_le p
  rw [heq, hdeg] at hle
  omega

noncomputable def errorPoly (p j : ℕ) : ZPoly :=
  if j = 0 then 0 else
    (1 - X^2) * cyclo3^(j-1) * frobQuot p ^ j

lemma Qseries_mul_frobError_pow {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) :
    Qseries * (frobError p : PowerSeries ℤ) ^ j =
      (errorPoly p j : PowerSeries ℤ) := by
  rw [frobError_eq_mul_quot' hp hp5, Polynomial.coe_mul]
  rw [errorPoly, if_neg (Nat.ne_of_gt hj), Polynomial.coe_mul, Polynomial.coe_mul]
  simp only [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_X]
  have hj_eq : j = (j-1)+1 := by omega
  conv_lhs =>
    enter [2]
    rw [hj_eq, pow_succ]
  have h := cyclo3_mul_Qseries
  change (cyclo3 : PowerSeries ℤ) * Qseries = 1 - PowerSeries.X^2 at h
  rw [← h]
  have hR : (frobQuot p : PowerSeries ℤ)^j =
      (frobQuot p : PowerSeries ℤ)^(j-1) * (frobQuot p : PowerSeries ℤ) := by
    conv_lhs => rw [hj_eq, pow_succ]
  rw [hR]
  ring


lemma reflect_frobError {p : ℕ} : Polynomial.reflect p (frobError p) = frobError p := by
  ext n
  change (Polynomial.reflect p (frobError p)).coeff n = (frobError p).coeff n

  rw [Polynomial.coeff_reflect]
  by_cases hnp : n ≤ p
  · rw [Polynomial.revAt_le hnp, coeff_frobError, coeff_frobError]
    by_cases hn0 : n = 0
    · subst n; simp
    by_cases hne : n = p
    · subst n; simp
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnlt : n < p := lt_of_le_of_ne hnp hne
    have hsubpos : 0 < p - n := Nat.sub_pos_of_lt hnlt
    have hsublt : p - n < p := Nat.sub_lt (by omega) hnpos
    simp only [hnpos, hnlt, hsubpos, hsublt, and_self, if_true]
    rw [Nat.choose_symm hnp]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hnp)]

private lemma reflect_cyclo3 : Polynomial.reflect 2 cyclo3 = cyclo3 := by
  ext n
  rw [Polynomial.coeff_reflect]
  by_cases hn : n ≤ 2
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;> norm_num [cyclo3, Polynomial.coeff_X, Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]

private lemma reflect_pow_eq {f : ZPoly} {N : ℕ} (hdeg : f.natDegree ≤ N)
    (href : Polynomial.reflect N f = f) (j : ℕ) :
    Polynomial.reflect (N*j) (f^j) = f^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Nat.mul_succ, Polynomial.reflect_mul (f^j) f]
      · rw [ih, href]
      · simpa [Nat.mul_comm] using
          Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hdeg)
      · exact hdeg

lemma reflect_frobQuot {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Polynomial.reflect (p-2) (frobQuot p) = frobQuot p := by
  have heq := frobError_eq_mul_quot' hp hp5
  have hdD : cyclo3.natDegree ≤ 2 := natDegree_cyclo3.le
  have hdR : (frobQuot p).natDegree ≤ p-2 :=
    (natDegree_frobQuot_le hp hp5).trans (by omega)
  have hprod := Polynomial.reflect_mul cyclo3 (frobQuot p) hdD hdR
  have hp2 : 2 + (p-2) = p := by omega
  rw [hp2, ← heq, reflect_frobError, reflect_cyclo3] at hprod
  apply (mul_left_cancel₀ (show cyclo3 ≠ 0 by
    have hm : cyclo3.Monic := by dsimp [cyclo3]; monicity <;> norm_num
    exact hm.ne_zero))
  calc
    cyclo3 * Polynomial.reflect (p-2) (frobQuot p) = frobError p := hprod.symm
    _ = cyclo3 * frobQuot p := heq

private lemma reflect_one_sub_X_sq :
    Polynomial.reflect 2 (1 - X^2 : ZPoly) = -(1-X^2) := by
  ext n
  simp [Polynomial.coeff_reflect, Polynomial.revAt]

lemma reflect_errorPoly {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) :
    Polynomial.reflect (p*j) (errorPoly p j) = - errorPoly p j := by
  rw [errorPoly, if_neg (Nat.ne_of_gt hj)]
  have hDdeg : cyclo3.natDegree ≤ 2 := natDegree_cyclo3.le
  have hRdeg : (frobQuot p).natDegree ≤ p-2 :=
    (natDegree_frobQuot_le hp hp5).trans (by omega)
  have hDpow := reflect_pow_eq hDdeg reflect_cyclo3 (j-1)
  have hRpow := reflect_pow_eq hRdeg (reflect_frobQuot hp hp5) j
  have hAdeg : (1-X^2 : ZPoly).natDegree ≤ 2 := by compute_degree <;> norm_num
  have hBDeg : (cyclo3^(j-1)).natDegree ≤ 2*(j-1) := by
    have := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (j-1) hDdeg)
    omega
  have hCDeg : (frobQuot p ^ j).natDegree ≤ (p-2)*j := by
    simpa [Nat.mul_comm] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hRdeg)
  have hmul1 := Polynomial.reflect_mul (1-X^2 : ZPoly) (cyclo3^(j-1)) hAdeg hBDeg
  have hmul2 := Polynomial.reflect_mul ((1-X^2 : ZPoly)*cyclo3^(j-1))
    (frobQuot p ^ j) (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hAdeg hBDeg)) hCDeg
  have htwo : 2 + 2 * (j - 1) = 2 * j := by omega
  have hpback : 2 + (p - 2) = p := by omega
  have hidx : 2 + 2*(j-1) + (p-2)*j = p*j := by
    rw [htwo, ← Nat.add_mul, hpback]
  rw [hidx] at hmul2
  rw [hmul1, reflect_one_sub_X_sq, hDpow, hRpow] at hmul2
  convert hmul2 using 1 <;> ring

lemma coeff_errorPoly_antisymm {p j d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) (hd : d ≤ j) :
    (errorPoly p j).coeff (p*(j-d)) = -(errorPoly p j).coeff (p*d) := by
  have h := congr_arg (fun f : ZPoly => f.coeff (p*d)) (reflect_errorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (errorPoly p j)).coeff (p*d) =
    (-errorPoly p j).coeff (p*d) at h

  rw [Polynomial.coeff_reflect] at h
  have hle : p*d ≤ p*j := Nat.mul_le_mul_left p hd
  rw [Polynomial.revAt_le hle, coeff_neg] at h
  rw [Nat.mul_sub_left_distrib]
  exact h





end Core

-- Development component: Shifted.lean
open Nat Finset BigOperators Int

def chooseSub (N B d : ℕ) : ℕ :=
  if d ≤ B then N.choose (B-d) else 0

private lemma factorial_choose_shift (B Y d e : ℕ) (hjA : d+e ≤ B+Y) :
    (d+e).factorial * (B+Y).choose (d+e) * chooseSub (B+Y-(d+e)) B d =
      (B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e := by
  by_cases hdB : d ≤ B
  · rw [chooseSub, if_pos hdB]
    by_cases heY : e ≤ Y
    · have harg : B-d ≤ B+Y-(d+e) := by omega
      have hrem : B+Y-(d+e)-(B-d) = Y-e := by omega
      have hArem : B+Y-(d+e) + (d+e) = B+Y := by omega
      have hBrem : B-d+d=B := by omega
      have hYrem : Y-e+e=Y := by omega
      apply Nat.mul_right_cancel (by positivity : 0 < (B-d).factorial * (Y-e).factorial)
      have h1 := Nat.choose_mul_factorial_mul_factorial hjA
      have h2 := Nat.choose_mul_factorial_mul_factorial harg
      have h3 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right B Y)
      have h4 := Nat.choose_mul_factorial_mul_factorial hdB
      have h5 := Nat.choose_mul_factorial_mul_factorial heY
      rw [hrem] at h2
      rw [show B+Y-B=Y by omega] at h3
      calc
        ((d+e).factorial * (B+Y).choose (d+e) *
            (B+Y-(d+e)).choose (B-d)) * ((B-d).factorial * (Y-e).factorial)
            = (B+Y).choose (d+e) * (d+e).factorial *
                ((B+Y-(d+e)).choose (B-d) * (B-d).factorial * (Y-e).factorial) := by ring
        _ = (B+Y).choose (d+e) * (d+e).factorial * (B+Y-(d+e)).factorial := by rw [h2]
        _ = (B+Y).factorial := h1
        _ = (B+Y).choose B * B.factorial * Y.factorial := h3.symm
        _ = (B+Y).choose B *
              (B.choose d * d.factorial * (B-d).factorial) *
              (Y.choose e * e.factorial * (Y-e).factorial) := by rw [h4, h5]
        _ = ((B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e) *
              ((B-d).factorial * (Y-e).factorial) := by ring
    · have hlt : B+Y-(d+e) < B-d := by omega
      have hYe : Y.choose e = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [Nat.choose_eq_zero_of_lt hlt, hYe]
      simp
  · rw [chooseSub, if_neg hdB, Nat.choose_eq_zero_of_lt (by omega : B < d)]
    simp

private lemma factorial_val_add_three_le {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) (hj : j = d+e) :
    padicValNat p j.factorial + 3 ≤ j := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p
    (show j ≠ 0 by omega)
  have hp4 : 4 ≤ p-1 := by omega
  have hv4 : 4 * padicValNat p j.factorial < j :=
    (Nat.mul_le_mul_right (padicValNat p j.factorial) hp4).trans_lt hv
  omega

lemma paired_shifted_choose_term_dvd
    {p lev B Y d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y)
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (hjA : d+e ≤ B+Y) :
    ((p : ℤ)^(3*(lev+1))) ∣
      (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) := by
  letI : Fact p.Prime := ⟨hp⟩
  let T : ℤ := ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e)
  rw [show (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) =
      (p : ℤ)^(d+e) * T by dsimp [T]; ring]

  by_cases hT : T = 0
  · change (p : ℤ)^(3*(lev+1)) ∣ (p : ℤ)^(d+e) * T
    rw [hT, mul_zero]
    exact dvd_zero _
  have hf1 := factorial_choose_shift B Y d e hjA
  have hf2 := factorial_choose_shift B Y e d (by omega)
  have hfac : ((d+e).factorial : ℤ) * T =
      ((B+Y).choose B : ℤ) * (d.factorial : ℤ) * e.factorial *
        ((B.choose d : ℤ) * Y.choose e - B.choose e * Y.choose d) := by
    dsimp [T]
    have hf1z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) =
        (((B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e : ℕ) : ℤ) := by
      exact_mod_cast hf1
    have hf2z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) =
        (((B+Y).choose B * e.factorial * d.factorial * B.choose e * Y.choose d : ℕ) : ℤ) := by
      rw [← show e+d=d+e by omega]
      exact_mod_cast hf2
    calc
      ((d+e).factorial : ℤ) *
          (((B+Y).choose (d+e) : ℤ) *
            ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e))
          = (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) -
            (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) := by push_cast; ring
      _ = _ := by rw [hf1z, hf2z]; push_cast; ring
  have hbase := factorial_choose_det_level_dvd hB hY hd he
  have hprod : ((p : ℤ)^(3*lev)) ∣ ((d+e).factorial : ℤ) * T := by
    rw [hfac]
    convert dvd_mul_of_dvd_right hbase ((B+Y).choose B : ℤ) using 1 <;> ring
  have hvalprod : 3*lev ≤ padicValInt p (((d+e).factorial : ℤ) * T) :=
    (padicValInt_dvd_iff (3*lev) _).mp hprod |>.resolve_left
      (mul_ne_zero (by positivity) hT)
  have hsplit : padicValInt p (((d+e).factorial : ℤ) * T) =
      padicValNat p (d+e).factorial + padicValInt p T := by
    rw [padicValInt.mul (by positivity) hT, padicValInt.of_nat]
  have hfacval := factorial_val_add_three_le hp hp5 hd he hne rfl
  have hgoalval : 3*(lev+1) ≤ padicValInt p ((p : ℤ)^(d+e) * T) := by
    rw [padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hT]
    change 3*(lev+1) ≤ padicValNat p (p^(d+e)) + padicValInt p T
    rw [padicValNat.prime_pow]
    rw [hsplit] at hvalprod
    omega
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr hgoalval)

lemma paired_shifted_choose_term_dvd_total
    {p L B Y d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hprod : ((p : ℤ)^L) ∣ (B : ℤ)*Y*((Y : ℤ)-B))
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (hjA : d+e ≤ B+Y) :
    ((p : ℤ)^(L+3)) ∣
      (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) := by
  letI : Fact p.Prime := ⟨hp⟩
  let T : ℤ := ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e)
  rw [show (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) =
      (p : ℤ)^(d+e) * T by dsimp [T]; ring]
  by_cases hT : T=0
  · rw [hT, mul_zero]
    exact dvd_zero _
  have hf1 := factorial_choose_shift B Y d e hjA
  have hf2 := factorial_choose_shift B Y e d (by omega)
  have hfac : ((d+e).factorial : ℤ) * T =
      ((B+Y).choose B : ℤ) * (d.factorial : ℤ) * e.factorial *
        ((B.choose d : ℤ) * Y.choose e - B.choose e * Y.choose d) := by
    dsimp [T]
    have hf1z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) =
        (((B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e : ℕ) : ℤ) := by
      exact_mod_cast hf1
    have hf2z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) =
        (((B+Y).choose B * e.factorial * d.factorial * B.choose e * Y.choose d : ℕ) : ℤ) := by
      rw [← show e+d=d+e by omega]
      exact_mod_cast hf2
    calc
      ((d+e).factorial : ℤ) *
          (((B+Y).choose (d+e) : ℤ) *
            ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e))
          = (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) -
            (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) := by push_cast; ring
      _ = _ := by rw [hf1z,hf2z]; push_cast; ring
  have hbase := factorial_choose_det_of_product_dvd hprod hd he
  have hwhole : ((p : ℤ)^L) ∣ ((d+e).factorial : ℤ)*T := by
    rw [hfac]
    convert dvd_mul_of_dvd_right hbase ((B+Y).choose B : ℤ) using 1 <;> ring
  have hval : L ≤ padicValInt p (((d+e).factorial : ℤ)*T) :=
    (padicValInt_dvd_iff L _).mp hwhole |>.resolve_left
      (mul_ne_zero (by positivity) hT)
  have hsplit : padicValInt p (((d+e).factorial : ℤ)*T) =
      padicValNat p (d+e).factorial + padicValInt p T := by
    rw [padicValInt.mul (by positivity) hT, padicValInt.of_nat]
  have hvfac := factorial_val_add_three_le hp hp5 hd he hne rfl
  have hgoal : L+3 ≤ padicValInt p ((p : ℤ)^(d+e)*T) := by
    rw [padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hT]
    change L+3 ≤ padicValNat p (p^(d+e)) + padicValInt p T
    rw [padicValNat.prime_pow]
    rw [hsplit] at hval
    omega
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr hgoal)

-- Development component: PairShift.lean
open Nat Finset BigOperators Int

lemma shifted_paired_sum_dvd
    {p lev B Y j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y) (hjA : j ≤ B+Y)
    (c : ℕ → ℤ) (hc0 : c 0 = 0)
    (hanti : ∀ d, d ≤ j → c (j-d) = -c d) :
    ((p : ℤ)^(3*(lev+1))) ∣
      ∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
          (chooseSub (B+Y-j) B d : ℤ) := by
  let M : ℕ := p^(3*(lev+1))
  let f : ℕ → ZMod M := fun d =>
    (((p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
      (chooseSub (B+Y-j) B d : ℤ) : ℤ) : ZMod M)
  have hsum : ∑ d ∈ Finset.range (j+1), f d = 0 := by
    apply Finset.sum_involution (fun d _ => j-d)
    · intro d hdmem
      have hdj : d ≤ j := by simpa [Finset.mem_range] using hdmem
      let e := j-d
      have hej : e ≤ j := Nat.sub_le _ _
      by_cases hd0 : d = 0
      · subst d
        have hcj : c j = 0 := by
          have ha := hanti 0 (Nat.zero_le j)
          simpa [hc0] using ha
        simp [f, hc0, hcj]
      by_cases he0 : e = 0
      · have hce : c e = 0 := by simpa [he0] using hc0
        have hcd : c d = 0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl, hce] at ha
          omega
        simp [f, hcd, hce, e]
      by_cases hde : d = e
      · have hcd : c d = 0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl, ← hde] at ha
          omega
        have hflip : j-d=d := by simpa [e] using hde.symm
        simp [f, hcd, hflip]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hepos : 0 < e := Nat.pos_of_ne_zero he0
        have hsumde : d+e=j := by dsimp [e]; omega
        have hdiv := paired_shifted_choose_term_dvd hp hp5 hB hY hdpos hepos hde
          (show d+e ≤ B+Y by omega)
        rw [hsumde] at hdiv
        have hdiv' : ((p : ℤ)^(3*(lev+1))) ∣
            c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ) - chooseSub (B+Y-j) B e)) := by
          convert dvd_mul_of_dvd_right hdiv (c d) using 1 <;> ring
        have hz : ((c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ) - chooseSub (B+Y-j) B e)) : ℤ) : ZMod M) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          simpa [M] using hdiv'
        have ha := hanti d hdj
        change f d + f e = 0
        dsimp [f]
        rw [ha]
        rw [← Int.cast_add]
        convert hz using 1 <;> ring
    · intro d hdmem hfd
      have hdj : d ≤ j := by simpa [Finset.mem_range] using hdmem
      intro heq
      have hc : c d = 0 := by
        have ha := hanti d hdj
        rw [heq] at ha
        omega
      simp [f, hc] at hfd
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
  have hz : (((∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
          (chooseSub (B+Y-j) B d : ℤ)) : ℤ) : ZMod M) = 0 := by
    simpa [f] using hsum
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  simpa [M] using hz


lemma shifted_paired_sum_dvd_total
    {p L B Y j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hprod : ((p : ℤ)^L) ∣ (B : ℤ)*Y*((Y : ℤ)-B)) (hjA : j ≤ B+Y)
    (c : ℕ → ℤ) (hc0 : c 0 = 0)
    (hanti : ∀ d, d ≤ j → c (j-d) = -c d) :
    ((p : ℤ)^(L+3)) ∣
      ∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
          (chooseSub (B+Y-j) B d : ℤ) := by
  let M : ℕ := p^(L+3)
  let f : ℕ → ZMod M := fun d =>
    (((p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
      (chooseSub (B+Y-j) B d : ℤ) : ℤ) : ZMod M)
  have hsum : ∑ d ∈ Finset.range (j+1), f d = 0 := by
    apply Finset.sum_involution (fun d _ => j-d)
    · intro d hdmem
      have hdj : d ≤ j := by simpa [Finset.mem_range] using hdmem
      let e := j-d
      by_cases hd0 : d=0
      · subst d
        have hcj : c j=0 := by
          have ha := hanti 0 (Nat.zero_le j)
          simpa [hc0] using ha
        simp [f,hc0,hcj]
      by_cases he0 : e=0
      · have hce : c e=0 := by simpa [he0] using hc0
        have hcd : c d=0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl,hce] at ha
          omega
        simp [f,hcd,hce,e]
      by_cases hde : d=e
      · have hcd : c d=0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl,←hde] at ha
          omega
        have hflip : j-d=d := by simpa [e] using hde.symm
        simp [f,hcd,hflip]
      · have hdpos : 0<d := Nat.pos_of_ne_zero hd0
        have hepos : 0<e := Nat.pos_of_ne_zero he0
        have hsumde : d+e=j := by dsimp [e]; omega
        have hdiv := paired_shifted_choose_term_dvd_total hp hp5 hprod hdpos hepos hde
          (show d+e ≤ B+Y by omega)
        rw [hsumde] at hdiv
        have hdiv' : ((p : ℤ)^(L+3)) ∣
            c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ)-chooseSub (B+Y-j) B e)) := by
          convert dvd_mul_of_dvd_right hdiv (c d) using 1 <;> ring
        have hz : ((c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ)-chooseSub (B+Y-j) B e)) : ℤ) : ZMod M)=0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          simpa [M] using hdiv'
        have ha := hanti d hdj
        change f d+f e=0
        dsimp [f]
        rw [ha,←Int.cast_add]
        convert hz using 1 <;> ring
    · intro d hdmem hfd
      have hdj : d≤j := by simpa [Finset.mem_range] using hdmem
      intro heq
      have hc : c d=0 := by
        have ha := hanti d hdj
        rw [heq] at ha
        omega
      simp [f,hc] at hfd
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
  have hz : (((∑ d ∈ Finset.range (j+1),
      (p : ℤ)^j*c d*((B+Y).choose j : ℤ)*(chooseSub (B+Y-j) B d : ℤ)) : ℤ) : ZMod M)=0 := by
    simpa [f] using hsum
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  simpa [M] using hz

-- Development component: Positive.lean
open Nat Finset BigOperators Int Polynomial
open Core

lemma coeff_series_mul_expand
    (q : ℕ → ℤ) {p : ℕ} (hp : 0 < p) (hq : ∀ n, q (n*p) = q n)
    (f : Polynomial ℤ) (n : ℕ) :
    PowerSeries.coeff (n*p)
        (PowerSeries.mk q * (Polynomial.expand ℤ p f : PowerSeries ℤ)) =
      PowerSeries.coeff n (PowerSeries.mk q * (f : PowerSeries ℤ)) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.sum_subset
    (s₁ := (Finset.antidiagonal n).image fun x => (x.1*p, x.2*p)), Finset.sum_image]
  · simp_rw [PowerSeries.coeff_mk, Polynomial.coeff_coe,
      Polynomial.coeff_expand_mul hp, hq]
  · intro x hx y hy heq
    simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp] using heq
  · simp_rw [Finset.subset_iff, Finset.mem_image, Finset.mem_antidiagonal]
    rintro _ ⟨x, rfl, rfl⟩
    simp_rw [Nat.add_mul]
  · simp_rw [Finset.mem_image, Finset.mem_antidiagonal]
    intro ⟨x,y⟩ heq hnmem
    by_cases hy : p ∣ y
    · obtain ⟨x', rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left hy).mpr
          (heq ▸ dvd_mul_left p n)
      obtain ⟨y', rfl⟩ := hy
      refine (hnmem ⟨⟨x',y'⟩, (Nat.mul_right_cancel_iff hp).mp ?_, by simp_rw [mul_comm]⟩).elim
      rw [← heq, mul_comm, mul_add]
    · rw [Polynomial.coeff_coe, Polynomial.coeff_expand hp, if_neg hy, mul_zero]

noncomputable def FNat (A B : ℕ) : ℤ :=
  PowerSeries.coeff B
    (Core.Qseries * (((1 + Polynomial.X : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ))

lemma base_eq_expand (p A : ℕ) :
    (1 + Polynomial.X^p : Polynomial ℤ)^A =
      Polynomial.expand ℤ p ((1+Polynomial.X)^A) := by
  rw [map_pow]
  simp

lemma FNat_base_scale {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (A B : ℕ) :
    PowerSeries.coeff (p*B)
      (Core.Qseries * (((1+Polynomial.X^p : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ)) =
      FNat A B := by
  rw [base_eq_expand, Nat.mul_comm p B]
  change PowerSeries.coeff (B*p)
      (PowerSeries.mk Core.qCoeff *
        (Polynomial.expand ℤ p ((1+Polynomial.X : Polynomial ℤ)^A) : PowerSeries ℤ)) = _
  rw [coeff_series_mul_expand Core.qCoeff hp.pos]
  · rfl
  · intro t
    simpa [Nat.mul_comm] using Core.qCoeff_mul_prime (hp := hp) (hp5 := hp5) (n := t)

lemma frobenius_expansion {p : ℕ} (hp : p.Prime) (A : ℕ) :
    (1+Polynomial.X : Polynomial ℤ)^(p*A) =
      ∑ j ∈ Finset.range (A+1),
        Polynomial.C ((p : ℤ)^j * (A.choose j : ℤ)) * Core.frobError p ^ j *
          (1+Polynomial.X^p : Polynomial ℤ)^(A-j) := by
  rw [pow_mul, Core.frob_decomposition hp]
  rw [show (1 + Polynomial.X^p + Polynomial.C (p : ℤ) * Core.frobError p : Polynomial ℤ) =
      Polynomial.C (p : ℤ) * Core.frobError p + (1+Polynomial.X^p) by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_pow, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast]
  rw [show Polynomial.C ((p : ℤ)^j) = (p : Polynomial ℤ)^j by
    rw [map_pow]; simp]
  ring

lemma coeff_mul_one_add_pow (f : Polynomial ℤ) (N B : ℕ) :
    (f * (1+Polynomial.X)^N).coeff B =
      ∑ d ∈ Finset.range (B+1), f.coeff d * (N.choose (B-d) : ℤ) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.coeff_one_add_X_pow]

lemma sum_chooseSub_eq {f : ℕ → ℤ} {N B j : ℕ}
    (hzero : ∀ d, j < d → f d = 0) :
    (∑ d ∈ Finset.range (B+1), f d * (N.choose (B-d) : ℤ)) =
      ∑ d ∈ Finset.range (j+1), f d * (chooseSub N B d : ℤ) := by
  by_cases hjB : j ≤ B
  · symm
    calc
      (∑ d ∈ Finset.range (j+1), f d * (chooseSub N B d : ℤ)) =
          ∑ d ∈ Finset.range (j+1), f d * (N.choose (B-d) : ℤ) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdj : d ≤ j := by
              simp only [Finset.mem_range] at hd
              omega
            rw [chooseSub, if_pos (le_trans hdj hjB)]
      _ = ∑ d ∈ Finset.range (B+1), f d * (N.choose (B-d) : ℤ) := by
            apply Finset.sum_subset
            · intro d hd
              simp only [Finset.mem_range] at hd ⊢
              omega
            · intro d hdB hdj
              rw [hzero d (by simp only [Finset.mem_range] at hdB hdj; omega)]
              simp
  · have hBj : B < j := by omega
    calc
      (∑ d ∈ Finset.range (B+1), f d * (N.choose (B-d) : ℤ)) =
          ∑ d ∈ Finset.range (B+1), f d * (chooseSub N B d : ℤ) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [chooseSub, if_pos]
            simpa [Finset.mem_range] using (show d ≤ B by
              simp only [Finset.mem_range] at hd; omega)
      _ = ∑ d ∈ Finset.range (j+1), f d * (chooseSub N B d : ℤ) := by
            apply Finset.sum_subset
            · intro d hd
              simp only [Finset.mem_range] at hd ⊢
              omega
            · intro d hdj hdB
              have hnot : ¬ d ≤ B := by
                simp only [Finset.mem_range] at hdj hdB
                omega
              simp [chooseSub, hnot]

lemma errorPoly_coeff_zero {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) :
    (Core.errorPoly p j).coeff 0 = 0 := by
  have h := congr_arg (PowerSeries.coeff 0)
    (Core.Qseries_mul_frobError_pow hp hp5 hj)
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_one, Core.Qseries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  simp [Core.qCoeff, Polynomial.coeff_coe, Core.coeff_frobError, hj.ne'] at h
  exact h.symm

lemma errorPoly_coeff_above {p j d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) (hd : j < d) :
    (Core.errorPoly p j).coeff (p*d) = 0 := by
  have h := congr_arg (fun f : Polynomial ℤ => f.coeff (p*d))
    (Core.reflect_errorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (Core.errorPoly p j)).coeff (p*d) =
    (-Core.errorPoly p j).coeff (p*d) at h
  rw [Polynomial.coeff_reflect,
    Polynomial.revAt_eq_self_of_lt (show p*j < p*d by
      exact Nat.mul_lt_mul_of_pos_left hd hp.pos), Polynomial.coeff_neg] at h
  omega

lemma contracted_error_coeff_sum {p j A B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) :
    (Core.errorPoly p j * (1+Polynomial.X^p)^(A-j)).coeff (p*B) =
      ∑ d ∈ Finset.range (j+1),
        (Core.errorPoly p j).coeff (p*d) * (chooseSub (A-j) B d : ℤ) := by
  rw [base_eq_expand]
  have hc := Polynomial.contract_mul_expand hp.ne_zero (Core.errorPoly p j)
    ((1+Polynomial.X : Polynomial ℤ)^(A-j))
  have heq := congr_arg (fun f : Polynomial ℤ => f.coeff B) hc
  change (Polynomial.contract p
      (Core.errorPoly p j * Polynomial.expand ℤ p ((1+Polynomial.X)^ (A-j)))).coeff B =
    (Polynomial.contract p (Core.errorPoly p j) * (1+Polynomial.X)^(A-j)).coeff B at heq
  rw [Polynomial.coeff_contract hp.ne_zero, coeff_mul_one_add_pow] at heq
  rw [Nat.mul_comm] at heq
  rw [heq]
  have hs := sum_chooseSub_eq (N := A-j) (B := B) (j := j)
    (f := fun d => (Polynomial.contract p (Core.errorPoly p j)).coeff d) (by
      intro d hd
      change (Polynomial.contract p (Core.errorPoly p j)).coeff d = 0
      rw [Polynomial.coeff_contract hp.ne_zero]
      simpa [Nat.mul_comm] using errorPoly_coeff_above hp hp5 hj hd)
  simpa only [Polynomial.coeff_contract hp.ne_zero, Nat.mul_comm] using hs

lemma correction_coeff_eq {p A B j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) :
    PowerSeries.coeff (p*B)
      (Core.Qseries *
        ((Polynomial.C ((p : ℤ)^j * (A.choose j : ℤ)) * Core.frobError p^j *
          (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ)) =
      ∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * (Core.errorPoly p j).coeff (p*d) * (A.choose j : ℤ) *
          (chooseSub (A-j) B d : ℤ) := by
  have herr := Core.Qseries_mul_frobError_pow hp hp5 hj
  have hs : Core.Qseries *
        ((Polynomial.C ((p : ℤ)^j * (A.choose j : ℤ)) * Core.frobError p^j *
          (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) =
      PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
        ((Core.errorPoly p j * (1+Polynomial.X^p)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) := by
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C]
    calc
      Core.Qseries * (PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
          (Core.frobError p : PowerSeries ℤ)^j *
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j)) =
        PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
          (Core.Qseries * (Core.frobError p : PowerSeries ℤ)^j) *
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by ring
      _ = PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
          (Core.errorPoly p j : PowerSeries ℤ) *
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by rw [herr]
      _ = _ := by ring
  rw [hs, PowerSeries.coeff_C_mul, Polynomial.coeff_coe,
    contracted_error_coeff_sum hp hp5 hj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma correction_coeff_dvd {p lev B Y j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y) (hj : 0 < j) (hjA : j ≤ B+Y) :
    ((p : ℤ)^(3*(lev+1))) ∣
    PowerSeries.coeff (p*B)
      (Core.Qseries *
        ((Polynomial.C ((p : ℤ)^j * ((B+Y).choose j : ℤ)) * Core.frobError p^j *
          (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-j) : Polynomial ℤ) : PowerSeries ℤ)) := by
  rw [correction_coeff_eq hp hp5 hj]
  apply shifted_paired_sum_dvd hp hp5 hB hY hjA
  · exact errorPoly_coeff_zero hp hp5 hj
  · intro d hd
    exact Core.coeff_errorPoly_antisymm hp hp5 hj hd


lemma coe_finset_sum_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) :
    ((∑ i ∈ s, f i : Polynomial ℤ) : PowerSeries ℤ) =
      ∑ i ∈ s, (f i : PowerSeries ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, Polynomial.coe_add]

lemma FNat_scale_expansion {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (A B : ℕ) :
    FNat (p*A) (p*B) = FNat A B +
      ∑ i ∈ Finset.range A,
        PowerSeries.coeff (p*B)
          (Core.Qseries *
            ((Polynomial.C ((p : ℤ)^(i+1) * (A.choose (i+1) : ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^(A-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ)) := by
  unfold FNat
  rw [frobenius_expansion hp]
  rw [coe_finset_sum_poly]
  rw [Finset.mul_sum, map_sum]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, Int.natCast_one,
    mul_one, Polynomial.C_1, one_mul, Nat.sub_zero]
  rw [FNat_base_scale hp hp5]
  abel


lemma FNat_scale_supercongruence {p lev B Y : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y) :
    FNat (p*(B+Y)) (p*B) ≡ FNat (B+Y) B
      [ZMOD ((p : ℤ)^(3*(lev+1)))] := by
  rw [Int.modEq_iff_dvd]
  rw [FNat_scale_expansion hp hp5]
  -- The remaining difference is the negative of the correction sum.
  rw [show FNat (B+Y) B -
      (FNat (B+Y) B + ∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Core.Qseries *
            ((Polynomial.C ((p : ℤ)^(i+1) * ((B+Y).choose (i+1) : ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) =
      -(∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Core.Qseries *
            ((Polynomial.C ((p : ℤ)^(i+1) * ((B+Y).choose (i+1) : ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) by ring]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro i hi
  have hiA : i+1 ≤ B+Y := by
    simp only [Finset.mem_range] at hi
    omega
  exact correction_coeff_dvd hp hp5 hB hY (by omega) hiA





-- Development component: Bridge.lean
open Nat Finset BigOperators Int Polynomial
open Core

noncomputable abbrev BS (z : ℤ) : PowerSeries ℤ :=
  PowerSeries.binomialSeries ℤ z

noncomputable def U : PowerSeries ℤ := PowerSeries.X * BS (-2)

noncomputable def geomPS (N : ℕ) : PowerSeries ℤ :=
  ∑ t ∈ Finset.range (N+1), U^t

noncomputable def ballotSeries (A N : ℕ) : PowerSeries ℤ :=
  (1-PowerSeries.X) * BS ((A : ℤ)-1) * geomPS N

lemma BS_add (x y : ℤ) : BS (x+y) = BS x * BS y := by
  exact PowerSeries.binomialSeries_add x y

lemma cyclo_mul_BS_neg_two :
    (Core.cyclo3 : PowerSeries ℤ) * BS (-2) = 1-U := by
  have h : BS (-2) * BS 2 = 1 := by
    rw [← BS_add]
    norm_num [BS]
  have h2 : BS 2 = (1+PowerSeries.X)^2 := by
    simpa [BS] using (PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) 2)
  rw [h2] at h
  rw [show (Core.cyclo3 : PowerSeries ℤ) =
      (1+PowerSeries.X)^2 - PowerSeries.X by
        simp [Core.cyclo3]; ring]
  dsimp [U]
  linear_combination h

lemma cyclo_mul_ballotSeries (A N : ℕ) :
    (Core.cyclo3 : PowerSeries ℤ) * ballotSeries A N =
      (1-PowerSeries.X^2) * BS (A : ℤ) * (1-U^(N+1)) := by
  have hneg : BS ((A : ℤ)-1) = BS (-2) * BS ((A : ℤ)+1) := by
    rw [← BS_add]
    congr 1
    ring
  have hone : BS 1 = (1+PowerSeries.X) := by
    simpa [BS] using (PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) 1)
  have hsucc : BS ((A : ℤ)+1) = BS (A : ℤ) * (1+PowerSeries.X) := by
    calc
      BS ((A : ℤ)+1) = BS (A : ℤ) * BS 1 := BS_add _ _
      _ = _ := by rw [hone]
  have hgeom := geom_sum_mul_neg U (N+1)
  change geomPS N * (1-U) = 1-U^(N+1) at hgeom
  rw [ballotSeries, hneg, hsucc]
  rw [show (Core.cyclo3 : PowerSeries ℤ) *
      ((1-PowerSeries.X) * (BS (-2) * (BS (A : ℤ) * (1+PowerSeries.X))) * geomPS N) =
      (1-PowerSeries.X) * BS (A : ℤ) * (1+PowerSeries.X) *
        (((Core.cyclo3 : PowerSeries ℤ) * BS (-2)) * geomPS N) by ring]
  rw [cyclo_mul_BS_neg_two]
  rw [show (1-U) * geomPS N = 1-U^(N+1) by
    rw [mul_comm]; exact hgeom]
  ring

lemma coeff_cyclo_mul (S : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((Core.cyclo3 : PowerSeries ℤ) * S) =
      PowerSeries.coeff n S +
        (if 1 ≤ n then PowerSeries.coeff (n-1) S else 0) +
        (if 2 ≤ n then PowerSeries.coeff (n-2) S else 0) := by
  rw [show (Core.cyclo3 : PowerSeries ℤ) =
      PowerSeries.X^2 + PowerSeries.X + 1 by simp [Core.cyclo3]]
  rw [add_mul, add_mul, map_add, map_add]
  rw [PowerSeries.coeff_X_pow_mul']
  rw [show PowerSeries.X * S = PowerSeries.X^1 * S by simp,
    PowerSeries.coeff_X_pow_mul']
  simp only [one_mul]
  ring

lemma coeff_eq_of_cyclo_mul_eq {S T : PowerSeries ℤ} {N : ℕ}
    (h : ∀ n, n ≤ N →
      PowerSeries.coeff n ((Core.cyclo3 : PowerSeries ℤ)*S) =
        PowerSeries.coeff n ((Core.cyclo3 : PowerSeries ℤ)*T)) :
    ∀ n, n ≤ N → PowerSeries.coeff n S = PowerSeries.coeff n T := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have heq := h n hn
      rw [coeff_cyclo_mul, coeff_cyclo_mul] at heq
      have hi1 : (if 1 ≤ n then PowerSeries.coeff (n-1) S else 0) =
          (if 1 ≤ n then PowerSeries.coeff (n-1) T else 0) := by
        by_cases h1 : 1 ≤ n
        · simp only [if_pos h1]
          exact ih (n-1) (by omega) (by omega)
        · simp only [if_neg h1]
      have hi2 : (if 2 ≤ n then PowerSeries.coeff (n-2) S else 0) =
          (if 2 ≤ n then PowerSeries.coeff (n-2) T else 0) := by
        by_cases h2 : 2 ≤ n
        · simp only [if_pos h2]
          exact ih (n-2) (by omega) (by omega)
        · simp only [if_neg h2]
      rw [hi1, hi2] at heq
      omega

lemma coeff_remainder_zero (A N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n
      ((1-PowerSeries.X^2) * BS (A : ℤ) * U^(N+1)) = 0 := by
  rw [U, mul_pow]
  rw [show (1-PowerSeries.X^2) * BS (A : ℤ) *
      (PowerSeries.X^(N+1) * BS (-2)^(N+1)) =
      PowerSeries.X^(N+1) *
        ((1-PowerSeries.X^2) * BS (A : ℤ) * BS (-2)^(N+1)) by ring]
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

lemma ballotSeries_coeff_eq_target (A N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (ballotSeries A N) =
      PowerSeries.coeff n (Core.Qseries * BS (A : ℤ)) := by
  apply coeff_eq_of_cyclo_mul_eq
  intro d hd
  rw [cyclo_mul_ballotSeries]
  have htarget : (Core.cyclo3 : PowerSeries ℤ) *
      (Core.Qseries * BS (A : ℤ)) =
      (1-PowerSeries.X^2) * BS (A : ℤ) := by
    rw [show (Core.cyclo3 : PowerSeries ℤ) *
        (Core.Qseries * BS (A : ℤ)) =
        ((Core.cyclo3 : PowerSeries ℤ) * Core.Qseries) * BS (A : ℤ) by ring,
      Core.cyclo3_mul_Qseries]
  rw [htarget]
  rw [mul_sub, mul_one, map_sub]
  rw [coeff_remainder_zero A N d hd, sub_zero]
  exact hn

lemma BS_neg_two_pow (t : ℕ) : BS (-2)^t = BS (-(2*(t : ℤ))) := by
  induction t with
  | zero => simp [BS]
  | succ t ih =>
      rw [pow_succ, ih, ← BS_add]
      congr 1
      push_cast
      ring

noncomputable def formalCatalanCoeff (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1 else
    Ring.choose (r + 2*(k : ℤ)-1) k -
      Ring.choose (r + 2*(k : ℤ)-1) (k-1)

noncomputable def formalPartial (r : ℤ) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N+1), formalCatalanCoeff r k

lemma coeff_one_sub_X_mul_BS (z : ℤ) (k : ℕ) :
    PowerSeries.coeff k ((1-PowerSeries.X)*BS z) =
      if k=0 then 1 else Ring.choose z k - Ring.choose z (k-1) := by
  rw [sub_mul, one_mul, map_sub]
  rw [show PowerSeries.X * BS z = PowerSeries.X^1 * BS z by simp,
    PowerSeries.coeff_X_pow_mul']
  rw [PowerSeries.binomialSeries_coeff]
  by_cases hk : k=0
  · subst k
    simp [Ring.choose_zero_right]
  · rw [if_neg hk, if_pos (show 1 ≤ k by omega)]
    simp

lemma coeff_ballotSeries_eq_formalPartial (A N : ℕ) :
    PowerSeries.coeff N (ballotSeries A N) =
      formalPartial ((A : ℤ)-2*(N : ℤ)) N := by
  rw [ballotSeries, geomPS, Finset.mul_sum, map_sum]
  rw [← Finset.sum_flip]
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
  let t := N-k
  have htN : t ≤ N := Nat.sub_le _ _
  change PowerSeries.coeff N
      ((1-PowerSeries.X) * BS ((A : ℤ)-1) * U^t) =
    formalCatalanCoeff ((A : ℤ)-2*(N : ℤ)) k
  rw [U, mul_pow, BS_neg_two_pow]
  rw [show (1-PowerSeries.X) * BS ((A : ℤ)-1) *
      (PowerSeries.X^t * BS (-(2*(t : ℤ)))) =
      PowerSeries.X^t * ((1-PowerSeries.X) *
        (BS ((A : ℤ)-1) * BS (-(2*(t : ℤ))))) by ring]
  rw [← BS_add]
  rw [PowerSeries.coeff_X_pow_mul', if_pos htN]
  rw [coeff_one_sub_X_mul_BS]
  unfold formalCatalanCoeff
  have hNk : N-t=k := by dsimp [t]; omega
  rw [hNk]
  have hz : (A : ℤ)-1 + -(2*(t : ℤ)) =
      ((A : ℤ)-2*(N : ℤ)) + 2*(k : ℤ)-1 := by
    dsimp [t]
    rw [Nat.cast_sub hkN]
    ring
  rw [hz]

lemma formalPartial_eq_FNat (A N : ℕ) :
    formalPartial ((A : ℤ)-2*(N : ℤ)) N = FNat A N := by
  rw [← coeff_ballotSeries_eq_formalPartial]
  rw [ballotSeries_coeff_eq_target A N N le_rfl]
  unfold FNat
  have hnat : BS (A : ℤ) = (1+PowerSeries.X)^A := by
    simpa [BS] using (PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) A)
  rw [hnat]
  simp


-- Development component: Actual.lean
open Nat Finset BigOperators Int

lemma generalized_choose_int_eq_choose (r : ℤ) (k : ℕ) :
    generalized_choose_int r k = Ring.choose r k := by
  rw [generalized_choose_int]
  split_ifs with hk
  · subst k
    simp [Ring.choose_zero_right]
  · apply Int.ediv_eq_of_eq_mul_left (by exact_mod_cast Nat.factorial_ne_zero k)
    rw [mul_comm, ← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose]
    rw [← Polynomial.eval_eq_smeval]
    exact (descPochhammer_eval_eq_prod_range k r).symm

lemma choose_mul_index (q : ℤ) {k : ℕ} (hk : 0 < k) :
    (k : ℤ) * Ring.choose q k =
      Ring.choose q (k - 1) * (q - (k - 1 : ℕ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := Ring.choose_smul_choose q (Nat.sub_le (j + 1) 1)
  rw [nsmul_eq_mul] at h
  simpa [Ring.choose_one_right] using h

lemma generalized_catalan_coefficient_eq_sub (r : ℤ) {k : ℕ} (hk : 0 < k)
    (hden : r + (k : ℤ) ≠ 0) :
    generalized_catalan_coefficient r k =
      Ring.choose (r + 2 * (k : ℤ) - 1) k -
        Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1) := by
  rw [generalized_catalan_coefficient, if_neg (Nat.ne_of_gt hk),
    generalized_choose_int_eq_choose]
  apply Int.ediv_eq_of_eq_mul_left hden
  have hratio := choose_mul_index (r + 2 * (k : ℤ) - 1) hk
  norm_num [Nat.cast_sub (by omega : 1 ≤ k)] at hratio
  rw [show (r * Ring.choose (r + 2 * (k : ℤ) - 1) k) =
      (Ring.choose (r + 2 * (k : ℤ) - 1) k -
       Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)) * (r + k) by
    linear_combination -hratio]

lemma generalized_catalan_eq_formal (r : ℤ) (k : ℕ)
    (hden : k=0 ∨ r+(k:ℤ) ≠ 0) :
    generalized_catalan_coefficient r k = formalCatalanCoeff r k := by
  by_cases hk0 : k=0
  · subst k
    simp [generalized_catalan_coefficient, formalCatalanCoeff]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hden' : r+(k:ℤ) ≠ 0 := hden.resolve_left hk0
    rw [generalized_catalan_coefficient_eq_sub r hk hden']
    simp [formalCatalanCoeff, hk0]

lemma a_gen_nat_eq_FNat (M N : ℕ) (hN : 0 < N) :
    a_gen (M : ℤ) N = FNat ((M+2)*N) N := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  rw [← formalPartial_eq_FNat ((M+2)*N) N]
  have hr : (((M+2)*N : ℕ) : ℤ) - 2*(N : ℤ) = (M : ℤ)*(N : ℤ) := by
    push_cast
    ring
  rw [hr]
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k hk
  apply generalized_catalan_eq_formal
  by_cases hk0 : k=0
  · exact Or.inl hk0
  · right
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    positivity

lemma formalCoeff_neg_one_endpoint (N : ℕ) (hN : 0 < N) :
    formalCatalanCoeff (-(N : ℤ)) N = -1 := by
  rw [formalCatalanCoeff, if_neg (Nat.ne_of_gt hN)]
  have hu : -(N : ℤ) + 2*(N : ℤ)-1 = ((N-1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  rw [hu, Ring.choose_natCast, Ring.choose_natCast]
  rw [Nat.choose_eq_zero_of_lt (by omega : N-1 < N), Nat.choose_self]
  norm_num

lemma actualCoeff_neg_one (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    generalized_catalan_coefficient (-(N : ℤ)) k =
      formalCatalanCoeff (-(N : ℤ)) k + (if k=N then 1 else 0) := by
  by_cases hkN : k=N
  · subst k
    rw [formalCoeff_neg_one_endpoint N hN]
    simp [generalized_catalan_coefficient, hN.ne']
  · rw [if_neg hkN, add_zero]
    apply generalized_catalan_eq_formal
    by_cases hk0 : k=0
    · exact Or.inl hk0
    · right
      push_cast
      omega

lemma a_gen_neg_one_eq_FNat (N : ℕ) (hN : 0 < N) :
    a_gen (-1) N = FNat N N + 1 := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  simp only [neg_one_mul]
  rw [← formalPartial_eq_FNat N N]
  have hr : ((N : ℤ)-2*(N : ℤ)) = -(N : ℤ) := by ring
  rw [hr]
  unfold formalPartial
  have hind : (∑ k ∈ Finset.range (N+1), (if k=N then (1:ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single N]
    · simp
    · intro b hb hne; simp [hne]
    · simp
  calc
    (∑ k ∈ Finset.range (N+1), generalized_catalan_coefficient (-(N:ℤ)) k) =
        ∑ k ∈ Finset.range (N+1),
          (formalCatalanCoeff (-(N:ℤ)) k + (if k=N then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply actualCoeff_neg_one N k hN
            simp only [Finset.mem_range] at hk
            omega
    _ = (∑ k ∈ Finset.range (N+1), formalCatalanCoeff (-(N:ℤ)) k) +
          ∑ k ∈ Finset.range (N+1), (if k=N then 1 else 0) :=
            Finset.sum_add_distrib
    _ = _ := by rw [hind]

lemma a_gen_neg_two_eq_FNat (N : ℕ) (hN : 0 < N) :
    a_gen (-2) N = FNat 0 N := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  rw [← formalPartial_eq_FNat 0 N]
  change (∑ k ∈ Finset.range (N+1),
      generalized_catalan_coefficient ((-2)*(N:ℤ)) k) =
    formalPartial ((0:ℤ)-2*(N:ℤ)) N

  have hr : ((0 : ℤ)-2*(N : ℤ)) = (-2)*(N : ℤ) := by ring
  rw [hr]
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k hk
  apply generalized_catalan_eq_formal
  by_cases hk0 : k=0
  · exact Or.inl hk0
  · right
    have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    push_cast
    omega

lemma FNat_zero (N : ℕ) : FNat 0 N = Core.qCoeff N := by
  unfold FNat
  simp only [pow_zero, Polynomial.coe_one, mul_one, Core.Qseries,
    PowerSeries.coeff_mk]

lemma a_gen_nat_scale {M p N lev : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^lev ∣ N) :
    a_gen (M:ℤ) (p*N) ≡ a_gen (M:ℤ) N
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  have hpN : 0 < p*N := mul_pos hp.pos hN
  rw [a_gen_nat_eq_FNat M (p*N) hpN, a_gen_nat_eq_FNat M N hN]
  have hY : p^lev ∣ (M+1)*N := dvd_mul_of_dvd_right hdiv (M+1)
  have h := FNat_scale_supercongruence hp hp5 hdiv hY
  convert h using 1 <;> ring

lemma a_gen_neg_one_scale {p N lev : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^lev ∣ N) :
    a_gen (-1) (p*N) ≡ a_gen (-1) N
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  rw [a_gen_neg_one_eq_FNat (p*N) (mul_pos hp.pos hN),
    a_gen_neg_one_eq_FNat N hN]
  exact (FNat_scale_supercongruence hp hp5 hdiv (dvd_zero _)).add rfl

lemma a_gen_neg_two_scale {p N lev : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    a_gen (-2) (p*N) ≡ a_gen (-2) N
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  rw [a_gen_neg_two_eq_FNat (p*N) (mul_pos hp.pos hN),
    a_gen_neg_two_eq_FNat N hN, FNat_zero, FNat_zero]
  have hq := Core.qCoeff_mul_prime (hp := hp) (hp5 := hp5) (n := N)
  rw [hq]


-- Development component: Negative.lean
open Nat Finset BigOperators Int Polynomial
open Core

noncomputable def V : PowerSeries ℤ :=
  -(PowerSeries.X * (1+PowerSeries.X))

noncomputable def geomV (N : ℕ) : PowerSeries ℤ :=
  ∑ t ∈ Finset.range (N+1), V^t

noncomputable def negSeries (A N : ℕ) : PowerSeries ℤ :=
  (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * geomV N

lemma cyclo_eq_one_sub_V :
    (Core.cyclo3 : PowerSeries ℤ) = 1-V := by
  rw [V]
  simp [Core.cyclo3]
  ring

lemma cyclo_mul_negSeries (A N : ℕ) :
    (Core.cyclo3 : PowerSeries ℤ) * negSeries A N =
      (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * (1-V^(N+1)) := by
  have hg := geom_sum_mul_neg V (N+1)
  change geomV N * (1-V) = 1-V^(N+1) at hg
  rw [negSeries]
  rw [show (Core.cyclo3 : PowerSeries ℤ) *
      ((1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * geomV N) =
    (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) *
      (geomV N * (Core.cyclo3 : PowerSeries ℤ)) by ring]
  rw [cyclo_eq_one_sub_V, hg]

lemma coeff_neg_remainder_zero (A N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n
      ((1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) * V^(N+1)) = 0 := by
  rw [V, neg_pow, mul_pow]
  rw [show (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) *
      ((-1 : PowerSeries ℤ)^(N+1) *
        (PowerSeries.X^(N+1) * (1+PowerSeries.X)^(N+1))) =
      PowerSeries.X^(N+1) *
        ((-1 : PowerSeries ℤ)^(N+1) * (1+2*PowerSeries.X) *
          (1+PowerSeries.X)^(A-1) * (1+PowerSeries.X)^(N+1)) by ring]
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

lemma cyclo_mul_neg_target (A : ℕ) (hA : 0 < A) :
    (Core.cyclo3 : PowerSeries ℤ) *
      (Core.Qseries * (1+PowerSeries.X)^A +
        PowerSeries.X * (1+PowerSeries.X)^(A-1)) =
      (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) := by
  have hpow : (1+PowerSeries.X : PowerSeries ℤ)^A =
      (1+PowerSeries.X : PowerSeries ℤ)^(A-1) *
        (1+PowerSeries.X : PowerSeries ℤ) := by
    conv_lhs => rw [show A=(A-1)+1 by omega, pow_succ]
  have hDQ := Core.cyclo3_mul_Qseries
  change (Core.cyclo3 : PowerSeries ℤ) * Core.Qseries =
    1-PowerSeries.X^2 at hDQ
  have hD : (Core.cyclo3 : PowerSeries ℤ) =
      PowerSeries.X^2+PowerSeries.X+1 := by simp [Core.cyclo3]
  calc
    (Core.cyclo3 : PowerSeries ℤ) *
        (Core.Qseries * (1+PowerSeries.X)^A +
          PowerSeries.X * (1+PowerSeries.X)^(A-1)) =
      ((Core.cyclo3 : PowerSeries ℤ) * Core.Qseries) *
          (1+PowerSeries.X)^A +
        (Core.cyclo3 : PowerSeries ℤ) * PowerSeries.X *
          (1+PowerSeries.X)^(A-1) := by ring
    _ = (1-PowerSeries.X^2) *
          ((1+PowerSeries.X)^(A-1) * (1+PowerSeries.X)) +
        (PowerSeries.X^2+PowerSeries.X+1) * PowerSeries.X *
          (1+PowerSeries.X)^(A-1) := by rw [hDQ, hpow, hD]
    _ = _ := by ring

lemma negSeries_coeff_eq_target (A N : ℕ) (hA : 0 < A) :
    PowerSeries.coeff N (negSeries A N) =
      PowerSeries.coeff N
        (Core.Qseries * (1+PowerSeries.X)^A +
          PowerSeries.X * (1+PowerSeries.X)^(A-1)) := by
  apply coeff_eq_of_cyclo_mul_eq
  intro d hd
  rw [cyclo_mul_negSeries, cyclo_mul_neg_target A hA]
  rw [mul_sub, mul_one, map_sub]
  rw [coeff_neg_remainder_zero A N d hd, sub_zero]
  exact le_rfl


noncomputable def negDiagTerm (R k : ℕ) : ℤ :=
  if k=0 then 1 else
    (-1 : ℤ)^k * ((R-k).choose k : ℤ) +
      (-1 : ℤ)^k * ((R-k-1).choose (k-1) : ℤ)

lemma formalCoeff_neg_eq (R k : ℕ) (h2k : 2*k ≤ R) :
    formalCatalanCoeff (-(R : ℤ)) k = negDiagTerm R k := by
  by_cases hk0 : k=0
  · subst k
    simp [formalCatalanCoeff, negDiagTerm]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [formalCatalanCoeff, if_neg hk0, negDiagTerm, if_neg hk0]
    let a := R-2*k+1
    have ha : 0 < a := by dsimp [a]; omega
    have hu : -(R : ℤ)+2*(k : ℤ)-1 = -(a : ℤ) := by
      dsimp [a]
      rw [Nat.cast_sub h2k]
      push_cast
      ring
    rw [hu, Ring.choose_neg, Ring.choose_neg]
    have hfirst : (a : ℤ)+(k : ℤ)-1 = ((R-k : ℕ) : ℤ) := by
      dsimp [a]
      rw [Nat.cast_sub h2k, Nat.cast_sub (by omega : k ≤ R)]
      push_cast
      ring
    have hsecond : (a : ℤ)+(k-1 : ℕ)-1 = ((R-k-1 : ℕ) : ℤ) := by
      dsimp [a]
      rw [Nat.cast_sub h2k, Nat.cast_sub (by omega : 1 ≤ k),
        Nat.cast_sub (by omega : 1 ≤ R-k), Nat.cast_sub (by omega : k ≤ R)]
      push_cast
      ring
    rw [hfirst, hsecond, Ring.choose_natCast, Ring.choose_natCast]
    simp only [Units.smul_def, Int.cast_negOnePow_natCast, zsmul_eq_mul]
    have hs : (-1 : ℤ)^k = -((-1 : ℤ)^(k-1)) := by
      conv_lhs => rw [show k=(k-1)+1 by omega, pow_succ]
      ring
    rw [hs]
    ring

lemma coeff_one_add_X_pow_int (L k : ℕ) :
    PowerSeries.coeff k ((1+PowerSeries.X : PowerSeries ℤ)^L) = (L.choose k : ℤ) := by
  rw [← PowerSeries.binomialSeries_nat (A := ℤ) (R := ℤ) L,
    PowerSeries.binomialSeries_coeff, Ring.choose_natCast]
  simp

lemma coeff_prefactor (L k : ℕ) :
    PowerSeries.coeff k
      ((1+2*PowerSeries.X) * (1+PowerSeries.X : PowerSeries ℤ)^L) =
      (L.choose k : ℤ) +
        (if 1 ≤ k then 2*(L.choose (k-1) : ℤ) else 0) := by
  rw [add_mul]
  rw [map_add]
  simp only [one_mul]
  rw [coeff_one_add_X_pow_int]
  rw [show (2 : PowerSeries ℤ) * PowerSeries.X *
      (1+PowerSeries.X : PowerSeries ℤ)^L =
      PowerSeries.C (2:ℤ) *
        (PowerSeries.X^1 * (1+PowerSeries.X : PowerSeries ℤ)^L) by simp; ring]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, if_pos hk, coeff_one_add_X_pow_int]
  · rw [if_neg hk, if_neg hk]
    ring

lemma neg_one_pow_mul_self (k : ℕ) :
    (-1 : ℤ)^k * (-1 : ℤ)^k = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      calc
        ((-1 : ℤ)^k * -1) * ((-1 : ℤ)^k * -1) =
            ((-1 : ℤ)^k * (-1 : ℤ)^k) * ((-1)*(-1)) := by ring
        _ = 1 := by rw [ih]; norm_num

lemma coeff_negSeries_eq_negDiagSum (A N : ℕ) (hA : 0 < A) :
    PowerSeries.coeff N (negSeries A N) =
      (-1 : ℤ)^N * ∑ k ∈ Finset.range (N+1), negDiagTerm (A+N) k := by
  rw [negSeries, geomV, Finset.mul_sum, map_sum]
  rw [← Finset.sum_flip]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
  let t := N-k
  have htN : t ≤ N := Nat.sub_le _ _
  rw [V, neg_pow, mul_pow]
  rw [show (1+2*PowerSeries.X) * (1+PowerSeries.X)^(A-1) *
      ((-1 : PowerSeries ℤ)^t *
        (PowerSeries.X^t * (1+PowerSeries.X : PowerSeries ℤ)^t)) =
      (-1 : PowerSeries ℤ)^t * PowerSeries.X^t *
        ((1+2*PowerSeries.X) *
          (1+PowerSeries.X : PowerSeries ℤ)^((A-1)+t)) by
            rw [pow_add]; ring]
  rw [show (-1 : PowerSeries ℤ)^t * PowerSeries.X^t *
      ((1+2*PowerSeries.X) *
        (1+PowerSeries.X : PowerSeries ℤ)^(A-1+t)) =
      PowerSeries.C ((-1 : ℤ)^t) *
        (PowerSeries.X^t * ((1+2*PowerSeries.X) *
          (1+PowerSeries.X : PowerSeries ℤ)^(A-1+t))) by simp; ring]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos htN]
  rw [coeff_prefactor]
  have hNt : N-t=k := by dsimp [t]; omega
  rw [hNt]
  by_cases hk0 : k=0
  · have ht : t=N := by dsimp [t]; omega
    simp [hk0, negDiagTerm, ht]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [negDiagTerm, if_neg hk0, if_pos (show 1 ≤ k by omega)]
    have hL : A-1+t+1=A+t := by omega
    have hchoose : (A+t).choose k =
        (A-1+t).choose (k-1) + (A-1+t).choose k := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      simpa [hL] using Nat.choose_succ_succ (A-1+t) q
    have hRk : A+N-k=A+t := by dsimp [t]; omega
    rw [hRk, hchoose]
    rw [show A+t-1=A-1+t by omega]
    have hsign : (-1 : ℤ)^t = (-1 : ℤ)^N * (-1 : ℤ)^k := by
      rw [show N=t+k by dsimp [t]; omega, pow_add]
      rw [mul_assoc, neg_one_pow_mul_self, mul_one]
    rw [hsign]
    push_cast
    ring

lemma negSeries_coeff_value (A N : ℕ) (hA : 0 < A) (hN : 0 < N) :
    PowerSeries.coeff N (negSeries A N) =
      FNat A N + ((A-1).choose (N-1) : ℤ) := by
  rw [negSeries_coeff_eq_target A N hA]
  rw [map_add]
  have hF : PowerSeries.coeff N
      (Core.Qseries * (1+PowerSeries.X : PowerSeries ℤ)^A) = FNat A N := by
    unfold FNat
    simp
  rw [hF]
  rw [show PowerSeries.X * (1+PowerSeries.X : PowerSeries ℤ)^(A-1) =
      PowerSeries.X^1 * (1+PowerSeries.X : PowerSeries ℤ)^(A-1) by simp,
    PowerSeries.coeff_X_pow_mul', if_pos (show 1 ≤ N by omega),
    coeff_one_add_X_pow_int]

lemma formalPartial_negative_involution (A N : ℕ) (hA : 0 < A) (hN : 0 < N)
    (hNA : N ≤ A) :
    formalPartial (-((A+N : ℕ) : ℤ)) N =
      (-1 : ℤ)^N * (FNat A N + ((A-1).choose (N-1) : ℤ)) := by
  have hsum : formalPartial (-((A+N : ℕ) : ℤ)) N =
      ∑ k ∈ Finset.range (N+1), negDiagTerm (A+N) k := by
    unfold formalPartial
    apply Finset.sum_congr rfl
    intro k hk
    apply formalCoeff_neg_eq
    have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    omega
  rw [hsum]
  have hc := coeff_negSeries_eq_negDiagSum A N hA
  rw [negSeries_coeff_value A N hA hN] at hc
  let S : ℤ := ∑ k ∈ Finset.range (N+1), negDiagTerm (A+N) k
  change FNat A N + ((A-1).choose (N-1) : ℤ) = (-1 : ℤ)^N * S at hc
  change S = (-1 : ℤ)^N * (FNat A N + ((A-1).choose (N-1) : ℤ))
  calc
    S = 1*S := by ring
    _ = (((-1 : ℤ)^N * (-1 : ℤ)^N) * S) := by rw [neg_one_pow_mul_self]
    _ = (-1 : ℤ)^N * ((-1 : ℤ)^N * S) := by ring
    _ = _ := by rw [← hc]

lemma a_gen_negative_involution (S N : ℕ) (hS : 2 ≤ S) (hN : 0 < N) :
    a_gen (-((S+1 : ℕ) : ℤ)) N =
      (-1 : ℤ)^N *
        (a_gen ((S-2 : ℕ) : ℤ) N + ((S*N-1).choose (N-1) : ℤ)) := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  have hr : -((S+1 : ℕ) : ℤ) * (N : ℤ) = -(((S*N)+N : ℕ) : ℤ) := by
    push_cast
    ring
  change (∑ k ∈ Finset.range (N+1),
      generalized_catalan_coefficient (-((S+1 : ℕ) : ℤ)*(N:ℤ)) k) = _
  rw [hr]
  rw [show (∑ k ∈ Finset.range (N+1),
      generalized_catalan_coefficient (-(((S*N)+N : ℕ) : ℤ)) k) =
      formalPartial (-(((S*N)+N : ℕ) : ℤ)) N by
    unfold formalPartial
    apply Finset.sum_congr rfl
    intro k hk
    apply generalized_catalan_eq_formal
    by_cases hk0 : k=0
    · exact Or.inl hk0
    · right
      have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
      have hSN : 2*N ≤ S*N := Nat.mul_le_mul_right N hS
      push_cast
      omega]
  rw [formalPartial_negative_involution (S*N) N (mul_pos (by omega) hN) hN
    (by nlinarith)]
  rw [a_gen_nat_eq_FNat (S-2) N hN]
  rw [show S-2+2=S by omega]



-- Development component: RationalR.lean
open Nat Finset BigOperators Int Polynomial
open Core

noncomputable def linear : Polynomial ℤ := 1+Polynomial.X

lemma frobError_dvd_linear {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    linear ∣ Core.frobError p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have he := congr_arg (fun f : Polynomial ℤ => f.eval (-1))
    (Core.frob_decomposition hp)
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at he
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hev : (Core.frobError p).eval (-1)=0 := by
    have hpow : (-1 : ℤ)^p = -1 := by
      obtain ⟨t,rfl⟩ := hodd
      simp [pow_succ,pow_mul]
    rw [hpow] at he
    norm_num [hp.ne_zero] at he
    exact he
  rw [show linear = Polynomial.X - Polynomial.C (-1) by
    ext n
    simp [linear,Polynomial.coeff_X]
    ring]
  exact (Polynomial.dvd_iff_isRoot).mpr hev

noncomputable def rQuot (p : ℕ) : Polynomial ℤ :=
  Core.frobError p /ₘ linear

lemma frobError_eq_linear_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Core.frobError p = linear * rQuot p := by
  have hm : linear.Monic := by dsimp [linear]; monicity <;> norm_num
  calc
    Core.frobError p = Core.frobError p %ₘ linear +
        linear * (Core.frobError p /ₘ linear) :=
      (Polynomial.modByMonic_add_div (Core.frobError p) hm).symm
    _ = linear*rQuot p := by
      rw [(Polynomial.modByMonic_eq_zero_iff_dvd hm).mpr
        (frobError_dvd_linear hp hp5), zero_add]
      rfl

lemma natDegree_linear : linear.natDegree=1 := by
  dsimp [linear]
  compute_degree <;> norm_num

lemma natDegree_rQuot_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (rQuot p).natDegree ≤ p-2 := by
  have heq := frobError_eq_linear_mul hp hp5
  have hq0 : rQuot p ≠ 0 := by
    intro h
    rw [h,mul_zero] at heq
    have hc := congr_arg (fun f : Polynomial ℤ => f.coeff 1) heq
    change (Core.frobError p).coeff 1 = (0 : Polynomial ℤ).coeff 1 at hc
    rw [Core.coeff_frobError] at hc
    norm_num [hp.one_lt,hp.ne_zero] at hc
  have hl0 : linear ≠ 0 := by
    have hm : linear.Monic := by dsimp [linear]; monicity <;> norm_num
    exact hm.ne_zero
  have hd := Polynomial.natDegree_mul hl0 hq0
  rw [_root_.natDegree_linear] at hd
  have hle := Core.natDegree_frobError_le p
  rw [heq,hd] at hle
  omega

lemma reflect_linear : Polynomial.reflect 1 linear = linear := by
  ext n
  rw [Polynomial.coeff_reflect]
  by_cases hn : n≤1
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;> norm_num [linear,Polynomial.coeff_X,Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]

lemma reflect_rQuot {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Polynomial.reflect (p-1) (rQuot p) = rQuot p := by
  have heq := frobError_eq_linear_mul hp hp5
  have hdL : linear.natDegree≤1 := natDegree_linear.le
  have hdQ : (rQuot p).natDegree≤p-1 := (natDegree_rQuot_le hp hp5).trans (by omega)
  have hm := Polynomial.reflect_mul linear (rQuot p) hdL hdQ
  have hi : 1+(p-1)=p := by omega
  rw [hi,←heq,Core.reflect_frobError,reflect_linear] at hm
  apply mul_left_cancel₀ (show linear≠0 by
    have hmon : linear.Monic := by dsimp [linear]; monicity <;> norm_num
    exact hmon.ne_zero)
  calc
    linear*Polynomial.reflect (p-1) (rQuot p) = Core.frobError p := hm.symm
    _ = linear*rQuot p := heq

noncomputable def rCoeff (n : ℕ) : ℤ :=
  if n=0 then 1 else 2*((-1 : ℤ)^n)

noncomputable def Rseries : PowerSeries ℤ := PowerSeries.mk rCoeff

lemma rCoeff_mul_prime {p n : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    rCoeff (p*n)=rCoeff n := by
  by_cases hn : n=0
  · subst n; simp [rCoeff]
  have hp0 := hp.ne_zero
  simp only [rCoeff,mul_eq_zero,hp0,hn,or_self,if_false]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [pow_mul]
  have hpneg : (-1 : ℤ)^p=-1 := by
    obtain ⟨t,rfl⟩ := hodd
    simp [pow_succ,pow_mul]
  rw [hpneg]

lemma linear_mul_Rseries :
    (linear : PowerSeries ℤ)*Rseries = 1-PowerSeries.X := by
  ext n
  rw [show (linear : PowerSeries ℤ)=1+PowerSeries.X by simp [linear]]
  rw [add_mul,map_add]
  simp only [one_mul,Rseries,PowerSeries.coeff_mk]
  rw [show PowerSeries.X*PowerSeries.mk rCoeff =
      PowerSeries.X^1*PowerSeries.mk rCoeff by simp,
    PowerSeries.coeff_X_pow_mul']
  by_cases hn0 : n=0
  · subst n; simp [rCoeff]
  have hn1 : 1≤n := by omega
  rw [if_pos hn1]
  simp only [map_sub,map_one,PowerSeries.coeff_X]
  by_cases hn1eq : n=1
  · subst n; norm_num [rCoeff]
  have hpred : n=(n-1)+1 := by omega
  rw [PowerSeries.coeff_mk]

  rw [show rCoeff n + rCoeff (n-1)=0 by
    simp only [rCoeff,hn0,if_false]
    have hp0 : n-1≠0 := by omega
    rw [if_neg hp0]
    have hs : (-1 : ℤ)^n = -((-1 : ℤ)^(n-1)) := by
      conv_lhs => rw [hpred,pow_succ]
      ring
    rw [hs]
    ring]
  simp [hn0,hn1eq]

noncomputable def rErrorPoly (p j : ℕ) : Polynomial ℤ :=
  if j=0 then 0 else
    (1-Polynomial.X)*linear^(j-1)*rQuot p^j

lemma Rseries_mul_frobError_pow {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) :
    Rseries*(Core.frobError p : PowerSeries ℤ)^j =
      (rErrorPoly p j : PowerSeries ℤ) := by
  rw [frobError_eq_linear_mul hp hp5,Polynomial.coe_mul]
  rw [rErrorPoly,if_neg (Nat.ne_of_gt hj),Polynomial.coe_mul,Polynomial.coe_mul]
  simp only [Polynomial.coe_pow,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_X]
  have hj_eq : j=(j-1)+1 := by omega
  conv_lhs => enter [2]; rw [hj_eq,pow_succ]
  have h := linear_mul_Rseries
  change (linear : PowerSeries ℤ)*Rseries=1-PowerSeries.X at h
  rw [←h]
  have hq : (rQuot p : PowerSeries ℤ)^j =
      (rQuot p : PowerSeries ℤ)^(j-1)*(rQuot p : PowerSeries ℤ) := by
    conv_lhs => rw [hj_eq,pow_succ]
  rw [hq]
  ring


lemma reflect_pow_local {f : Polynomial ℤ} {D : ℕ} (hdeg : f.natDegree≤D)
    (href : Polynomial.reflect D f=f) (j : ℕ) :
    Polynomial.reflect (D*j) (f^j)=f^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ,Nat.mul_succ,Polynomial.reflect_mul (f^j) f]
      · rw [ih,href]
      · simpa [Nat.mul_comm] using
          Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hdeg)
      · exact hdeg

lemma reflect_one_sub_X :
    Polynomial.reflect 1 (1-Polynomial.X : Polynomial ℤ) = -(1-Polynomial.X) := by
  ext n
  rw [Polynomial.coeff_reflect]
  by_cases hn : n≤1
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;> norm_num [Polynomial.coeff_X,Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]
    simp only [Polynomial.coeff_neg, Polynomial.coeff_sub,
      Polynomial.coeff_X, Polynomial.coeff_one]
    simp [show 1 ≠ n by omega, show n ≠ 0 by omega]

lemma reflect_rErrorPoly {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hj : 0<j) :
    Polynomial.reflect (p*j) (rErrorPoly p j) = -rErrorPoly p j := by
  rw [rErrorPoly,if_neg (Nat.ne_of_gt hj)]
  have hdL : linear.natDegree≤1 := natDegree_linear.le
  have hdQ : (rQuot p).natDegree≤p-1 := (natDegree_rQuot_le hp hp5).trans (by omega)
  have hLp := reflect_pow_local hdL reflect_linear (j-1)
  have hQp := reflect_pow_local hdQ (reflect_rQuot hp hp5) j
  have hdA : (1-Polynomial.X : Polynomial ℤ).natDegree≤1 := by compute_degree <;> norm_num
  have hdB : (linear^(j-1)).natDegree≤1*(j-1) := by
    simpa [Nat.mul_comm] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (j-1) hdL)
  have hdC : (rQuot p^j).natDegree≤(p-1)*j := by
    simpa [Nat.mul_comm] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hdQ)
  have hm1 := Polynomial.reflect_mul (1-Polynomial.X : Polynomial ℤ)
    (linear^(j-1)) hdA hdB
  have hm2 := Polynomial.reflect_mul
    ((1-Polynomial.X : Polynomial ℤ)*linear^(j-1)) (rQuot p^j)
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hdA hdB)) hdC
  have hi : 1+1*(j-1)+(p-1)*j=p*j := by
    simp only [one_mul]
    calc
      1 + (j-1) + (p-1)*j = j + (p-1)*j := by
        rw [show 1 + (j-1) = j by omega]
      _ = (1+(p-1))*j := by rw [Nat.add_mul, one_mul]
      _ = p*j := by rw [show 1+(p-1)=p by omega]
  rw [hi] at hm2
  rw [hm1,reflect_one_sub_X,hLp,hQp] at hm2
  convert hm2 using 1 <;> ring

lemma rError_coeff_antisymm {p j d : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) (hd : d≤j) :
    (rErrorPoly p j).coeff (p*(j-d)) = -(rErrorPoly p j).coeff (p*d) := by
  have h := congr_arg (fun f : Polynomial ℤ => f.coeff (p*d))
    (reflect_rErrorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (rErrorPoly p j)).coeff (p*d) =
    (-rErrorPoly p j).coeff (p*d) at h
  rw [Polynomial.coeff_reflect,Polynomial.revAt_le (Nat.mul_le_mul_left p hd),
    Polynomial.coeff_neg] at h
  rw [Nat.mul_sub_left_distrib]
  exact h

lemma rError_coeff_zero {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hj : 0<j) :
    (rErrorPoly p j).coeff 0=0 := by
  have h := congr_arg (PowerSeries.coeff 0) (Rseries_mul_frobError_pow hp hp5 hj)
  simp only [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_one,Rseries,PowerSeries.coeff_mk,Polynomial.coeff_coe] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow,
    ←PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  simp [rCoeff,Polynomial.coeff_coe,Core.coeff_frobError,hj.ne'] at h
  exact h.symm

lemma rError_coeff_above {p j d : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) (hd : j<d) : (rErrorPoly p j).coeff (p*d)=0 := by
  have h := congr_arg (fun f : Polynomial ℤ => f.coeff (p*d))
    (reflect_rErrorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (rErrorPoly p j)).coeff (p*d) =
    (-rErrorPoly p j).coeff (p*d) at h
  rw [Polynomial.coeff_reflect,Polynomial.revAt_eq_self_of_lt
      (Nat.mul_lt_mul_of_pos_left hd hp.pos),Polynomial.coeff_neg] at h
  omega

lemma contracted_rError_coeff_sum {p j A B : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) :
    (rErrorPoly p j*(1+Polynomial.X^p)^(A-j)).coeff (p*B) =
      ∑ d ∈ Finset.range (j+1), (rErrorPoly p j).coeff (p*d)*
        (chooseSub (A-j) B d : ℤ) := by
  rw [base_eq_expand]
  have hc := Polynomial.contract_mul_expand hp.ne_zero (rErrorPoly p j)
    ((1+Polynomial.X : Polynomial ℤ)^(A-j))
  have heq := congr_arg (fun f : Polynomial ℤ => f.coeff B) hc
  change (Polynomial.contract p
      (rErrorPoly p j*Polynomial.expand ℤ p ((1+Polynomial.X)^(A-j)))).coeff B =
    (Polynomial.contract p (rErrorPoly p j)*(1+Polynomial.X)^(A-j)).coeff B at heq
  rw [Polynomial.coeff_contract hp.ne_zero,coeff_mul_one_add_pow] at heq
  rw [Nat.mul_comm] at heq
  rw [heq]
  have hs := sum_chooseSub_eq (N:=A-j) (B:=B) (j:=j)
    (f:=fun d => (Polynomial.contract p (rErrorPoly p j)).coeff d) (by
      intro d hd
      change (Polynomial.contract p (rErrorPoly p j)).coeff d=0
      rw [Polynomial.coeff_contract hp.ne_zero]
      simpa [Nat.mul_comm] using rError_coeff_above hp hp5 hj hd)
  simpa only [Polynomial.coeff_contract hp.ne_zero,Nat.mul_comm] using hs

noncomputable def RNat (A B : ℕ) : ℤ :=
  PowerSeries.coeff B
    (Rseries*(((1+Polynomial.X : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ))

lemma RNat_base_scale {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) (A B : ℕ) :
    PowerSeries.coeff (p*B)
      (Rseries*(((1+Polynomial.X^p : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ)) =
      RNat A B := by
  rw [base_eq_expand,Nat.mul_comm p B]
  change PowerSeries.coeff (B*p)
    (PowerSeries.mk rCoeff*(Polynomial.expand ℤ p
      ((1+Polynomial.X : Polynomial ℤ)^A) : PowerSeries ℤ))=_
  rw [coeff_series_mul_expand rCoeff hp.pos]
  · rfl
  · intro t
    simpa [Nat.mul_comm] using rCoeff_mul_prime (hp:=hp) (hp5:=hp5) (n:=t)

lemma rCorrection_coeff_eq {p A B j : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) :
    PowerSeries.coeff (p*B)
      (Rseries*((Polynomial.C ((p:ℤ)^j*(A.choose j:ℤ))*Core.frobError p^j*
        (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ)) =
      ∑ d ∈ Finset.range (j+1), (p:ℤ)^j*(rErrorPoly p j).coeff (p*d)*
        (A.choose j:ℤ)*(chooseSub (A-j) B d:ℤ) := by
  have herr := Rseries_mul_frobError_pow hp hp5 hj
  have hs : Rseries*((Polynomial.C ((p:ℤ)^j*(A.choose j:ℤ))*Core.frobError p^j*
        (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) =
      PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*
        ((rErrorPoly p j*(1+Polynomial.X^p)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) := by
    simp only [Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_C]
    calc
      Rseries*(PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*
          (Core.frobError p : PowerSeries ℤ)^j*
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j)) =
        PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*
          (Rseries*(Core.frobError p : PowerSeries ℤ)^j)*
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by ring
      _ = PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*(rErrorPoly p j : PowerSeries ℤ)*
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by rw [herr]
      _ = _ := by ring
  rw [hs,PowerSeries.coeff_C_mul,Polynomial.coeff_coe,
    contracted_rError_coeff_sum hp hp5 hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma rCorrection_coeff_dvd_total {p L B Y j : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hprod : ((p:ℤ)^L) ∣ (B:ℤ)*Y*((Y:ℤ)-B)) (hj : 0<j) (hjA : j≤B+Y) :
    ((p:ℤ)^(L+3)) ∣ PowerSeries.coeff (p*B)
      (Rseries*((Polynomial.C ((p:ℤ)^j*((B+Y).choose j:ℤ))*Core.frobError p^j*
        (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-j) : Polynomial ℤ) : PowerSeries ℤ)) := by
  rw [rCorrection_coeff_eq hp hp5 hj]
  apply shifted_paired_sum_dvd_total hp hp5 hprod hjA
  · exact rError_coeff_zero hp hp5 hj
  · intro d hd
    exact rError_coeff_antisymm hp hp5 hj hd

lemma RNat_scale_expansion {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) (A B : ℕ) :
    RNat (p*A) (p*B) = RNat A B +
      ∑ i ∈ Finset.range A,
        PowerSeries.coeff (p*B)
          (Rseries *
            ((Polynomial.C ((p:ℤ)^(i+1) * (A.choose (i+1):ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^(A-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ)) := by
  unfold RNat
  rw [frobenius_expansion hp]
  rw [coe_finset_sum_poly]
  rw [Finset.mul_sum, map_sum]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, Int.natCast_one,
    mul_one, Polynomial.C_1, one_mul, Nat.sub_zero]
  rw [RNat_base_scale hp hp5]
  abel

lemma RNat_scale_supercongruence_total {p L B Y : ℕ}
    (hp : p.Prime) (hp5 : 5≤p)
    (hprod : ((p:ℤ)^L) ∣ (B:ℤ)*Y*((Y:ℤ)-B)) :
    RNat (p*(B+Y)) (p*B) ≡ RNat (B+Y) B [ZMOD ((p:ℤ)^(L+3))] := by
  rw [Int.modEq_iff_dvd]
  rw [RNat_scale_expansion hp hp5]
  rw [show RNat (B+Y) B -
      (RNat (B+Y) B + ∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Rseries *
            ((Polynomial.C ((p:ℤ)^(i+1) * ((B+Y).choose (i+1):ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) =
      -(∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Rseries *
            ((Polynomial.C ((p:ℤ)^(i+1) * ((B+Y).choose (i+1):ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) by ring]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro i hi
  have hiA : i+1≤B+Y := by
    simp only [Finset.mem_range] at hi
    omega
  exact rCorrection_coeff_dvd_total hp hp5 hprod (by omega) hiA


lemma RNat_eq_choose_sub {A B : ℕ} (hA : 0<A) (hB : 0<B) :
    RNat A B = (A-1).choose B - (A-1).choose (B-1) := by
  have hAs : A=(A-1)+1 := by omega
  have hBs : B=(B-1)+1 := by omega
  have hseries : Rseries *
      (((1+Polynomial.X : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ) =
      (((1-Polynomial.X)*linear^(A-1) : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [show (1+Polynomial.X : Polynomial ℤ)=linear by rfl]
    simp only [Polynomial.coe_pow, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X]
    change Rseries * (linear : PowerSeries ℤ)^A =
      (1-PowerSeries.X) * (linear : PowerSeries ℤ)^(A-1)
    rw [show (linear : PowerSeries ℤ)^A =
        (linear : PowerSeries ℤ)^(A-1)*linear by
      calc
        (linear : PowerSeries ℤ)^A = linear^((A-1)+1) := congrArg _ hAs
        _ = linear^(A-1)*linear := pow_succ _ _]
    have h := linear_mul_Rseries
    change (linear : PowerSeries ℤ)*Rseries=1-PowerSeries.X at h
    rw [←h]
    ring
  unfold RNat
  rw [hseries, Polynomial.coeff_coe]
  rw [show (1-Polynomial.X)*linear^(A-1) =
      linear^(A-1)-Polynomial.X*linear^(A-1) by ring,
    Polynomial.coeff_sub]
  rw [hBs, Polynomial.coeff_X_mul]
  simp only [linear, Polynomial.coeff_one_add_X_pow]
  rw [show B-1+1-1=B-1 by omega]

lemma RNat_eq_boundary_mul (S N : ℕ) (hS : 2≤S) (hN : 0<N) :
    RNat (S*N) N = ((S:ℤ)-2) * (((S*N-1).choose (N-1) : ℕ) : ℤ) := by
  have hA : 0<S*N := mul_pos (by omega) hN
  rw [RNat_eq_choose_sub hA hN]
  have hNS : N≤S*N := by
    simpa only [one_mul] using Nat.mul_le_mul_right N (show 1≤S by omega)
  have hc := Nat.choose_succ_right_eq (S*N-1) (N-1)
  have hmul : (S-1)*N=S*N-N := by
    rw [Nat.sub_mul, one_mul]
  have hsub : (S*N-1)-(N-1)=(S-1)*N := by
    rw [hmul]
    omega
  rw [show (N-1)+1=N by omega, hsub] at hc
  apply mul_left_cancel₀ (show (N:ℤ)≠0 by exact_mod_cast hN.ne')
  have hcz : (((S*N-1).choose N : ℕ):ℤ) * N =
      (((S*N-1).choose (N-1):ℕ):ℤ) * (((S:ℤ)-1)*N) := by
    have hz := congrArg (fun x : ℕ => (x:ℤ)) hc
    push_cast at hz
    rw [Nat.cast_sub (show 1≤S by omega)] at hz
    exact hz
  calc
    (N:ℤ) * (((S*N-1).choose N:ℕ) - (S*N-1).choose (N-1)) =
        (((S*N-1).choose N:ℕ):ℤ)*N -
          (((S*N-1).choose (N-1):ℕ):ℤ)*N := by push_cast; ring
    _ = (((S*N-1).choose (N-1):ℕ):ℤ) * (((S:ℤ)-1)*N) -
          (((S*N-1).choose (N-1):ℕ):ℤ)*N := by rw [hcz]
    _ = (N:ℤ) * (((S:ℤ)-2) * (((S*N-1).choose (N-1):ℕ):ℤ)) := by ring


-- Development component: Boundary.lean
open Nat Finset BigOperators Int Polynomial

lemma boundary_scale_gt_two {S p N lev : ℕ} (hS : 2<S)
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev ∣ N) :
    (((S*(p*N)-1).choose (p*N-1) : ℕ) : ℤ) ≡
      (((S*N-1).choose (N-1) : ℕ) : ℤ)
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  let q := padicValNat p (S-2)
  let c : ℤ := (S:ℤ)-2
  let BH : ℤ := ((S*(p*N)-1).choose (p*N-1) : ℕ)
  let BL : ℤ := ((S*N-1).choose (N-1) : ℕ)
  letI : Fact p.Prime := ⟨hp⟩
  have hc0 : c≠0 := by dsimp [c]; omega
  have hqnat : p^q ∣ S-2 := by
    dsimp [q]
    exact pow_padicValNat_dvd
  have hprod : ((p:ℤ)^(3*lev+q)) ∣
      (N:ℤ)*(((S-1)*N:ℕ):ℤ)*((((S-1)*N:ℕ):ℤ)-N) := by
    obtain ⟨u,hu⟩ := hdiv
    obtain ⟨v,hv⟩ := hqnat
    use (u:ℤ)^3 * (S-1) * v
    have hpcast : ((p^lev:ℕ):ℤ)=(p:ℤ)^lev := by push_cast; rfl
    have hpcq : ((p^q:ℕ):ℤ)=(p:ℤ)^q := by push_cast; rfl
    have hNcast : (N:ℤ)=(p:ℤ)^lev*(u:ℤ) := by
      exact_mod_cast hu
    have hScast : ((S-2:ℕ):ℤ)=(p:ℤ)^q*(v:ℤ) := by
      exact_mod_cast hv
    have hdiff : ((((S-1)*N:ℕ):ℤ)-(N:ℤ)) = ((S-2:ℕ):ℤ)*(N:ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1≤S), Nat.cast_sub (by omega : 2≤S)]
      push_cast
      ring
    rw [hdiff]
    push_cast
    rw [hNcast, hScast]
    rw [pow_add, pow_mul]
    push_cast
    rw [Nat.cast_sub (show 1≤S by omega)]
    ring
  have hr := RNat_scale_supercongruence_total
    (p:=p) (L:=3*lev+q) (B:=N) (Y:=(S-1)*N) hp hp5 hprod
  have hsum : N+(S-1)*N=S*N := by
    calc
      N+(S-1)*N = 1*N+(S-1)*N := by rw [one_mul]
      _ = (1+(S-1))*N := (Nat.add_mul _ _ _).symm
      _ = S*N := by rw [show 1+(S-1)=S by omega]
  rw [hsum] at hr
  have hpN : 0<p*N := mul_pos hp.pos hN
  have hlow := RNat_eq_boundary_mul S N (by omega) hN
  have hhigh := RNat_eq_boundary_mul S (p*N) (by omega) hpN
  have harg : S*(p*N)=p*(S*N) := by ring
  rw [harg] at hhigh
  change RNat (p*(S*N)) (p*N) ≡ RNat (S*N) N
      [ZMOD ((p:ℤ)^((3*lev+q)+3))] at hr
  rw [hhigh, hlow] at hr
  change c * (((p*(S*N)-1).choose (p*N-1):ℕ):ℤ) ≡ c*BL
      [ZMOD ((p:ℤ)^((3*lev+q)+3))] at hr
  rw [show p*(S*N)=S*(p*N) by ring] at hr
  change c*BH ≡ c*BL [ZMOD ((p:ℤ)^((3*lev+q)+3))] at hr
  rw [Int.modEq_iff_dvd] at hr ⊢
  have hexp : (3*lev+q)+3=3*(lev+1)+q := by omega
  rw [hexp] at hr
  let D : ℤ := BL-BH
  change ((p:ℤ)^(3*(lev+1))) ∣ D
  have hrD : ((p:ℤ)^(3*(lev+1)+q)) ∣ c*D := by
    dsimp [D]
    convert hr using 1 <;> ring
  by_cases hD : D=0
  · simp [hD]
  have hval := (padicValInt_dvd_iff (3*(lev+1)+q) (c*D)).mp hrD
  have hval' : 3*(lev+1)+q ≤ padicValInt p (c*D) :=
    hval.resolve_left (mul_ne_zero hc0 hD)
  rw [padicValInt.mul hc0 hD] at hval'
  have hvc : padicValInt p c=q := by
    dsimp [c,q]
    rw [← padicValInt.of_nat]
    congr 2
    omega
  rw [hvc] at hval'
  apply (padicValInt_dvd_iff (3*(lev+1)) D).mpr
  exact Or.inr (by omega)

-- Development component: Perturb.lean
open Nat Finset BigOperators Int Polynomial

private def fallTop (X k : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, ((X:ℤ)-i)

private lemma fallTop_eq (X k : ℕ) :
    fallTop X k = (k.factorial:ℤ) * (X.choose k:ℤ) := by
  rw [fallTop, ← Ring.choose_natCast (R:=ℤ), ← nsmul_eq_mul,
    ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.eval_eq_smeval]
  exact (descPochhammer_eval_eq_prod_range k (X:ℤ)).symm

lemma choose_modEq_of_top_modEq {p E X Y k : ℕ} (hp : p.Prime)
    (hXY : (X:ℤ) ≡ (Y:ℤ)
      [ZMOD ((p:ℤ)^(E+padicValNat p k.factorial))]) :
    (X.choose k:ℤ) ≡ (Y.choose k:ℤ) [ZMOD ((p:ℤ)^E)] := by
  let v := padicValNat p k.factorial
  let D : ℤ := (Y.choose k:ℤ)-(X.choose k:ℤ)
  letI : Fact p.Prime := ⟨hp⟩
  have hfall : fallTop X k ≡ fallTop Y k [ZMOD ((p:ℤ)^(E+v))] := by
    apply Int.ModEq.prod
    intro i hi
    exact hXY.sub rfl
  rw [fallTop_eq, fallTop_eq, Int.modEq_iff_dvd] at hfall
  have hfac : (k.factorial:ℤ)≠0 := by positivity
  have hwhole : ((p:ℤ)^(E+v)) ∣ (k.factorial:ℤ)*D := by
    dsimp [D]
    convert hfall using 1 <;> ring
  rw [Int.modEq_iff_dvd]
  change ((p:ℤ)^E) ∣ D
  by_cases hD : D=0
  · simp [hD]
  have hvall := (padicValInt_dvd_iff (E+v) ((k.factorial:ℤ)*D)).mp hwhole
  have hvall' : E+v≤padicValInt p ((k.factorial:ℤ)*D) :=
    hvall.resolve_left (mul_ne_zero hfac hD)
  rw [padicValInt.mul hfac hD, padicValInt.of_nat] at hvall'
  apply (padicValInt_dvd_iff E D).mpr
  exact Or.inr (by dsimp [v] at hvall' ⊢; omega)

lemma boundary_scale_two {p N lev : ℕ}
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev∣N) :
    (((2*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((2*N-1).choose (N-1):ℕ):ℤ)
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  let E := 3*(lev+1)
  let vL := padicValNat p (N-1).factorial
  let vH := padicValNat p (p*N-1).factorial
  let T := E+vL+vH
  let Sp := 2+p^T
  have hSp : 2<Sp := by
    have hpow : 0<p^T := pow_pos hp.pos T
    dsimp [Sp]
    omega
  have hmain := boundary_scale_gt_two hSp hp hp5 hN hdiv
  have hEL : E+vL≤T := by dsimp [T]; omega
  have hEH : E+vH≤T := by dsimp [T]; omega
  have htopL : ((Sp*N-1:ℕ):ℤ) ≡ ((2*N-1:ℕ):ℤ)
      [ZMOD ((p:ℤ)^(E+vL))] := by
    rw [Int.modEq_iff_dvd]
    have hpdiv : ((p:ℤ)^(E+vL)) ∣ (p:ℤ)^T :=
      pow_dvd_pow (p:ℤ) hEL
    have hd : ((p:ℤ)^(E+vL)) ∣ (p:ℤ)^T*(N:ℤ) :=
      dvd_mul_of_dvd_left hpdiv N
    have heq : ((2*N-1:ℕ):ℤ)-((Sp*N-1:ℕ):ℤ) =
        -((p:ℤ)^T*(N:ℤ)) := by
      dsimp [Sp]
      push_cast
      have h2N : 0<2*N := mul_pos (by omega) hN
      have hSpN : 0<(2+p^T)*N := mul_pos (by positivity) hN
      rw [Nat.cast_sub (by omega : 1≤2*N),
        Nat.cast_sub (by omega : 1≤(2+p^T)*N)]
      push_cast
      ring
    rw [heq]
    exact dvd_neg.mpr hd
  have htopH : ((Sp*(p*N)-1:ℕ):ℤ) ≡ ((2*(p*N)-1:ℕ):ℤ)
      [ZMOD ((p:ℤ)^(E+vH))] := by
    rw [Int.modEq_iff_dvd]
    have hpdiv : ((p:ℤ)^(E+vH)) ∣ (p:ℤ)^T :=
      pow_dvd_pow (p:ℤ) hEH
    have hd : ((p:ℤ)^(E+vH)) ∣ (p:ℤ)^T*(p*N:ℤ) :=
      dvd_mul_of_dvd_left hpdiv (p*N)
    have heq : ((2*(p*N)-1:ℕ):ℤ)-((Sp*(p*N)-1:ℕ):ℤ) =
        -((p:ℤ)^T*(p*N:ℤ)) := by
      dsimp [Sp]
      have hpN : 0<p*N := mul_pos hp.pos hN
      have htwo : 0<2*(p*N) := mul_pos (by omega) hpN
      have hbig : 0<(2+p^T)*(p*N) := mul_pos (by positivity) hpN
      rw [Nat.cast_sub (by omega : 1≤2*(p*N)),
        Nat.cast_sub (by omega : 1≤(2+p^T)*(p*N))]
      push_cast
      ring
    rw [heq]
    exact dvd_neg.mpr hd
  have hlow := choose_modEq_of_top_modEq (p:=p) (E:=E)
    (X:=Sp*N-1) (Y:=2*N-1) (k:=N-1) hp (by simpa [vL] using htopL)
  have hhigh := choose_modEq_of_top_modEq (p:=p) (E:=E)
    (X:=Sp*(p*N)-1) (Y:=2*(p*N)-1) (k:=p*N-1) hp
      (by simpa [vH] using htopH)
  change (((Sp*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((Sp*N-1).choose (N-1):ℕ):ℤ) [ZMOD ((p:ℤ)^E)] at hmain
  change (((2*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((2*N-1).choose (N-1):ℕ):ℤ) [ZMOD ((p:ℤ)^E)]
  exact hhigh.symm.trans (hmain.trans hlow)

lemma boundary_scale {S p N lev : ℕ} (hS : 2≤S)
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev∣N) :
    (((S*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((S*N-1).choose (N-1):ℕ):ℤ)
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  rcases hS.eq_or_lt with rfl | hgt
  · exact boundary_scale_two hp hp5 hN hdiv
  · exact boundary_scale_gt_two hgt hp hp5 hN hdiv


-- Development component: AllScale.lean
open Nat Finset BigOperators Int Polynomial

lemma neg_one_pow_prime_mul {p N : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    (-1:ℤ)^(p*N)=(-1:ℤ)^N := by
  rw [pow_mul]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpw : (-1:ℤ)^p=-1 := by
    obtain ⟨t,rfl⟩ := hodd
    simp [pow_succ, pow_mul]
  rw [hpw]

lemma a_gen_scale_all (m : ℤ) {p N lev : ℕ}
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev∣N) :
    a_gen m (p*N) ≡ a_gen m N [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  cases m with
  | ofNat M =>
      exact a_gen_nat_scale hp hp5 hN hdiv
  | negSucc t =>
      cases t with
      | zero =>
          simpa using a_gen_neg_one_scale hp hp5 hN hdiv
      | succ t =>
          cases t with
          | zero =>
              simpa using a_gen_neg_two_scale (lev:=lev) hp hp5 hN
          | succ u =>
              let S := u+2
              have hS : 2≤S := by dsimp [S]; omega
              have hpN : 0<p*N := mul_pos hp.pos hN
              have hhigh := a_gen_negative_involution S (p*N) hS hpN
              have hlow := a_gen_negative_involution S N hS hN
              have hpos := a_gen_nat_scale (M:=S-2) hp hp5 hN hdiv
              have hbound := boundary_scale hS hp hp5 hN hdiv
              have hsum := hpos.add hbound
              have hsign := neg_one_pow_prime_mul hp hp5 (N:=N)
              change a_gen (-((S+1:ℕ):ℤ)) (p*N) ≡
                a_gen (-((S+1:ℕ):ℤ)) N [ZMOD ((p:ℤ)^(3*(lev+1)))]
              rw [hhigh, hlow, hsign]
              have hmul := Int.ModEq.mul_left ((-1:ℤ)^N) hsum
              simpa [S] using hmul

/--
A333096 supercongruence (all integral parameters).
-/
theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  let N := n*p^(k-1)
  have hN : 0<N := by
    dsimp [N]
    exact mul_pos hn (pow_pos hp.pos _)
  have hdiv : p^(k-1)∣N := by
    dsimp [N]
    exact dvd_mul_left _ _
  have hs := a_gen_scale_all m hp hp5 hN hdiv
  have hkpow : p^k=p^(k-1)*p := by
    conv_lhs => rw [show k=(k-1)+1 by omega, pow_succ]
  have hhigh : p*N=n*p^k := by
    dsimp [N]
    rw [hkpow]
    ring
  have hlow : N=n*p^(k-1) := rfl
  have hexp : 3*((k-1)+1)=3*k := by omega
  rw [hhigh, hlow, hexp] at hs
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs
