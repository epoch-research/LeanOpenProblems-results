import FormalConjectures.Util.ProblemImports

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)


/-
The proof uses Euler's transformation for formal hypergeometric series. Two
instances have the same factor (1-X)^(2n+1); comparing coefficients gives a
finite-sum transformation. In the transformed sum, each nonzero term has
p-adic valuation at least three.
-/
open Finset
namespace A374605

noncomputable def rf (x : ℚ) (k : ℕ) : ℚ := (ascPochhammer ℚ k).eval x

@[simp] lemma rf_zero (x : ℚ) : rf x 0 = 1 := by simp [rf]
lemma rf_succ (x : ℚ) (k : ℕ) : rf x (k+1) = rf x k * (x+k) :=
  ascPochhammer_succ_eval k x
lemma rf_pos {x : ℚ} (hx : 0 < x) (k : ℕ) : 0 < rf x k := ascPochhammer_pos k x hx

noncomputable def hgCoeff (a b c : ℚ) (k : ℕ) : ℚ :=
  rf a k * rf b k / (rf c k * k.factorial)
noncomputable def hg (a b c : ℚ) : PowerSeries ℚ := PowerSeries.mk (hgCoeff a b c)

@[simp] lemma coeff_hg (a b c : ℚ) (k : ℕ) : PowerSeries.coeff k (hg a b c) = hgCoeff a b c k := by simp [hg]
@[simp] lemma hgCoeff_zero (a b c : ℚ) : hgCoeff a b c 0 = 1 := by simp [hgCoeff]
lemma hgCoeff_succ (a b c : ℚ) (hc : 0 < c) (k : ℕ) :
    ((k:ℚ)+1)*((k:ℚ)+c)*hgCoeff a b c (k+1) =
      ((k:ℚ)+a)*((k:ℚ)+b)*hgCoeff a b c k := by
  have hc0 := ne_of_gt (rf_pos hc k)
  have hck : c + (k:ℚ) ≠ 0 := by positivity
  have hk : (k.factorial:ℚ) ≠ 0 := by positivity
  simp only [hgCoeff, rf_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

open PowerSeries
local notation "D" => PowerSeries.derivative ℚ
local notation "Xq" => (PowerSeries.X : PowerSeries ℚ)

noncomputable def ode (a b c : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  Xq * (1-Xq) * D (D f) + (C c - C (a+b+1)*Xq)*D f - C (a*b)*f

lemma coeff_X_D (f : PowerSeries ℚ) (k : ℕ) :
    coeff k (Xq * D f) = (k:ℚ) * coeff k f := by
  cases k with
  | zero => simp only [coeff_zero_X_mul, Nat.cast_zero, zero_mul]
  | succ k => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]; ring

lemma coeff_ode (a b c : ℚ) (f : PowerSeries ℚ) (k : ℕ) :
    coeff k (ode a b c f) =
      ((k:ℚ)+1)*((k:ℚ)+c)*coeff (k+1) f -
      ((k:ℚ)+a)*((k:ℚ)+b)*coeff k f := by
  have he : ode a b c f =
      Xq * D (D f) + C c * D f - Xq * D (Xq * D f) -
      C a * (Xq * D f) - C b * (Xq * D f) - C (a*b)*f := by
    simp only [ode, Derivation.leibniz, derivative_X, smul_eq_mul, mul_one,
      map_add, map_one]
    ring
  rw [he]
  simp only [map_sub, map_add, coeff_X_D, coeff_C_mul, coeff_derivative]
  ring

lemma ode_hg (a b c : ℚ) (hc : 0 < c) : ode a b c (hg a b c) = 0 := by
  ext k
  simp only [coeff_ode, coeff_hg, map_zero]
  exact sub_eq_zero.mpr (hgCoeff_succ a b c hc k)

lemma ode_unique (a b c : ℚ) (hc : 0 < c) (f g : PowerSeries ℚ)
    (hf : ode a b c f = 0) (hg : ode a b c g = 0)
    (h0 : coeff 0 f = coeff 0 g) : f = g := by
  ext k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hf' := congrArg (coeff k) hf
    have hg' := congrArg (coeff k) hg
    rw [coeff_ode, map_zero] at hf' hg'
    have hk : ((k:ℚ)+1)*((k:ℚ)+c) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hk)
    rw [sub_eq_zero.mp hf', sub_eq_zero.mp hg', ih]

lemma power_deriv (L : ℕ) :
    (1-Xq) * D ((1-Xq)^L) = -C (L:ℚ)*(1-Xq)^L := by
  cases L with
  | zero => simp
  | succ L =>
    rw [Derivation.leibniz_pow, map_sub]
    simp only [Derivation.map_one_eq_zero, derivative_X, zero_sub, smul_eq_mul, nsmul_eq_mul]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one, Nat.add_sub_cancel]
    rw [pow_succ]
    ring

lemma power_deriv2 (L : ℕ) :
    (1-Xq)^2 * D (D ((1-Xq)^L)) = C ((L:ℚ)*((L:ℚ)-1))*(1-Xq)^L := by
  have h := congrArg D (power_deriv L)
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X, zero_sub,
    map_neg, derivative_C, neg_zero, smul_eq_mul] at h
  have h' := congrArg (fun f : PowerSeries ℚ => (1-Xq)*f) h
  have h1 := power_deriv L
  simp only [map_mul, map_sub, map_natCast, map_one] at *
  linear_combination h' - ((L:PowerSeries ℚ)-1)*h1

lemma ode_euler (a b c : ℚ) (L : ℕ) (hL : (L:ℚ) = a+b-c)
    (f : PowerSeries ℚ) (hf : ode a b c f = 0) :
    ode (c-a) (c-b) c ((1-Xq)^L * f) = 0 := by
  have h1 := power_deriv L
  have h2 := power_deriv2 L
  have hn : (1-Xq : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    norm_num at this
  apply (mul_left_cancel₀ hn)
  rw [mul_zero]
  unfold ode at *
  simp only [Derivation.leibniz, map_add, smul_eq_mul] 
  simp only [map_add, map_sub, map_mul, map_one, hL] at h1 h2 hf ⊢
  -- Polynomial identity giving the conjugation of the differential equation.
  linear_combination (1-Xq)^L * (1-Xq) * hf +
    (2*Xq*(1-Xq)*D f + (C c - (2*C c-C a-C b+1)*Xq)*f) * h1 + Xq*f*h2

/-- Euler's transformation, proved using the formal differential equation. -/
lemma hg_euler (a b c : ℚ) (hc : 0 < c) (L : ℕ) (hL : (L:ℚ) = a+b-c) :
    (1-Xq)^L * hg a b c = hg (c-a) (c-b) c := by
  apply ode_unique (c-a) (c-b) c hc
  · exact ode_euler a b c L hL _ (ode_hg a b c hc)
  · exact ode_hg (c-a) (c-b) c hc
  · simp [hg, hgCoeff]

lemma rf_one (k : ℕ) : rf 1 k = (k.factorial:ℚ) := by
  exact ascPochhammer_eval_one ℚ k

lemma rf_nat (n k : ℕ) : rf ((n:ℚ)+1) k = ((n+k).factorial:ℚ) / n.factorial := by
  apply (eq_div_iff (by positivity : (n.factorial:ℚ) ≠ 0)).mpr
  simpa only [rf, mul_comm] using factorial_mul_ascPochhammer ℚ n k

lemma rf_neg (n k : ℕ) : rf (-(n:ℚ)) k = (-1)^k * (n.descFactorial k:ℚ) := by
  simp only [rf, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial]

lemma rf_double (x : ℚ) (k : ℕ) :
    rf x (2*k) = 4^k * rf (x/2) k * rf ((x+1)/2) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = 2*k+1+1 by omega, rf_succ, rf_succ, ih,
      rf_succ, rf_succ, pow_succ]
    push_cast
    ring

lemma hgCoeff_nat (n k : ℕ) :
    hgCoeff ((n:ℚ)+1) ((n:ℚ)+1) 1 k = (Nat.choose (n+k) n:ℚ)^2 := by
  rw [hgCoeff, rf_one, rf_nat, Nat.cast_choose ℚ (by omega : n ≤ n+k)]
  rw [Nat.add_sub_cancel_left]
  ring

lemma hgCoeff_neg (n k : ℕ) :
    hgCoeff (-(n:ℚ)) (-(n:ℚ)) 1 k = (Nat.choose n k:ℚ)^2 := by
  rw [hgCoeff, rf_one, rf_neg, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hk : (k.factorial:ℚ) ≠ 0 := by positivity
  have hs : ((-1:ℚ)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  field_simp
  linear_combination (Nat.choose n k:ℚ)^2 * hs

lemma hgCoeff_half (x : ℚ) (n k : ℕ) :
    hgCoeff (x/2) ((x+1)/2) ((n:ℚ)+1/2) k =
      rf x (2*k) * (n+k).factorial * (2*n).factorial /
        ((2*n+2*k).factorial * (n.factorial:ℚ) * k.factorial) := by
  have hx := rf_double x k
  have hy := rf_double ((2*n:ℕ)+1) k
  have hr : rf (((2*n:ℕ):ℚ)+1) (2*k) =
      ((2*n+2*k).factorial:ℚ) / (2*n).factorial := rf_nat (2*n) (2*k)
  push_cast at hy hr
  rw [show ((2*(n:ℚ)+1)+1)/2 = (n:ℚ)+1 by ring,
    show (2*(n:ℚ)+1)/2 = (n:ℚ)+1/2 by ring, rf_nat] at hy
  rw [hr] at hy
  have hnc : rf ((n:ℚ)+1/2) k ≠ 0 := ne_of_gt (rf_pos (by positivity) k)
  have hf (j : ℕ) : (j.factorial:ℚ) ≠ 0 := by positivity
  unfold hgCoeff
  apply (div_eq_div_iff (mul_ne_zero hnc (hf k)) (by positivity)).mpr
  field_simp at hy
  rw [show ((n:ℚ)*2+1)/2 = (n:ℚ)+1/2 by ring] at hy
  field_simp
  -- use the duplication identities, without cancelling a possibly zero numerator
  calc
    _ = (4^k * rf (x/2) k * rf ((x+1)/2) k) *
        ((n+k).factorial:ℚ) * (2*n).factorial * rf ((n:ℚ)+1/2) k := by
      linear_combination rf (x/2) k * rf ((x+1)/2) k * hy
    _ = _ := by rw [← hx, show (2*(n:ℚ)+1)/2 = (n:ℚ)+1/2 by ring]

lemma hgCoeff_comm (a b c : ℚ) (k : ℕ) : hgCoeff a b c k = hgCoeff b a c k := by
  unfold hgCoeff; ring

lemma hgCoeff_original (n k : ℕ) :
    (Nat.choose (3*n) n:ℚ) *
      hgCoeff ((3*(n:ℚ)+1)/2) ((3*(n:ℚ)+2)/2) ((n:ℚ)+1/2) k =
    (Nat.choose (n+k) k:ℚ) * Nat.choose (3*n+2*k) n := by
  rw [show (3*(n:ℚ)+2)/2 = ((3*(n:ℚ)+1)+1)/2 by ring, hgCoeff_half]
  rw [show 3*(n:ℚ)+1 = ((3*n:ℕ):ℚ)+1 by push_cast; ring, rf_nat]
  rw [Nat.cast_choose ℚ (by omega : n ≤ 3*n),
    Nat.cast_choose ℚ (by omega : k ≤ n+k),
    Nat.cast_choose ℚ (by omega : n ≤ 3*n+2*k)]
  rw [show 3*n-n = 2*n by omega, show n+k-k = n by omega,
    show 3*n+2*k-n = 2*n+2*k by omega]
  field_simp

noncomputable def q (n k : ℕ) : ℚ :=
  hgCoeff (-(n:ℚ)/2) (-((n:ℚ)+1)/2) ((n:ℚ)+1/2) k

lemma q_eq (n k : ℕ) :
    q n k = ( (n+1).descFactorial (2*k):ℚ) * (n+k).factorial * (2*n).factorial /
      ((2*n+2*k).factorial * (n.factorial:ℚ) * k.factorial) := by
  unfold q
  rw [hgCoeff_comm]
  rw [show -(n:ℚ)/2 = (-((n:ℚ)+1)+1)/2 by ring, hgCoeff_half]
  rw [show -((n:ℚ)+1) = -((n+1:ℕ):ℚ) by push_cast; ring, rf_neg]
  simp only [pow_mul, neg_one_sq, one_pow, one_mul]

lemma q_zero {n k : ℕ} (h : n+1 < 2*k) : q n k = 0 := by
  rw [q_eq, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

/-- The common Euler factor cancels between these two series. -/
lemma series_transform (n : ℕ) :
    hg ((3*(n:ℚ)+1)/2) ((3*(n:ℚ)+2)/2) ((n:ℚ)+1/2) * hg (-(n:ℚ)) (-(n:ℚ)) 1 =
      hg (-(n:ℚ)/2) (-((n:ℚ)+1)/2) ((n:ℚ)+1/2) * hg ((n:ℚ)+1) ((n:ℚ)+1) 1 := by
  have h1 := hg_euler ((3*(n:ℚ)+1)/2) ((3*(n:ℚ)+2)/2) ((n:ℚ)+1/2)
    (by positivity) (2*n+1) (by push_cast; ring)
  have h2 := hg_euler ((n:ℚ)+1) ((n:ℚ)+1) 1 (by norm_num)
    (2*n+1) (by push_cast; ring)
  rw [show (n:ℚ)+1/2 - (3*(n:ℚ)+1)/2 = -(n:ℚ)/2 by ring,
    show (n:ℚ)+1/2 - (3*(n:ℚ)+2)/2 = -((n:ℚ)+1)/2 by ring] at h1
  rw [show (1:ℚ)-((n:ℚ)+1) = -(n:ℚ) by ring] at h2
  rw [← h1, ← h2]
  ring

lemma sum_transform (n : ℕ) :
    (∑ k ∈ range (n+1), (Nat.choose n k:ℚ)^2 * Nat.choose (n+k) k * Nat.choose (3*n+2*k) n) =
    ∑ k ∈ range (n+1), (Nat.choose (3*n) n:ℚ) * q n k * (Nat.choose (2*n-k) n:ℚ)^2 := by
  have h := congrArg (coeff n) (series_transform n)
  simp only [coeff_mul, coeff_hg, hgCoeff_nat, hgCoeff_neg] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have h' := congrArg (fun x : ℚ => (Nat.choose (3*n) n:ℚ)*x) h
  simp only [mul_sum] at h'
  calc
    _ = ∑ k ∈ range (n+1), (Nat.choose (3*n) n:ℚ) *
        (hgCoeff ((3*(n:ℚ)+1)/2) ((3*(n:ℚ)+2)/2) ((n:ℚ)+1/2) k *
          (Nat.choose n (n-k):ℚ)^2) := by
      apply sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by simpa using mem_range.mp hk
      rw [Nat.choose_symm hkn]
      rw [← mul_assoc, hgCoeff_original]
      ring
    _ = _ := by
      rw [h']
      apply sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by simpa using mem_range.mp hk
      rw [show n+(n-k) = 2*n-k by omega]
      simp only [q, mul_assoc]

noncomputable def term (n k : ℕ) : ℚ :=
  (Nat.choose (3*n) n:ℚ) * q n k * (Nat.choose (2*n-k) n:ℚ)^2

lemma cast_descFactorial {n k : ℕ} (h : k ≤ n) :
    (n.descFactorial k:ℚ) = (n.factorial:ℚ) / (n-k).factorial := by
  apply (eq_div_iff (by positivity : ((n-k).factorial:ℚ) ≠ 0)).mpr
  have hh := Nat.factorial_mul_descFactorial h
  exact_mod_cast (mul_comm _ _).trans hh

/-- A factorial expression for each nonzero transformed summand. -/
lemma term_eq {n k : ℕ} (hkn : k ≤ n) (hk : 2*k ≤ n+1) :
    term n k =
      ((3*n).factorial:ℚ) * (n+1).factorial * (n+k).factorial * ((2*n-k).factorial:ℚ)^2 /
      ((n.factorial:ℚ)^4 * (n+1-2*k).factorial * (2*n+2*k).factorial * k.factorial * ((n-k).factorial:ℚ)^2) := by
  rw [term, q_eq, cast_descFactorial hk,
    Nat.cast_choose ℚ (by omega : n ≤ 3*n),
    Nat.cast_choose ℚ (by omega : n ≤ 2*n-k)]
  rw [show 3*n-n = 2*n by omega, show 2*n-k-n = n-k by omega]
  field_simp

/-- Below p², Legendre’s formula has just one nonzero summand. -/
lemma val_factorial {p m : ℕ} [Fact p.Prime] (hm : m < p^2) :
    padicValRat p (m.factorial:ℚ) = (m/p:ℕ) := by
  rw [padicValRat.of_nat]
  by_cases hz : m = 0
  · simp [hz]
  · rw [padicValNat_factorial (Nat.log_lt_of_lt_pow hz hm)]
    norm_num [show Ico 1 2 = ({1}:Finset ℕ) by decide]

lemma val_term {p n k : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hn : 2*p+1 ≤ 3*n) (hnp : n < p) (hkn : k ≤ n) (hk : 2*k ≤ n+1) :
    3 ≤ padicValRat p (term n k) := by
  have hsq : 3*n+1 < p^2 := by nlinarith
  have h3 : (3*n)/p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h2 : (2*n-k)/p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h0 : n/p = 0 := Nat.div_eq_of_lt hnp
  have hk0 : k/p = 0 := Nat.div_eq_of_lt (by omega)
  have hnk0 : (n-k)/p = 0 := Nat.div_eq_of_lt (by omega)
  -- The possible extra factor of p in (2n+2k)! is supplied by (n+k)!.
  have hrel : (2*n+2*k)/p = (n+k)/p + 1 := by
    by_cases h : n+k < p
    · rw [Nat.div_eq_of_lt h]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · have ha : (n+k)/p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [ha]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hmono : (n+1-2*k)/p ≤ (n+1)/p := Nat.div_le_div_right (by omega)
  rw [term_eq hkn hk]
  simp (disch := positivity) only [padicValRat.div, padicValRat.mul, padicValRat.pow]
  rw [val_factorial (by omega : 3*n < p^2),
    val_factorial (by omega : n+1 < p^2),
    val_factorial (by omega : n+k < p^2),
    val_factorial (by omega : 2*n-k < p^2),
    val_factorial (by omega : n < p^2),
    val_factorial (by omega : n+1-2*k < p^2),
    val_factorial (by omega : 2*n+2*k < p^2),
    val_factorial (by omega : k < p^2),
    val_factorial (by omega : n-k < p^2)]
  rw [h3, h2, h0, hk0, hnk0, hrel]
  omega

lemma sum_val {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ) (m : ℤ)
    (h : ∀ k ∈ s, f k = 0 ∨ m ≤ padicValRat p (f k)) :
    (∑ k ∈ s, f k) = 0 ∨ m ≤ padicValRat p (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha]
    have hs := ih (fun k hk => h k (mem_insert_of_mem hk))
    have ht := h a (mem_insert_self a s)
    rcases hs with hs | hs
    · simpa only [hs, add_zero] using ht
    rcases ht with ht | ht
    · simpa only [ht, zero_add] using Or.inr hs
    by_cases hz : f a + ∑ k ∈ s, f k = 0
    · exact Or.inl hz
    · exact Or.inr ((le_min ht hs).trans (padicValRat.min_le_padicValRat_add hz))

lemma divisible_sum {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 2*p+1 ≤ 3*n) (hnp : n < p) :
    p^3 ∣ (∑ k ∈ range (n+1), (Nat.choose n k)^2 * Nat.choose (n+k) k * Nat.choose (3*n+2*k) n) := by
  letI : Fact p.Prime := ⟨hp⟩
  have ht : ∀ k ∈ range (n+1), term n k = 0 ∨ 3 ≤ padicValRat p (term n k) := by
    intro k hkm
    have hkn : k ≤ n := by simpa using mem_range.mp hkm
    by_cases hk : 2*k ≤ n+1
    · exact Or.inr (val_term hp5 hn hnp hkn hk)
    · left
      simp [term, q_zero (by omega : n+1 < 2*k)]
  have hs := sum_val (range (n+1)) (term n) 3 ht
  have he : (∑ k ∈ range (n+1), term n k) =
      ((∑ k ∈ range (n+1), (Nat.choose n k)^2 * Nat.choose (n+k) k * Nat.choose (3*n+2*k) n):ℕ) := by
    push_cast
    exact (sum_transform n).symm
  rw [he] at hs
  rw [padicValNat_dvd_iff]
  rcases hs with hs | hs
  · left
    exact_mod_cast hs
  · right
    rw [padicValRat.of_nat] at hs
    exact_mod_cast hs

end A374605

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn hn'
  have hlo : 2 * p + 1 ≤ 3 * n := by omega
  have hhi : n < p := by omega
  simpa only [a] using A374605.divisible_sum hp hp5 hlo hhi

theorem oeis_374605_conjecture_0.disproof : ¬ (type_of% @oeis_374605_conjecture_0) := sorry
