import FormalConjectures.Util.ProblemImports

open scoped Real BigOperators
open Finset

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

/-! ### Bridge: `a n` equals an explicit factorial/product rational. -/

noncomputable def Preal (n : ℕ) : ℝ := ∏ j ∈ range (3*n), ((3*(n:ℝ)+1+2*j))

lemma gamma_ne (x : ℝ) (hx : 0 < x) : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'

lemma dup (c : ℕ) (n : ℕ) :
    Real.Gamma (c / 2 * (n:ℝ) + 1) * Real.Gamma ((c*(n:ℝ)+1)/2)
      = Real.Gamma (c*(n:ℝ)+1) * (2:ℝ)^(-(c*(n:ℝ))) * Real.sqrt π := by
  have h := Real.Gamma_mul_Gamma_add_half ((c*(n:ℝ)+1)/2)
  rw [show (c*(n:ℝ)+1)/2 + 1/2 = c/2*(n:ℝ)+1 by ring,
      show 2*((c*(n:ℝ)+1)/2) = c*(n:ℝ)+1 by ring,
      show (1:ℝ) - (c*(n:ℝ)+1) = -(c*(n:ℝ)) by ring] at h
  rw [mul_comm (Real.Gamma (c / 2 * (n:ℝ) + 1)) (Real.Gamma ((c*(n:ℝ)+1)/2))]
  exact h

lemma gamma_add_nat (x : ℝ) (k : ℕ) (hx : ∀ j : ℕ, x + j ≠ 0) :
    Real.Gamma (x + k) = Real.Gamma x * ∏ j ∈ range k, (x + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk : x + (k:ℝ) ≠ 0 := hx k
    rw [prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ,
        show x + ((k:ℝ)+1) = (x + (k:ℝ)) + 1 by ring, Real.Gamma_add_one hxk, mul_comm]

lemma H3_ne (n : ℕ) : Real.Gamma ((3*(n:ℝ)+1)/2) ≠ 0 := by apply gamma_ne; positivity
lemma H9_ne (n : ℕ) : Real.Gamma ((9*(n:ℝ)+1)/2) ≠ 0 := by apply gamma_ne; positivity

lemma H9_eq (n : ℕ) :
    Real.Gamma ((9*(n:ℝ)+1)/2) = Real.Gamma ((3*(n:ℝ)+1)/2) * ∏ j ∈ range (3*n), ((3*(n:ℝ)+1)/2 + j) := by
  have := gamma_add_nat ((3*(n:ℝ)+1)/2) (3*n) (by
    intro j; have : (0:ℝ) < (3*(n:ℝ)+1)/2 + j := by positivity
    exact this.ne')
  rw [show (3*(n:ℝ)+1)/2 + (3*n : ℕ) = (9*(n:ℝ)+1)/2 by push_cast; ring] at this
  exact this

lemma g3half (n : ℕ) :
    Real.Gamma (3 / 2 * (n:ℝ) + 1)
      = Real.Gamma (3*(n:ℝ)+1) * (2:ℝ)^(-(3*(n:ℝ))) * Real.sqrt π / Real.Gamma ((3*(n:ℝ)+1)/2) := by
  have h := dup 3 n
  norm_num at h ⊢
  rw [eq_div_iff (H3_ne n)]; linear_combination h

lemma g9half (n : ℕ) :
    Real.Gamma (9 / 2 * (n:ℝ) + 1)
      = Real.Gamma (9*(n:ℝ)+1) * (2:ℝ)^(-(9*(n:ℝ))) * Real.sqrt π / Real.Gamma ((9*(n:ℝ)+1)/2) := by
  have h := dup 9 n
  norm_num at h ⊢
  rw [eq_div_iff (H9_ne n)]; linear_combination h

lemma two_negrpow (k : ℕ) : (2:ℝ)^(-(k:ℝ)) = ((2:ℝ)^k)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

lemma prod_half (n : ℕ) :
    (∏ j ∈ range (3*n), ((3*(n:ℝ)+1)/2 + j)) * 2^(3*n) = Preal n := by
  rw [Preal, show (2:ℝ)^(3*n) = ∏ _j ∈ range (3*n), (2:ℝ) by rw [prod_const, card_range],
      ← prod_mul_distrib]
  apply prod_congr rfl; intro j _; ring

lemma two_neg3 (n:ℕ) : (2:ℝ)^(-(3*(n:ℝ))) = ((2:ℝ)^(3*n))⁻¹ := by
  rw [show 3*(n:ℝ) = ((3*n:ℕ):ℝ) by push_cast; ring, two_negrpow]
lemma two_neg9 (n:ℕ) : (2:ℝ)^(-(9*(n:ℝ))) = ((2:ℝ)^(9*n))⁻¹ := by
  rw [show 9*(n:ℝ) = ((9*n:ℕ):ℝ) by push_cast; ring, two_negrpow]

theorem a_eq (n : ℕ) :
    a n = 2^(3*n) * (Nat.factorial (2*n)) * Preal n / ((Nat.factorial (4*n)) * (Nat.factorial n)) := by
  have e2 : Real.Gamma (2*(n:ℝ)+1) = (Nat.factorial (2*n)) := by
    rw [show 2*(n:ℝ)+1 = ((2*n:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have e4 : Real.Gamma (4*(n:ℝ)+1) = (Nat.factorial (4*n)) := by
    rw [show 4*(n:ℝ)+1 = ((4*n:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have e1 : Real.Gamma ((n:ℝ)+1) = (Nat.factorial n) := by
    rw [show (n:ℝ)+1 = ((n:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have hg9 : Real.Gamma (9*(n:ℝ)+1) ≠ 0 := by apply gamma_ne; positivity
  have hg3 : Real.Gamma (3*(n:ℝ)+1) ≠ 0 := by apply gamma_ne; positivity
  have hsqrtpi : Real.sqrt π ≠ 0 := by positivity
  have hf4 : (Nat.factorial (4*n) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have hf1 : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have hph : (∏ j ∈ range (3*n), ((3*(n:ℝ)+1)/2 + j)) * 2^(3*n) = Preal n := prod_half n
  have h2a : ((2:ℝ)^(3*n)) ≠ 0 := by positivity
  have h2b : ((2:ℝ)^(9*n)) ≠ 0 := by positivity
  have hh3 : Real.Gamma ((3*(n:ℝ)+1)/2) ≠ 0 := H3_ne n
  unfold a
  simp only
  rw [g3half, g9half, H9_eq n, e2, e4, e1, two_neg3, two_neg9, ← hph]
  field_simp
  ring

noncomputable def Rrat (n : ℕ) : ℚ :=
  2^(3*n) * (Nat.factorial (2*n)) * (∏ j ∈ range (3*n), ((3*(n:ℚ)+1+2*j))) / ((Nat.factorial (4*n)) * (Nat.factorial n))

lemma Rrat_cast (n : ℕ) : ((Rrat n : ℚ) : ℝ) = a n := by
  rw [a_eq n, Rrat]; push_cast [Preal]; ring

/-! ### Core supercongruence (the arithmetic heart). -/

/-- Single-level supercongruence, the arithmetic heart: writing `A(m)` for the integer value
of `a m`, this expresses `A(m*p) ≡ A(m) (mod p^(3*(1+v_p(m))))`. The full multi-level
conjecture reduces to this by a p-adic telescoping. -/
lemma single (p m : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : 0 < m)
    (D : ℤ) (hD : (D : ℚ) = Rrat (m * p) - Rrat m) :
    (p : ℤ) ^ (3 * (1 + padicValNat p m)) ∣ D := by
  sorry

lemma core (p n r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r)
    (D : ℤ) (hD : (D : ℚ) = Rrat (n * p ^ r) - Rrat (n * p ^ (r - 1))) :
    (p : ℤ) ^ (3 * r) ∣ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpp : (0:ℕ) < p := hp.pos
  have hp_pow : p ^ r = p ^ (r-1) * p := by
    rw [← pow_succ]; congr 1; omega
  have hsplit : n * p ^ r = (n * p ^ (r-1)) * p := by
    rw [hp_pow]; ring
  have hD' : (D : ℚ) = Rrat ((n * p ^ (r-1)) * p) - Rrat (n * p ^ (r-1)) := by
    rw [hD, hsplit]
  have hm : 0 < n * p ^ (r-1) := by positivity
  have hdvd := single p (n * p ^ (r-1)) hp h5 hm D hD'
  have hv : r - 1 ≤ padicValNat p (n * p ^ (r-1)) := by
    rw [padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow]
    omega
  have hle : 3 * r ≤ 3 * (1 + padicValNat p (n * p ^ (r-1))) := by omega
  exact dvd_trans (pow_dvd_pow (p:ℤ) hle) hdvd

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
by
  intro p hp h5 n r hn hr
  have hspec : ∀ k, ((Classical.choose (h_int k) : ℤ) : ℝ) = a k :=
    fun k => Classical.choose_spec (h_int k)
  have hXQ : ∀ k, ((Classical.choose (h_int k) : ℤ) : ℚ) = Rrat k := by
    intro k
    apply (Rat.cast_injective (α := ℝ))
    rw [Rat.cast_intCast, hspec k, ← Rrat_cast k]
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
  apply core p n r hp h5 hn hr
  rw [Int.cast_sub, hXQ, hXQ]
