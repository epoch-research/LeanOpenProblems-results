import Submission.Arithmetic

/-!
# Exact censored greatest-prime-factor comparisons

This is prerequisite arithmetic, not a proof of Erdős 371. The censor threshold
is real, while the signs and inclusive prefix sums are integer-valued. We use
the actual `Nat.maxPrimeFac`, including `P(1) = 1`, and the three-valued
`signedComparison` from `Submission.Arithmetic`: a tied gap contributes zero.

The notation in the companion notes is represented by `F y a b`, `h y n`,
and `J y X`. The finite von Mangoldt renewal is also proved with all floors
and actual endpoints retained. No density, source bound, or analytic half-kernel
estimate is assumed or concluded.
-/

set_option autoImplicit false

noncomputable section

namespace Erdos371.CensoredComparison

/-- `F_y(a,b)`: the signed comparison of the actual labels, censored at `y`. -/
def F (y : ℝ) (a b : ℕ) : ℤ :=
  if y < (max (Nat.maxPrimeFac a) (Nat.maxPrimeFac b) : ℕ) then
    signedComparison (Nat.maxPrimeFac a) (Nat.maxPrimeFac b)
  else 0

/-- `h_y(n)`: the censored unit edge, retaining the endpoint `n + 1`. -/
def h (y : ℝ) (n : ℕ) : ℤ := F y n (n + 1)

/-- `J_y(X)`: the inclusive ordinary prefix from one through `X`. -/
def J (y : ℝ) (X : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 X, h y n

@[simp]
theorem F_self (y : ℝ) (a : ℕ) : F y a a = 0 := by
  simp [F]

/-- A label tie is zero even if the censor test itself succeeds. -/
theorem F_eq_zero_of_labels_eq {y : ℝ} {a b : ℕ}
    (hab : Nat.maxPrimeFac a = Nat.maxPrimeFac b) : F y a b = 0 := by
  simp [F, hab]

theorem F_eq_zero_of_max_le {y : ℝ} {a b : ℕ}
    (hmax : (max (Nat.maxPrimeFac a) (Nat.maxPrimeFac b) : ℕ) ≤ y) :
    F y a b = 0 := by
  exact if_neg (not_lt_of_ge hmax)

/-- Censoring after a common maximum is exactly raising the censor state. -/
theorem signedComparison_censor_max (y : ℝ) (a b c : ℕ) :
    (if y < (max (max c a) (max c b) : ℕ) then
      signedComparison (max c a) (max c b) else 0) =
    if max y (c : ℝ) < (max a b : ℕ) then signedComparison a b else 0 := by
  rw [signedComparison_max]
  by_cases hc : c < max a b
  · have hmax : max (max c a) (max c b) = max a b := by
      simp only [max_def] at hc ⊢
      split_ifs at hc ⊢ <;> omega
    have hcR : (c : ℝ) < (max a b : ℕ) := by exact_mod_cast hc
    rw [if_pos hc, hmax]
    simp only [max_lt_iff, hcR, and_true]
  · have hcR : ¬ (c : ℝ) < (max a b : ℕ) := by exact_mod_cast hc
    have hnot : ¬ max y (c : ℝ) < (max a b : ℕ) := by
      intro hlt
      exact hcR ((le_max_right _ _).trans_lt hlt)
    simp only [if_neg hc, if_neg hnot, ite_self]

/-- Exact transport for every positive multiplier and positive pair.
There is no fixed-multiplier or asymptotic restriction. -/
theorem F_mul (y : ℝ) {k a b : ℕ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) :
    F y (k * a) (k * b) = F (max y (Nat.maxPrimeFac k : ℝ)) a b := by
  unfold F
  rw [maxPrimeFac_mul_of_pos hk ha, maxPrimeFac_mul_of_pos hk hb]
  exact signedComparison_censor_max y _ _ _

/-- The multiplied unit edge has gap `k`, not gap one. -/
theorem F_mul_gap (y : ℝ) {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    F y (k * n) (k * n + k) = h (max y (Nat.maxPrimeFac k : ℝ)) n := by
  have heq : k * n + k = k * (n + 1) := by ring
  rw [heq, F_mul y hk hn (by omega)]
  rfl

/-- The exact divisor specialization, with the actual endpoint `n + k`.
It is not truncated at any ambient prefix cutoff. -/
theorem F_divisor_gap (y : ℝ) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkn : k ∣ n) :
    F y n (n + k) = h (max y (Nat.maxPrimeFac k : ℝ)) (n / k) := by
  have hquot : 0 < n / k := Nat.div_pos (Nat.le_of_dvd hn hkn) hk
  have heq : k * (n / k) = n := Nat.mul_div_cancel' hkn
  simpa only [heq] using F_mul_gap y hk hquot

/-- At censor one, every positive unit edge survives, including `n = 1`. -/
theorem h_one {n : ℕ} (hn : 1 ≤ n) : h 1 n = comparisonSign n := by
  have hp : 1 < Nat.maxPrimeFac (n + 1) :=
    (Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)).one_lt
  have hmax : 1 < max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) :=
    hp.trans_le (le_max_right _ _)
  have hmaxR : (1 : ℝ) < (max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) :=
    by exact_mod_cast hmax
  unfold h F
  rw [if_pos hmaxR, signedComparison_adjacent]

@[simp]
theorem h_one_at_one : h 1 1 = 1 := by
  rw [h_one (by omega)]
  norm_num [comparisonSign, Nat.prime_two.maxPrimeFac_eq_self]

/-- The matched inclusive endpoint is `N` on both sides. The extra one is
exactly the omitted `n = 1` term of `comparisonSum`. -/
theorem J_one {N : ℕ} (hN : 1 ≤ N) : J 1 N = comparisonSum N + 1 := by
  unfold J
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) :=
    (Finset.insert_Icc_add_one_left_eq_Icc hN).symm
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [h_one_at_one]
  have hsum : (∑ n ∈ Finset.Icc 2 N, h 1 n) = comparisonSum N := by
    unfold comparisonSum
    apply Finset.sum_congr rfl
    intro n hn
    exact h_one (by have := (Finset.mem_Icc.mp hn).1; omega)
  rw [hsum, add_comm]

/- ## Child support, with both endpoints retained -/

@[simp]
theorem J_zero (y : ℝ) : J y 0 = 0 := by simp [J]

/-- Both labels of the unit edge are at most its right endpoint. -/
theorem unit_edge_max_le_endpoint (n : ℕ) :
    max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ≤ n + 1 := by
  exact max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le

/-- A unit edge is killed if its right endpoint is at most the censor. -/
theorem h_eq_zero_of_endpoint_le {y : ℝ} {n : ℕ} (hn : (n + 1 : ℕ) ≤ y) :
    h y n = 0 := by
  apply F_eq_zero_of_max_le
  have hlabels : (max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) ≤
      ((n + 1 : ℕ) : ℝ) := by exact_mod_cast unit_edge_max_le_endpoint n
  exact hlabels.trans hn

/-- Retaining the final `X + 1` endpoint is essential in this support bound. -/
theorem J_eq_zero_of_endpoint_le {y : ℝ} {X : ℕ} (hX : (X + 1 : ℕ) ≤ y) :
    J y X = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply h_eq_zero_of_endpoint_le
  have hnX : n + 1 ≤ X + 1 := Nat.add_le_add_right (Finset.mem_Icc.mp hn).2 1
  exact (by exact_mod_cast hnX : (n + 1 : ℕ) ≤ ((X + 1 : ℕ) : ℝ)).trans hX

/-- If the next prime power exceeds `X`, the inclusive child has right
endpoint at most `p`. This also holds for exponent zero. -/
theorem primePower_child_endpoint_le {p a X : ℕ} (hp : p.Prime)
    (hX : X < p ^ (a + 1)) : X / p ^ a + 1 ≤ p := by
  have ht : X / p ^ a < p :=
    (Nat.div_lt_iff_lt_mul (pow_pos hp.pos a)).mpr
      (by simpa only [pow_succ, mul_comm] using hX)
  omega

/-- Every label in every child edge, including the last right endpoint,
is at most the actual prime color. -/
theorem primePower_child_labels_le {p a X m : ℕ} (hp : p.Prime)
    (hX : X < p ^ (a + 1)) (hm : m ≤ X / p ^ a) :
    max (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) ≤ p := by
  exact (unit_edge_max_le_endpoint m).trans
    ((Nat.add_le_add_right hm 1).trans (primePower_child_endpoint_le hp hX))

/-- Exact annihilation of the prime-colored child prefix; no estimate or
limiting fixed-prime law is used. -/
theorem J_primePower_child_eq_zero (y : ℝ) {p a X : ℕ} (hp : p.Prime)
    (hX : X < p ^ (a + 1)) : J (max y (p : ℝ)) (X / p ^ a) = 0 := by
  apply J_eq_zero_of_endpoint_le
  have ht : (X / p ^ a + 1 : ℕ) ≤ (p : ℝ) :=
    by exact_mod_cast primePower_child_endpoint_le hp hX
  exact ht.trans (le_max_right _ _)

/-- For a positive exponent this is the child at the multiplier's actual
color `P(p^a) = p`. Exponent zero is excluded because `P(1) = 1`. -/
theorem J_primePower_actual_color_eq_zero (y : ℝ) {p a X : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hX : X < p ^ (a + 1)) :
    J (max y (Nat.maxPrimeFac (p ^ a) : ℝ)) (X / p ^ a) = 0 := by
  rw [Nat.maxPrimeFac_pow (by omega) p, hp.maxPrimeFac_eq_self]
  exact J_primePower_child_eq_zero y hp hX

/-- In particular, the prime part of a finite renewal has support `p² ≤ X`. -/
theorem J_prime_child_eq_zero (y : ℝ) {p X : ℕ} (hp : p.Prime)
    (hX : X < p ^ 2) : J (max y (p : ℝ)) (X / p) = 0 := by
  simpa only [pow_one] using J_primePower_child_eq_zero y (a := 1) hp hX

/-- Exact finite change of variables `n = k * m`, over positive integers. -/
theorem sum_divisors_reindex {M : Type*} [AddCommMonoid M] (X : ℕ) (f : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, f k (n / k)) =
    ∑ k ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 (X / k), f k m := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun q _ => ⟨q.2, q.1 / q.2⟩)
    (fun q _ => ⟨q.1 * q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, k⟩ hnk
    obtain ⟨hn, hk⟩ := Finset.mem_sigma.mp hnk
    dsimp at hn hk ⊢
    have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hkn : k ∣ n := Nat.dvd_of_mem_divisors hk
    have hkN : k ≤ n := Nat.le_of_dvd hn0 hkn
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hk0, hkN.trans (Finset.mem_Icc.mp hn).2⟩,
      Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Nat.succ_le_of_lt (Nat.div_pos hkN hk0)
    · exact Nat.div_le_div_right (Finset.mem_Icc.mp hn).2
  · rintro ⟨k, m⟩ hkm
    obtain ⟨hk, hm⟩ := Finset.mem_sigma.mp hkm
    dsimp at hk hm ⊢
    have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
    have hprod : k * m ≤ X := by
      simpa only [mul_comm] using
        (Nat.le_div_iff_mul_le hk0).mp (Finset.mem_Icc.mp hm).2
    have hprod0 : 0 < k * m := Nat.mul_pos hk0 hm0
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hprod0, hprod⟩,
      Nat.mem_divisors.mpr ⟨⟨m, rfl⟩, hprod0.ne'⟩⟩
  · rintro ⟨n, k⟩ hnk
    have hkn := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hnk).2
    dsimp
    rw [Nat.mul_div_cancel' hkn]
  · rintro ⟨k, m⟩ hkm
    have hk0 : 0 < k := by
      have hk := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hkm).1).1
      dsimp at hk
      omega
    dsimp
    rw [Nat.mul_div_cancel_left m hk0]
  · rintro ⟨n, k⟩ _
    rfl

/- ## Exact finite von Mangoldt renewal (no analytic estimate) -/

/-- The signed local unit-neighbor versus divisor-neighbor source.
The second endpoint is the actual `n + k`, even when it exceeds `X` in a prefix. -/
def e (y : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ n.divisors, ArithmeticFunction.vonMangoldt k *
    ((h y n : ℝ) - (F y n (n + k) : ℝ))

/-- The inclusive ordinary prefix of the signed local source. -/
def E (y : ℝ) (X : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 X, e y n

/-- The exact logarithmic endpoint remainder. The quotient here is real,
not natural-number division. No remainder estimate is asserted. -/
def R (y : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, (h y n : ℝ) * Real.log ((X : ℝ) / n)

/-- The full finite divisor-convolution kernel, with actual variable colors
and natural-number floors. No half-mass estimate is asserted. -/
def kernel (y : ℝ) (X : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k *
    (J (max y (Nat.maxPrimeFac k : ℝ)) (X / k) : ℝ)

/-- Pointwise logarithmic-divisor partition with exact color transport. -/
theorem e_eq_log_mul_sub_divisor (y : ℝ) {n : ℕ} (hn : 0 < n) :
    e y n = Real.log n * (h y n : ℝ) -
      ∑ k ∈ n.divisors, ArithmeticFunction.vonMangoldt k *
        (h (max y (Nat.maxPrimeFac k : ℝ)) (n / k) : ℝ) := by
  unfold e
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ArithmeticFunction.vonMangoldt_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [F_divisor_gap y hn (Nat.pos_of_mem_divisors hk) (Nat.dvd_of_mem_divisors hk)]

/-- The finite divisor sum is exactly the full floor-indexed kernel. -/
theorem divisor_sum_eq_kernel (y : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors,
      ArithmeticFunction.vonMangoldt k *
        (h (max y (Nat.maxPrimeFac k : ℝ)) (n / k) : ℝ)) = kernel y X := by
  rw [sum_divisors_reindex X (fun k m => ArithmeticFunction.vonMangoldt k *
    (h (max y (Nat.maxPrimeFac k : ℝ)) m : ℝ))]
  simp only [kernel, J, Int.cast_sum, Finset.mul_sum]

/-- Exact prefix source identity, valid even for the empty prefix. -/
theorem E_eq_weightedPrefix_sub_kernel (y : ℝ) (X : ℕ) :
    E y X = (∑ n ∈ Finset.Icc 1 X, Real.log n * (h y n : ℝ)) - kernel y X := by
  unfold E
  calc
    _ = ∑ n ∈ Finset.Icc 1 X,
        (Real.log n * (h y n : ℝ) -
          ∑ k ∈ n.divisors, ArithmeticFunction.vonMangoldt k *
            (h (max y (Nat.maxPrimeFac k : ℝ)) (n / k) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact e_eq_log_mul_sub_divisor y (by have := (Finset.mem_Icc.mp hn).1; omega)
    _ = _ := by rw [Finset.sum_sub_distrib, divisor_sum_eq_kernel]

/-- The logarithmic weight is split exactly at the same inclusive endpoint. -/
theorem weightedPrefix_add_R (y : ℝ) {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, Real.log n * (h y n : ℝ)) + R y X =
      (J y X : ℝ) * Real.log X := by
  unfold R J
  rw [← Finset.sum_add_distrib, Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  rw [Real.log_div hX0 hn0]
  ring

/-- The exact full-color finite renewal. This is an identity, not a source
bound, kernel asymptotic, or density conclusion. -/
theorem finite_renewal (y : ℝ) {X : ℕ} (hX : 1 ≤ X) :
    (J y X : ℝ) * Real.log X = kernel y X + E y X + R y X := by
  calc
    _ = (∑ n ∈ Finset.Icc 1 X, Real.log n * (h y n : ℝ)) + R y X :=
      (weightedPrefix_add_R y hX).symm
    _ = _ := by rw [E_eq_weightedPrefix_sub_kernel]; ring

/-- The actual prime-power term vanishes before any kernel estimate. -/
theorem vonMangoldt_primePower_child_term_eq_zero (y : ℝ) {p a X : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hX : X < p ^ (a + 1)) :
    ArithmeticFunction.vonMangoldt (p ^ a) *
      (J (max y (Nat.maxPrimeFac (p ^ a) : ℝ)) (X / p ^ a) : ℝ) = 0 := by
  rw [J_primePower_actual_color_eq_zero y hp ha hX]
  simp

end Erdos371.CensoredComparison

#print axioms Erdos371.CensoredComparison.F
#print axioms Erdos371.CensoredComparison.h
#print axioms Erdos371.CensoredComparison.J
#print axioms Erdos371.CensoredComparison.F_self
#print axioms Erdos371.CensoredComparison.F_eq_zero_of_labels_eq
#print axioms Erdos371.CensoredComparison.F_eq_zero_of_max_le
#print axioms Erdos371.CensoredComparison.signedComparison_censor_max
#print axioms Erdos371.CensoredComparison.F_mul
#print axioms Erdos371.CensoredComparison.F_mul_gap
#print axioms Erdos371.CensoredComparison.F_divisor_gap
#print axioms Erdos371.CensoredComparison.h_one
#print axioms Erdos371.CensoredComparison.h_one_at_one
#print axioms Erdos371.CensoredComparison.J_one
#print axioms Erdos371.CensoredComparison.J_zero
#print axioms Erdos371.CensoredComparison.unit_edge_max_le_endpoint
#print axioms Erdos371.CensoredComparison.h_eq_zero_of_endpoint_le
#print axioms Erdos371.CensoredComparison.J_eq_zero_of_endpoint_le
#print axioms Erdos371.CensoredComparison.primePower_child_endpoint_le
#print axioms Erdos371.CensoredComparison.primePower_child_labels_le
#print axioms Erdos371.CensoredComparison.J_primePower_child_eq_zero
#print axioms Erdos371.CensoredComparison.J_primePower_actual_color_eq_zero
#print axioms Erdos371.CensoredComparison.J_prime_child_eq_zero
#print axioms Erdos371.CensoredComparison.sum_divisors_reindex
#print axioms Erdos371.CensoredComparison.e
#print axioms Erdos371.CensoredComparison.E
#print axioms Erdos371.CensoredComparison.R
#print axioms Erdos371.CensoredComparison.kernel
#print axioms Erdos371.CensoredComparison.e_eq_log_mul_sub_divisor
#print axioms Erdos371.CensoredComparison.divisor_sum_eq_kernel
#print axioms Erdos371.CensoredComparison.E_eq_weightedPrefix_sub_kernel
#print axioms Erdos371.CensoredComparison.weightedPrefix_add_R
#print axioms Erdos371.CensoredComparison.finite_renewal
#print axioms Erdos371.CensoredComparison.vonMangoldt_primePower_child_term_eq_zero
