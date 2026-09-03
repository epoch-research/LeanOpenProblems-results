import Submission.Spec

/-!
# A certificate criterion for polynomially large representation counts

These lemmas check the passage from an integer polynomial identity to a family
of distinct bounded integer representations. They do not assert that a suitable
identity exists for any of the unresolved exponents.
-/

namespace Erdos322Research.PolynomialPeakCriterion

open Erdos322

/-- An injective family of nonnegative integer representations is counted by
`representationCount`; the coordinate bounds follow from the sum identity. -/
theorem count_lower_of_injective {k n M : ℕ} (hk : 0 < k)
    (v : Fin M → Fin k → ℕ)
    (hsum : ∀ a, ∑ i, v a i ^ k = n) (hinj : Function.Injective v) :
    M ≤ representationCount k n := by
  classical
  let w : Fin M → Fin k → Fin (n + 1) := fun a i ↦ ⟨v a i, by
    have h₁ : v a i ≤ v a i ^ k := Nat.le_pow hk
    have h₂ : v a i ^ k ≤ ∑ j, v a j ^ k :=
      Finset.single_le_sum (f := fun j ↦ v a j ^ k)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have h₃ := hsum a
    omega⟩
  have hw : Function.Injective w := by
    intro a b h
    apply hinj
    funext i
    exact congrArg Fin.val (congrFun h i)
  unfold representationCount
  have hc := Finset.card_le_card_of_injOn w
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin k → Fin (n + 1) ↦
      ∑ i, (a i : ℕ)^k = n))
    (by intro a _; simpa [w] using hsum a) hw.injOn
  simpa using hc

/-- Linear-sized families at polynomially growing targets give genuine power
peaks. No asymptotic estimate or unspecified constant is needed. -/
theorem power_peaks_of_linear_family {k D N : ℕ} (hk : 0 < k)
    (hD : 0 < D) (hN : 0 < N)
    (v : (m : ℕ) → Fin (m + 1) → Fin k → ℕ)
    (hsum : ∀ m, 0 < m → ∀ a, ∑ i, v m a i ^ k = N * m^D)
    (hinj : ∀ m, 0 < m → Function.Injective (v m)) :
    {n : ℕ | (n : ℝ)^((2 * D : ℕ) : ℝ)⁻¹ < representationCount k n}.Infinite := by
  have hi : Function.Injective (fun m : ℕ ↦ N * (m + N + 1)^D) := by
    intro a b h
    have hp : (a + N + 1)^D = (b + N + 1)^D := Nat.eq_of_mul_eq_mul_left hN h
    have he := Nat.pow_left_injective hD.ne' hp
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨m, rfl⟩
  let L := m + N + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hNL : N ≤ L := by dsimp [L]; omega
  have hNP : N ≤ L^D := hNL.trans (Nat.le_pow hD)
  have hbound : N * L^D ≤ L^(2 * D) := by
    calc
      N * L^D ≤ L^D * L^D := Nat.mul_le_mul_right _ hNP
      _ = L^(2 * D) := by rw [two_mul, pow_add]
  have hreal : ((N * L^D : ℕ) : ℝ)^((2 * D : ℕ) : ℝ)⁻¹ ≤ L := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N * L^D : ℕ))
      (by exact_mod_cast hbound : ((N * L^D : ℕ) : ℝ) ≤ ((L^(2 * D) : ℕ) : ℝ))
      (by positivity : (0 : ℝ) ≤ ((2 * D : ℕ) : ℝ)⁻¹)
    rw [Nat.cast_pow, Real.pow_rpow_inv_natCast (Nat.cast_nonneg L) (by omega)] at h
    exact h
  have hc := count_lower_of_injective hk (v L) (hsum L hL) (hinj L hL)
  change ((N * L^D : ℕ) : ℝ)^((2 * D : ℕ) : ℝ)⁻¹ < _
  exact hreal.trans_lt (by exact_mod_cast (show L < representationCount k (N * L^D) by omega))

/-- Integer evaluation of a homogeneous polynomial obtained by clearing the
sampling denominator. -/
def homogeneousValue (p : Polynomial ℤ) (d m a : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), p.coeff j * (a : ℤ)^j * (m : ℤ)^(d - j)

theorem homogeneousValue_cast (p : Polynomial ℤ) {d m a : ℕ}
    (hd : p.natDegree ≤ d) (hm : 0 < m) :
    (homogeneousValue p d m a : ℚ) =
      (m : ℚ)^d * p.eval₂ (Int.castRingHom ℚ) ((a : ℚ) / m) := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Polynomial.eval₂_eq_sum_range' _ (by omega : p.natDegree < d + 1)]
  unfold homogeneousValue
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ d := by simpa using Finset.mem_range.mp hj
  have hpow : (m : ℚ)^d = (m : ℚ)^j * (m : ℚ)^(d - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjd]
  rw [hpow, div_pow]
  change _ = ((m : ℚ)^j * (m : ℚ)^(d - j)) * ((p.coeff j : ℚ) * ((a : ℚ)^j / (m : ℚ)^j))
  field_simp


private theorem sampling_mem {m : ℕ} (hm : 0 < m) (a : Fin (m + 1)) :
    (a : ℚ) / m ∈ Set.Icc (0 : ℚ) 1 := by
  constructor
  · positivity
  · apply (div_le_one (by exact_mod_cast hm : (0 : ℚ) < m)).mpr
    exact_mod_cast (Nat.le_of_lt_succ a.isLt)

/-- Homogenized coordinates are nonnegative at every sample in the interval. -/
theorem homogeneousValue_nonneg (p : Polynomial ℤ) {d m : ℕ}
    (hd : p.natDegree ≤ d) (hm : 0 < m)
    (hpos : ∀ x ∈ Set.Icc (0 : ℚ) 1, 0 ≤ p.eval₂ (Int.castRingHom ℚ) x)
    (a : Fin (m + 1)) : 0 ≤ homogeneousValue p d m a := by
  have hh := homogeneousValue_cast p hd hm (a := a.val)
  have h : (0 : ℚ) ≤ homogeneousValue p d m a := by
    rw [hh]
    exact mul_nonneg (by positivity) (hpos _ (sampling_mem hm a))
  exact_mod_cast h

/-- The nonnegative integer tuple obtained from a polynomial family. -/
def homogeneousPoint {k : ℕ} (p : Fin k → Polynomial ℤ) (d m : ℕ)
    (a : Fin (m + 1)) : Fin k → ℕ :=
  fun i ↦ (homogeneousValue (p i) d m a).toNat

theorem homogeneousPoint_sum {k d m N : ℕ} (p : Fin k → Polynomial ℤ)
    (hd : ∀ i, (p i).natDegree ≤ d) (hm : 0 < m)
    (hpos : ∀ i x, x ∈ Set.Icc (0 : ℚ) 1 →
      0 ≤ (p i).eval₂ (Int.castRingHom ℚ) x)
    (hid : ∑ i, p i ^ k = Polynomial.C (N : ℤ))
    (a : Fin (m + 1)) :
    ∑ i, homogeneousPoint p d m a i ^ k = N * m^(d * k) := by
  have heval := congrArg (Polynomial.eval₂ (Int.castRingHom ℚ) ((a : ℚ) / m)) hid
  simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_C] at heval
  change (∑ i, (p i).eval₂ (Int.castRingHom ℚ) ((a : ℚ) / m) ^ k) = (N : ℚ) at heval
  have hcast (i : Fin k) :
      (homogeneousPoint p d m a i : ℚ) =
        (m : ℚ)^d * (p i).eval₂ (Int.castRingHom ℚ) ((a : ℚ) / m) := by
    have hz := Int.toNat_of_nonneg (homogeneousValue_nonneg (p i) (hd i) hm (hpos i) a)
    have hzQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hz
    push_cast at hzQ
    exact hzQ.trans (homogeneousValue_cast (p i) (hd i) hm)
  have hs : (∑ i, (homogeneousPoint p d m a i : ℚ)^k) =
      (N : ℚ) * (m : ℚ)^(d * k) := by
    simp_rw [hcast, mul_pow]
    rw [← Finset.mul_sum, heval, ← pow_mul, mul_comm]
  exact_mod_cast hs

theorem homogeneousPoint_injective {k d m : ℕ} (p : Fin k → Polynomial ℤ)
    (hd : ∀ i, (p i).natDegree ≤ d) (hm : 0 < m)
    (hpos : ∀ i x, x ∈ Set.Icc (0 : ℚ) 1 →
      0 ≤ (p i).eval₂ (Int.castRingHom ℚ) x)
    (i₀ : Fin k)
    (hmono : StrictMonoOn (fun x : ℚ ↦ (p i₀).eval₂ (Int.castRingHom ℚ) x) (Set.Icc (0 : ℚ) 1)) :
    Function.Injective (homogeneousPoint p d m) := by
  intro a b hab
  have ha := Int.toNat_of_nonneg
    (homogeneousValue_nonneg (p i₀) (hd i₀) hm (hpos i₀) a)
  have hb := Int.toNat_of_nonneg
    (homogeneousValue_nonneg (p i₀) (hd i₀) hm (hpos i₀) b)
  have he := congrArg (fun v : Fin k → ℕ ↦ (v i₀ : ℤ)) hab
  dsimp only [homogeneousPoint] at he
  rw [ha, hb] at he
  have heQ := congrArg (fun z : ℤ ↦ (z : ℚ)) he
  dsimp only at heQ
  rw [homogeneousValue_cast (p i₀) (hd i₀) hm,
    homogeneousValue_cast (p i₀) (hd i₀) hm] at heQ
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hep := mul_left_cancel₀ (pow_ne_zero d hm0) heQ
  have heab := hmono.injOn (sampling_mem hm a) (sampling_mem hm b) hep
  have heval : (a : ℚ) = b := (div_left_inj' hm0).mp heab
  apply Fin.ext
  exact_mod_cast heval

/-- A usable polynomial identity is a complete certificate for power peaks:
its coordinates must be nonnegative on the sampling interval, and at least
one coordinate must be strictly monotone there. This theorem does not assume
or provide such identities at the unresolved exponents. -/
theorem polynomial_identity_gives_power_peaks {k d N : ℕ}
    (hk : 0 < k) (hdpos : 0 < d) (hN : 0 < N)
    (p : Fin k → Polynomial ℤ) (hd : ∀ i, (p i).natDegree ≤ d)
    (hpos : ∀ i x, x ∈ Set.Icc (0 : ℚ) 1 →
      0 ≤ (p i).eval₂ (Int.castRingHom ℚ) x)
    (hid : ∑ i, p i ^ k = Polynomial.C (N : ℤ))
    (i₀ : Fin k)
    (hmono : StrictMonoOn (fun x : ℚ ↦ (p i₀).eval₂ (Int.castRingHom ℚ) x) (Set.Icc (0 : ℚ) 1)) :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite := by
  refine ⟨((2 * (d * k) : ℕ) : ℝ)⁻¹, by positivity, ?_⟩
  exact power_peaks_of_linear_family hk (Nat.mul_pos hdpos hk) hN
    (homogeneousPoint p d)
    (fun m hm a ↦ homogeneousPoint_sum p hd hm hpos hid a)
    (fun m hm ↦ homogeneousPoint_injective p hd hm hpos i₀ hmono)


/-- A test of the certificate interface on the known cubic construction. This
is weaker than the sharp cubic exponent already proved in `Submission.Spec`. -/
theorem cubic_case_from_polynomial_certificate :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount 3 n}.Infinite := by
  let p : Fin 3 → Polynomial ℤ :=
    ![9 * Polynomial.X^4, 81 * Polynomial.X - 9 * Polynomial.X^4,
      81 - 27 * Polynomial.X^3]
  apply polynomial_identity_gives_power_peaks (k := 3) (d := 4) (N := 3^12)
    (by decide) (by decide) (by decide) p (i₀ := 0)
  · intro i
    fin_cases i <;> dsimp [p] <;> compute_degree
    all_goals norm_num
  · intro i x hx
    have hx0 := hx.1
    have hx1 := hx.2
    have hx40 : 0 ≤ x^4 := pow_nonneg hx0 4
    have hx3 : x^3 ≤ 1 := pow_le_one₀ hx0 hx1
    have hx4 : x^4 ≤ x := by
      calc
        x^4 = x*x^3 := by ring
        _ ≤ x*1 := mul_le_mul_of_nonneg_left hx3 hx0
        _ = x := mul_one x
    fin_cases i <;> simp [p, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X] <;> nlinarith
  · simp [p, Fin.sum_univ_three]
    ring
  · intro x hx y hy hxy
    have hp : x^4 < y^4 := pow_lt_pow_left₀ hxy hx.1 (by decide)
    simpa [p] using (mul_lt_mul_of_pos_left hp (by norm_num : (0 : ℚ) < 9))

end Erdos322Research.PolynomialPeakCriterion
