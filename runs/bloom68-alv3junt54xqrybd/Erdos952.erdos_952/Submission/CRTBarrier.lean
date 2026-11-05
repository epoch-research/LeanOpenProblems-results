import Submission.SmallStepArithmetic

/-!
# CRT barriers in horizontal strips of Gaussian integers

For any finite strip height and any finite band width, the Chinese remainder
theorem produces a prime-free vertical band arbitrarily far to the right.
Its reflection is prime-free as well. These are barriers **inside a fixed
horizontal strip**, not moats in the unrestricted plane.

The factors used for the finite cells are `2^(2^j) + i`. Their squared norms
are the pairwise coprime Fermat numbers `Nat.fermatNumber (j + 1)`. No factor
is assumed prime, and no distribution theorem for primes is needed. Moving
a CRT solution by a multiple of the positive product of its moduli makes all
cell norms larger than all factor norms, excluding the associated-prime
exceptions by irreducibility.
-/

namespace GaussianCRTBarrier

open GaussianSmallStep.Arithmetic
open scoped BigOperators

/-- The linear congruence for divisibility by `a + i`. -/
theorem dvd_linear_factor_of_modEq (z : GaussianInt) (a : ℤ)
    (h : z.re ≡ a * z.im [ZMOD a ^ 2 + 1]) :
    (⟨a, 1⟩ : GaussianInt) ∣ z := by
  have hd : a ^ 2 + 1 ∣ a * z.im - z.re := Int.modEq_iff_dvd.mp h
  apply dvd_of_conjugate_coordinates z (⟨a, 1⟩ : GaussianInt)
  · intro hz
    have hi := congrArg Zsqrtd.im hz
    simp at hi
  · have hr := dvd_sub (dvd_mul_right (a ^ 2 + 1) z.im)
      (dvd_mul_of_dvd_right hd a)
    convert hr using 1
    · simp [norm_eq_sum_sq]
    · simp [Zsqrtd.re_mul]
      ring
  · simpa [norm_eq_sum_sq, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star,
      sub_eq_add_neg, mul_comm, add_comm] using hd

/-- Exact equivalence between the linear congruence and divisibility by `a + i`. -/
theorem dvd_linear_factor_iff_modEq (z : GaussianInt) (a : ℤ) :
    (⟨a, 1⟩ : GaussianInt) ∣ z ↔ z.re ≡ a * z.im [ZMOD a ^ 2 + 1] := by
  constructor
  · rintro ⟨q, rfl⟩
    apply Int.modEq_iff_dvd.mpr
    refine ⟨q.im, ?_⟩
    simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  · exact dvd_linear_factor_of_modEq z a

/-- The real coordinate of the `j`th factor. -/
def coefficient (j : ℕ) : ℤ := 2 ^ (2 ^ j)

/-- These factors need not be Gaussian primes. -/
def factor (j : ℕ) : GaussianInt := ⟨coefficient j, 1⟩

/-- Squaring the real coordinate shifts the Fermat-number index by one. -/
theorem coefficient_sq_add_one (j : ℕ) :
    coefficient j ^ 2 + 1 = (Nat.fermatNumber (j + 1) : ℤ) := by
  simp only [coefficient, Nat.fermatNumber, Nat.cast_add, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one]
  rw [show 2 ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]

/-- The moduli in the CRT are exactly the Gaussian factor norms. -/
theorem norm_factor (j : ℕ) :
    (factor j).norm = (Nat.fermatNumber (j + 1) : ℤ) := by
  simpa [factor, norm_eq_sum_sq] using coefficient_sq_add_one j

/-- Every factor is a nonunit, since its squared norm is greater than one. -/
theorem one_lt_norm_factor (j : ℕ) : 1 < (factor j).norm := by
  rw [norm_factor]
  have h := Nat.three_le_fermatNumber (j + 1)
  exact_mod_cast (by omega : 1 < Nat.fermatNumber (j + 1))

/-- Finite CRT with integer residues, lifted to nonnegative natural residues. -/
theorem exists_nat_crt {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (r : ι → ℤ) : ∃ t : ℕ, ∀ i, (t : ℤ) ≡ r i [ZMOD (m i : ℤ)] := by
  classical
  let a : ι → ℕ := fun i => (r i % (m i : ℤ)).toNat
  let t := Nat.chineseRemainderOfFinset a m Finset.univ
    (fun i _ => (hm i).ne') (fun i _ j _ hij => hc hij)
  refine ⟨t.val, fun i => ?_⟩
  have h : (t.val : ℤ) ≡ (a i : ℤ) [ZMOD (m i : ℤ)] :=
    Int.natCast_modEq_iff.mpr (t.property i (Finset.mem_univ i))
  have ha : (a i : ℤ) = r i % (m i : ℤ) := by
    apply Int.toNat_of_nonneg
    apply Int.emod_nonneg
    exact_mod_cast (hm i).ne'
  rw [ha] at h
  exact h.trans (Int.mod_modEq _ _)

/--
A prime-free band `[T, T + D]` across the entire strip `|im| ≤ M` can be
placed beyond any integer `B`. The statement allows arbitrary integer
parameters; an empty cell interval simply gives a vacuous band condition.
-/
theorem exists_positive_prime_free_band (D M B : ℤ) :
    ∃ T : ℤ, B < T ∧ 0 < T ∧
      ∀ z : GaussianInt, T ≤ z.re → z.re ≤ T + D → |z.im| ≤ M → ¬ Prime z := by
  classical
  let cells : Finset (ℤ × ℤ) := (Finset.Icc 0 D).product (Finset.Icc (-M) M)
  let ι := ↥cells
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let j : ι → ℕ := fun c => (e c).val
  have hj : Function.Injective j := Fin.val_injective.comp e.injective
  let m : ι → ℕ := fun c => Nat.fermatNumber (j c + 1)
  have hm : ∀ c, 0 < m c := by
    intro c
    have := Nat.three_le_fermatNumber (j c + 1)
    dsimp [m]
    omega
  have hc : Pairwise (fun c d => Nat.Coprime (m c) (m d)) := by
    intro c d hcd
    apply Nat.coprime_fermatNumber_fermatNumber
    intro h
    exact hcd (hj (Nat.add_right_cancel h))
  let r : ι → ℤ := fun c => coefficient (j c) * c.val.2 - c.val.1
  obtain ⟨t, ht⟩ := exists_nat_crt m hm hc r
  let P : ℕ := ∏ c : ι, m c
  have hP : 0 < P := Finset.prod_pos (fun c _ => hm c)
  have hdP : ∀ c, m c ∣ P := fun c => Finset.dvd_prod_of_mem m (Finset.mem_univ c)
  let Q : ℕ := B.natAbs + P + 1
  let T : ℕ := t + P * Q
  have hQT : Q ≤ T := (Nat.le_mul_of_pos_left Q hP).trans (Nat.le_add_left _ _)
  have hlarge : (P : ℤ) < (T : ℤ) := by
    dsimp [Q] at hQT
    exact_mod_cast (by omega : P < T)
  have hB : B < (T : ℤ) := by
    have hBT : B.natAbs < T := by dsimp [Q] at hQT; omega
    have hBT' : |B| < (T : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hBT
    exact (le_abs_self B).trans_lt hBT'
  have hT : ∀ c, (T : ℤ) ≡ r c [ZMOD (m c : ℤ)] := by
    intro c
    have hd : (m c : ℤ) ∣ (P : ℤ) := by exact_mod_cast hdP c
    have hz : (P : ℤ) * (Q : ℤ) ≡ 0 [ZMOD (m c : ℤ)] :=
      (dvd_mul_of_dvd_left hd (Q : ℤ)).modEq_zero_int
    simpa [T] using (ht c).add hz
  refine ⟨T, hB, lt_trans (by exact_mod_cast hP) hlarge, ?_⟩
  intro z hzlo hzhi hzim hzprime
  have hcell : (z.re - (T : ℤ), z.im) ∈ cells := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr (abs_le.mp hzim)⟩
  let c : ι := ⟨(z.re - (T : ℤ), z.im), hcell⟩
  have hmod : z.re ≡ coefficient (j c) * z.im [ZMOD (m c : ℤ)] := by
    convert (hT c).add_right (z.re - (T : ℤ)) using 1 <;> dsimp [r, c] <;> ring
  have hdiv : factor (j c) ∣ z := by
    apply dvd_linear_factor_of_modEq z (coefficient (j c))
    simpa only [coefficient_sq_add_one, m] using hmod
  have hfactorle : (factor (j c)).norm ≤ (P : ℤ) := by
    rw [norm_factor]
    exact_mod_cast Nat.le_of_dvd hP (hdP c)
  have hnorm : (P : ℤ) < z.norm := by
    rw [norm_eq_sum_sq]
    have hre : (P : ℤ) < z.re := hlarge.trans_le hzlo
    have hp : 0 < (P : ℤ) := by exact_mod_cast hP
    nlinarith [sq_nonneg z.im]
  have he := prime_norm_eq_of_dvd hzprime (ne_of_gt (one_lt_norm_factor (j c))) hdiv
  omega

/--
Symmetric prime-free barriers outside a finite real interval, wide enough
for any prescribed integer real-jump bound `D`, throughout `|im| ≤ M`.
-/
theorem exists_symmetric_prime_free_barriers (D M start : ℤ) :
    ∃ A : ℤ, |start| ≤ A ∧
      ∀ z : GaussianInt, A < |z.re| → |z.re| ≤ A + D → |z.im| ≤ M → ¬ Prime z := by
  obtain ⟨T, hstart, _, hband⟩ := exists_positive_prime_free_band D M |start|
  refine ⟨T - 1, by omega, ?_⟩
  intro z hzlo hzhi hzim hzprime
  by_cases hre : 0 ≤ z.re
  · apply hband z (by rw [abs_of_nonneg hre] at hzlo; omega)
      (by rw [abs_of_nonneg hre] at hzhi; omega) hzim hzprime
  · have hre' : z.re < 0 := lt_of_not_ge hre
    apply hband (-z) _ _ _ hzprime.neg
    · simp only [Zsqrtd.re_neg]
      rw [abs_of_neg hre'] at hzlo
      omega
    · simp only [Zsqrtd.re_neg]
      rw [abs_of_neg hre'] at hzhi
      omega
    · simpa only [Zsqrtd.im_neg, abs_neg] using hzim

end GaussianCRTBarrier
