import FormalConjecturesUtil
import Submission.WallDataChecker
import Submission.SmallBound
import Submission.DiagonalArithmetic
import Submission.WallObstruction
import Submission.FinitePotential

/-!
# From a black-wall obstruction to a Gaussian-prime bound

The affine map `z w = 1 + (1 + i) * w` identifies the odd-parity Gaussian
integers with the wall lattice. Each of the ten exact tests in `WallData.Black`
supplies an explicit nonunit divisor of `z w` of norm at most 37. Consequently,
Gaussian primes outside that finite norm ball lift to white vertices, and
squared step norms less than eight lift to king steps.

The final obstruction is conditional on the nonexistence of an injective white
king sequence for `WallData.Black`. It concerns only integral bounds `C ≤ 8`,
not arbitrary bounds in the Gaussian moat problem.
-/

namespace Erdos952.WallPrimeBridge

/-- The affine change from wall coordinates to odd-parity Gaussian integers. -/
def z (w : GaussianInt) : GaussianInt := 1 + SmallBound.oneAddI * w

@[simp]
theorem z_re (w : GaussianInt) : (z w).re = 1 + w.re - w.im := by
  simp [z, SmallBound.oneAddI]
  ring

@[simp]
theorem z_im (w : GaussianInt) : (z w).im = w.re + w.im := by
  simp [z, SmallBound.oneAddI, add_comm]

/-- Every exact black test supplies a nonunit divisor of norm at most 37.
The divisors, in label order, are `3`, `2+i`, `2-i`, `3+2i`, `3-2i`,
`4+i`, `4-i`, `5+2i`, `5-2i`, and `6+i`. No primality of these divisors is needed. -/
theorem black_has_small_divisor {w : GaussianInt} (hw : WallData.Black w) :
    ∃ a : GaussianInt, a.norm ≠ 1 ∧ a.norm ≤ 37 ∧ a ∣ z w := by
  obtain ⟨label, h⟩ := hw
  unfold WallData.LabelBlack at h
  split at h
  · obtain ⟨r, hr⟩ := Int.dvd_of_emod_eq_zero h.1
    obtain ⟨s, hs⟩ := Int.dvd_of_emod_eq_zero h.2
    refine ⟨⟨3, 0⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨r, s⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp <;> omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨2, 1⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨2 * t + (z w).im, -t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp
    omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨2, -1⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨2 * t - (z w).im, t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp
    omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨3, 2⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨3 * t - (z w).im, (z w).im - 2 * t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp <;> omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨3, -2⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨3 * t + (z w).im, (z w).im + 2 * t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp <;> omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨4, 1⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨4 * t + (z w).im, -t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp
    omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨4, -1⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨4 * t - (z w).im, t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp
    omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨5, 2⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨5 * t - 2 * (z w).im, (z w).im - 2 * t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp <;> omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨5, -2⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨5 * t + 2 * (z w).im, (z w).im + 2 * t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp <;> omega
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
    refine ⟨⟨6, 1⟩, by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm],
      ⟨⟨6 * t + (z w).im, -t⟩, ?_⟩⟩
    apply Zsqrtd.ext <;> simp
    omega
  · exact False.elim h

/-- A prime above the exceptional norm bound cannot lift from a black point. -/
theorem not_black_of_prime_of_norm_gt {w : GaussianInt} (hp : Prime (z w))
    (hn : 37 < (z w).norm) : ¬ WallData.Black w := by
  intro hw
  obtain ⟨a, ha, hbound, hdvd⟩ := black_has_small_divisor hw
  have heq := DiagonalBound.norm_eq_of_prime_dvd hp ha hdvd
  omega

/-- All Gaussian integers of norm at most 37, including the even-parity primes. -/
def E : Set GaussianInt := {p | p.norm ≤ 37}

@[simp]
theorem mem_E_iff {p : GaussianInt} : p ∈ E ↔ p.norm ≤ 37 := Iff.rfl

/-- A concrete finite coordinate box containing `E`. -/
def exceptionBox : Finset GaussianInt :=
  ((Finset.Icc (-7 : ℤ) 7) ×ˢ (Finset.Icc (-7 : ℤ) 7)).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))

/-- The norm bound gives both coordinate bounds in the finite box. -/
theorem mem_exceptionBox_of_norm_le {p : GaussianInt} (hp : p.norm ≤ 37) :
    p ∈ exceptionBox := by
  have hn : p.re ^ 2 + p.im ^ 2 ≤ 37 := by
    simpa [Zsqrtd.norm, pow_two] using hp
  have hre : -7 ≤ p.re ∧ p.re ≤ 7 := by
    constructor <;> nlinarith [sq_nonneg p.im]
  have him : -7 ≤ p.im ∧ p.im ≤ 7 := by
    constructor <;> nlinarith [sq_nonneg p.re]
  apply Finset.mem_image.mpr
  refine ⟨(p.re, p.im), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hre, Finset.mem_Icc.mpr him⟩
  · cases p
    rfl

/-- Finiteness of the norm-ball exceptions, proved by the explicit box. -/
theorem finite_E : E.Finite := by
  apply exceptionBox.finite_toSet.subset
  intro p hp
  exact mem_exceptionBox_of_norm_le (p := p) (mem_E_iff.mp hp)

/-- Outside `E`, the norm is strictly greater than 37. -/
theorem norm_gt_of_not_mem_E {p : GaussianInt} (hp : p ∉ E) : 37 < p.norm := by
  simpa only [mem_E_iff, not_le] using hp

/-- A prime outside `E` has odd real-plus-imaginary part. -/
theorem odd_re_add_im_of_prime_not_mem_E {p : GaussianInt} (hp : Prime p)
    (he : p ∉ E) : Odd (p.re + p.im) := by
  apply SmallBound.odd_re_add_im_of_prime_not_mem hp
  intro h
  apply he
  change p.norm ≤ 37
  rw [SmallBound.mem_evenPrimeExceptions_iff.mp h]
  norm_num

/-- Odd coordinate sum is enough to lift through `z`, by division of `p - 1`
by `1 + i`. -/
theorem exists_eq_z_of_odd {p : GaussianInt} (hp : Odd (p.re + p.im)) :
    ∃ w : GaussianInt, p = z w := by
  have he : Even ((p - 1).re + (p - 1).im) := by
    have hsum : (p - 1).re + (p - 1).im = (p.re + p.im) - 1 := by
      simp
      ring
    rw [hsum]
    exact hp.sub_odd (by decide : Odd (1 : ℤ))
  obtain ⟨w, hw⟩ := (SmallBound.oneAddI_dvd_iff_even (p - 1)).mpr he
  refine ⟨w, ?_⟩
  unfold z
  rw [← hw]
  abel

/-- Every nonexceptional prime has a wall-coordinate lift. -/
theorem exists_eq_z_of_prime_not_mem_E {p : GaussianInt} (hp : Prime p)
    (he : p ∉ E) : ∃ w : GaussianInt, p = z w :=
  exists_eq_z_of_odd (odd_re_add_im_of_prime_not_mem_E hp he)

/-- The affine change of coordinates is injective. -/
theorem z_injective : Function.Injective z := by
  intro u v h
  have hre := congrArg Zsqrtd.re h
  have him := congrArg Zsqrtd.im h
  simp only [z_re, z_im] at hre him
  apply Zsqrtd.ext <;> omega

/-- Differences under `z` are multiplied by `1 + i`. -/
theorem z_sub_z (u v : GaussianInt) : z v - z u = SmallBound.oneAddI * (v - u) := by
  unfold z
  ring

/-- The squared norm of a difference is doubled by the affine change. -/
theorem norm_z_sub_z (u v : GaussianInt) : (z v - z u).norm = 2 * (v - u).norm := by
  rw [z_sub_z, Zsqrtd.norm_mul, SmallBound.norm_oneAddI]

/-- A squared step norm below eight lifts to a king step: the lifted norm is
below four, so each integral coordinate difference has absolute value at most one. -/
theorem kingAdjacent_of_norm_z_sub_z_lt_eight {u v : GaussianInt}
    (h : (z v - z u).norm < 8) : WallObstruction.KingAdjacent u v := by
  rw [norm_z_sub_z] at h
  have hn : (v - u).norm < 4 := by omega
  have hs : (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 < 4 := by
    simpa only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub, neg_one_mul,
      neg_mul, one_mul, sub_neg_eq_add, pow_two] using hn
  constructor
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (v.im - u.im)]
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (v.re - u.re)]

/-- Conditional prime-sequence obstruction for squared-norm bounds `C ≤ 8`.
The sole wall hypothesis is that there is no injective infinite white king
sequence for the exact predicate `WallData.Black`. -/
theorem no_bounded_step_sequence_of_bound_le_eight
    (noWhite : ¬ ∃ w : ℕ → GaussianInt, Function.Injective w ∧
      (∀ n, ¬ WallData.Black (w n)) ∧
      ∀ n, WallObstruction.KingAdjacent (w n) (w (n + 1)))
    {C : ℤ} (hC : C ≤ 8) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  rintro ⟨x, hx, hstep⟩
  obtain ⟨N, hN⟩ := FinitePotential.exists_tail_avoiding hx finite_E
  have hlifts : ∀ n : ℕ, ∃ w : GaussianInt, x (N + n) = z w := by
    intro n
    exact exists_eq_z_of_prime_not_mem_E (hstep (N + n)).1 (hN n)
  choose w hw using hlifts
  apply noWhite
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i j hij
    apply Nat.add_left_cancel (n := N)
    apply hx
    rw [hw i, hw j, hij]
  · intro n
    apply not_black_of_prime_of_norm_gt
    · rw [← hw n]
      exact (hstep (N + n)).1
    · rw [← hw n]
      exact norm_gt_of_not_mem_E (hN n)
  · intro n
    apply kingAdjacent_of_norm_z_sub_z_lt_eight
    rw [← hw n, ← hw (n + 1)]
    apply lt_of_lt_of_le _ hC
    simpa only [Nat.add_assoc] using (hstep (N + n)).2

end Erdos952.WallPrimeBridge
