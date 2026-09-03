import Submission.StripCRT
import Submission.FinitePotential

/-!
# Bounded-step Gaussian-prime sequences cannot stay in a horizontal strip

For every integral squared-step bound `C` and every fixed strip `a ≤ im ≤ b`,
there is no injective sequence of Gaussian primes in the strip with all squared
step norms less than `C`.

Apply the finite-pattern CRT to a rectangle of width `|C| + 1`. Its periodic
translates contain no primes outside a finite norm-bounded exceptional set.
An injective sequence eventually avoids this set. On that tail, the Euclidean
remainder of the real coordinate avoids the whole crosscut, so a bounded step
cannot change the corresponding quotient. The tail therefore lies in one
finite rectangle, contradicting injectivity.

This is only the fixed-horizontal-strip case, not the unrestricted Gaussian
moat problem. This file neither imports nor modifies `Submission.Spec`.
-/

namespace Erdos952
namespace StripBound

/-- The Gaussian integers in a finite coordinate rectangle. -/
def rectangle (u v a b : ℤ) : Finset GaussianInt :=
  ((Finset.Icc u v) ×ˢ (Finset.Icc a b)).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))

@[simp]
theorem mem_rectangle {u v a b : ℤ} {z : GaussianInt} :
    z ∈ rectangle u v a b ↔
      (u ≤ z.re ∧ z.re ≤ v) ∧ (a ≤ z.im ∧ z.im ≤ b) := by
  constructor
  · intro hz
    obtain ⟨⟨r, s⟩, hrs, rfl⟩ := Finset.mem_image.mp hz
    simpa only [Finset.mem_product, Finset.mem_Icc] using hrs
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨(z.re, z.im), ?_, ?_⟩
    · simpa only [Finset.mem_product, Finset.mem_Icc] using hz
    · cases z
      rfl

/-- For integer coordinates, the absolute real coordinate is bounded by the
squared Gaussian norm. -/
theorem abs_re_le_norm (z : GaussianInt) : |z.re| ≤ z.norm := by
  have hn : z.norm = z.re ^ 2 + z.im ^ 2 := by
    simp [Zsqrtd.norm, pow_two]
  rw [abs_le]
  constructor <;> nlinarith [Int.le_self_sq z.re, Int.le_self_sq (-z.re), sq_nonneg z.im]

/-- The corresponding integral bound on the imaginary coordinate. -/
theorem abs_im_le_norm (z : GaussianInt) : |z.im| ≤ z.norm := by
  have hn : z.norm = z.re ^ 2 + z.im ^ 2 := by
    simp [Zsqrtd.norm, pow_two]
  rw [abs_le]
  constructor <;> nlinarith [Int.le_self_sq z.im, Int.le_self_sq (-z.im), sq_nonneg z.re]

/-- Every bounded-norm set of Gaussian integers is finite, including when the
bound is negative (and the set is empty). -/
theorem finite_norm_le (K : ℤ) : {z : GaussianInt | z.norm ≤ K}.Finite := by
  apply (rectangle (-K) K (-K) K).finite_toSet.subset
  intro z hz
  apply mem_rectangle.mpr
  exact ⟨abs_le.mp ((abs_re_le_norm z).trans hz),
    abs_le.mp ((abs_im_le_norm z).trans hz)⟩

/-- The CRT period can be made larger than any prescribed integer by passing
to a subprogression. -/
theorem exists_periodic_prime_exclusion_gt (F : Finset GaussianInt) (L : ℤ) :
    ∃ t P K : ℤ, 0 < P ∧ L < P ∧ ∀ n : ℤ, ∀ z ∈ F,
      Prime (((t + P * n : ℤ) : GaussianInt) + z) →
        (((t + P * n : ℤ) : GaussianInt) + z).norm ≤ K := by
  obtain ⟨t, P, K, hP, ht⟩ := StripCRT.exists_periodic_prime_exclusion F
  refine ⟨t, P * (|L| + 1), K, mul_pos hP (by positivity), ?_, ?_⟩
  · have hP1 : 1 ≤ P := hP
    nlinarith [abs_nonneg L, le_abs_self L]
  · intro n z hz hp
    simpa only [mul_assoc] using
      ht ((|L| + 1) * n) z hz (by simpa only [mul_assoc] using hp)

/-- Periodic rectangular crosscuts exclude every prime in the strip outside
a bounded-norm exceptional set. Remainders include negative real coordinates
via integer Euclidean division. -/
theorem exists_strip_barriers (L a b : ℤ) :
    ∃ t P K : ℤ, 0 < P ∧ L < P ∧ ∀ z : GaussianInt,
      Prime z → a ≤ z.im → z.im ≤ b → K < z.norm → L < (z.re - t) % P := by
  obtain ⟨t, P, K, hP, hLP, ht⟩ :=
    exists_periodic_prime_exclusion_gt (rectangle 0 L a b) L
  refine ⟨t, P, K, hP, hLP, ?_⟩
  intro z hp ha hb hK
  by_contra hr
  have hmem : (⟨(z.re - t) % P, z.im⟩ : GaussianInt) ∈ rectangle 0 L a b := by
    apply mem_rectangle.mpr
    exact ⟨⟨Int.emod_nonneg _ hP.ne', le_of_not_gt hr⟩, ha, hb⟩
  have heq : (((t + P * ((z.re - t) / P) : ℤ) : GaussianInt) +
      (⟨(z.re - t) % P, z.im⟩ : GaussianInt)) = z := by
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_add, Zsqrtd.re_intCast]
      have hdiv := Int.mul_ediv_add_emod (z.re - t) P
      omega
    · simp
  have hbound := ht ((z.re - t) / P) _ hmem (by simpa only [heq] using hp)
  rw [heq] at hbound
  omega

/-- Between remainders strictly above a blocked interval `0, ..., L`, a jump
of absolute size at most `L` cannot change the period quotient. -/
theorem ediv_eq_of_emod_gt {u v P L : ℤ} (hP : 0 < P)
    (hu : L < u % P) (hv : L < v % P) (hstep : |v - u| ≤ L) :
    u / P = v / P := by
  have hum := Int.emod_lt_of_pos u hP
  have hvm := Int.emod_lt_of_pos v hP
  have hud := Int.mul_ediv_add_emod u P
  have hvd := Int.mul_ediv_add_emod v P
  obtain ⟨hlo, hhi⟩ := abs_le.mp hstep
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hq : u / P + 1 ≤ v / P := by omega
    have hmul := mul_le_mul_of_nonneg_left hq hP.le
    nlinarith
  · have hq : v / P + 1 ≤ u / P := by omega
    have hmul := mul_le_mul_of_nonneg_left hq hP.le
    nlinarith

end StripBound

/-- The fixed-horizontal-strip case of the Gaussian moat problem, for every
integral squared-step bound. No ordering assumption on the strip endpoints
and no positivity assumption on `C` are required. This does not exclude
bounded-step prime sequences with unbounded imaginary coordinates. -/
theorem no_bounded_step_prime_sequence_in_horizontal_strip (C a b : ℤ) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ∧
      (∀ n, a ≤ (x n).im ∧ (x n).im ≤ b) := by
  rintro ⟨x, hx, hstep, hstrip⟩
  let L : ℤ := |C| + 1
  obtain ⟨t, P, K, hP, _hLP, hbarrier⟩ := StripBound.exists_strip_barriers L a b
  obtain ⟨N, hN⟩ := FinitePotential.exists_tail_avoiding hx (StripBound.finite_norm_le K)
  have hnorm (n : ℕ) : K < (x (N + n)).norm := by
    have hn := hN n
    change ¬ (x (N + n)).norm ≤ K at hn
    exact lt_of_not_ge hn
  have hrem (n : ℕ) : L < ((x (N + n)).re - t) % P :=
    hbarrier _ (hstep _).1 (hstrip _).1 (hstrip _).2 (hnorm n)
  have hreal (n : ℕ) : |(x (N + (n + 1))).re - (x (N + n)).re| ≤ L := by
    have hs : (x (N + (n + 1)) - x (N + n)).norm < C := by
      simpa only [Nat.add_assoc] using (hstep (N + n)).2
    have hr := StripBound.abs_re_le_norm (x (N + (n + 1)) - x (N + n))
    simp only [Zsqrtd.re_sub] at hr
    have hCL : C ≤ L := by
      dsimp [L]
      linarith [le_abs_self C]
    exact hr.trans (hs.le.trans hCL)
  have hquotstep (n : ℕ) :
      ((x (N + (n + 1))).re - t) / P = ((x (N + n)).re - t) / P := by
    apply (StripBound.ediv_eq_of_emod_gt hP (hrem n) (hrem (n + 1)) ?_).symm
    simpa only [sub_sub_sub_cancel_right] using hreal n
  have hquot (n : ℕ) : ((x (N + n)).re - t) / P = ((x N).re - t) / P := by
    induction n with
    | zero => simp
    | succ n ih => exact (hquotstep n).trans ih
  let B : ℤ := t + P * (((x N).re - t) / P)
  have hbox (n : ℕ) : x (N + n) ∈ StripBound.rectangle B (B + P) a b := by
    apply StripBound.mem_rectangle.mpr
    refine ⟨?_, hstrip _⟩
    have hd := Int.mul_ediv_add_emod ((x (N + n)).re - t) P
    rw [hquot n] at hd
    have hl := Int.emod_nonneg ((x (N + n)).re - t) hP.ne'
    have hu := Int.emod_lt_of_pos ((x (N + n)).re - t) hP
    dsimp [B]
    constructor <;> omega
  have htailinj : Function.Injective (fun n => x (N + n)) :=
    fun _ _ h => Nat.add_left_cancel (hx h)
  have hfinite : (Set.range (fun n => x (N + n))).Finite := by
    apply (StripBound.rectangle B (B + P) a b).finite_toSet.subset
    rintro z ⟨n, rfl⟩
    exact hbox n
  exact Set.infinite_range_of_injective htailinj hfinite

end Erdos952
