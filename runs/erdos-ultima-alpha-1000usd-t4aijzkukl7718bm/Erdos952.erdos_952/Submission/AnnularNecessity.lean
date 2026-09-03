import Submission.StripObstruction

/-! Necessary annular and rational-prime-gap consequences of a Gaussian prime ray.
These implications do not prove or refute the Gaussian moat conjecture. -/
namespace Erdos952Investigation
namespace AnnularNecessity

set_option maxHeartbeats 0

lemma prime_dvd_nat_prime {z : GaussianInt} (hz : Prime z) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p : GaussianInt) := by
  have hn : z.norm.natAbs ≠ 0 := by
    intro hn
    exact hz.ne_zero (GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp hn))
  have hzdvd : z ∣ ((z.norm.natAbs.primeFactorsList.map
      (fun q : ℕ => (q : GaussianInt))).prod) := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hn]
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right z (star z)
  obtain ⟨q', hq', hzq'⟩ := hz.dvd_prod_iff.mp hzdvd
  obtain ⟨q, hqmem, rfl⟩ := List.mem_map.mp hq'
  exact ⟨q, Nat.prime_of_mem_primeFactorsList hqmem, hzq'⟩

lemma norm_prime_of_off_axis {z : GaussianInt} (hz : Prime z)
    (hre : z.re ≠ 0) (him : z.im ≠ 0) : z.norm.natAbs.Prime := by
  obtain ⟨p, hp, a, ha⟩ := prime_dvd_nat_prime hz
  have hn : z.norm.natAbs ∣ p ^ 2 := by
    apply Int.natCast_dvd_natCast.mp
    have ht := congrArg Zsqrtd.norm ha
    have he : z.norm ∣ (p : ℤ)^2 := by
      refine ⟨a.norm, ?_⟩
      simpa only [Zsqrtd.norm_mul, Zsqrtd.norm_natCast, pow_two] using ht
    simpa using he
  obtain ⟨k, hk, hnk⟩ := (Nat.dvd_prime_pow hp).mp hn
  interval_cases k
  · have hunit : IsUnit z := Zsqrtd.norm_eq_one_iff.mp (by simpa using hnk)
    exact (hz.not_unit hunit).elim
  · simpa only [hnk, pow_one] using hp
  · have hnz : z.norm = (p : ℤ)^2 := by
      have ht := congrArg (fun n : ℕ => (n : ℤ)) hnk
      simpa using ht
    have hna : a.norm = 1 := by
      have ht := congrArg Zsqrtd.norm ha
      have hp0 : 0 < (p : ℤ) := by exact_mod_cast hp.pos
      have ht' : (p : ℤ)^2 = (p : ℤ)^2 * a.norm := by
        simpa only [Zsqrtd.norm_mul, hnz, Zsqrtd.norm_natCast, pow_two] using ht
      nlinarith [sq_pos_of_pos hp0]
    have haunit : IsUnit a :=
      (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) a).mp hna
    have hpz : (p : GaussianInt) ∣ z := by
      rw [ha]
      exact (associated_mul_unit_right z a haunit).symm.dvd
    have hcoords : (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
      exact (Zsqrtd.intCast_dvd p z).mp (by simpa using hpz)
    have hr : (p : ℤ) ≤ |z.re| := Int.le_of_dvd (abs_pos.mpr hre) ((dvd_abs _ _).mpr hcoords.1)
    have hi : (p : ℤ) ≤ |z.im| := Int.le_of_dvd (abs_pos.mpr him) ((dvd_abs _ _).mpr hcoords.2)
    have hp0 : 0 < (p : ℤ) := by exact_mod_cast hp.pos
    have hr2 : (p : ℤ)^2 ≤ z.re^2 := by nlinarith [sq_abs z.re]
    have hi2 : (p : ℤ)^2 ≤ z.im^2 := by nlinarith [sq_abs z.im]
    rw [gaussian_norm_sq] at hnz
    nlinarith [sq_pos_of_pos hp0]

lemma norm_mod_four_of_large_prime {z : GaussianInt} (hz : Prime z)
    (hlarge : 2 < z.norm) : z.norm % 4 = 1 := by
  have hodd := prime_large_odd_coordinate_sum hz hlarge
  have hr : z.re % 4 = 0 ∨ z.re % 4 = 1 ∨ z.re % 4 = 2 ∨ z.re % 4 = 3 := by omega
  have hi : z.im % 4 = 0 ∨ z.im % 4 = 1 ∨ z.im % 4 = 2 ∨ z.im % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;> rcases hi with hi | hi | hi | hi
  all_goals first | omega | norm_num [gaussian_norm_sq, Int.add_emod, pow_two, Int.mul_emod, hr, hi]

lemma complex_radius_sq (z : GaussianInt) : ‖(z : ℂ)‖ ^ 2 = (z.norm : ℝ) := by
  rw [GaussianInt.intCast_real_norm, Complex.sq_norm]

lemma norm_lt_square_after_step {z w : GaussianInt} {R C : ℤ}
    (hR : 0 ≤ R) (hC : 0 < C) (hz : z.norm ≤ R^2)
    (hstep : (w - z).norm < C) : w.norm < (R + C)^2 := by
  have hzreal : ‖(z : ℂ)‖ ≤ (R : ℝ) := by
    have hs : ‖(z : ℂ)‖^2 ≤ (R : ℝ)^2 := by
      rw [complex_radius_sq]
      exact_mod_cast hz
    have hRreal : (0 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith [norm_nonneg (z : ℂ)]
  have hdreal : ‖((w - z : GaussianInt) : ℂ)‖ < (C : ℝ) := by
    have hs : ‖((w - z : GaussianInt) : ℂ)‖^2 < (C : ℝ) := by
      rw [complex_radius_sq]
      exact_mod_cast hstep
    have hCreal : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith [norm_nonneg ((w - z : GaussianInt) : ℂ)]
  have hwreal : ‖(w : ℂ)‖ < (R : ℝ) + C := by
    have ht : ‖(w : ℂ)‖ ≤ ‖(z : ℂ)‖ + ‖((w - z : GaussianInt) : ℂ)‖ := by
      simpa [GaussianInt.toComplex_sub, add_comm] using norm_add_le (w - z : ℂ) (z : ℂ)
    linarith
  have hsq : ‖(w : ℂ)‖^2 < ((R : ℝ) + C)^2 := by
    nlinarith [norm_nonneg (w : ℂ)]
  rw [complex_radius_sq] at hsq
  exact_mod_cast hsq

/-- Every sufficiently large integral-radius annulus of fixed width meets the ray. -/
theorem ray_meets_annulus (x : ℕ → GaussianInt) (C R : ℤ)
    (hx : Function.Injective x)
    (hs : ∀ n, (x (n + 1) - x n).norm < C)
    (hR : 0 ≤ R) (hstart : (x 0).norm ≤ R^2) :
    ∃ n : ℕ, R^2 < (x n).norm ∧ (x n).norm < (R + C)^2 := by
  have hC : 0 < C := lt_of_le_of_lt (GaussianInt.norm_nonneg _) (hs 0)
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx (R^2)
  have hex : ∃ n, R^2 < (x n).norm := ⟨N, hN N le_rfl⟩
  let n := Nat.find hex
  have hn : R^2 < (x n).norm := Nat.find_spec hex
  have hn0 : n ≠ 0 := by intro he; rw [he] at hn; omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : (x m).norm ≤ R^2 := by
    have hm' : m < Nat.find hex := by change m < n; omega
    exact le_of_not_gt (Nat.find_min hex hm')
  refine ⟨n, hn, ?_⟩
  rw [hm]
  exact norm_lt_square_after_step hR hC hprev (hs m)

/-- An axis point in a factorial composite interval cannot be a Gaussian prime. -/
lemma axis_not_prime_in_factorial_annulus (D q : ℕ) (hq : 0 < q)
    {z : GaussianInt}
    (hl : ((q * (D + 2).factorial : ℕ) + 2 : ℤ)^2 < z.norm)
    (hu : z.norm < ((q * (D + 2).factorial : ℕ) + 2 + D : ℤ)^2)
    (haxis : z.re = 0 ∨ z.im = 0) : ¬ Prime z := by
  let P : ℕ := (D + 2).factorial
  have hP : 0 < P := Nat.factorial_pos _
  let t : ℤ := |z.re| + |z.im|
  have ht0 : 0 ≤ t := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have ht : z.norm = t^2 := by
    rcases haxis with hr | hi
    · simp [gaussian_norm_sq, t, hr]
    · simp [gaussian_norm_sq, t, hi]
  have hqP : 0 < (q : ℤ) * P := by positivity
  have htl : (q : ℤ) * P + 2 < t := by
    have hs : ((q : ℤ) * P + 2)^2 < t^2 := by simpa [P, ht] using hl
    nlinarith
  have htu : t < (q : ℤ) * P + 2 + D := by
    have hs : t^2 < ((q : ℤ) * P + 2 + D)^2 := by simpa [P, ht] using hu
    have hD : (0 : ℤ) ≤ D := Int.natCast_nonneg D
    nlinarith
  let j : ℕ := (t - (q : ℤ) * P).toNat
  have hj : (j : ℤ) = t - (q : ℤ) * P := Int.toNat_of_nonneg (by omega)
  have hj2 : 2 ≤ j := by omega
  have hjD : j ≤ D + 2 := by omega
  have hjP : j ∣ P := Nat.dvd_factorial (by omega) hjD
  have hjt : (j : ℤ) ∣ t := by
    have hprod : (j : ℤ) ∣ (q : ℤ) * P := dvd_mul_of_dvd_right (by exact_mod_cast hjP) _
    have he : t = (q : ℤ) * P + (j : ℤ) := by omega
    rw [he]
    exact dvd_add hprod (dvd_refl _)
  have hjcoords : (j : ℤ) ∣ z.re ∧ (j : ℤ) ∣ z.im := by
    rcases haxis with hr | hi
    · have h : (j : ℤ) ∣ |z.im| := by simpa [t, hr] using hjt
      exact ⟨by rw [hr]; exact dvd_zero _, by simpa only [dvd_abs] using h⟩
    · have h : (j : ℤ) ∣ |z.re| := by simpa [t, hi] using hjt
      exact ⟨by simpa only [dvd_abs] using h, by rw [hi]; exact dvd_zero _⟩
  apply not_prime_of_small_divisor (a := (j : GaussianInt))
  · exact (Zsqrtd.intCast_dvd j z).mpr hjcoords
  · simp only [gaussian_norm_sq, Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    have hji : (2 : ℤ) ≤ j := by exact_mod_cast hj2
    nlinarith
  · have hjlt : (j : ℤ) < t := by omega
    simp only [gaussian_norm_sq, Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    rw [← gaussian_norm_sq, ht]
    nlinarith [Int.natCast_nonneg j]

/-- A Gaussian prime ray would imply a uniform square-root-scale bound on
ordinary prime gaps. The constant obtained here is ineffective for small-scale
applications (it contains a factorial), but independent of the radius. -/
theorem split_prime_between_shifted_squares
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    ∃ K : ℕ, 0 < K ∧ ∀ r : ℕ, ∃ p : ℕ,
      p.Prime ∧ p % 4 = 1 ∧ r^2 < p ∧ p < (r + K)^2 := by
  have hC : 0 < C := lt_of_le_of_lt (GaussianInt.norm_nonneg _) (h 0).2
  let D : ℕ := C.toNat
  have hD : (D : ℤ) = C := Int.toNat_of_nonneg hC.le
  let P : ℕ := (D + 2).factorial
  have hP : 0 < P := Nat.factorial_pos _
  let S : ℕ := (x 0).norm.natAbs + 1
  let K : ℕ := S + P + D + 2
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro r
  let q : ℕ := (r + S) / P + 1
  have hq : 0 < q := Nat.succ_pos _
  have hqPeq : q * P = ((r + S) / P) * P + P := by dsimp [q]; ring
  have hmod := Nat.mod_lt (r + S) hP
  have hdiv := Nat.mod_add_div (r + S) P
  rw [Nat.mul_comm P] at hdiv
  have hqPl : r + S < q * P := by omega
  have hqPu : q * P ≤ r + S + P := by omega
  let R : ℤ := (q * P : ℕ) + 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrR : (r : ℤ) < R := by dsimp [R]; exact_mod_cast (by omega : r < q * P + 2)
  have hstart : (x 0).norm ≤ R^2 := by
    have hn0 : (x 0).norm ≤ (S : ℤ) := by simp [S]
    have hSR : (S : ℤ) ≤ R := by dsimp [R]; exact_mod_cast (by omega : S ≤ q * P + 2)
    exact (hn0.trans hSR).trans (Int.le_self_sq R)
  obtain ⟨n, hnlo, hnhi⟩ := ray_meets_annulus x C R hx (fun n => (h n).2) hR hstart
  have hnprime := (h n).1
  have hoffaxis : (x n).re ≠ 0 ∧ (x n).im ≠ 0 := by
    have hl : ((q * (D + 2).factorial : ℕ) + 2 : ℤ)^2 < (x n).norm := hnlo
    have hu : (x n).norm < ((q * (D + 2).factorial : ℕ) + 2 + D : ℤ)^2 := by
      simpa only [hD] using hnhi
    constructor
    · intro he
      exact axis_not_prime_in_factorial_annulus D q hq hl hu (Or.inl he) hnprime
    · intro he
      exact axis_not_prime_in_factorial_annulus D q hq hl hu (Or.inr he) hnprime
  have hnmod : (x n).norm.natAbs % 4 = 1 := by
    have hR2 : (2 : ℤ) ≤ R := by dsimp [R]; omega
    have hlarge : 2 < (x n).norm := by nlinarith
    have hm := norm_mod_four_of_large_prime hnprime hlarge
    have hm' : ((x n).norm.natAbs : ℤ) % 4 = 1 := by simpa using hm
    exact_mod_cast hm'
  refine ⟨(x n).norm.natAbs, norm_prime_of_off_axis hnprime hoffaxis.1 hoffaxis.2,
    hnmod, ?_, ?_⟩
  · have hr2 : (r : ℤ)^2 < R^2 := by nlinarith [Int.natCast_nonneg r]
    have ht : (r : ℤ)^2 < ((x n).norm.natAbs : ℤ) := by
      rw [GaussianInt.abs_natCast_norm]
      exact hr2.trans hnlo
    exact_mod_cast ht
  · have hRK : R + C ≤ ((r + K : ℕ) : ℤ) := by
      have hpu : ((q * P : ℕ) : ℤ) ≤ ((r + S + P : ℕ) : ℤ) := by exact_mod_cast hqPu
      dsimp [R, K]
      push_cast at hpu ⊢
      omega
    have hsq : (R + C)^2 ≤ (((r + K : ℕ) : ℤ))^2 := by nlinarith
    have ht : ((x n).norm.natAbs : ℤ) < (((r + K : ℕ) : ℤ))^2 := by
      rw [GaussianInt.abs_natCast_norm]
      exact hnhi.trans_le hsq
    exact_mod_cast ht

theorem rational_prime_between_shifted_squares
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    ∃ K : ℕ, 0 < K ∧ ∀ r : ℕ, ∃ p : ℕ,
      p.Prime ∧ r^2 < p ∧ p < (r + K)^2 := by
  obtain ⟨K, hK, hp⟩ := split_prime_between_shifted_squares x C hx h
  refine ⟨K, hK, fun r => ?_⟩
  obtain ⟨p, hprime, _, hl, hu⟩ := hp r
  exact ⟨p, hprime, hl, hu⟩

#print axioms split_prime_between_shifted_squares

#print axioms axis_not_prime_in_factorial_annulus
#print axioms rational_prime_between_shifted_squares

#print axioms norm_prime_of_off_axis
#print axioms ray_meets_annulus

end AnnularNecessity
end Erdos952Investigation
