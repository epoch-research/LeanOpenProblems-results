import Submission.PowerfulStructure

/-!
# Quartic rigidity and kernel exclusions for powerful triples

This helper file is unconditional. It does not import `Submission.Spec`, prove
Erdős 364, or use a powerful-triple existence/nonexistence assertion as a premise.
`Submission.PowerfulStructure` is imported without modification.

The main results are:
* Fermat's square-area right-triangle theorem, proved by infinite descent using
  mathlib's classification of primitive Pythagorean triples;
* quartic rigidity over both `ℤ` and `ℕ`, in particular `x⁴ + 1 = 2y²`;
* exclusion of the entire `D = 1` and `S = 1` slices of `t³ - t = D³S²`;
* exclusion of every prime `D` for even centers, giving infinitely many excluded
  positive squarefree kernels;
* complete exclusion of every `D = 2p` with prime `p` for even centers, by
  elementary coprime factorization and quartic rigidity, without Pell sequences;
* infinitely many excluded composite positive squarefree kernels;
* an exact strengthened global reduction requiring composite squarefree `D`
  that is not twice a prime, and `S ≥ 2`.

The `D = 2p` gap is fully closed. No exclusion of all remaining kernels, and no
resolution of the unrestricted powerful-triple problem, is claimed here.
-/

namespace Erdos364.QuarticObstruction

/- ## Fermat's square-area descent -/

private structure SquareArea (a b c d : ℤ) : Prop where
  pos_left : 0 < a
  pos_right : 0 < b
  pos_hyp : 0 < c
  pythagorean : PythagoreanTriple a b c
  area : 2 * a * b = d ^ 2

private def MinimalSquareArea (a b c d : ℤ) : Prop :=
  SquareArea a b c d ∧
    ∀ a' b' c' d' : ℤ, SquareArea a' b' c' d' → c.natAbs ≤ c'.natAbs

private theorem exists_minimal_square_area {a b c d : ℤ} (h : SquareArea a b c d) :
    ∃ a' b' c' d', MinimalSquareArea a' b' c' d' := by
  classical
  have hex : ∃ n : ℕ, ∃ a' b' c' d' : ℤ,
      SquareArea a' b' c' d' ∧ c'.natAbs = n :=
    ⟨c.natAbs, a, b, c, d, h, rfl⟩
  obtain ⟨a', b', c', d', hs, hc⟩ := Nat.find_spec hex
  refine ⟨a', b', c', d', hs, ?_⟩
  intro a'' b'' c'' d'' hh
  rw [hc]
  exact Nat.find_min' hex ⟨a'', b'', c'', d'', hh, rfl⟩

private theorem coprime_of_minimal_square_area {a b c d : ℤ}
    (h : MinimalSquareArea a b c d) : Int.gcd a b = 1 := by
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a', ha⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b', hb⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ∣ c := by
    apply (Int.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    refine ⟨a' ^ 2 + b' ^ 2, ?_⟩
    have ht := h.1.pythagorean.eq
    rw [ha, hb] at ht
    linear_combination -ht
  have hpd : (p : ℤ) ∣ d := by
    apply (Int.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    refine ⟨2 * a' * b', ?_⟩
    have ht := h.1.area
    rw [ha, hb] at ht
    linear_combination -ht
  obtain ⟨c', hc⟩ := hpc
  obtain ⟨d', hd⟩ := hpd
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hpp : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hh : SquareArea a' b' c' d' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (mul_pos_iff_of_pos_left hpp).mp (ha ▸ h.1.pos_left)
    · exact (mul_pos_iff_of_pos_left hpp).mp (hb ▸ h.1.pos_right)
    · exact (mul_pos_iff_of_pos_left hpp).mp (hc ▸ h.1.pos_hyp)
    · apply (PythagoreanTriple.mul_iff (p : ℤ) hp0).mp
      simpa only [← ha, ← hb, ← hc] using h.1.pythagorean
    · apply (mul_left_inj' (pow_ne_zero 2 hp0)).mp
      have ht := h.1.area
      rw [ha, hb, hd] at ht
      linear_combination ht
  have hlt : c'.natAbs < c.natAbs := by
    rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hh.pos_hyp.ne') hp.one_lt
  exact (not_le_of_gt hlt) (h.2 a' b' c' d' hh)

private theorem positive_square_factor {a b c : ℤ} (ha : 0 < a)
    (hab : IsCoprime a b) (h : a * b = c ^ 2) : ∃ r : ℤ, a = r ^ 2 := by
  obtain ⟨r, hr | hr⟩ := Int.sq_of_isCoprime hab h
  · exact ⟨r, hr⟩
  · have := sq_nonneg r
    omega

private theorem coprime_add_sub {m n : ℤ} (h : Int.gcd m n = 1)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Int.gcd (m + n) (m - n) = 1 := by
  have hsum : (m + n) % 2 = 1 := by
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩ <;> simp [Int.add_emod, hm, hn]
  by_contra hh
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
  rw [← Int.natCast_dvd] at hpa hpb
  have hpm : (p : ℤ) ∣ 2 * m ^ 2 := by
    convert dvd_mul_of_dvd_left (dvd_add hpa hpb) m using 1; ring
  have hpn : (p : ℤ) ∣ 2 * n ^ 2 := by
    convert dvd_mul_of_dvd_left (dvd_sub hpa hpb) n using 1; ring
  have hm := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp hpm
  have hn := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp hpn
  by_cases hp2 : p = 2
  · have hh : (m + n) % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      simpa only [hp2] using hpa
    omega
  · apply hp.not_dvd_one
    rw [← h]
    exact Nat.dvd_gcd (hm.resolve_left hp2) (hn.resolve_left hp2)

/- The descent factors the square area into the pairwise-coprime factors
`m`, `n`, `m+n`, `m-n`. They are squares. If `m+n=w²`, `m-n=z²`,
the smaller square-area triangle has legs `(w+z)/2`, `(w-z)/2` and
hypotenuse `√m`. Oddness makes the two half-sums integers. -/
private theorem not_minimal_square_area {a b c d : ℤ}
    (h : MinimalSquareArea a b c d) (haodd : a % 2 = 1) : False := by
  have hcop := coprime_of_minimal_square_area h
  obtain ⟨m, n, ham, hbn, hcm, hmn, hpar, hm⟩ :=
    h.1.pythagorean.coprime_classification' hcop haodd h.1.pos_hyp
  have hm0 : m ≠ 0 := by
    intro hz
    have hb := h.1.pos_right
    rw [hbn, hz] at hb
    norm_num at hb
  have hmpos : 0 < m := lt_of_le_of_ne hm hm0.symm
  have hnpos : 0 < n := by
    apply (mul_pos_iff_of_pos_left (mul_pos (by norm_num : (0 : ℤ) < 2) hmpos)).mp
    rw [← hbn]
    exact h.1.pos_right
  have hnm : n < m := by
    apply (sq_lt_sq₀ hnpos.le hmpos.le).mp
    have ha := h.1.pos_left
    rw [ham] at ha
    omega
  have hd2 : (2 : ℤ) ∣ d := by
    apply (Int.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    refine ⟨a * m * n, ?_⟩
    have ht := h.1.area
    rw [hbn] at ht
    linear_combination -ht
  obtain ⟨e, he⟩ := hd2
  have harea : m * (n * (m ^ 2 - n ^ 2)) = e ^ 2 := by
    have ht := h.1.area
    rw [ham, hbn, he] at ht
    nlinarith only [ht]
  have hcp : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hma : IsCoprime m (m ^ 2 - n ^ 2) := by
    convert (hcp.pow_right (n := 2)).neg_right.add_mul_right_right m using 1; ring
  have hna : IsCoprime n (m ^ 2 - n ^ 2) := by
    convert (hcp.symm.pow_right (n := 2)).add_mul_right_right (-n) using 1; ring
  obtain ⟨i, hi⟩ := positive_square_factor hmpos (hcp.mul_right hma) harea
  have hnarea : n * (m * (m ^ 2 - n ^ 2)) = e ^ 2 := by
    nlinarith only [harea]
  obtain ⟨j, hj⟩ := positive_square_factor hnpos (hcp.symm.mul_right hna) hnarea
  have haarea : (m ^ 2 - n ^ 2) * (m * n) = e ^ 2 := by
    nlinarith only [harea]
  obtain ⟨k, hk⟩ := positive_square_factor (ham ▸ h.1.pos_left)
    (hma.symm.mul_right hna.symm) haarea
  have hpm : (m + n) * (m - n) = k ^ 2 := by
    nlinarith only [hk]
  have hpmcop : IsCoprime (m + n) (m - n) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (coprime_add_sub hmn hpar)
  obtain ⟨w0, hw0⟩ := positive_square_factor (by omega : 0 < m + n) hpmcop hpm
  obtain ⟨z0, hz0⟩ := positive_square_factor (by omega : 0 < m - n)
    hpmcop.symm (by simpa only [mul_comm] using hpm)
  let w : ℤ := |w0|
  let z : ℤ := |z0|
  have hw : m + n = w ^ 2 := by simpa only [w, sq_abs] using hw0
  have hz : m - n = z ^ 2 := by simpa only [z, sq_abs] using hz0
  have hwpos : 0 < w := by
    have := abs_nonneg w0
    change 0 ≤ w at this
    nlinarith
  have hznonneg : 0 ≤ z := abs_nonneg z0
  have hzw : z < w := by
    apply (sq_lt_sq₀ hznonneg hwpos.le).mp
    omega
  have hsumodd : Odd (m + n) := by
    apply Int.odd_iff.mpr
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩ <;> simp [Int.add_emod, hm, hn]
  have hdiffodd : Odd (m - n) := by
    apply Int.odd_iff.mpr
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩ <;> simp [Int.sub_emod, hm, hn]
  have hwodd : Odd w := (Int.odd_pow.mp (hw ▸ hsumodd)).resolve_right (by decide : 2 ≠ 0)
  have hzodd : Odd z := (Int.odd_pow.mp (hz ▸ hdiffodd)).resolve_right (by decide : 2 ≠ 0)
  obtain ⟨u, hu⟩ := hwodd
  obtain ⟨v, hv⟩ := hzodd
  let r : ℤ := u + v + 1
  let s : ℤ := u - v
  have hrpos : 0 < r := by dsimp [r]; omega
  have hspos : 0 < s := by dsimp [s]; omega
  have hmrs : r ^ 2 + s ^ 2 = m := by
    dsimp [r, s]
    have hw' := hw
    have hz' := hz
    rw [hu] at hw'
    rw [hv] at hz'
    nlinarith only [hw', hz']
  have hnrs : 2 * r * s = n := by
    dsimp [r, s]
    have hw' := hw
    have hz' := hz
    rw [hu] at hw'
    rw [hv] at hz'
    nlinarith only [hw', hz']
  have hi0 : i ≠ 0 := by intro hh; rw [hh] at hi; norm_num at hi; omega
  have hnew : SquareArea r s |i| j := by
    refine ⟨hrpos, hspos, abs_pos.mpr hi0, ?_, ?_⟩
    · unfold PythagoreanTriple
      nlinarith only [hmrs, hi, sq_abs i]
    · exact hnrs.trans hj
  have hsmall : (|i|).natAbs < c.natAbs := by
    rw [Int.natAbs_abs]
    apply Int.ofNat_lt.mp
    rw [Int.natAbs_of_nonneg h.1.pos_hyp.le]
    have hiabs := Int.natAbs_le_self_sq i
    rw [← hi] at hiabs
    have hmm := Int.le_self_sq m
    have hn := sq_pos_of_ne_zero hnpos.ne'
    rw [hcm]
    omega
  exact (not_le_of_gt hsmall) (h.2 r s |i| j hnew)

/-- Fermat's square-area obstruction, in a denominator-free form. -/
theorem not_square_area_triangle {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hpy : PythagoreanTriple a b c) : 2 * a * b ≠ d ^ 2 := by
  intro heq
  obtain ⟨a', b', c', d', hh⟩ := exists_minimal_square_area
    (show SquareArea a b c d from ⟨ha, hb, hc, hpy, heq⟩)
  have hcop := coprime_of_minimal_square_area hh
  rcases hh.1.pythagorean.even_odd_of_coprime hcop with hp | hp
  · apply not_minimal_square_area (a := b') (b := a') (c := c') (d := d') _ hp.2
    refine ⟨⟨hh.1.pos_right, hh.1.pos_left, hh.1.pos_hyp,
      hh.1.pythagorean.symm, ?_⟩, hh.2⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh.1.area
  · exact not_minimal_square_area hh hp.1


/- ## Quartic rigidity over `ℤ` and `ℕ` -/

/-- Signed legs give the same square-area obstruction after taking absolute values. -/
theorem not_square_area_triangle_of_ne_zero {a b c d : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hpy : PythagoreanTriple a b c) : 2 * a * b ≠ d ^ 2 := by
  intro heq
  have hd : d ≠ 0 := by
    intro hd
    have hmul : (2 : ℤ) * a * b ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
    apply hmul
    simpa only [hd, zero_pow (by decide : 2 ≠ 0)] using heq
  have hab : 0 < a * b := by nlinarith [sq_pos_of_ne_zero hd]
  have hc : c ≠ 0 := by
    intro hc
    have hh := hpy.eq
    rw [hc] at hh
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
  have hpabs : PythagoreanTriple |a| |b| |c| := by
    unfold PythagoreanTriple
    nlinarith only [hpy.eq, sq_abs a, sq_abs b, sq_abs c]
  apply not_square_area_triangle (abs_pos.mpr ha) (abs_pos.mpr hb) (abs_pos.mpr hc) hpabs
  calc
    2 * |a| * |b| = 2 * |a * b| := by rw [abs_mul]; ring
    _ = 2 * (a * b) := by rw [abs_of_pos hab]
    _ = d ^ 2 := by nlinarith only [heq]

/-- Fermat's quartic rigidity: the two fourth powers in twice a square must be equal. -/
theorem two_fourth_powers_rigidity_int {a b c : ℤ}
    (h : a ^ 4 + b ^ 4 = 2 * c ^ 2) : a ^ 2 = b ^ 2 ∧ c ^ 2 = a ^ 4 := by
  have hab : a ^ 2 = b ^ 2 := by
    by_contra hh
    have hd : a ^ 2 - b ^ 2 ≠ 0 := sub_ne_zero.mpr hh
    have harea : 2 * (c + a * b) * (c - a * b) = (a ^ 2 - b ^ 2) ^ 2 := by
      nlinarith only [h]
    have hleft : c + a * b ≠ 0 := by
      intro hz
      rw [hz] at harea
      have := pow_ne_zero 2 hd
      simp only [mul_zero, zero_mul] at harea
      exact this harea.symm
    have hright : c - a * b ≠ 0 := by
      intro hz
      rw [hz] at harea
      have := pow_ne_zero 2 hd
      simp only [mul_zero] at harea
      exact this harea.symm
    have hpy : PythagoreanTriple (c + a * b) (c - a * b) (a ^ 2 + b ^ 2) := by
      unfold PythagoreanTriple
      nlinarith only [h]
    exact not_square_area_triangle_of_ne_zero hleft hright hpy harea
  refine ⟨hab, ?_⟩
  have hab4 : a ^ 4 = b ^ 4 := by nlinarith only [congrArg (fun z : ℤ => z ^ 2) hab]
  omega

/-- Over the naturals there are no distinct fourth powers with square average. -/
theorem two_fourth_powers_rigidity_nat {a b c : ℕ}
    (h : a ^ 4 + b ^ 4 = 2 * c ^ 2) : a = b ∧ c = a ^ 2 := by
  have hh : (a : ℤ) ^ 4 + (b : ℤ) ^ 4 = 2 * (c : ℤ) ^ 2 := by exact_mod_cast h
  obtain ⟨hab, hc⟩ := two_fourth_powers_rigidity_int hh
  have hab' : a ^ 2 = b ^ 2 := by exact_mod_cast hab
  have hc' : c ^ 2 = (a ^ 2) ^ 2 := by exact_mod_cast (by nlinarith only [hc] :
    (c : ℤ) ^ 2 = ((a : ℤ) ^ 2) ^ 2)
  exact ⟨(Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hab',
    (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hc'⟩

/-- The requested integer equation has only the four sign choices of `(1, 1)`. -/
theorem fermat_quartic_int {x y : ℤ} (h : x ^ 4 + 1 = 2 * y ^ 2) :
    (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) := by
  have hh : x ^ 4 + (1 : ℤ) ^ 4 = 2 * y ^ 2 := by simpa only [one_pow] using h
  obtain ⟨hx, hy⟩ := two_fourth_powers_rigidity_int hh
  have hx' : x ^ 2 = 1 := by simpa only [one_pow] using hx
  have hx4 : x ^ 4 = 1 := by nlinarith only [congrArg (fun z : ℤ => z ^ 2) hx']
  have hy' : y ^ 2 = 1 := by omega
  exact ⟨eq_or_eq_neg_of_sq_eq_sq x 1 (by simpa only [one_pow] using hx'),
    eq_or_eq_neg_of_sq_eq_sq y 1 (by simpa only [one_pow] using hy')⟩

/-- Natural-number quartic rigidity, including all zero and boundary cases. -/
theorem fermat_quartic_nat {x y : ℕ} (h : x ^ 4 + 1 = 2 * y ^ 2) : x = 1 ∧ y = 1 := by
  have hh : x ^ 4 + (1 : ℕ) ^ 4 = 2 * y ^ 2 := by simpa only [one_pow] using h
  obtain ⟨hx, hy⟩ := two_fourth_powers_rigidity_nat hh
  exact ⟨hx, by simpa only [hx, one_pow] using hy⟩

theorem fermat_quartic_nat_iff (x y : ℕ) :
    x ^ 4 + 1 = 2 * y ^ 2 ↔ x = 1 ∧ y = 1 := by
  refine ⟨fermat_quartic_nat, ?_⟩
  rintro ⟨rfl, rfl⟩
  norm_num

theorem fermat_quartic_int_iff (x y : ℤ) :
    x ^ 4 + 1 = 2 * y ^ 2 ↔ (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) := by
  refine ⟨fermat_quartic_int, ?_⟩
  rintro ⟨rfl | rfl, rfl | rfl⟩ <;> norm_num

/- ## The `S = 1` and `D = 1` slices -/

/-- The centered cubic lies strictly between two consecutive cubes for `t ≥ 2`. -/
theorem cube_sub_self_between_cubes {t : ℕ} (ht : 2 ≤ t) :
    (t - 1) ^ 3 < t ^ 3 - t ∧ t ^ 3 - t < t ^ 3 := by
  have hprev : t - 1 + 1 = t := by omega
  have hlow : (t - 1) ^ 3 + (t - 1 + 1) < (t - 1 + 1) ^ 3 := by
    have hpos : 0 < t - 1 := by omega
    nlinarith [Nat.zero_le ((t - 1) ^ 2)]
  rw [hprev] at hlow
  have hle : t ≤ t ^ 3 := Nat.le_self_pow (by decide : 3 ≠ 0) t
  have hadd := Nat.sub_add_cancel hle
  constructor <;> omega

/-- Thus the entire `S = 1` slice of the canonical equation is impossible. -/
theorem cube_sub_self_ne_cube {t D : ℕ} (ht : 2 ≤ t) : t ^ 3 - t ≠ D ^ 3 := by
  intro heq
  have hb := cube_sub_self_between_cubes ht
  rw [heq] at hb
  have hl := (Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp hb.1
  have hu := (Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp hb.2
  omega

/-- The `D = 1` slice is impossible even without the even-center hypothesis. -/
theorem cube_sub_self_ne_square {t S : ℕ} (ht : 2 ≤ t) : t ^ 3 - t ≠ S ^ 2 := by
  intro heq
  have hle : t ≤ t ^ 3 := Nat.le_self_pow (by decide : 3 ≠ 0) t
  have heqadd := (Nat.sub_eq_iff_eq_add hle).mp heq
  have heqZ : (t : ℤ) ^ 3 = (S : ℤ) ^ 2 + t := by exact_mod_cast heqadd
  have htZ : (2 : ℤ) ≤ t := by exact_mod_cast ht
  have hpy : PythagoreanTriple ((t : ℤ) ^ 2 - 1) (2 * t) ((t : ℤ) ^ 2 + 1) := by
    unfold PythagoreanTriple
    ring
  apply not_square_area_triangle (a := (t : ℤ) ^ 2 - 1) (b := 2 * t)
    (c := (t : ℤ) ^ 2 + 1) (d := 2 * S) (by nlinarith) (by omega) (by positivity) hpy
  nlinarith only [heqZ]

open Erdos364.PowerfulStructure

/- ## Coprime extraction and the infinite prime-kernel family -/

/-- A coprime factor of a natural-number square is itself a square. -/
theorem square_of_coprime_mul {a b c : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ 2) : ∃ u : ℕ, a = u ^ 2 := by
  apply exists_eq_pow_of_mul_eq_pow (c := c) (k := 2) _ h
  change IsUnit (Nat.gcd a b)
  rw [hab]
  exact isUnit_one

/-- A factor coprime to the cubic kernel is a square, provided it is coprime to
its complementary factor. Squarefreeness of the kernel is not needed. -/
theorem square_factor_of_cubic_product {a b D S : ℕ} (hab : Nat.Coprime a b)
    (haD : Nat.Coprime a D) (heq : a * b = D ^ 3 * S ^ 2) : ∃ u : ℕ, a = u ^ 2 := by
  apply square_of_coprime_mul ((haD.pow_right 3).mul_right hab)
  calc
    a * (D ^ 3 * b) = D ^ 3 * (a * b) := by ring
    _ = D ^ 3 * (D ^ 3 * S ^ 2) := by rw [heq]
    _ = (D ^ 3 * S) ^ 2 := by ring

/-- Any entry coprime to `D` in an even-centered cubic solution must be a square. -/
theorem centered_cubic_square_factors {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) :
    (Nat.Coprime (t - 1) D → ∃ u : ℕ, t - 1 = u ^ 2) ∧
      (Nat.Coprime t D → ∃ u : ℕ, t = u ^ 2) ∧
      (Nat.Coprime (t + 1) D → ∃ u : ℕ, t + 1 = u ^ 2) := by
  have hc := centered_pairwise_coprime ht he
  have hp := heq
  rw [cube_sub_self_eq_centered_product] at hp
  refine ⟨?_, ?_, ?_⟩
  · intro hD
    apply square_factor_of_cubic_product (hc.1.mul_right hc.2.1) hD
    simpa only [mul_assoc] using hp
  · intro hD
    apply square_factor_of_cubic_product (hc.1.symm.mul_right hc.2.2) hD
    calc
      t * ((t - 1) * (t + 1)) = (t - 1) * t * (t + 1) := by ring
      _ = D ^ 3 * S ^ 2 := hp
  · intro hD
    apply square_factor_of_cubic_product (hc.2.1.symm.mul_right hc.2.2.symm) hD
    calc
      (t + 1) * ((t - 1) * t) = (t - 1) * t * (t + 1) := by ring
      _ = D ^ 3 * S ^ 2 := hp

/-- Consecutive squares above zero are at least three apart. -/
theorem sq_add_one_ne_sq {a b : ℕ} (ha : 0 < a) : a ^ 2 + 1 ≠ b ^ 2 := by
  intro h
  have hab : a < b := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  have hb : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega : a + 1 ≤ b) 2
  nlinarith

theorem sq_add_two_ne_sq {a b : ℕ} (ha : 0 < a) : a ^ 2 + 2 ≠ b ^ 2 := by
  intro h
  have hab : a < b := (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (by omega)
  have hb : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega : a + 1 ≤ b) 2
  nlinarith

private theorem prime_not_dvd_other {p a b : ℕ} (hp : Nat.Prime p)
    (hab : Nat.Coprime a b) (hpa : p ∣ a) : ¬p ∣ b := by
  intro hpb
  apply hp.not_dvd_one
  have hh := Nat.dvd_gcd hpa hpb
  rwa [hab] at hh

/-- Every prime cubic kernel is excluded, uniformly in the square factor.
This is an unbounded infinite family of canonical-kernel exclusions. -/
theorem even_cube_sub_self_ne_prime_cube_mul_sq {t p S : ℕ}
    (ht : 2 ≤ t) (he : Even t) (hp : Nat.Prime p) :
    t ^ 3 - t ≠ p ^ 3 * S ^ 2 := by
  intro heq
  have hs := centered_cubic_square_factors ht he heq
  have hc := centered_pairwise_coprime ht he
  have hprev : t - 1 + 1 = t := by omega
  have hnext : t - 1 + 2 = t + 1 := by omega
  by_cases hpleft : p ∣ t - 1
  · have hnmid := prime_not_dvd_other hp hc.1 hpleft
    have hnright := prime_not_dvd_other hp hc.2.1 hpleft
    obtain ⟨a, ha⟩ := hs.2.1 (hp.coprime_iff_not_dvd.mpr hnmid).symm
    obtain ⟨b, hb⟩ := hs.2.2 (hp.coprime_iff_not_dvd.mpr hnright).symm
    have hapos : 0 < a := by nlinarith [ht]
    apply sq_add_one_ne_sq (b := b) hapos
    omega
  · by_cases hpright : p ∣ t + 1
    · have hnmid := prime_not_dvd_other hp hc.2.2.symm hpright
      obtain ⟨a, ha⟩ := hs.1 (hp.coprime_iff_not_dvd.mpr hpleft).symm
      obtain ⟨b, hb⟩ := hs.2.1 (hp.coprime_iff_not_dvd.mpr hnmid).symm
      have hapos : 0 < a := by nlinarith [show 0 < t - 1 by omega]
      apply sq_add_one_ne_sq (b := b) hapos
      omega
    · obtain ⟨a, ha⟩ := hs.1 (hp.coprime_iff_not_dvd.mpr hpleft).symm
      obtain ⟨b, hb⟩ := hs.2.2 (hp.coprime_iff_not_dvd.mpr hpright).symm
      have hapos : 0 < a := by nlinarith [show 0 < t - 1 by omega]
      apply sq_add_two_ne_sq (b := b) hapos
      omega

/-- No cubic solution relevant to a powerful triple can have prime `D`. -/
theorem cubic_solution_D_not_prime {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : ¬Nat.Prime D := by
  intro hp
  exact even_cube_sub_self_ne_prime_cube_mul_sq ht he hp heq

/-- There are infinitely many positive squarefree kernels for which every
even-centered cubic equation is excluded. -/
theorem infinitely_many_excluded_squarefree_kernels :
    {D : ℕ | 0 < D ∧ Squarefree D ∧
      ¬∃ t S : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = D ^ 3 * S ^ 2}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨p, ⟨hp.pos, hp.squarefree, ?_⟩, by omega⟩
  rintro ⟨t, S, he, ht, heq⟩
  exact even_cube_sub_self_ne_prime_cube_mul_sq ht he hp heq

/- ## Strengthened canonical reduction -/

/-- Any positive-center cubic solution has a nontrivial cube factor. -/
theorem cubic_solution_D_ne_one {t D S : ℕ} (ht : 2 ≤ t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : D ≠ 1 := by
  intro hD
  apply cube_sub_self_ne_square (S := S) ht
  simpa only [hD, one_pow, one_mul] using heq

/-- Any positive-center cubic solution has a square factor greater than one. -/
theorem cubic_solution_S_ne_one {t D S : ℕ} (ht : 2 ≤ t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : S ≠ 1 := by
  intro hS
  apply cube_sub_self_ne_cube (D := D) ht
  simpa only [hS, one_pow, mul_one] using heq

/-- Necessary restrictions on the parameters of every even-centered cubic solution. -/
theorem cubic_solution_parameters {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : 1 < D ∧ ¬Nat.Prime D ∧ 2 ≤ S := by
  obtain ⟨_, _, _, _, _, hD, hS⟩ := cubic_solution_structure ht he heq
  have hDne := cubic_solution_D_ne_one ht heq
  have hSne := cubic_solution_S_ne_one ht heq
  exact ⟨by omega, cubic_solution_D_not_prime ht he heq, by omega⟩

/-- The full unbounded triple problem still has an exact canonical reduction
when the excluded kernel and square-factor families are removed. -/
theorem exists_powerful_triple_iff_composite_squarefree_cubic :
    (∃ n : ℕ, Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) ↔
      ∃ t D S : ℕ, Even t ∧ 2 ≤ t ∧ 1 < D ∧ Squarefree D ∧ ¬Nat.Prime D ∧
        2 ≤ S ∧ t ^ 3 - t = D ^ 3 * S ^ 2 := by
  rw [exists_powerful_triple_iff_squarefree_cubic]
  constructor
  · rintro ⟨t, D, S, he, ht, _, hsf, heq⟩
    have hp := cubic_solution_parameters ht he heq
    exact ⟨t, D, S, he, ht, hp.1, hsf, hp.2.1, hp.2.2, heq⟩
  · rintro ⟨t, D, S, he, ht, hD, hsf, _, _, heq⟩
    exact ⟨t, D, S, he, ht, by omega, hsf, heq⟩

/- ## Elementary `D = 2p` allocation and a direct quartic consequence -/

/-- If the complementary factor is coprime to the kernel, the entire cube
belongs to this factor, and what remains is a square. -/
theorem cubic_factor_of_coprime_product {a b D S : ℕ} (hD : 0 < D)
    (hab : Nat.Coprime a b) (hbD : Nat.Coprime b D)
    (heq : a * b = D ^ 3 * S ^ 2) : ∃ u : ℕ, a = D ^ 3 * u ^ 2 := by
  have hcube : D ^ 3 ∣ a := by
    apply (hbD.pow_right 3).symm.dvd_of_dvd_mul_right
    exact ⟨S ^ 2, heq⟩
  obtain ⟨r, hr⟩ := hcube
  have hra : r ∣ a := ⟨D ^ 3, by rw [hr]; ring⟩
  have hrcp : Nat.Coprime r b := hab.of_dvd_left hra
  have hrprod : r * b = S ^ 2 := by
    apply (mul_left_inj' (pow_ne_zero 3 hD.ne')).mp
    rw [hr] at heq
    nlinarith only [heq]
  obtain ⟨u, hu⟩ := square_of_coprime_mul hrcp hrprod
  exact ⟨u, by rw [hr, hu]⟩

private theorem centered_coprime_two {t : ℕ} (ht : 2 ≤ t) (he : Even t) :
    Nat.Coprime (t - 1) 2 ∧ Nat.Coprime (t + 1) 2 := by
  have hmod := Nat.even_iff.mp he
  constructor <;> apply Nat.coprime_two_right.mpr <;> apply Nat.odd_iff.mpr <;> omega

/-- For `D = 2p`, the odd prime cannot belong to the middle entry. -/
theorem two_prime_kernel_middle_not_dvd {t p S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (hp : Nat.Prime p) (heq : t ^ 3 - t = (2 * p) ^ 3 * S ^ 2) : ¬p ∣ t := by
  intro hpt
  have hc := centered_pairwise_coprime ht he
  have htwo := centered_coprime_two ht he
  have hs := centered_cubic_square_factors ht he heq
  have hpl : ¬p ∣ t - 1 := prime_not_dvd_other hp hc.1.symm hpt
  have hpr : ¬p ∣ t + 1 := prime_not_dvd_other hp hc.2.2 hpt
  obtain ⟨a, ha⟩ := hs.1 (htwo.1.mul_right (hp.coprime_iff_not_dvd.mpr hpl).symm)
  obtain ⟨b, hb⟩ := hs.2.2 (htwo.2.mul_right (hp.coprime_iff_not_dvd.mpr hpr).symm)
  have hapos : 0 < a := by nlinarith [show 0 < t - 1 by omega]
  apply sq_add_two_ne_sq (b := b) hapos
  omega

/-- Exact factor allocation for a hypothetical `D = 2p` solution.
Both resulting prime-cube/square Pell-neighbor systems are ruled out below by
`even_cube_sub_self_ne_two_prime_cube_mul_sq`. -/
theorem two_prime_kernel_pell_shape {t p S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (hp : Nat.Prime p) (heq : t ^ 3 - t = (2 * p) ^ 3 * S ^ 2) :
    ∃ u v w : ℕ, 0 < u ∧ 0 < v ∧ 0 < w ∧ t = 8 * u ^ 2 ∧
      ((t - 1 = p ^ 3 * v ^ 2 ∧ t + 1 = w ^ 2) ∨
       (t - 1 = w ^ 2 ∧ t + 1 = p ^ 3 * v ^ 2)) := by
  have hc := centered_pairwise_coprime ht he
  have htwo := centered_coprime_two ht he
  have hs := centered_cubic_square_factors ht he heq
  have hpt := two_prime_kernel_middle_not_dvd ht he hp heq
  have htp : Nat.Coprime t p := (hp.coprime_iff_not_dvd.mpr hpt).symm
  have htodd : Nat.Coprime t ((t - 1) * (t + 1)) := hc.1.symm.mul_right hc.2.2
  have hprod : t * ((t - 1) * (t + 1)) = 8 * (p ^ 3 * S ^ 2) := by
    calc
      _ = (t - 1) * t * (t + 1) := by ring
      _ = (2 * p) ^ 3 * S ^ 2 := by simpa only [cube_sub_self_eq_centered_product] using heq
      _ = 8 * (p ^ 3 * S ^ 2) := by ring
  have h8cp : Nat.Coprime 8 ((t - 1) * (t + 1)) := by
    have hh := (htwo.1.symm.mul_right htwo.2.symm).pow_left 3
    simpa only [show (2 : ℕ) ^ 3 = 8 by norm_num] using hh
  have h8 : 8 ∣ t := h8cp.dvd_of_dvd_mul_right ⟨p ^ 3 * S ^ 2, hprod⟩
  obtain ⟨r, hr⟩ := h8
  have hrt : r ∣ t := ⟨8, by rw [hr]; ring⟩
  have hrp : Nat.Coprime r p := htp.of_dvd_left hrt
  have hrodd : Nat.Coprime r ((t - 1) * (t + 1)) := htodd.of_dvd_left hrt
  have hprodR : r * ((t - 1) * (t + 1)) = p ^ 3 * S ^ 2 := by
    apply (mul_right_inj' (by norm_num : (8 : ℕ) ≠ 0)).mp
    calc
      8 * (r * ((t - 1) * (t + 1))) = (8 * r) * ((t - 1) * (t + 1)) := by ring
      _ = t * ((t - 1) * (t + 1)) := by rw [← hr]
      _ = 8 * (p ^ 3 * S ^ 2) := hprod
  obtain ⟨u, hu⟩ := square_factor_of_cubic_product hrodd hrp hprodR
  have htform : t = 8 * u ^ 2 := by rw [hr, hu]
  have hup : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] at htform
    omega
  have hleftprod : (t - 1) * (r * (t + 1)) = p ^ 3 * S ^ 2 := by
    nlinarith only [hprodR]
  have hrightprod : (t + 1) * (r * (t - 1)) = p ^ 3 * S ^ 2 := by
    nlinarith only [hprodR]
  have hcleft : Nat.Coprime (t - 1) (r * (t + 1)) :=
    (hc.1.of_dvd_right hrt).mul_right hc.2.1
  have hcright : Nat.Coprime (t + 1) (r * (t - 1)) :=
    (hc.2.2.symm.of_dvd_right hrt).mul_right hc.2.1.symm
  by_cases hpl : p ∣ t - 1
  · have hpr : ¬p ∣ t + 1 := by
      intro hh
      apply hp.not_dvd_one
      have hg := Nat.dvd_gcd hpl hh
      rwa [hc.2.1] at hg
    have hrightp : Nat.Coprime (t + 1) p := (hp.coprime_iff_not_dvd.mpr hpr).symm
    obtain ⟨v, hv⟩ := cubic_factor_of_coprime_product hp.pos hcleft
      (hrp.mul_left hrightp) hleftprod
    obtain ⟨w, hw⟩ := hs.2.2 (htwo.2.mul_right hrightp)
    have hvp : 0 < v := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp [hz] at hv
      omega
    have hwp : 0 < w := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp [hz] at hw
    exact ⟨u, v, w, hup, hvp, hwp, htform, Or.inl ⟨hv, hw⟩⟩
  · have hleftp : Nat.Coprime (t - 1) p := (hp.coprime_iff_not_dvd.mpr hpl).symm
    obtain ⟨v, hv⟩ := cubic_factor_of_coprime_product hp.pos hcright
      (hrp.mul_left hleftp) hrightprod
    obtain ⟨w, hw⟩ := hs.1 (htwo.1.mul_right hleftp)
    have hvp : 0 < v := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp [hz] at hv
    have hwp : 0 < w := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp [hz] at hw
      omega
    exact ⟨u, v, w, hup, hvp, hwp, htform, Or.inr ⟨hw, hv⟩⟩

/-- No first-index theorem or Pell classification is hidden in this equivalence:
excluding `D = 2p` is exactly excluding the displayed positive integer systems. -/
theorem exists_even_cubic_two_prime_iff (p : ℕ) (hp : Nat.Prime p) :
    (∃ t S : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = (2 * p) ^ 3 * S ^ 2) ↔
      ∃ u v w : ℕ, 0 < u ∧ 0 < v ∧ 0 < w ∧
        ((8 * u ^ 2 - 1 = p ^ 3 * v ^ 2 ∧ 8 * u ^ 2 + 1 = w ^ 2) ∨
         (8 * u ^ 2 - 1 = w ^ 2 ∧ 8 * u ^ 2 + 1 = p ^ 3 * v ^ 2)) := by
  constructor
  · rintro ⟨t, S, he, ht, heq⟩
    obtain ⟨u, v, w, hu, hv, hw, htform, hshape⟩ := two_prime_kernel_pell_shape ht he hp heq
    rw [htform] at hshape
    exact ⟨u, v, w, hu, hv, hw, hshape⟩
  · rintro ⟨u, v, w, hu, _, _, hshape⟩
    have ht : 2 ≤ 8 * u ^ 2 := by
      have hh := pow_pos hu 2
      omega
    refine ⟨8 * u ^ 2, u * v * w, ⟨4 * u ^ 2, by ring⟩, ht, ?_⟩
    rw [cube_sub_self_eq_centered_product]
    rcases hshape with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rw [hl, hr] <;> ring

/-- A direct quartic application: an eight-times-square center cannot be
one greater than a fourth power. There are no omitted zero cases here. -/
theorem eight_mul_sq_ne_fourth_add_one {u x : ℕ} : 8 * u ^ 2 ≠ x ^ 4 + 1 := by
  intro h
  have hh : x ^ 4 + 1 = 2 * (2 * u) ^ 2 := by
    calc
      _ = 8 * u ^ 2 := h.symm
      _ = 2 * (2 * u) ^ 2 := by ring
  have hy := (fermat_quartic_nat hh).2
  omega

theorem eight_mul_sq_sub_one_ne_fourth {u x : ℕ} (hu : 0 < u) :
    8 * u ^ 2 - 1 ≠ x ^ 4 := by
  intro h
  have hpos := pow_pos hu 2
  have hle : 1 ≤ 8 * u ^ 2 := by omega
  exact eight_mul_sq_ne_fourth_add_one ((Nat.sub_eq_iff_eq_add hle).mp h)

/-- A direct quartic consequence of the `D = 2p` allocation: the predecessor
cannot be a fourth power. The stronger exclusion of the whole family follows below. -/
theorem two_prime_kernel_predecessor_ne_fourth {t p S x : ℕ} (ht : 2 ≤ t)
    (he : Even t) (hp : Nat.Prime p)
    (heq : t ^ 3 - t = (2 * p) ^ 3 * S ^ 2) : t - 1 ≠ x ^ 4 := by
  obtain ⟨u, _, _, hu, _, _, htform, _⟩ := two_prime_kernel_pell_shape ht he hp heq
  rw [htform]
  exact eight_mul_sq_sub_one_ne_fourth hu

/- ## Complete `D = 2p` exclusion by elementary negative-Pell factors -/

private theorem pell_factor_bounds {u w : ℕ} (hu : 0 < u)
    (hw : w ^ 2 = 8 * u ^ 2 + 1) : 2 * u < w ∧ w < 4 * u := by
  have hu2 := pow_pos hu 2
  constructor <;> apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp <;>
    nlinarith only [hw, hu2]

private theorem square_mod_four_ne_three (w : ℕ) : w ^ 2 % 4 ≠ 3 := by
  have hm := Nat.mod_lt w (by decide : 0 < 4)
  have cases : w % 4 = 0 ∨ w % 4 = 1 ∨ w % 4 = 2 ∨ w % 4 = 3 := by omega
  rcases cases with h | h | h | h <;> simp [Nat.pow_mod, h]

private theorem pell_w_odd {u w : ℕ} (hw : w ^ 2 = 8 * u ^ 2 + 1) : Odd w := by
  apply (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp
  exact ⟨4 * u ^ 2, by omega⟩

/-- The two positive odd conjugate factors of `8u² - 1` are coprime.
A common prime is odd, divides `u` and `w`, and would therefore divide `1`. -/
theorem pell_factors_coprime {u w : ℕ} (hu : 0 < u)
    (hw : w ^ 2 = 8 * u ^ 2 + 1) : Nat.Coprime (4 * u - w) (4 * u + w) := by
  obtain ⟨_, hhigh⟩ := pell_factor_bounds hu hw
  have hGodd : Odd (4 * u + w) := by
    obtain ⟨r, hr⟩ := pell_w_odd hw
    exact ⟨2 * u + r, by omega⟩
  by_contra hcop
  obtain ⟨q, hq, hqF, hqG⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    have hGcp : Nat.Coprime 2 (4 * u + w) := Nat.coprime_two_left.mpr hGodd
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hGcp) hqG
  have hq8u : q ∣ 8 * u := by
    convert dvd_add hqF hqG using 1
    omega
  have hqu : q ∣ u := by
    rcases hq.dvd_mul.mp hq8u with hq8 | hqu
    · have hqpow : q ∣ 2 ^ 3 := by
        simpa only [show (2 : ℕ) ^ 3 = 8 by norm_num] using hq8
      have hqdiv2 := hq.dvd_of_dvd_pow hqpow
      exact False.elim (hq2 ((Nat.dvd_prime Nat.prime_two).mp hqdiv2 |>.resolve_left hq.ne_one))
    · exact hqu
  have hq4u : q ∣ 4 * u := dvd_mul_of_dvd_right hqu 4
  have hqw : q ∣ w := (Nat.dvd_add_iff_right hq4u).mpr hqG
  have hqw2 : q ∣ w ^ 2 := dvd_pow hqw (by decide : 2 ≠ 0)
  have hqu2 : q ∣ 8 * u ^ 2 :=
    dvd_mul_of_dvd_right (dvd_pow hqu (by decide : 2 ≠ 0)) 8
  apply hq.not_dvd_one
  exact (Nat.dvd_add_iff_right hqu2).mpr (hw ▸ hqw2)

/-- Explicit positivity, parity, and coprimality of the two factors used in the
obstruction; in particular the larger factor can never be `1`. -/
theorem pell_factor_properties {u w : ℕ} (hu : 0 < u)
    (hw : w ^ 2 = 8 * u ^ 2 + 1) :
    0 < 4 * u - w ∧ 7 ≤ 4 * u + w ∧ Odd (4 * u - w) ∧ Odd (4 * u + w) ∧
      Nat.Coprime (4 * u - w) (4 * u + w) := by
  obtain ⟨hlow, hhigh⟩ := pell_factor_bounds hu hw
  have hwmod := Nat.odd_iff.mp (pell_w_odd hw)
  exact ⟨by omega, by omega, Nat.odd_iff.mpr (by omega),
    Nat.odd_iff.mpr (by omega), pell_factors_coprime hu hw⟩

/-- Multiplying a prime-cube/square product by the prime makes a square.
At least one coprime factor is coprime to the prime, so that factor is a square. -/
theorem square_or_square_of_coprime_prime_cube_mul_sq {a b p v : ℕ}
    (hp : Nat.Prime p) (hab : Nat.Coprime a b) (heq : a * b = p ^ 3 * v ^ 2) :
    (∃ x : ℕ, a = x ^ 2) ∨ (∃ x : ℕ, b = x ^ 2) := by
  have hs : a * (p * b) = (p ^ 2 * v) ^ 2 := by
    calc
      _ = p * (a * b) := by ring
      _ = p * (p ^ 3 * v ^ 2) := by rw [heq]
      _ = _ := by ring
  by_cases hpa : p ∣ a
  · have hpb : ¬p ∣ b := prime_not_dvd_other hp hab hpa
    have hbp : Nat.Coprime b p := (hp.coprime_iff_not_dvd.mpr hpb).symm
    apply Or.inr
    apply square_of_coprime_mul (c := p ^ 2 * v) (hbp.mul_right hab.symm)
    nlinarith only [hs]
  · exact Or.inl (square_of_coprime_mul
      ((hp.coprime_iff_not_dvd.mpr hpa).symm.mul_right hab) hs)

/-- The conjugate factors have product `8u² - 1`, and both satisfy a
negative-Pell equation. All natural-number subtractions are justified by bounds. -/
theorem pell_factor_identities {u w : ℕ} (hu : 0 < u)
    (hw : w ^ 2 = 8 * u ^ 2 + 1) :
    (4 * u - w) * (4 * u + w) = 8 * u ^ 2 - 1 ∧
      (4 * u - w) ^ 2 + 1 = 2 * (w - 2 * u) ^ 2 ∧
      (4 * u + w) ^ 2 + 1 = 2 * (w + 2 * u) ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := pell_factor_bounds hu hw
  have hle : 1 ≤ 8 * u ^ 2 := by
    have hh := pow_pos hu 2
    omega
  constructor
  · zify [hhigh.le, hle] at hw ⊢
    nlinarith only [hw]
  constructor
  · zify [hhigh.le, hlow.le] at hw ⊢
    nlinarith only [hw]
  · nlinarith only [hw]

/-- The complete elementary prime-cube Pell obstruction. No positivity assumption
on `v`, fundamental-unit theorem, or Pell sequence is needed.

One of `4u-w`, `4u+w` is a square. Its negative-Pell equation and Fermat's quartic
rigidity force it to be `1`. The larger factor is at least `7`; the smaller factor
being `1` forces `u = 1`, leaving the impossible equation `7 = p³v²`. -/
theorem prime_cube_pell_obstruction {u w p v : ℕ} (hu : 0 < u)
    (hp : Nat.Prime p) (hw : w ^ 2 = 8 * u ^ 2 + 1)
    (hcube : 8 * u ^ 2 - 1 = p ^ 3 * v ^ 2) : False := by
  obtain ⟨_, hGseven, _, _, hcop⟩ := pell_factor_properties hu hw
  obtain ⟨hprod, hF, hG⟩ := pell_factor_identities hu hw
  rcases square_or_square_of_coprime_prime_cube_mul_sq hp hcop
      (hprod.trans hcube) with ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [hx] at hF
    have hquartic : x ^ 4 + 1 = 2 * (w - 2 * u) ^ 2 := by
      simpa only [← pow_mul, show 2 * 2 = 4 by norm_num] using hF
    have hxone := (fermat_quartic_nat hquartic).1
    have hFone : 4 * u - w = 1 := by simpa only [hxone, one_pow] using hx
    have hwlin : w + 1 = 4 * u := by omega
    have hwlin2 := congrArg (fun n : ℕ => n ^ 2) hwlin
    have huu : u ^ 2 = u := by nlinarith only [hw, hwlin, hwlin2]
    have huone : u = 1 := by nlinarith only [hu, huu]
    have heq7 : 7 = p ^ 3 * v ^ 2 := by simpa only [huone] using hcube
    have hvpos : 0 < v := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp [hz] at heq7
    have hp3 : 8 ≤ p ^ 3 := by
      have hh := Nat.pow_le_pow_left hp.two_le 3
      norm_num at hh
      exact hh
    have hv2 : 1 ≤ v ^ 2 := Nat.one_le_pow 2 v hvpos
    have hprodge := Nat.mul_le_mul_left (p ^ 3) hv2
    nlinarith only [heq7, hp3, hprodge]
  · rw [hx] at hG
    have hquartic : x ^ 4 + 1 = 2 * (w + 2 * u) ^ 2 := by
      simpa only [← pow_mul, show 2 * 2 = 4 by norm_num] using hG
    have hxone := (fermat_quartic_nat hquartic).1
    have hGone : 4 * u + w = 1 := by simpa only [hxone, one_pow] using hx
    omega

/-- The predecessor of a positive multiple of four is never a square. -/
theorem predecessor_ne_sq_of_mod_four_zero {t w : ℕ} (ht : 1 ≤ t)
    (hmod : t % 4 = 0) : t - 1 ≠ w ^ 2 := by
  intro hsq
  have hm : w ^ 2 % 4 = 3 := by omega
  exact square_mod_four_ne_three w hm

/-- The entire `D = 2p` family is excluded for every prime `p` and every square
factor `S`. Neither squarefreeness nor positivity of `S` is assumed. -/
theorem even_cube_sub_self_ne_two_prime_cube_mul_sq {t p S : ℕ}
    (ht : 2 ≤ t) (he : Even t) (hp : Nat.Prime p) :
    t ^ 3 - t ≠ (2 * p) ^ 3 * S ^ 2 := by
  intro heq
  obtain ⟨u, v, w, hu, _, _, htform, hshape⟩ := two_prime_kernel_pell_shape ht he hp heq
  rcases hshape with ⟨hv, hw⟩ | ⟨hw, _⟩
  · apply prime_cube_pell_obstruction hu hp (by omega : w ^ 2 = 8 * u ^ 2 + 1)
    simpa only [htform] using hv
  · exact predecessor_ne_sq_of_mod_four_zero (by omega) (by omega) hw

/- ## Infinite composite-kernel exclusions and the restricted global reduction -/

/-- The exclusion of `D = 2p` holds for the full unbounded existence statement. -/
theorem not_exists_even_cubic_two_prime (p : ℕ) (hp : Nat.Prime p) :
    ¬∃ t S : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = (2 * p) ^ 3 * S ^ 2 := by
  rintro ⟨t, S, he, ht, heq⟩
  exact even_cube_sub_self_ne_two_prime_cube_mul_sq ht he hp heq

/-- No kernel of an even-centered cubic solution can be twice a prime.
Squarefreeness of the kernel is not needed. -/
theorem cubic_solution_D_not_twice_prime {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) : ¬∃ p : ℕ, Nat.Prime p ∧ D = 2 * p := by
  rintro ⟨p, hp, rfl⟩
  exact even_cube_sub_self_ne_two_prime_cube_mul_sq ht he hp heq

/-- There are infinitely many excluded composite positive squarefree kernels.
The witnesses are `2p` for arbitrarily large odd primes `p`. -/
theorem infinitely_many_excluded_composite_squarefree_kernels :
    {D : ℕ | 1 < D ∧ Squarefree D ∧ ¬Nat.Prime D ∧
      ¬∃ t S : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = D ^ 3 * S ^ 2}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 3)
  have hp2 : p ≠ 2 := by omega
  have hcp : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have hsf : Squarefree (2 * p) :=
    (Nat.squarefree_mul hcp).mpr ⟨Nat.prime_two.squarefree, hp.squarefree⟩
  refine ⟨2 * p, ⟨by omega, hsf,
    Nat.not_prime_mul (by decide : 2 ≠ 1) hp.ne_one,
    not_exists_even_cubic_two_prime p hp⟩, by omega⟩

/-- Joint necessary restrictions after removing all prime and twice-prime kernels. -/
theorem cubic_solution_restricted_parameters {t D S : ℕ} (ht : 2 ≤ t) (he : Even t)
    (heq : t ^ 3 - t = D ^ 3 * S ^ 2) :
    1 < D ∧ ¬Nat.Prime D ∧ (¬∃ p : ℕ, Nat.Prime p ∧ D = 2 * p) ∧ 2 ≤ S := by
  obtain ⟨hD, hprime, hS⟩ := cubic_solution_parameters ht he heq
  exact ⟨hD, hprime, cubic_solution_D_not_twice_prime ht he heq, hS⟩

/-- An exact global reduction removing the excluded families, not a proof of the
remaining nonexistence problem: `D` is squarefree and composite but not twice a
prime, and `S ≥ 2`. The original triple-existence statement is unchanged. -/
theorem exists_powerful_triple_iff_restricted_squarefree_cubic :
    (∃ n : ℕ, Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) ↔
      ∃ t D S : ℕ, Even t ∧ 2 ≤ t ∧ 1 < D ∧ Squarefree D ∧ ¬Nat.Prime D ∧
        (¬∃ p : ℕ, Nat.Prime p ∧ D = 2 * p) ∧ 2 ≤ S ∧ t ^ 3 - t = D ^ 3 * S ^ 2 := by
  rw [exists_powerful_triple_iff_composite_squarefree_cubic]
  constructor
  · rintro ⟨t, D, S, he, ht, hD, hsf, hprime, hS, heq⟩
    exact ⟨t, D, S, he, ht, hD, hsf, hprime,
      cubic_solution_D_not_twice_prime ht he heq, hS, heq⟩
  · rintro ⟨t, D, S, he, ht, hD, hsf, hprime, _, hS, heq⟩
    exact ⟨t, D, S, he, ht, hD, hsf, hprime, hS, heq⟩

end Erdos364.QuarticObstruction

-- Exhaustive axiom audit of the public helper theorems.
#print axioms Erdos364.QuarticObstruction.not_square_area_triangle
#print axioms Erdos364.QuarticObstruction.not_square_area_triangle_of_ne_zero
#print axioms Erdos364.QuarticObstruction.two_fourth_powers_rigidity_int
#print axioms Erdos364.QuarticObstruction.two_fourth_powers_rigidity_nat
#print axioms Erdos364.QuarticObstruction.fermat_quartic_int
#print axioms Erdos364.QuarticObstruction.fermat_quartic_nat
#print axioms Erdos364.QuarticObstruction.fermat_quartic_nat_iff
#print axioms Erdos364.QuarticObstruction.fermat_quartic_int_iff
#print axioms Erdos364.QuarticObstruction.cube_sub_self_between_cubes
#print axioms Erdos364.QuarticObstruction.cube_sub_self_ne_cube
#print axioms Erdos364.QuarticObstruction.cube_sub_self_ne_square
#print axioms Erdos364.QuarticObstruction.square_of_coprime_mul
#print axioms Erdos364.QuarticObstruction.square_factor_of_cubic_product
#print axioms Erdos364.QuarticObstruction.centered_cubic_square_factors
#print axioms Erdos364.QuarticObstruction.sq_add_one_ne_sq
#print axioms Erdos364.QuarticObstruction.sq_add_two_ne_sq
#print axioms Erdos364.QuarticObstruction.even_cube_sub_self_ne_prime_cube_mul_sq
#print axioms Erdos364.QuarticObstruction.cubic_solution_D_not_prime
#print axioms Erdos364.QuarticObstruction.infinitely_many_excluded_squarefree_kernels
#print axioms Erdos364.QuarticObstruction.cubic_solution_D_ne_one
#print axioms Erdos364.QuarticObstruction.cubic_solution_S_ne_one
#print axioms Erdos364.QuarticObstruction.cubic_solution_parameters
#print axioms Erdos364.QuarticObstruction.exists_powerful_triple_iff_composite_squarefree_cubic
#print axioms Erdos364.QuarticObstruction.cubic_factor_of_coprime_product
#print axioms Erdos364.QuarticObstruction.two_prime_kernel_middle_not_dvd
#print axioms Erdos364.QuarticObstruction.two_prime_kernel_pell_shape
#print axioms Erdos364.QuarticObstruction.exists_even_cubic_two_prime_iff
#print axioms Erdos364.QuarticObstruction.eight_mul_sq_ne_fourth_add_one
#print axioms Erdos364.QuarticObstruction.eight_mul_sq_sub_one_ne_fourth
#print axioms Erdos364.QuarticObstruction.two_prime_kernel_predecessor_ne_fourth
#print axioms Erdos364.QuarticObstruction.pell_factors_coprime
#print axioms Erdos364.QuarticObstruction.pell_factor_properties
#print axioms Erdos364.QuarticObstruction.square_or_square_of_coprime_prime_cube_mul_sq
#print axioms Erdos364.QuarticObstruction.pell_factor_identities
#print axioms Erdos364.QuarticObstruction.prime_cube_pell_obstruction
#print axioms Erdos364.QuarticObstruction.predecessor_ne_sq_of_mod_four_zero
#print axioms Erdos364.QuarticObstruction.even_cube_sub_self_ne_two_prime_cube_mul_sq
#print axioms Erdos364.QuarticObstruction.not_exists_even_cubic_two_prime
#print axioms Erdos364.QuarticObstruction.cubic_solution_D_not_twice_prime
#print axioms Erdos364.QuarticObstruction.infinitely_many_excluded_composite_squarefree_kernels
#print axioms Erdos364.QuarticObstruction.cubic_solution_restricted_parameters
#print axioms Erdos364.QuarticObstruction.exists_powerful_triple_iff_restricted_squarefree_cubic
