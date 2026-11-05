import Submission.Classification

/-!
# Exact norm-compatible shifted certificates (conditional, not an ESC proof)

The polynomial families below produce strictly ordered decompositions for
selected norm-valued initial candidates.  In particular the `j = 5` and
`j = 4` certificates use the **full** square-divisor conditions: the Type-II
divisor need not divide `x`, nor need the Type-I cofactor divide `x`.
No theorem claims that an arbitrary hard prime belongs to these families.
`Submission.Spec` is not imported or modified.
-/

namespace Erdos242

/-- A split-prime fiber with `3 ∣ 4x-p` cannot hit either complete divisor
target.  The norm-theoretic argument that an odd primitive Eisenstein norm
has only `1 (mod 3)` prime divisors is separate from this elementary lemma. -/
theorem no_types_if_divisors_one_mod_three (p x : ℕ)
    (ha : 3 ∣ 4 * x - p) (hx : x % 3 = 1)
    (hdiv : ∀ e : ℕ, 0 < e → e ∣ x ^ 2 → e % 3 = 1) :
    ¬TypeI p x ∧ ¬TypeII p x := by
  constructor
  · rintro ⟨c, hc, hcx, hac⟩
    have hc3 := hdiv c hc hcx
    have h3 : 3 ∣ 4 * c + 1 := dvd_trans ha hac
    omega
  · rintro ⟨d, hd, _, hdx, had⟩
    have hd3 := hdiv d hd hdx
    have h3 : 3 ∣ x + d := dvd_trans ha had
    omega

/-- A first shifted denominator `x=5q` with `p=20q-7` has a Type-I
cofactor `5`.  No primality is needed for the ordered identity. -/
theorem seven_seed_typeI_and_good (q : ℕ) (hq : 1 ≤ q) :
    TypeI (20 * q - 7) (5 * q) ∧ Good (20 * q - 7) := by
  let p := 20 * q - 7
  let x := 5 * q
  change TypeI p x ∧ Good p
  have hpq : p + 7 = 20 * q := by dsimp [p]; omega
  have ha : 4 * x - p = 7 := by dsimp [x]; omega
  have hI : TypeI p x := by
    refine ⟨5, by norm_num, ?_, ?_⟩
    · refine ⟨5 * q ^ 2, ?_⟩
      dsimp [x]
      ring
    · rw [ha]
      norm_num
  have hp : 0 < p := by omega
  have hlo : p < 4 * x := by dsimp [x]; omega
  have hhi : 2 * x < p := by dsimp [x]; omega
  exact ⟨hI, good_of_typeI p x hp hlo hhi hI⟩

/-- The norm `N=1+3(2(5s+2))²`, the hard-form integer `p=4N-3`, and
`x=N+1` have the actual Type-I cofactor `c=5`.  This includes `p=193`
at `s=0`; it does not assert that the quadratic polynomial is prime for
infinitely many `s`. -/
theorem norm_one_shift_family (s : ℕ) :
    let N := 1 + 3 * (2 * (5 * s + 2)) ^ 2
    TypeI (4 * N - 3) (N + 1) ∧ Good (4 * N - 3) := by
  let N := 1 + 3 * (2 * (5 * s + 2)) ^ 2
  let q := 10 + 48 * s + 60 * s ^ 2
  have hx : N + 1 = 5 * q := by dsimp [N, q]; ring
  have hp : 4 * N - 3 = 20 * q - 7 := by
    have hn : 3 ≤ 4 * N := by dsimp [N]; omega
    omega
  change TypeI (4 * N - 3) (N + 1) ∧ Good (4 * N - 3)
  rw [hp, hx]
  exact seven_seed_typeI_and_good q (by dsimp [q]; omega)

/-- The linear family `p=1104w+313`, `x=12(23w+7)` simultaneously has a
full Type-I cofactor `c=9(23w+7)` and a full Type-II divisor `d=8` at
`a=23`.  Both divide `x²`; `c` does not divide `x`. -/
theorem twenty_three_both_types_and_good (w : ℕ) :
    TypeI (1104 * w + 313) (12 * (23 * w + 7)) ∧
    TypeII (1104 * w + 313) (12 * (23 * w + 7)) ∧
    Good (1104 * w + 313) := by
  let u := 23 * w + 7
  let p := 1104 * w + 313
  let x := 12 * u
  change TypeI p x ∧ TypeII p x ∧ Good p
  have hpx : 4 * x = p + 23 := by dsimp [x, u, p]; ring
  have ha : 4 * x - p = 23 := by omega
  have hu : 0 < u := by dsimp [u]; omega
  have hI : TypeI p x := by
    refine ⟨9 * u, by omega, ?_, ?_⟩
    · refine ⟨16 * u, ?_⟩
      dsimp [x]
      ring
    · rw [ha]
      refine ⟨36 * w + 11, ?_⟩
      dsimp [u]
      ring
  have hII : TypeII p x := by
    refine ⟨8, by norm_num, ?_, ?_, ?_⟩
    · dsimp [x, u]; omega
    · refine ⟨18 * u ^ 2, ?_⟩
      dsimp [x]
      ring
    · rw [ha]
      refine ⟨12 * w + 4, ?_⟩
      dsimp [x, u]
      ring
  have hlo : p < 4 * x := by omega
  have hhi : 2 * x < p := by dsimp [p, x, u]; omega
  exact ⟨hI, hII, good_of_typeI p x (by dsimp [p]; omega) hlo hhi hI⟩

/-- The primitive norm `N=(22+1932s)²+3·7²` falls into the preceding
full-Type-I-and-II family at `x=N+5`.  At `s=0`, `p=2521` and `x=636`;
`d=8` divides `x²` but not `x`.  Infinitely many parameter *values* are
covered; infinitude of prime values is not claimed. -/
theorem norm_five_shift_family (s : ℕ) :
    let N := (22 + 1932 * s) ^ 2 + 3 * 7 ^ 2
    TypeI (4 * N - 3) (N + 5) ∧ TypeII (4 * N - 3) (N + 5) ∧
      Good (4 * N - 3) := by
  let N := (22 + 1932 * s) ^ 2 + 3 * 7 ^ 2
  let w := 2 + 308 * s + 13524 * s ^ 2
  have hx : N + 5 = 12 * (23 * w + 7) := by dsimp [N, w]; ring
  have hp : 4 * N - 3 = 1104 * w + 313 := by
    have h : 4 * N = 1104 * w + 316 := by dsimp [N, w]; ring
    omega
  change TypeI (4 * N - 3) (N + 5) ∧ TypeII (4 * N - 3) (N + 5) ∧
    Good (4 * N - 3)
  rw [hp, hx]
  exact twenty_three_both_types_and_good w

/-- A general full-Type-I *square-cofactor* identity: `x=r u`,
`c=r u²`, and `a | 4r u²+1` give `c | x²` even when `c ∤ x`.
This is a conditional descent template, not an all-prime covering theorem. -/
theorem good_of_square_cofactor (r u a : ℕ) (hr : 0 < r) (hu : 0 < u)
    (ha : 0 < a) (ha_small : a < 2 * r * u)
    (hdiv : a ∣ 4 * r * u ^ 2 + 1) :
    Good (4 * r * u - a) := by
  let x := r * u
  let p := 4 * r * u - a
  have hxpos : 0 < x := Nat.mul_pos hr hu
  have hsmall : a < 2 * x := by simpa only [x, mul_assoc] using ha_small
  have hfour : 4 * r * u = 4 * x := by dsimp [x]; ring
  have hpexpr : p = 4 * x - a := by dsimp [p]; rw [hfour]
  have hpx : p + a = 4 * x := by rw [hpexpr]; omega
  have hhi : 2 * x < p := by omega
  have hpos : 0 < p := by omega
  have hlo : p < 4 * x := by omega
  have hI : TypeI p x := by
    refine ⟨r * u ^ 2, Nat.mul_pos hr (pow_pos hu 2), ?_, ?_⟩
    · refine ⟨r, ?_⟩
      dsimp [x]
      ring
    · have heq : 4 * x - p = a := by omega
      rw [heq]
      simpa only [mul_assoc] using hdiv
  exact good_of_typeI p x hpos hlo hhi hI

/-- A general `a=19` full-Type-I family with `x=127q`,
`q=19t+17`, `c=127q²`.  The complementary factor `x²/c=127` is
constant.  The sample `t=6` is `p=66529`, `x=16637`. -/
theorem nineteen_square_cofactor_family (t : ℕ) :
    TypeI (9652 * t + 8617) (127 * (19 * t + 17)) ∧
    Good (9652 * t + 8617) := by
  let q := 19 * t + 17
  let p := 9652 * t + 8617
  let x := 127 * q
  change TypeI p x ∧ Good p
  have hpx : 4 * x = p + 19 := by dsimp [p, x, q]; ring
  have ha : 4 * x - p = 19 := by omega
  have hq : 0 < q := by dsimp [q]; omega
  have hI : TypeI p x := by
    refine ⟨127 * q ^ 2, Nat.mul_pos (by norm_num) (pow_pos hq 2), ?_, ?_⟩
    · refine ⟨127, ?_⟩
      dsimp [x]
      ring
    · rw [ha]
      refine ⟨9652 * t ^ 2 + 17272 * t + 7727, ?_⟩
      dsimp [q]
      ring
  have hlo : p < 4 * x := by omega
  have hhi : 2 * x < p := by dsimp [p, x, q]; omega
  exact ⟨hI, good_of_typeI p x (by dsimp [p]; omega) hlo hhi hI⟩

/-- The primitive norm `N=(85+405384s)²+3·56²` has the explicit
shift-four square cofactor above.  At `s=0` it yields the first ordered
success for `p=66529`; the full Type-I cofactor exceeds `x` there. -/
theorem norm_four_shift_family (s : ℕ) :
    let N := (85 + 405384 * s) ^ 2 + 3 * 56 ^ 2
    TypeI (4 * N - 3) (N + 4) ∧ Good (4 * N - 3) := by
  let N := (85 + 405384 * s) ^ 2 + 3 * 56 ^ 2
  let t := 6 + 28560 * s + 68104512 * s ^ 2
  have hx : N + 4 = 127 * (19 * t + 17) := by dsimp [N, t]; ring
  have hp : 4 * N - 3 = 9652 * t + 8617 := by
    have h : 4 * N = 9652 * t + 8620 := by dsimp [N, t]; ring
    omega
  change TypeI (4 * N - 3) (N + 4) ∧ Good (4 * N - 3)
  rw [hp, hx]
  exact nineteen_square_cofactor_family t

/-- The three motivating primes have different *first* successful shifts.
The family theorems certify the ordered solutions at those shifts; the
absence of earlier certificates is audited separately by all-divisor checks
in `NormShiftAudit.py`. -/
theorem norm_shift_193_certificate : TypeI 193 50 ∧ Good 193 := by
  simpa using norm_one_shift_family 0

theorem norm_shift_2521_certificates :
    TypeI 2521 636 ∧ TypeII 2521 636 ∧ Good 2521 := by
  simpa using norm_five_shift_family 0

theorem norm_shift_66529_certificate : TypeI 66529 16637 ∧ Good 66529 := by
  simpa using norm_four_shift_family 0

/-- The Type-II branch at the early shifted denominator of 2521 gives
these *specific* distinct ordered denominators. -/
theorem norm_shift_2521_typeII_explicit :
    (4 / 2521 : ℚ) = 1 / 636 + 1 / 70588 + 1 / 5611746 := by
  norm_num

/-- The full Type-I cofactor, larger than `x`, at 66529 gives these
*specific* distinct ordered denominators. -/
theorem norm_shift_66529_typeI_explicit :
    (4 / 66529 : ℚ) = 1 / 16637 + 1 / 58254900 + 1 / 507708871715100 := by
  norm_num

/-- A fourth, more delayed soluble split-norm prime.  Only the witness
at `j=26`, not the absence of earlier witnesses, is proved here. -/
theorem norm_shift_8803369_typeII : TypeII 8803369 2200869 := by
  refine ⟨121, by norm_num, by norm_num, ?_, ?_⟩ <;> norm_num

theorem norm_shift_8803369_prime_data :
    Nat.Prime 8803369 ∧ Nat.Prime 2200843 ∧
      2200843 = 1480 ^ 2 + 3 * 59 ^ 2 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num


theorem norm_shift_8803369_explicit : Good 8803369 := by
  refine ⟨2200869, 181085300330, 3293760527702370,
    by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num



end Erdos242
