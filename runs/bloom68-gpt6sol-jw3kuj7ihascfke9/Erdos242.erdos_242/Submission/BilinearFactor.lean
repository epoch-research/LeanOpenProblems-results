import Submission.AdjacentFactor

/-!
# A bilinear lattice for restricted Type-I Egyptian-fraction witnesses

For `p=24k+1`, a Type-I certificate with the *extra* hypothesis `c ∣ x`
is equivalent to representing `6k+1` as

    (3i+2)t + ((4i+3)t-1)j,     t>0.

The representation gives the first-denominator index `j` and the auxiliary
factor index `i` simultaneously. It does NOT characterize arbitrary Type-I
certificates, Type II, or all ordered solutions. In particular, none of the
theorems asserts that every prime has such a representation.
-/

namespace Erdos242

/-- Recover the exact auxiliary factor equations from a bilinear representation.
The cofactor is `c=(4i+3)j+3i+2`, and the divisor is `q=(4i+3)t-1`. -/
theorem factor_data_of_bilinear (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    ∃ q c : ℕ, 1 < q ∧ 0 < c ∧ q + 1 = (4 * i + 3) * t ∧
      c = (4 * i + 3) * j + 3 * i + 2 ∧
      t * c = 6 * k + 1 + j ∧
      (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c := by
  let h := 4 * i + 3
  let q := h * t - 1
  let c := h * j + 3 * i + 2
  have hht : 3 ≤ h * t := by
    have hm := Nat.mul_le_mul_left h (show 1 ≤ t by omega)
    dsimp [h] at *
    omega
  have hq : 1 < q := by dsimp [q]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hqt : q + 1 = h * t := by dsimp [q]; omega
  have hrel' : 6 * k + 1 = (3 * i + 2) * t + q * j := hrel
  have hx : t * c = 6 * k + 1 + j := by
    dsimp [c]
    nlinarith only [hrel', congrArg (fun n : ℕ => n * j) hqt]
  have hca : h * (4 * j + 3) = 4 * c + 1 := by
    dsimp [h, c]
    ring
  have hpax : 24 * k + 1 + (4 * j + 3) = 4 * (6 * k + 1 + j) := by omega
  have hpcplus : h * (24 * k + 1) + 1 + 4 * c = 4 * q * c + 4 * c := by
    calc
      h * (24 * k + 1) + 1 + 4 * c = h * (24 * k + 1 + (4 * j + 3)) := by
        nlinarith only [hca]
      _ = h * (4 * (6 * k + 1 + j)) := by rw [hpax]
      _ = 4 * c * (h * t) := by rw [← hx]; ring
      _ = 4 * c * (q + 1) := by rw [hqt]
      _ = 4 * q * c + 4 * c := by ring
  refine ⟨q, c, hq, hc, ?_, ?_, hx, ?_⟩
  · exact hqt
  · rfl
  · change h * (24 * k + 1) + 1 = 4 * q * c
    exact Nat.add_right_cancel hpcplus

/-- Unpack **any specified eligible divisor** `q∣M_i` into its own
factor-product data `c=M_i/q`, `t=(q+1)/(4i+3)`. In particular the
following sharp parameter bounds will apply to this same `q`, rather
than to an existentially different divisor. -/
theorem factor_product_of_auxiliary_divisor (k i q : ℕ)
    (hq : 1 < q) (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    ∃ c t : ℕ, 0 < c ∧ 0 < t ∧ q + 1 = (4 * i + 3) * t ∧
      (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c := by
  let h := 4 * i + 3
  let c := auxiliaryFactor k i / q
  let t := (q + 1) / h
  have hqdiv : h ∣ q + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    change (q + 1) % (4 * i + 3) = 0
    rw [Nat.add_mod, hres, Nat.mod_eq_of_lt (by omega : 1 < 4 * i + 3)]
    have heq : 4 * i + 2 + 1 = 4 * i + 3 := by omega
    rw [heq, Nat.mod_self]
  have hqt : q + 1 = h * t := (Nat.mul_div_cancel' hqdiv).symm
  have ht : 0 < t := by
    by_contra hn
    have htzero : t = 0 := Nat.eq_zero_of_not_pos hn
    rw [htzero, mul_zero] at hqt
    omega
  have hM : q * c = auxiliaryFactor k i := Nat.mul_div_cancel' hdiv
  have hc : 0 < c := by
    have hMpos : 0 < auxiliaryFactor k i := by dsimp [auxiliaryFactor]; omega
    by_contra hn
    have hczero : c = 0 := Nat.eq_zero_of_not_pos hn
    rw [hczero, mul_zero] at hM
    omega
  have hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c := by
    have haux := auxiliaryFactor_identity k i
    nlinarith only [haux, hM]
  exact ⟨c, t, hc, ht, hqt, hpc⟩


/-- A bilinear point gives a simple Type-I witness and an *ordered* unit-fraction
identity, without a primality assumption on `24k+1`. The specified `c` really
divides `x` itself; this is stronger than the full Type-I condition. -/
theorem simple_typeI_of_bilinear (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    ∃ c : ℕ, 0 < c ∧ c ∣ 6 * k + 1 + j ∧
      (4 * (6 * k + 1 + j) - (24 * k + 1)) ∣ 4 * c + 1 ∧
      TypeI (24 * k + 1) (6 * k + 1 + j) ∧ Good (24 * k + 1) := by
  obtain ⟨q, c, hq, hc, hqt, hcform, hx, hpc⟩ :=
    factor_data_of_bilinear k i t j ht hrel
  have hproduct := good_of_factor_product (24 * k + 1) (4 * i + 3) q c t
    (by omega) (by omega) hq hc ht hqt hpc
  have hca : (4 * i + 3) * (4 * j + 3) = 4 * c + 1 := by
    rw [hcform]
    ring
  have hax : 4 * (6 * k + 1 + j) - (24 * k + 1) = 4 * j + 3 := by omega
  have hdiv : (4 * (6 * k + 1 + j) - (24 * k + 1)) ∣ 4 * c + 1 := by
    rw [hax]
    exact ⟨4 * i + 3, by simpa only [mul_comm] using hca.symm⟩
  have hI : TypeI (24 * k + 1) (6 * k + 1 + j) := by
    rw [← hx]
    exact hproduct.1
  exact ⟨c, hc, ⟨t, by calc
    6 * k + 1 + j = t * c := hx.symm
    _ = c * t := mul_comm _ _⟩, hdiv, hI, hproduct.2⟩

/-- The converse: every simple Type-I witness for a hard integer lies at
`x=6k+1+j` and satisfies the bilinear equation. The factor index `i` and
cofactor `t` are recovered from the **specified** witness `c ∣ x`. -/
theorem bilinear_of_simple_typeI (k x c : ℕ) (hcx : c ∣ x)
    (hlo : 24 * k + 1 < 4 * x) (hhi : 2 * x < 24 * k + 1)
    (hac : 4 * x - (24 * k + 1) ∣ 4 * c + 1) :
    ∃ i t j : ℕ, 0 < t ∧ j < 6 * k ∧ x = 6 * k + 1 + j ∧
      c = (4 * i + 3) * j + 3 * i + 2 ∧
      6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j := by
  obtain ⟨i, q, t, ht, hq, hxt, hqt, hpc⟩ :=
    simple_typeI_factor_product (24 * k + 1) x c (by omega) hlo hcx hac
  let j := x - (6 * k + 1)
  have hx : x = 6 * k + 1 + j := by dsimp [j]; omega
  have hj : j < 6 * k := by dsimp [j]; omega
  let h := 4 * i + 3
  let a := 4 * x - (24 * k + 1)
  have haeq : a + (24 * k + 1) = 4 * x := by dsimp [a]; omega
  have hsum : h * (4 * x) = h * (24 * k + 1) + 4 * c + 1 := by
    calc
      h * (4 * x) = 4 * c * (h * t) := by rw [hxt]; ring
      _ = 4 * c * (q + 1) := by rw [hqt]
      _ = h * (24 * k + 1) + 4 * c + 1 := by dsimp [h]; nlinarith only [hpc]
  have hca : h * a = 4 * c + 1 := by
    have hmul := congrArg (fun n : ℕ => h * n) haeq
    nlinarith only [hmul, hsum]
  have ha : a = 4 * j + 3 := by dsimp [a]; rw [hx]; omega
  have hcform : c = (4 * i + 3) * j + 3 * i + 2 := by
    rw [ha] at hca
    dsimp [h] at hca
    nlinarith only [hca]
  have hmul : 6 * k + 1 + j = (3 * i + 2) * t + (q + 1) * j := by
    calc
      6 * k + 1 + j = x := hx.symm
      _ = t * c := hxt
      _ = (3 * i + 2) * t + (h * t) * j := by rw [hcform]; dsimp [h]; ring
      _ = (3 * i + 2) * t + (q + 1) * j := by rw [hqt]
  have hbil : 6 * k + 1 = (3 * i + 2) * t + q * j := by
    nlinarith only [hmul]
  have hqform : q = (4 * i + 3) * t - 1 := by omega
  refine ⟨i, t, j, ht, hj, hx, hcform, ?_⟩
  rwa [hqform] at hbil

/-- Exact **parameter-preserving** converse to `factor_data_of_bilinear`:
any auxiliary product produces the *same* `i,q,c,t` on the bilinear
lattice, rather than merely asserting existence of another witness.
This is useful for transferring the sharp bilinear bounds to **every**
eligible auxiliary divisor, not just some selected factor. -/
theorem bilinear_of_factor_product (k i q c t : ℕ)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c) :
    ∃ j : ℕ, c = (4 * i + 3) * j + 3 * i + 2 ∧
      t * c = 6 * k + 1 + j ∧
      6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j := by
  let h := 4 * i + 3
  let p := 24 * k + 1
  let x := t * c
  have hsum : h * (4 * x) = h * p + 4 * c + 1 := by
    calc
      h * (4 * x) = 4 * c * (h * t) := by dsimp [x]; ring
      _ = 4 * c * (q + 1) := by rw [hqt]
      _ = h * p + 4 * c + 1 := by dsimp [h, p]; nlinarith only [hpc]
  have hlo : p < 4 * x := by
    by_contra hn
    have hle : 4 * x ≤ p := by omega
    have hm := Nat.mul_le_mul_left h hle
    omega
  let j := x - (6 * k + 1)
  have hx : x = 6 * k + 1 + j := by dsimp [j, p] at *; omega
  let a := 4 * x - p
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hca : h * a = 4 * c + 1 := by
    have hmul := congrArg (fun n : ℕ => h * n) haeq
    nlinarith only [hmul, hsum]
  have ha : a = 4 * j + 3 := by dsimp [a, p]; rw [hx]; omega
  have hcform : c = (4 * i + 3) * j + 3 * i + 2 := by
    rw [ha] at hca
    dsimp [h] at hca
    nlinarith only [hca]
  have hmul : 6 * k + 1 + j = (3 * i + 2) * t + (q + 1) * j := by
    calc
      6 * k + 1 + j = x := hx.symm
      _ = t * c := rfl
      _ = (3 * i + 2) * t + (h * t) * j := by rw [hcform]; dsimp [h]; ring
      _ = (3 * i + 2) * t + (q + 1) * j := by rw [hqt]
  have hbil : 6 * k + 1 = (3 * i + 2) * t + q * j := by
    nlinarith only [hmul]
  have hqform : q = (4 * i + 3) * t - 1 := by omega
  refine ⟨j, hcform, hx, ?_⟩
  rwa [hqform] at hbil


/-- The sharp auxiliary-index cutoff is an elementary consequence of the
bilinear equation, independent of the older factor-product size proof.
If `j>0`, the right-hand side is at least `(3i+2)+(4i+2)=7i+4`.
If `j=0`, parity and `6k+1≡1 (mod 3)` force `t≥3`, and then
`6k+1≥3(3i+2)`. Both cases imply `7i+3≤6k`. -/
theorem bilinear_index_sharp_direct (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    7 * i + 3 ≤ 6 * k := by
  by_cases hjzero : j = 0
  · subst j
    have ht3 : 3 ≤ t := by
      by_contra hne
      have hcases : t = 1 ∨ t = 2 := by omega
      rcases hcases with h1 | h2
      · subst t
        norm_num at hrel
        omega
      · subst t
        norm_num at hrel
        omega
    have hmul := Nat.mul_le_mul_left (3 * i + 2) ht3
    norm_num at hrel
    omega
  · have hjpos : 1 ≤ j := by omega
    have hle : 4 * i + 2 ≤ (4 * i + 3) * t - 1 := by
      have hmul := Nat.mul_le_mul_left (4 * i + 3) (show 1 ≤ t by omega)
      omega
    have hbase : 3 * i + 2 ≤ (3 * i + 2) * t := by
      have hmul := Nat.mul_le_mul_left (3 * i + 2) (show 1 ≤ t by omega)
      omega
    have hterm : 4 * i + 2 ≤ ((4 * i + 3) * t - 1) * j := by
      have hmul := Nat.mul_le_mul_left ((4 * i + 3) * t - 1) hjpos
      omega
    omega

/-- The explicit simple-Type-I cofactor `c=(4i+3)j+3i+2` is at least
`5`. The apparent smallest possibility `i=j=0`, `c=2`, would require
the odd number `6k+1` to equal the even number `2t`. Both equality
families below attain `c=5`. -/
theorem bilinear_cofactor_at_least_five (k i t j : ℕ)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    5 ≤ (4 * i + 3) * j + 3 * i + 2 := by
  by_cases hipos : 0 < i
  · omega
  · have hi0 : i = 0 := by omega
    have hjpos : 0 < j := by
      by_contra hnot
      have hj0 : j = 0 := by omega
      subst i
      subst j
      norm_num at hrel
      omega
    subst i
    omega

/-- **Sharp first-denominator index cutoff for the restricted `c∣x` family.**
Every bilinear point obeys `5j+3≤6k`, so its first denominator is at most
`(3p+1)/10`, much smaller than the general ordered range `x<p/2`.
When `i=0`, `t=1` would make `6k+1=2+2j` even, so `t≥2`, yielding
`6k+1≥4+5j`. When `i>0`, the right side is at least `5+6j`.
Equality occurs for hard primes in `p≡73 (mod 120)` below. -/
theorem bilinear_first_index_sharp (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    5 * j + 3 ≤ 6 * k := by
  by_cases hi0 : i = 0
  · subst i
    have ht2 : 2 ≤ t := by
      by_contra hne
      have ht1 : t = 1 := by omega
      subst t
      norm_num at hrel
      omega
    have hcoef : 5 ≤ 3 * t - 1 := by omega
    have hcoefj : 5 * j ≤ (3 * t - 1) * j :=
      Nat.mul_le_mul_right j hcoef
    norm_num at hrel
    omega
  · have hipos : 1 ≤ i := by omega
    have hbase : 5 ≤ (3 * i + 2) * t := by
      have hm := Nat.mul_le_mul_left (3 * i + 2) (show 1 ≤ t by omega)
      omega
    have hcoeff : 6 ≤ (4 * i + 3) * t - 1 := by
      have hm := Nat.mul_le_mul_left (4 * i + 3) (show 1 ≤ t by omega)
      omega
    have hterm : 6 * j ≤ ((4 * i + 3) * t - 1) * j :=
      Nat.mul_le_mul_right j hcoeff
    omega

/-- Equality in `5j+3≤6k` is rigid: **exactly** `i=0,t=2`.
Consequently equality forces `k≡3 (mod 5)` and hence
`p=24k+1≡73 (mod 120)`; the subsequent explicit family supplies
equality for every integer in that progression (and infinitely many primes).
This is classification of *equality in the restricted family only*. -/
theorem bilinear_first_equality_iff (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    5 * j + 3 = 6 * k ↔ i = 0 ∧ t = 2 := by
  constructor
  · intro heq
    have hi0 : i = 0 := by
      by_contra hne
      have hipos : 1 ≤ i := by omega
      have hbase : 5 ≤ (3 * i + 2) * t := by
        have hm := Nat.mul_le_mul_left (3 * i + 2) (show 1 ≤ t by omega)
        omega
      have hcoeff : 6 ≤ (4 * i + 3) * t - 1 := by
        have hm := Nat.mul_le_mul_left (4 * i + 3) (show 1 ≤ t by omega)
        omega
      have hterm : 6 * j ≤ ((4 * i + 3) * t - 1) * j :=
        Nat.mul_le_mul_right j hcoeff
      omega
    have ht2 : t = 2 := by
      by_contra hne
      have ht3 : 3 ≤ t := by
        by_contra hn
        have ht1 : t = 1 := by omega
        subst i
        subst t
        norm_num at hrel
        omega
      have hcoeff : 8 ≤ 3 * t - 1 := by omega
      have hterm : 8 * j ≤ (3 * t - 1) * j := Nat.mul_le_mul_right j hcoeff
      subst i
      norm_num at hrel
      omega
    exact ⟨hi0, ht2⟩
  · rintro ⟨rfl, rfl⟩
    norm_num at hrel
    omega

/-- Any equality witness to the sharp restricted first-denominator bound
lies in the *specific* progression `p≡73 (mod 120)`. This does not
characterize arbitrary Type-I or Type-II witnesses. -/
theorem bilinear_first_equality_progression (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j)
    (heq : 5 * j + 3 = 6 * k) :
    i = 0 ∧ t = 2 ∧ k % 5 = 3 ∧ (24 * k + 1) % 120 = 73 := by
  have hrigid := (bilinear_first_equality_iff k i t j ht hrel).mp heq
  exact ⟨hrigid.1, hrigid.2, by omega, by omega⟩


/-- In terms of the actual first denominator `x=6k+1+j`, the preceding
bound is `10x≤3p+1` for `p=24k+1`. It applies only when a witness has
`c∣x`, not to all Type-I or Type-II solutions. -/
theorem bilinear_first_denominator_sharp (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    10 * (6 * k + 1 + j) ≤ 3 * (24 * k + 1) + 1 := by
  have hj := bilinear_first_index_sharp k i t j ht hrel
  omega

/-- Direct formulation for the **specified** original simple Type-I divisor
`c∣x`: `x≤(3p+1)/10`. The nearby assertion for general Type I with
only `c∣x²` is false (e.g. `p=97,x=34,c=68`). The bound is optimal even
for primes by `infinitely_many_bilinear_first_sharp`. -/
theorem simple_typeI_first_denominator_sharp (k x c : ℕ)
    (hcx : c ∣ x) (hlo : 24 * k + 1 < 4 * x)
    (hhi : 2 * x < 24 * k + 1)
    (hac : 4 * x - (24 * k + 1) ∣ 4 * c + 1) :
    10 * x ≤ 3 * (24 * k + 1) + 1 := by
  obtain ⟨i, t, j, ht, hj, hx, hcform, hrel⟩ :=
    bilinear_of_simple_typeI k x c hcx hlo hhi hac
  rw [hx]
  exact bilinear_first_denominator_sharp k i t j ht hrel





/-- Elementary restrictions on *every* bilinear point: `j` is an admissible
first-denominator index, `i` obeys the previous sharp auxiliary bound,
and its shift obeys a new sharp bound `5t≤6k+2`. The stronger
`5t≤6k+1` holds whenever `i>0`. None supplies a point for all `k`. -/
theorem bilinear_parameter_bounds (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    j < 6 * k ∧ (3 * i + 2) * t ≤ 6 * k + 1 ∧
      7 * i + 3 ≤ 6 * k ∧ 5 * t ≤ 6 * k + 2 ∧
      (0 < i → 5 * t ≤ 6 * k + 1) := by
  have hjsharp : 5 * j + 3 ≤ 6 * k := bilinear_first_index_sharp k i t j ht hrel
  have hj : j < 6 * k := by omega
  have hhyper : (3 * i + 2) * t ≤ 6 * k + 1 := by omega
  have hi : 7 * i + 3 ≤ 6 * k := bilinear_index_sharp_direct k i t j ht hrel
  have hcond : 0 < i → 5 * t ≤ 6 * k + 1 := by
    intro hipos
    have hcoeff : 5 ≤ 3 * i + 2 := by omega
    have hmul := Nat.mul_le_mul_right t hcoeff
    omega
  have hshift : 5 * t ≤ 6 * k + 2 := by
    by_cases hipos : 0 < i
    · have := hcond hipos
      omega
    · have hi0 : i = 0 := by omega
      have hjpos : 0 < j := by
        by_contra hjnot
        have hj0 : j = 0 := by omega
        subst i
        subst j
        norm_num at hrel
        omega
      have hjmul' : (3 * t - 1) ≤ (3 * t - 1) * j := by
        have hm := Nat.mul_le_mul_left (3 * t - 1) (show 1 ≤ j by omega)
        simpa only [mul_one] using hm
      subst i
      norm_num at hrel
      omega
  exact ⟨hj, hhyper, hi, hshift, hcond⟩

/-- A sharp *auxiliary-divisor size* bound. For `q=(4i+3)t−1`,
`5(q+1)≤7(6k+1)`; unlike the auxiliary factors `M_i` themselves,
**every eligible factor `q` in the restricted construction is O(p)**.
For `i≥1`, combine `(3i+2)t≤6k+1` with
`5(4i+3)≤7(3i+2)`; for `i=0`, use the sharp shift bound.
Equality occurs for `(i,j)=(1,0)` in the `p=120n+97` family,
including infinitely many prime values. It does not force existence of
an eligible divisor for any specified prime. -/
theorem bilinear_auxiliary_divisor_sharp (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    5 * ((4 * i + 3) * t) ≤ 7 * (6 * k + 1) := by
  have hbounds := bilinear_parameter_bounds k i t j ht hrel
  by_cases hi0 : i = 0
  · have hshift : 5 * t ≤ 6 * k + 2 := hbounds.2.2.2.1
    subst i
    norm_num
    omega
  · have hipos : 1 ≤ i := by omega
    have hcoeff : 5 * (4 * i + 3) ≤ 7 * (3 * i + 2) := by omega
    have hmul := Nat.mul_le_mul_right t hcoeff
    have hN := Nat.mul_le_mul_left 7 hbounds.2.1
    nlinarith only [hmul, hN]

/-- The bound on `q` holds for **each individual** auxiliary factor product,
not just for a favorably chosen witness. -/
theorem factor_product_divisor_size_sharp (k i q c t : ℕ) (ht : 0 < t)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c) :
    5 * (q + 1) ≤ 7 * (6 * k + 1) := by
  obtain ⟨j, hcform, hx, hrel⟩ := bilinear_of_factor_product k i q c t hqt hpc
  rw [hqt]
  exact bilinear_auxiliary_divisor_sharp k i t j ht hrel

/-- Consequently **every** divisor meeting the exact restricted criterion
`q∣M_i, q≡-1 (mod 4i+3)` satisfies the sharp finite cutoff
`5(q+1)≤7(6k+1)`. This is a valid pruning rule for an individual hard
prime, not a proof that any divisor passes the test. -/
theorem auxiliary_divisor_size_sharp (k i q : ℕ)
    (hq : 1 < q) (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    5 * (q + 1) ≤ 7 * (6 * k + 1) := by
  obtain ⟨c, t, hc, ht, hqt, hpc⟩ :=
    factor_product_of_auxiliary_divisor k i q hq hdiv hres
  exact factor_product_divisor_size_sharp k i q c t ht hqt hpc



/-- Equality in the uniform *shift* bound `5t≤6k+2` is also rigid:
**exactly** `i=0,j=1`. Unlike first-denominator equality (which has
`t=2` and a growing `j`), shift equality has `j=1` and a growing `t`.
The two distinct equality witnesses coexist for `p≡73 (mod 120)`. -/
theorem bilinear_shift_equality_iff (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j) :
    5 * t = 6 * k + 2 ↔ i = 0 ∧ j = 1 := by
  constructor
  · intro heq
    have hbounds := bilinear_parameter_bounds k i t j ht hrel
    have hi0 : i = 0 := by
      by_contra hne
      have hipos : 0 < i := by omega
      have hstrict := hbounds.2.2.2.2 hipos
      omega
    have hmul : (3 * t - 1) * j = (3 * t - 1) * 1 := by
      subst i
      norm_num at hrel
      omega
    have hc : 0 < 3 * t - 1 := by omega
    exact ⟨hi0, Nat.eq_of_mul_eq_mul_left hc hmul⟩
  · rintro ⟨rfl, rfl⟩
    norm_num at hrel
    omega

/-- Sharp shift equality, too, is possible only in the progression
`p=24k+1≡73 (mod 120)`. Prime values in this progression exist by
Dirichlet, but it is not a universal factor covering. -/
theorem bilinear_shift_equality_progression (k i t j : ℕ) (ht : 0 < t)
    (hrel : 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j)
    (heq : 5 * t = 6 * k + 2) :
    i = 0 ∧ j = 1 ∧ k % 5 = 3 ∧ (24 * k + 1) % 120 = 73 := by
  have hrigid := (bilinear_shift_equality_iff k i t j ht hrel).mp heq
  exact ⟨hrigid.1, hrigid.2, by omega, by omega⟩


/-- Exact purely additive reparameterization of the restricted Type-I
subfamily `c ∣ x`. The RHS has no explicit bound on `i,j,t` because the
preceding theorem *deduces* the bounds from its one equation. This is NOT an
equivalence with arbitrary Type I or `Good`. -/
theorem simple_typeI_iff_bilinear (k : ℕ) :
    (∃ x c : ℕ, 0 < c ∧ c ∣ x ∧
        24 * k + 1 < 4 * x ∧ 2 * x < 24 * k + 1 ∧
        (4 * x - (24 * k + 1)) ∣ 4 * c + 1) ↔
      ∃ i t j : ℕ, 0 < t ∧
        6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j := by
  constructor
  · rintro ⟨x, c, hc, hcx, hlo, hhi, hdiv⟩
    obtain ⟨i, t, j, ht, hj, hx, hcform, hrel⟩ :=
      bilinear_of_simple_typeI k x c hcx hlo hhi hdiv
    exact ⟨i, t, j, ht, hrel⟩
  · rintro ⟨i, t, j, ht, hrel⟩
    obtain ⟨c, hc, hcx, hdiv, hI, hgood⟩ :=
      simple_typeI_of_bilinear k i t j ht hrel
    have hj : j < 6 * k := (bilinear_parameter_bounds k i t j ht hrel).1
    exact ⟨6 * k + 1 + j, c, hc, hcx, by omega, by omega, hdiv⟩

/-- Equality in the *uniform* shift bound occurs already at `p=73` and
throughout `p=120n+73`, with `i=0`, `j=1`, `c=5`, `t=6n+4`.
All these integers (including composites) have strictly ordered solutions. -/
theorem bilinear_shift_sharp_family (n : ℕ) :
    let k := 5 * n + 3
    let t := 6 * n + 4
    6 * k + 1 = (3 * 0 + 2) * t + ((4 * 0 + 3) * t - 1) * 1 ∧
      5 * t = 6 * k + 2 ∧ Good (120 * n + 73) := by
  dsimp
  have hrel : 6 * (5 * n + 3) + 1 =
      (3 * 0 + 2) * (6 * n + 4) + ((4 * 0 + 3) * (6 * n + 4) - 1) * 1 := by
    omega
  obtain ⟨c, hc, hcx, hdiv, hI, hgood⟩ :=
    simple_typeI_of_bilinear (5 * n + 3) 0 (6 * n + 4) 1 (by omega) hrel
  have hpform : 24 * (5 * n + 3) + 1 = 120 * n + 73 := by omega
  rw [hpform] at hgood
  exact ⟨hrel, by omega, hgood⟩

/-- Equality in the independent sharp *first-denominator* bound occurs
throughout the same progression `p=120n+73`, but now with `i=0`, `t=2`,
`j=6n+3`, `c=18n+11`, `x=36n+22`. At `p=73` this is the
ordered Type-I identity with first denominator `22` (not the separate
shift-sharp identity starting at `20`). -/
theorem bilinear_first_sharp_family (n : ℕ) :
    let k := 5 * n + 3
    let j := 6 * n + 3
    let x := 36 * n + 22
    6 * k + 1 = (3 * 0 + 2) * 2 + ((4 * 0 + 3) * 2 - 1) * j ∧
      5 * j + 3 = 6 * k ∧ 10 * x = 3 * (120 * n + 73) + 1 ∧
      TypeI (120 * n + 73) x ∧ Good (120 * n + 73) := by
  dsimp
  have hrel : 6 * (5 * n + 3) + 1 =
      (3 * 0 + 2) * 2 + ((4 * 0 + 3) * 2 - 1) * (6 * n + 3) := by
    omega
  obtain ⟨c, hc, hcx, hdiv, hI, hgood⟩ :=
    simple_typeI_of_bilinear (5 * n + 3) 0 2 (6 * n + 3) (by omega) hrel
  have hpform : 24 * (5 * n + 3) + 1 = 120 * n + 73 := by omega
  have hxform : 6 * (5 * n + 3) + 1 + (6 * n + 3) = 36 * n + 22 := by omega
  rw [hpform] at hI hgood
  rw [hxform] at hI
  exact ⟨hrel, by omega, by omega, hI, hgood⟩


/-- Equality in the sharper hyperbolic bound for `i>0` occurs at
`p=120n+97`, with `i=1`, `j=0`, `c=5`, `t=6n+5`. -/
theorem bilinear_hyperbolic_sharp_family (n : ℕ) :
    let k := 5 * n + 4
    let t := 6 * n + 5
    6 * k + 1 = (3 * 1 + 2) * t + ((4 * 1 + 3) * t - 1) * 0 ∧
      5 * t = 6 * k + 1 ∧ Good (120 * n + 97) := by
  dsimp
  have hrel : 6 * (5 * n + 4) + 1 =
      (3 * 1 + 2) * (6 * n + 5) + ((4 * 1 + 3) * (6 * n + 5) - 1) * 0 := by
    omega
  obtain ⟨c, hc, hcx, hdiv, hI, hgood⟩ :=
    simple_typeI_of_bilinear (5 * n + 4) 1 (6 * n + 5) 0 (by omega) hrel
  have hpform : 24 * (5 * n + 4) + 1 = 120 * n + 97 := by omega
  rw [hpform] at hgood
  exact ⟨hrel, by omega, hgood⟩

/-- Equality in the auxiliary-divisor cutoff is attained by the
**specified composite** divisor `q=42n+34=2(21n+17)` of `M₁`, with
`p=120n+97`, `i=1`, `t=6n+5`, `j=0`, `c=5`.
Every integer in the progression is soluble by this ordered identity;
Dirichlet makes infinitely many of them hard primes. -/
theorem bilinear_auxiliary_divisor_sharp_family (n : ℕ) :
    (42 * n + 34) ∣ auxiliaryFactor (5 * n + 4) 1 ∧
      (42 * n + 34) % 7 = 6 ∧
      5 * ((42 * n + 34) + 1) = 7 * (6 * (5 * n + 4) + 1) ∧
      Good (120 * n + 97) := by
  obtain ⟨hrel, htsharp, hgood⟩ := bilinear_hyperbolic_sharp_family n
  refine ⟨⟨5, ?_⟩, by omega, by omega, hgood⟩
  unfold auxiliaryFactor
  ring


/-- Dirichlet makes the *uniform shift bound* optimal even for arbitrarily
large hard primes, not just for the small integer `73`. -/
theorem infinitely_many_bilinear_shift_sharp (N : ℕ) :
    ∃ p k i t j : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j ∧
      5 * t = 6 * k + 2 ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 120) (a := 73)
      (by decide) (by decide)
  have hrem : p % 120 = 73 := by simpa [Nat.ModEq] using hmod
  let n := p / 120
  have hpform : p = 120 * n + 73 := by dsimp [n]; omega
  obtain ⟨hrel, hsharp, hgood⟩ := bilinear_shift_sharp_family n
  refine ⟨p, 5 * n + 3, 0, 6 * n + 4, 1, hpN, hp, ?_, hrel, hsharp, ?_⟩
  · omega
  · rwa [hpform]

/-- Dirichlet gives arbitrarily large hard **prime** equality cases for
the restricted first-denominator bound `10x≤3p+1`. Here
`p=120n+73`, `x=36n+22`, `j=6n+3`, and the *specified* simple
Type-I divisor is `c=18n+11` (so `x=2c`). This cannot be upgraded
to a size bound for all Type-I certificates. -/
theorem infinitely_many_bilinear_first_sharp (N : ℕ) :
    ∃ p k j c : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      5 * j + 3 = 6 * k ∧ 10 * (6 * k + 1 + j) = 3 * p + 1 ∧
      0 < c ∧ c ∣ 6 * k + 1 + j ∧
      (4 * (6 * k + 1 + j) - p) ∣ 4 * c + 1 ∧
      TypeI p (6 * k + 1 + j) ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 120) (a := 73)
      (by decide) (by decide)
  have hrem : p % 120 = 73 := by simpa [Nat.ModEq] using hmod
  let n := p / 120
  have hpform : p = 120 * n + 73 := by dsimp [n]; omega
  obtain ⟨hrel, hsharp, hxsharp, hI, hgood⟩ := bilinear_first_sharp_family n
  have hxform : 6 * (5 * n + 3) + 1 + (6 * n + 3) = 36 * n + 22 := by omega
  refine ⟨p, 5 * n + 3, 6 * n + 3, 18 * n + 11, hpN, hp, ?_,
    hsharp, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hpform, hxform]
    exact hxsharp
  · refine ⟨2, ?_⟩
    omega
  · have ha : 4 * (6 * (5 * n + 3) + 1 + (6 * n + 3)) - p = 24 * n + 15 := by
      rw [hpform]
      omega
    rw [ha]
    exact ⟨3, by omega⟩
  · rw [hpform, hxform]
    exact hI
  · rw [hpform]
    exact hgood


/-- Dirichlet also supplies arbitrarily large prime equality cases for
`(3i+2)t≤6k+1` with `i>0`. This selected progression is not a
pointwise witness for primes outside it. -/
theorem infinitely_many_bilinear_hyperbolic_sharp (N : ℕ) :
    ∃ p k i t j : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      0 < i ∧ 6 * k + 1 = (3 * i + 2) * t + ((4 * i + 3) * t - 1) * j ∧
      5 * t = 6 * k + 1 ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 120) (a := 97)
      (by decide) (by decide)
  have hrem : p % 120 = 97 := by simpa [Nat.ModEq] using hmod
  let n := p / 120
  have hpform : p = 120 * n + 97 := by dsimp [n]; omega
  obtain ⟨hrel, hsharp, hgood⟩ := bilinear_hyperbolic_sharp_family n
  refine ⟨p, 5 * n + 4, 1, 6 * n + 5, 0, hpN, hp, ?_, by omega, hrel,
    hsharp, ?_⟩
  · omega
  · rwa [hpform]

/-- The divisor bound `5(q+1)≤7(6k+1)` is sharp even **among eligible
factors at arbitrarily large prime** `p=24k+1`: choose prime
`p≡97 (mod 120)` and the necessarily composite divisor
`q=42n+34` of `M₁`. This only certifies selected prime families. -/
theorem infinitely_many_auxiliary_divisor_size_sharp (N : ℕ) :
    ∃ p k i q : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      1 < q ∧ q ∣ auxiliaryFactor k i ∧
      q % (4 * i + 3) = 4 * i + 2 ∧
      5 * (q + 1) = 7 * (6 * k + 1) ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 120) (a := 97)
      (by decide) (by decide)
  have hrem : p % 120 = 97 := by simpa [Nat.ModEq] using hmod
  let n := p / 120
  have hpform : p = 120 * n + 97 := by dsimp [n]; omega
  obtain ⟨hqdiv, hres, hsharp, hgood⟩ :=
    bilinear_auxiliary_divisor_sharp_family n
  refine ⟨p, 5 * n + 4, 1, 42 * n + 34, hpN, hp, ?_, by omega,
    hqdiv, ?_, hsharp, ?_⟩
  · omega
  · simpa using hres
  · rwa [hpform]


end Erdos242
