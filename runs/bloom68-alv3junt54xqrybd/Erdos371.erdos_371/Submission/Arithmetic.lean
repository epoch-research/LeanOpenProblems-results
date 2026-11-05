import Submission.Comparison

/-!
# Elementary arithmetic reductions for greatest-prime-factor comparisons

Write `P(n) = Nat.maxPrimeFac n`. This file proves exact cofactor order reversal,
the positive product law, the sharp max-censoring identity for gap signs, and the
first-cofactor-center / repeated-maximum bijection. The conventions `P(0) = 0`
and `P(1) = 1` are retained. Gap signs, unlike `comparisonSign`, are zero at ties.

These are arithmetic identities only. They do **not** prove `S(N) / N → 0` or
any density assertion, and require no analytic cancellation hypothesis.
-/

namespace Erdos371

/- ## Products and cofactors -/

/-- The library product law includes factors equal to one, but excludes zero. -/
theorem maxPrimeFac_mul_of_pos {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    Nat.maxPrimeFac (k * m) = max (Nat.maxPrimeFac k) (Nat.maxPrimeFac m) :=
  Nat.maxPrimeFac_mul (by omega) (by omega)

/-- The total version explicitly separates the junk value at zero. -/
theorem maxPrimeFac_mul_eq (k m : ℕ) :
    Nat.maxPrimeFac (k * m) =
      if k = 0 ∨ m = 0 then 0 else max (Nat.maxPrimeFac k) (Nat.maxPrimeFac m) := by
  by_cases hk : k = 0
  · simp [hk]
  by_cases hm : m = 0
  · simp [hm]
  simp only [hk, hm, or_self, if_false]
  exact Nat.maxPrimeFac_mul hk hm

/-- A positive integer has positive greatest prime factor, including at one. -/
theorem maxPrimeFac_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < Nat.maxPrimeFac n := by
  by_cases h : n = 1
  · simp [h]
  exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).pos

/-- The actual cofactor after removing one copy of the greatest prime factor. -/
def cofactor (n : ℕ) : ℕ := n / Nat.maxPrimeFac n

@[simp]
theorem cofactor_zero : cofactor 0 = 0 := by simp [cofactor]

@[simp]
theorem cofactor_one : cofactor 1 = 1 := by simp [cofactor]

/-- Exact reconstruction, valid even at zero and one. -/
theorem cofactor_mul_maxPrimeFac (n : ℕ) :
    cofactor n * Nat.maxPrimeFac n = n :=
  Nat.div_mul_cancel Nat.maxPrimeFac_dvd

theorem cofactor_pos {n : ℕ} (hn : 0 < n) : 0 < cofactor n :=
  Nat.div_pos Nat.maxPrimeFac_le (maxPrimeFac_pos_of_pos hn)

theorem cofactor_dvd (n : ℕ) : cofactor n ∣ n :=
  ⟨Nat.maxPrimeFac n, (cofactor_mul_maxPrimeFac n).symm⟩

/-- For a nontrivial integer, cofactor one is exactly primality. -/
theorem cofactor_eq_one_iff {n : ℕ} (hn : 2 ≤ n) : cofactor n = 1 ↔ n.Prime := by
  constructor
  · intro h
    have heq : Nat.maxPrimeFac n = n := by
      simpa only [h, one_mul] using cofactor_mul_maxPrimeFac n
    exact heq ▸ Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  · intro hp
    unfold cofactor
    rw [hp.maxPrimeFac_eq_self]
    exact Nat.div_self hp.pos

/-- Cofactors cannot introduce a larger prime than the original positive integer. -/
theorem maxPrimeFac_cofactor_le {n : ℕ} (hn : 0 < n) :
    Nat.maxPrimeFac (cofactor n) ≤ Nat.maxPrimeFac n := by
  by_cases hc : cofactor n = 1
  · rw [hc, Nat.maxPrimeFac_one]
    have := maxPrimeFac_pos_of_pos hn
    omega
  have hc0 := cofactor_pos hn
  exact Nat.le_maxPrimeFac (by omega)
    (Nat.prime_maxPrimeFac_of_one_lt (cofactor n) (by omega))
    (Nat.maxPrimeFac_dvd.trans (cofactor_dvd n))

/-- The endpoint is necessary: `c(1) = c(2) = c(3) = 1`. -/
theorem no_adjacent_cofactor_tie {n : ℕ} (hn : 3 ≤ n) :
    cofactor (n + 1) ≠ cofactor n := by
  intro h
  have hd : cofactor n ∣ n := cofactor_dvd n
  have hd_next : cofactor n ∣ n + 1 := by
    simpa only [h] using cofactor_dvd (n + 1)
  have hc : cofactor n = 1 :=
    Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd).mpr hd_next)
  have hp : n.Prime := (cofactor_eq_one_iff (by omega)).mp hc
  have hq : (n + 1).Prime := (cofactor_eq_one_iff (by omega)).mp (h.trans hc)
  have hpodd : n % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hqodd : (n + 1) % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  omega

/-- Actual ascending greatest-prime-factor comparisons reverse the cofactor order. -/
theorem maxPrimeFac_lt_iff_cofactor_lt {n : ℕ} (hn : 3 ≤ n) :
    Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) ↔ cofactor (n + 1) < cofactor n := by
  constructor
  · intro hpq
    by_contra hc
    have hne := no_adjacent_cofactor_tie hn
    have hab : cofactor n + 1 ≤ cofactor (n + 1) := by omega
    have hle : (cofactor n + 1) * Nat.maxPrimeFac n ≤
        cofactor (n + 1) * Nat.maxPrimeFac (n + 1) :=
      (Nat.mul_le_mul_right _ hab).trans (Nat.mul_le_mul_left _ hpq.le)
    rw [Nat.add_mul, one_mul, cofactor_mul_maxPrimeFac, cofactor_mul_maxPrimeFac] at hle
    have hp2 := (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).two_le
    omega
  · intro hc
    by_contra hpq
    have hqp : Nat.maxPrimeFac (n + 1) ≤ Nat.maxPrimeFac n := by omega
    have hab : cofactor (n + 1) + 1 ≤ cofactor n := by omega
    have hle : (cofactor (n + 1) + 1) * Nat.maxPrimeFac (n + 1) ≤
        cofactor n * Nat.maxPrimeFac n :=
      (Nat.mul_le_mul_right _ hab).trans (Nat.mul_le_mul_left _ hqp)
    rw [Nat.add_mul, one_mul, cofactor_mul_maxPrimeFac, cofactor_mul_maxPrimeFac] at hle
    omega

/-- The decreasing case of the same exact order reversal. -/
theorem maxPrimeFac_next_lt_iff_cofactor_lt {n : ℕ} (hn : 3 ≤ n) :
    Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n ↔ cofactor n < cofactor (n + 1) := by
  have h := maxPrimeFac_lt_iff_cofactor_lt hn
  have hpne := no_adjacent_tie n
  have hcne := no_adjacent_cofactor_tie hn
  omega

/- ## Signed comparisons and the sharp multiplication formula -/

/-- A generic integer-valued comparison, with zero for equal inputs. -/
def signedComparison (a b : ℕ) : ℤ :=
  if a < b then 1 else if b < a then -1 else 0

@[simp]
theorem signedComparison_self (a : ℕ) : signedComparison a a = 0 := by
  simp [signedComparison]

theorem signedComparison_eq_zero_iff (a b : ℕ) : signedComparison a b = 0 ↔ a = b := by
  by_cases hab : a < b
  · simp [signedComparison, hab, ne_of_lt hab]
  by_cases hba : b < a
  · simp [signedComparison, hab, hba, ne_of_gt hba]
  have heq : a = b := by omega
  simp [heq]

/-- This if-else comparison is exactly the sign of the integer difference. -/
theorem signedComparison_eq_int_sign (a b : ℕ) :
    signedComparison a b = Int.sign ((b : ℤ) - a) := by
  by_cases hab : a < b
  · simp [signedComparison, hab,
      Int.sign_eq_one_of_pos (by omega : (0 : ℤ) < (b : ℤ) - a)]
  by_cases hba : b < a
  · simp [signedComparison, hab, hba,
      Int.sign_eq_neg_one_of_neg (by omega : (b : ℤ) - a < 0)]
  have heq : a = b := by omega
  simp [heq]

/-- Applying a common maximum preserves order above its cutoff and ties below it. -/
theorem signedComparison_max (a b c : ℕ) :
    signedComparison (max c a) (max c b) =
      if c < max a b then signedComparison a b else 0 := by
  simp only [max_def, signedComparison]
  split_ifs <;> omega

/-- On consecutive inputs the zero case is impossible, even at zero and one. -/
theorem signedComparison_adjacent (n : ℕ) :
    signedComparison (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) = comparisonSign n := by
  have hne := no_adjacent_tie n
  unfold signedComparison comparisonSign
  split_ifs <;> omega

/-- Equivalently, the adjacent sign is the sign of `c(n) - c(n+1)`. -/
theorem comparisonSign_eq_cofactor_sign {n : ℕ} (hn : 3 ≤ n) :
    comparisonSign n = signedComparison (cofactor (n + 1)) (cofactor n) := by
  have hne := no_adjacent_cofactor_tie hn
  unfold comparisonSign signedComparison
  simp only [maxPrimeFac_lt_iff_cofactor_lt hn]
  split_ifs <;> omega

/-- Integer-sign form of the exact cofactor duality, with the reversed difference. -/
theorem comparisonSign_eq_int_cofactor_sign {n : ℕ} (hn : 3 ≤ n) :
    comparisonSign n = Int.sign ((cofactor n : ℤ) - cofactor (n + 1)) := by
  rw [comparisonSign_eq_cofactor_sign hn, signedComparison_eq_int_sign]

/-- The comparison at a gap is an ordinary three-valued sign, not a strict indicator. -/
def gapComparisonSign (h n : ℕ) : ℤ :=
  signedComparison (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + h))

/-- Sharp identity at `kn` with gap `k`, for every `n ≥ 2` and `k ≥ 1`. -/
theorem gapComparisonSign_mul {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    gapComparisonSign k (k * n) =
      if Nat.maxPrimeFac k < max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) then
        comparisonSign n
      else 0 := by
  have hk0 : 0 < k := by omega
  have hn0 : 0 < n := by omega
  have hnext : k * n + k = k * (n + 1) := by ring
  unfold gapComparisonSign
  rw [hnext, maxPrimeFac_mul_of_pos hk0 hn0,
    maxPrimeFac_mul_of_pos hk0 (by omega : 0 < n + 1),
    signedComparison_max, signedComparison_adjacent]

/-- No loss of the original sign when the original maximum exceeds the multiplier's. -/
theorem gapComparisonSign_mul_of_lt {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (h : Nat.maxPrimeFac k < max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))) :
    gapComparisonSign k (k * n) = comparisonSign n := by
  rw [gapComparisonSign_mul hn hk, if_pos h]

/-- If both original primes lie below the cutoff, the gap comparison is tied. -/
theorem gapComparisonSign_mul_of_le {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (h : max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ≤ Nat.maxPrimeFac k) :
    gapComparisonSign k (k * n) = 0 := by
  rw [gapComparisonSign_mul hn hk, if_neg (not_lt_of_ge h)]

/-- Exact characterization of the exceptional set; no spurious `-1` at gap ties. -/
theorem gapComparisonSign_mul_eq_zero_iff {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    gapComparisonSign k (k * n) = 0 ↔
      max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ≤ Nat.maxPrimeFac k := by
  have hz : comparisonSign n ≠ 0 := by
    rcases comparisonSign_eq_one_or_neg_one n with h | h <;> simp [h]
  rw [gapComparisonSign_mul hn hk]
  by_cases h : Nat.maxPrimeFac k < max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))
  · simp [h, hz]
    omega
  · simp [h]
    omega

/- ## First cofactor support and repeated maxima -/

/-- The first center at which the positive cofactor `k` can occur. -/
def firstCenter (k : ℕ) : ℕ := k * Nat.maxPrimeFac k

/-- The greatest prime at the first center is the greatest prime of its cofactor. -/
theorem firstCenter_max {k : ℕ} (hk : 1 ≤ k) :
    Nat.maxPrimeFac (firstCenter k) = Nat.maxPrimeFac k := by
  by_cases h : k = 1
  · simp [h, firstCenter]
  have hp := Nat.prime_maxPrimeFac_of_one_lt k (by omega)
  unfold firstCenter
  rw [Nat.maxPrimeFac_mul (by omega) hp.ne_zero, hp.maxPrimeFac_eq_self, max_self]

/-- Cofactor is an explicit left inverse, also covering `k = 1`. -/
theorem firstCenter_cofactor {k : ℕ} (hk : 1 ≤ k) : cofactor (firstCenter k) = k := by
  unfold cofactor
  rw [firstCenter_max hk]
  exact Nat.mul_div_cancel k (maxPrimeFac_pos_of_pos (by omega))

theorem firstCenter_pos {k : ℕ} (hk : 1 ≤ k) : 0 < firstCenter k :=
  Nat.mul_pos (by omega) (maxPrimeFac_pos_of_pos (by omega))

theorem firstCenter_ge_two {k : ℕ} (hk : 2 ≤ k) : 2 ≤ firstCenter k := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt k (by omega)
  exact (by decide : 2 ≤ 2 * 2).trans (Nat.mul_le_mul hk hp.two_le)

/-- Every occurrence is at least its first center. -/
theorem firstCenter_cofactor_le {m : ℕ} (hm : 0 < m) : firstCenter (cofactor m) ≤ m := by
  unfold firstCenter
  calc
    cofactor m * Nat.maxPrimeFac (cofactor m) ≤ cofactor m * Nat.maxPrimeFac m :=
      Nat.mul_le_mul_left _ (maxPrimeFac_cofactor_le hm)
    _ = m := cofactor_mul_maxPrimeFac m

/-- Exact positive cofactor support below any cutoff, including the empty cutoff `X = 0`.
In particular, this proves that `firstCenter k` really is the first occurrence. -/
theorem cofactor_support_iff (X k : ℕ) :
    (∃ m : ℕ, 1 ≤ m ∧ m ≤ X ∧ cofactor m = k) ↔ 1 ≤ k ∧ firstCenter k ≤ X := by
  constructor
  · rintro ⟨m, hm, hmX, rfl⟩
    have hc := cofactor_pos (by omega : 0 < m)
    exact ⟨by omega, (firstCenter_cofactor_le (by omega)).trans hmX⟩
  · rintro ⟨hk, hkX⟩
    exact ⟨firstCenter k, by have := firstCenter_pos hk; omega,
      hkX, firstCenter_cofactor hk⟩

/-- Set form of the exact support identity, with the necessary positive restriction. -/
theorem cofactor_support_eq (X : ℕ) :
    cofactor '' Set.Icc 1 X = {k : ℕ | 1 ≤ k ∧ firstCenter k ≤ X} := by
  ext k
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_setOf_eq, and_assoc]
  exact cofactor_support_iff X k

/-- Every nontrivial first center has a repeated greatest prime. -/
theorem firstCenter_repeated {k : ℕ} (hk : 2 ≤ k) :
    (Nat.maxPrimeFac (firstCenter k)) ^ 2 ∣ firstCenter k := by
  rw [firstCenter_max (by omega : 1 ≤ k), firstCenter, pow_two]
  exact mul_dvd_mul Nat.maxPrimeFac_dvd (dvd_refl _)

/-- Conversely, a repeated maximum forces the cofactor to have the same maximum,
and the actual cofactor reconstructs the unique first center. -/
theorem repeated_max_firstCenter {m : ℕ} (hm : 2 ≤ m)
    (hrep : (Nat.maxPrimeFac m) ^ 2 ∣ m) :
    2 ≤ cofactor m ∧ Nat.maxPrimeFac (cofactor m) = Nat.maxPrimeFac m ∧
      firstCenter (cofactor m) = m := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
  have hp0 : 0 < Nat.maxPrimeFac m := hp.pos
  have hd : Nat.maxPrimeFac m ∣ m := Nat.maxPrimeFac_dvd
  have hmul_le : Nat.maxPrimeFac m * Nat.maxPrimeFac m ≤ m :=
    Nat.le_of_dvd (by omega) (by simpa [pow_two] using hrep)
  have hquot_le : Nat.maxPrimeFac m ≤ cofactor m :=
    (Nat.le_div_iff_mul_le hp0).mpr hmul_le
  have hc2 : 2 ≤ cofactor m := hp.two_le.trans hquot_le
  have hdquot : Nat.maxPrimeFac m ∣ cofactor m :=
    (Nat.dvd_div_iff_mul_dvd hd).mpr (by simpa [pow_two] using hrep)
  have hl : Nat.maxPrimeFac m ≤ Nat.maxPrimeFac (cofactor m) :=
    Nat.le_maxPrimeFac (by omega) hp hdquot
  have heq : Nat.maxPrimeFac (cofactor m) = Nat.maxPrimeFac m :=
    le_antisymm (maxPrimeFac_cofactor_le (by omega)) hl
  exact ⟨hc2, heq, by unfold firstCenter; rw [heq]; exact cofactor_mul_maxPrimeFac m⟩

theorem firstCenter_injective {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (h : firstCenter k = firstCenter l) : k = l := by
  calc
    k = cofactor (firstCenter k) := (firstCenter_cofactor hk).symm
    _ = cofactor (firstCenter l) := congrArg cofactor h
    _ = l := firstCenter_cofactor hl

/-- Pointwise characterization; the endpoint excludes junk repeated maxima at zero and one. -/
theorem repeated_max_iff_firstCenter {m : ℕ} (hm : 2 ≤ m) :
    (Nat.maxPrimeFac m) ^ 2 ∣ m ↔ ∃ k : ℕ, 2 ≤ k ∧ firstCenter k = m := by
  constructor
  · intro hrep
    have h := repeated_max_firstCenter hm hrep
    exact ⟨cofactor m, h.1, h.2.2⟩
  · rintro ⟨k, hk, rfl⟩
    exact firstCenter_repeated hk

/-- An actual bijection, with inverse `cofactor`, not just an existence claim. -/
def firstCenterEquiv :
    {k : ℕ // 2 ≤ k} ≃ {m : ℕ // 2 ≤ m ∧ (Nat.maxPrimeFac m) ^ 2 ∣ m} where
  toFun k := ⟨firstCenter k, firstCenter_ge_two k.property, firstCenter_repeated k.property⟩
  invFun m := ⟨cofactor m, (repeated_max_firstCenter m.property.1 m.property.2).1⟩
  left_inv k := Subtype.ext (firstCenter_cofactor (by have := k.property; omega))
  right_inv m := Subtype.ext (repeated_max_firstCenter m.property.1 m.property.2).2.2

/- ## Actual Euclidean seeds and sign reversal -/

/-- A prime times a positive smaller integer has that actual greatest prime. -/
theorem prime_product_max {p r : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hrp : r < p) : Nat.maxPrimeFac (r * p) = p := by
  rw [Nat.maxPrimeFac_mul (by omega) hp.ne_zero, hp.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.maxPrimeFac_le.trans hrp.le)

/-- The product of two positive integers below `p` has actual maximum below `p`. -/
theorem small_product_max {p b u : ℕ} (hb : 0 < b) (hu : 0 < u)
    (hbp : b < p) (hup : u < p) : Nat.maxPrimeFac (b * u) < p := by
  rw [maxPrimeFac_mul_of_pos hb hu]
  exact max_lt (Nat.maxPrimeFac_le.trans_lt hbp) (Nat.maxPrimeFac_le.trans_lt hup)

/-- The `+1` Euclidean seed is an actual descent, not a substituted-label comparison. -/
theorem euclidean_plus_seed {p b r u : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hrb : r < b) (hbp : b < p)
    (heq : r * p + 1 = b * u) :
    Nat.maxPrimeFac (r * p) = p ∧ Nat.maxPrimeFac (r * p + 1) < p := by
  have hb : 0 < b := lt_trans hr hrb
  have hu : 0 < u := by
    by_contra h
    have hz : u = 0 := by omega
    simp [hz] at heq
  have hrp : r < p := lt_trans hrb hbp
  have hmul : r * p + p ≤ b * p := by
    simpa [Nat.add_mul, one_mul] using
      (Nat.mul_le_mul_right p (Nat.succ_le_of_lt hrb))
  have hup : u < p := by
    by_contra h
    have hpu : p ≤ u := by omega
    have hle : b * p ≤ b * u := Nat.mul_le_mul_left b hpu
    have hp2 : 2 ≤ p := hp.two_le
    omega
  exact ⟨prime_product_max hp hr hrp, heq ▸ small_product_max hb hu hbp hup⟩

/-- The `-1` Euclidean seed is an actual ascent. -/
theorem euclidean_minus_seed {p b r u : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hrb : r < b) (hbp : b < p)
    (heq : b * u + 1 = r * p) :
    Nat.maxPrimeFac (b * u) < p ∧ Nat.maxPrimeFac (b * u + 1) = p := by
  have hb : 0 < b := lt_trans hr hrb
  have hp2 : 2 ≤ p := hp.two_le
  have hple : p ≤ r * p := by
    simpa using (Nat.mul_le_mul_right p (Nat.succ_le_of_lt hr))
  have hu : 0 < u := by
    by_contra h
    have hz : u = 0 := by omega
    simp [hz] at heq
    omega
  have hrp : r < p := lt_trans hrb hbp
  have hmul : r * p + p ≤ b * p := by
    simpa [Nat.add_mul, one_mul] using
      (Nat.mul_le_mul_right p (Nat.succ_le_of_lt hrb))
  have hup : u < p := by
    by_contra h
    have hpu : p ≤ u := by omega
    have hle : b * p ≤ b * u := Nat.mul_le_mul_left b hpu
    omega
  exact ⟨small_product_max hb hu hbp hup, heq ▸ prime_product_max hp hr hrp⟩

theorem euclidean_plus_seed_sign {p b r u : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hrb : r < b) (hbp : b < p) (heq : r * p + 1 = b * u) :
    comparisonSign (r * p) = -1 := by
  have h := euclidean_plus_seed hp hr hrb hbp heq
  apply (comparisonSign_eq_neg_one_iff _).mpr
  rw [h.1]
  exact h.2

theorem euclidean_minus_seed_sign {p b r u : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hrb : r < b) (hbp : b < p) (heq : b * u + 1 = r * p) :
    comparisonSign (b * u) = 1 := by
  have h := euclidean_minus_seed hp hr hrb hbp heq
  unfold comparisonSign
  rw [h.2, if_pos h.1]

/-- For an actual ascent `ap+1=bq` with `2 ≤ b < p < q`, Euclidean reduction
constructs an actual opposite-sign seed at `(a % b) * p`. No seed primality or
smoothness is assumed. -/
theorem euclidean_ascent_reversal {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : 2 ≤ b) (hbp : b < p) (hpq : p < q)
    (hmax : Nat.maxPrimeFac (a * p) = p) (heq : a * p + 1 = b * q) :
    Nat.maxPrimeFac ((a % b) * p) = p ∧ Nat.maxPrimeFac ((a % b) * p + 1) < p ∧
      comparisonSign ((a % b) * p) = -comparisonSign (a * p) := by
  have hd : b ∣ a * p + 1 := ⟨q, heq⟩
  have hdseed : b ∣ (a % b) * p + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hd
  have hr : 0 < a % b := by
    by_contra h
    have hz : a % b = 0 := by omega
    have hb1 : b = 1 := Nat.dvd_one.mp (by simpa [hz] using hdseed)
    omega
  have hrb : a % b < b := Nat.mod_lt _ (by omega)
  let u := ((a % b) * p + 1) / b
  have hseed : (a % b) * p + 1 = b * u := (Nat.mul_div_cancel' hdseed).symm
  have ht := euclidean_plus_seed hp hr hrb hbp hseed
  have hqmax : Nat.maxPrimeFac (a * p + 1) = q := by
    rw [heq]
    exact prime_product_max hq (by omega) (hbp.trans hpq)
  have hsource : comparisonSign (a * p) = 1 := by
    simp [comparisonSign, hmax, hqmax, hpq]
  have htarget := euclidean_plus_seed_sign hp hr hrb hbp hseed
  exact ⟨ht.1, ht.2, by rw [htarget, hsource]⟩

/-- The corresponding actual descent `bq+1=ap` reduces to `(a % b) * p - 1`.
The target can be two; no invalid `n ≥ 3` requirement is imposed on its sign. -/
theorem euclidean_descent_reversal {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : 2 ≤ b) (hbp : b < p) (hpq : p < q)
    (hmax : Nat.maxPrimeFac (a * p) = p) (heq : b * q + 1 = a * p) :
    Nat.maxPrimeFac ((a % b) * p - 1) < p ∧
      Nat.maxPrimeFac ((a % b) * p - 1 + 1) = p ∧
      comparisonSign ((a % b) * p - 1) = -comparisonSign (b * q) := by
  have hmod : (a * p) % b = 1 := by
    rw [← heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < b)]
  have hrmod : ((a % b) * p) % b = 1 := by
    simpa only [Nat.mul_mod, Nat.mod_mod] using hmod
  have hr : 0 < a % b := by
    by_contra h
    have hz : a % b = 0 := by omega
    simp [hz] at hrmod
  have hrb : a % b < b := Nat.mod_lt _ (by omega)
  let u := ((a % b) * p) / b
  have hseed : b * u + 1 = (a % b) * p := by
    simpa only [hrmod, add_comm] using Nat.mod_add_div ((a % b) * p) b
  have hminus : b * u = (a % b) * p - 1 := by omega
  have ht := euclidean_minus_seed hp hr hrb hbp hseed
  have htarget := euclidean_minus_seed_sign hp hr hrb hbp hseed
  rw [hminus] at ht htarget
  have hqmax : Nat.maxPrimeFac (b * q) = q :=
    prime_product_max hq (by omega) (hbp.trans hpq)
  have hsource : comparisonSign (b * q) = -1 := by
    apply (comparisonSign_eq_neg_one_iff _).mpr
    rw [heq, hmax, hqmax]
    exact hpq
  exact ⟨ht.1, ht.2, by rw [htarget, hsource]; norm_num⟩

end Erdos371

#print axioms Erdos371.maxPrimeFac_mul_of_pos
#print axioms Erdos371.maxPrimeFac_mul_eq
#print axioms Erdos371.maxPrimeFac_pos_of_pos
#print axioms Erdos371.cofactor
#print axioms Erdos371.cofactor_zero
#print axioms Erdos371.cofactor_one
#print axioms Erdos371.cofactor_mul_maxPrimeFac
#print axioms Erdos371.cofactor_pos
#print axioms Erdos371.cofactor_dvd
#print axioms Erdos371.cofactor_eq_one_iff
#print axioms Erdos371.maxPrimeFac_cofactor_le
#print axioms Erdos371.no_adjacent_cofactor_tie
#print axioms Erdos371.maxPrimeFac_lt_iff_cofactor_lt
#print axioms Erdos371.maxPrimeFac_next_lt_iff_cofactor_lt
#print axioms Erdos371.signedComparison
#print axioms Erdos371.signedComparison_self
#print axioms Erdos371.signedComparison_eq_zero_iff
#print axioms Erdos371.signedComparison_max
#print axioms Erdos371.signedComparison_adjacent
#print axioms Erdos371.comparisonSign_eq_cofactor_sign
#print axioms Erdos371.gapComparisonSign
#print axioms Erdos371.gapComparisonSign_mul
#print axioms Erdos371.gapComparisonSign_mul_of_lt
#print axioms Erdos371.gapComparisonSign_mul_of_le
#print axioms Erdos371.gapComparisonSign_mul_eq_zero_iff
#print axioms Erdos371.firstCenter
#print axioms Erdos371.firstCenter_max
#print axioms Erdos371.firstCenter_cofactor
#print axioms Erdos371.firstCenter_pos
#print axioms Erdos371.firstCenter_ge_two
#print axioms Erdos371.firstCenter_cofactor_le
#print axioms Erdos371.cofactor_support_iff
#print axioms Erdos371.firstCenter_repeated
#print axioms Erdos371.repeated_max_firstCenter
#print axioms Erdos371.firstCenter_injective
#print axioms Erdos371.repeated_max_iff_firstCenter
#print axioms Erdos371.firstCenterEquiv
#print axioms Erdos371.signedComparison_eq_int_sign
#print axioms Erdos371.comparisonSign_eq_int_cofactor_sign
#print axioms Erdos371.cofactor_support_eq
#print axioms Erdos371.prime_product_max
#print axioms Erdos371.small_product_max
#print axioms Erdos371.euclidean_plus_seed
#print axioms Erdos371.euclidean_minus_seed
#print axioms Erdos371.euclidean_plus_seed_sign
#print axioms Erdos371.euclidean_minus_seed_sign
#print axioms Erdos371.euclidean_ascent_reversal
#print axioms Erdos371.euclidean_descent_reversal
