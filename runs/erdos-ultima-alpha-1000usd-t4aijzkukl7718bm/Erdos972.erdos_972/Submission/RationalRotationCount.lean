import FormalConjecturesUtil

/-!
Elementary interval discrepancy from a rational approximation. These estimates
count natural inputs, not prime inputs, and can be used to estimate the local
terms in a two-coordinate sieve.
-/
namespace Erdos972RationalRotationCount

open Finset

lemma card_integer_interval_le {L U : ℝ} (hLU : L ≤ U) :
    ((Icc ⌈L⌉ ⌊U⌋).card : ℝ) ≤ U - L + 1 := by
  by_cases h : ⌈L⌉ ≤ ⌊U⌋
  · have hc : ((Icc ⌈L⌉ ⌊U⌋).card : ℝ) = (⌊U⌋ : ℝ) + 1 - ⌈L⌉ := by
      exact_mod_cast Int.card_Icc_of_le ⌈L⌉ ⌊U⌋ (by omega)
    rw [hc]
    linarith [Int.floor_le U, Int.le_ceil L]
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge h), card_empty, Nat.cast_zero]
    linarith

noncomputable def rotationInterval (θ : ℝ) (K : ℕ) (l u : ℝ) : Finset ℕ :=
  (range K).filter fun n => l ≤ Int.fract (θ * n) ∧ Int.fract (θ * n) < u

/-- The exact lattice-point bound before simplifying the main and error terms. -/
theorem rotationInterval_card_le {a q K : ℕ} (hq : 0 < q)
    (haq : a.Coprime q) {θ l u E : ℝ} (hlu : l ≤ u) (hE : 0 ≤ E)
    (happrox : |θ - (a : ℝ) / q| * K ≤ E) :
    ((rotationInterval θ K l u).card : ℝ) ≤
      ((K / q : ℕ) + 1) * ((q : ℝ) * (u - l + 2 * E) + 1) := by
  classical
  let J : Finset ℤ := Icc ⌈-(q : ℝ) * (u + E)⌉ ⌊(q : ℝ) * (E - l)⌋
  let j : ℕ → ℤ := fun n => (q : ℤ) * ⌊θ * n⌋ - (a : ℤ) * n
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hj (n : ℕ) : (j n : ℝ) =
      (q : ℝ) * ((θ - (a : ℝ) / q) * n - Int.fract (θ * n)) := by
    simp only [j, Int.fract, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  have hJ : (J.card : ℝ) ≤ (q : ℝ) * (u - l + 2 * E) + 1 := by
    have hb : -(q : ℝ) * (u + E) ≤ (q : ℝ) * (E - l) := by nlinarith
    have hc := card_integer_interval_le hb
    dsimp [J]
    convert hc using 1
    ring
  have hcard : (rotationInterval θ K l u).card ≤ (K / q + 1) * J.card := by
    apply (card_le_card_of_injOn (s := rotationInterval θ K l u)
      (t := range (K / q + 1) ×ˢ J) (fun n => (n / q, j n)) ?_ ?_).trans_eq
        (by rw [card_product, card_range])
    · intro n hn
      obtain ⟨hnK, hlo, hhi⟩ := mem_filter.mp (show n ∈ (range K).filter _ from hn)
      have hnle : n ≤ K := (mem_range.mp hnK).le
      have hnR : (n : ℝ) ≤ K := Nat.cast_le.mpr hnle
      have he : |(θ - (a : ℝ) / q) * n| ≤ E := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
        exact (mul_le_mul_of_nonneg_left hnR (abs_nonneg _)).trans happrox
      obtain ⟨he₁, he₂⟩ := abs_le.mp he
      apply mem_product.mpr
      refine ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnle)), ?_⟩
      apply mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        rw [hj]
        nlinarith
      · apply Int.le_floor.mpr
        rw [hj]
        nlinarith
    · intro m hm n hn he
      have hdiv : m / q = n / q := congrArg Prod.fst he
      have hjj : j m = j n := congrArg Prod.snd he
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      have hz : (a : ZMod q) * m = (a : ZMod q) * n := by
        have hc := congrArg (fun z : ℤ => (z : ZMod q)) hjj
        simpa [j] using hc
      have hmodz : (m : ZMod q) = (n : ZMod q) := by
        exact (Units.mul_right_inj (ZMod.unitOfCoprime a haq)).mp hz
      have hmod : m % q = n % q := by
        simpa only [ZMod.val_natCast] using congrArg ZMod.val hmodz
      have hm' := Nat.div_add_mod m q
      have hn' := Nat.div_add_mod n q
      rw [hdiv, hmod] at hm'
      exact hm'.symm.trans hn'
  have hcR : ((rotationInterval θ K l u).card : ℝ) ≤
      ((K / q : ℕ) + 1) * (J.card : ℝ) := by exact_mod_cast hcard
  exact hcR.trans (mul_le_mul_of_nonneg_left hJ (by positivity))


/-- A convenient main term plus an explicit, power-saving error at suitable
rational-approximation scales. -/
theorem rotationInterval_card_upper {a q K : ℕ} (hq : 0 < q)
    (haq : a.Coprime q) {θ l u E : ℝ} (hlu : l ≤ u)
    (hwidth : u - l ≤ 1) (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (happrox : |θ - (a : ℝ) / q| * K ≤ E) :
    ((rotationInterval θ K l u).card : ℝ) ≤
      K * (u - l) + 2 * K * E + K / (q : ℝ) + 3 * q + 1 := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hw0 : 0 ≤ u - l := sub_nonneg.mpr hlu
  have hmain : 0 ≤ (q : ℝ) * (u - l + 2 * E) + 1 := by positivity
  have hc := rotationInterval_card_le hq haq hlu hE happrox
  have hdiv : ((K / q : ℕ) : ℝ) + 1 ≤ (K : ℝ) / q + 1 :=
    by
      have hd : ((K / q : ℕ) : ℝ) ≤ (K : ℝ) / q := Nat.cast_div_le
      linarith
  have hb := hc.trans (mul_le_mul_of_nonneg_right hdiv hmain)
  have he : ((K : ℝ) / q + 1) * ((q : ℝ) * (u - l + 2 * E) + 1) =
      K * (u - l) + 2 * K * E + K / (q : ℝ) + q * (u - l) + 2 * q * E + 1 := by
    field_simp
    ring
  rw [he] at hb
  nlinarith

lemma rotationInterval_card_split (θ : ℝ) (K : ℕ) (t : ℝ) :
    (rotationInterval θ K 0 t).card + (rotationInterval θ K t 1).card = K := by
  classical
  simp only [rotationInterval, Int.fract_nonneg, true_and, Int.fract_lt_one,
    and_true]
  simp_rw [← not_lt]
  exact (card_filter_add_card_filter_not (fun n : ℕ => Int.fract (θ * n) < t)).trans
    (card_range K)

/-- Two-sided discrepancy for a fractional-part interval beginning at zero. -/
theorem rotationInterval_card_discrepancy {a q K : ℕ} (hq : 0 < q)
    (haq : a.Coprime q) {θ t E : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (happrox : |θ - (a : ℝ) / q| * K ≤ E) :
    |((rotationInterval θ K 0 t).card : ℝ) - K * t| ≤
      2 * K * E + K / (q : ℝ) + 3 * q + 1 := by
  have hu := rotationInterval_card_upper hq haq ht (by linarith) hE hE1 happrox
  have hl := rotationInterval_card_upper hq haq ht1 (by linarith) hE hE1 happrox
  have hs : ((rotationInterval θ K 0 t).card : ℝ) +
      (rotationInterval θ K t 1).card = K := by
    exact_mod_cast rotationInterval_card_split θ K t
  rw [sub_zero] at hu
  apply abs_le.mpr
  constructor <;> nlinarith


lemma floor_dvd_iff_fract_div_lt {x : ℝ} (hx : 0 ≤ x) {e : ℕ} (he : 0 < e) :
    e ∣ ⌊x⌋₊ ↔ Int.fract (x / e) < 1 / (e : ℝ) := by
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  let k : ℕ := ⌊x / e⌋₊
  have hfr : Int.fract (x / e) = x / e - (k : ℝ) := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor (div_nonneg hx heR.le)]
    rfl
  have hdecomp : x = e * ((k : ℝ) + Int.fract (x / e)) := by
    rw [hfr]
    field_simp
    ring
  constructor
  · intro hd
    have heq : ⌊x⌋₊ = e * k := by
      dsimp [k]
      rw [Nat.floor_div_natCast]
      exact (Nat.mul_div_cancel' hd).symm
    have hu := Nat.lt_floor_add_one x
    rw [heq, Nat.cast_mul] at hu
    apply (lt_div_iff₀ heR).mpr
    nlinarith
  · intro h
    have hh := (lt_div_iff₀ heR).mp h
    have heq : ⌊x⌋₊ = e * k := by
      apply (Nat.floor_eq_iff hx).mpr
      rw [Nat.cast_mul]
      constructor <;> nlinarith [Int.fract_nonneg (x / e)]
    rw [heq]
    exact dvd_mul_right e k

lemma nonneg_rat_cast_eq_natAbs_div (r : ℚ) (hr : 0 ≤ r) :
    (r : ℝ) = (r.num.natAbs : ℝ) / r.den := by
  have he : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    have hi : (r.num.natAbs : ℤ) = r.num :=
      (Int.natCast_natAbs r.num).trans (abs_of_nonneg (Rat.num_nonneg.mpr hr))
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi
  rw [he]
  exact_mod_cast (Rat.num_div_den r).symm

lemma den_mul_nat_le (r : ℚ) (d : ℕ) : (r * d).den ≤ r.den := by
  have h := Rat.mul_den_dvd r (d : ℚ)
  simp only [Rat.den_natCast, mul_one] at h
  exact Nat.le_of_dvd r.pos h

lemma den_mul_div_nat_le (r : ℚ) (d e : ℕ) (he : 0 < e) :
    (r * d / e).den ≤ r.den * e := by
  have h := Rat.mul_den_dvd (r * d) (e : ℚ)⁻¹
  rw [Rat.den_inv_of_ne_zero (Nat.cast_ne_zero.mpr he.ne'), Rat.num_natCast,
    Int.natAbs_natCast] at h
  apply (Nat.le_of_dvd (Nat.mul_pos (r * d).pos he) h).trans
  exact Nat.mul_le_mul_right e (den_mul_nat_le r d)

lemma den_le_mul_div_nat_den (r : ℚ) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    r.den ≤ d * (r * d / e).den := by
  have h := den_mul_div_nat_le (r * d / e) e d hd
  have heq : r * d / e * e / d = r := by
    field_simp
  rw [heq] at h
  simpa only [mul_comm] using h

/-- Divisibility of the second coordinate on a progression of first coordinates. -/
noncomputable def divisorRow (α : ℝ) (K d e : ℕ) : Finset ℕ :=
  (range K).filter fun k => e ∣ ⌊α * (d * k)⌋₊

lemma divisorRow_eq_rotationInterval {α : ℝ} (hα : 0 ≤ α)
    (K d e : ℕ) (he : 0 < e) :
    divisorRow α K d e = rotationInterval (α * d / e) K 0 (1 / e) := by
  classical
  ext k
  simp only [divisorRow, rotationInterval, mem_filter, Int.fract_nonneg, true_and]
  rw [floor_dvd_iff_fract_div_lt (by positivity) he]
  have heq : α * ((d : ℝ) * k) / e = (α * d / e) * k := by ring
  rw [heq]

/-- Explicit two-coordinate local-density estimate from one rational
approximation. This is a natural-input sieve estimate, not a primality theorem. -/
theorem divisorRow_discrepancy {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (K d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hsmall : |α - r| * ((d : ℝ) / e) * K ≤ 1) :
    |((divisorRow α K d e).card : ℝ) - K / (e : ℝ)| ≤
      2 * K * (|α - r| * ((d : ℝ) / e) * K) +
        (K * d : ℝ) / r.den + 3 * e * r.den + 1 := by
  let s : ℚ := r * d / e
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hqR : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hsR : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have herr : |α * d / e - (s.num.natAbs : ℝ) / s.den| * K =
      |α - r| * ((d : ℝ) / e) * K := by
    rw [← nonneg_rat_cast_eq_natAbs_div s hs]
    simp only [s, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    rw [← sub_div, ← sub_mul, abs_div, abs_mul,
      abs_of_nonneg hdR.le, abs_of_nonneg heR.le]
    ring
  have happ : |α * d / e - (s.num.natAbs : ℝ) / s.den| * K ≤
      |α - r| * ((d : ℝ) / e) * K := herr.le
  have hc := rotationInterval_card_discrepancy s.pos s.reduced
    (show (0 : ℝ) ≤ 1 / e by positivity)
    ((div_le_one heR).mpr he1) (by positivity) hsmall happ
  rw [← divisorRow_eq_rotationInterval hα K d e he] at hc
  simp only [mul_one_div] at hc
  apply hc.trans
  have hlo : (r.den : ℝ) ≤ d * s.den := by
    exact_mod_cast den_le_mul_div_nat_den r d e hd he
  have hhi : (s.den : ℝ) ≤ r.den * e := by
    exact_mod_cast den_mul_div_nat_le r d e he
  have hdiv : (K : ℝ) / s.den ≤ (K * d : ℝ) / r.den := by
    apply (div_le_div_iff₀ hsR hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α := ℝ) K)]
  nlinarith

#print axioms rotationInterval_card_discrepancy
#print axioms divisorRow_discrepancy

end Erdos972RationalRotationCount
