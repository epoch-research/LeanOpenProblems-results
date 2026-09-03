import Submission.IntegerSieveArithmetic

/-!
# Exact CRT rounding on a window

This file does not import `Submission.Spec` or assume any Jacobsthal conjecture.
It proves exact pair counts, a complete criterion for the implication
"both singleton counts are ceilings => the pair count is a ceiling", and
a quantitative obstruction to that implication for nearby moduli.
-/

namespace IntegerSieve.CRTWindow

open Finset

/-- The exact count of a residue in `[0,L)`. -/
def residueCount (L p a : ℕ) : ℕ := Nat.count (fun n => n ≡ a [MOD p]) L

/-- The count at residue zero is always the largest singleton count. -/
lemma residueCount_le_zero (L : ℕ) {p : ℕ} (hp : 0 < p) (a : ℕ) :
    residueCount L p a ≤ residueCount L p 0 := by
  simp only [residueCount, Nat.count_modEq_card L hp, Nat.zero_mod]
  split_ifs <;> omega

/-- The last-position remainder, unlike `L % p`, also handles integral counts:
all residues are maximal when `p ∣ L`. -/
lemma residueCount_max_iff {L p : ℕ} (hL : 0 < L) (hp : 0 < p) (a : ℕ) :
    residueCount L p a = residueCount L p 0 ↔ a % p ≤ (L - 1) % p := by
  have ha : a % p < p := Nat.mod_lt _ hp
  have ht : (L - 1) % p < p := Nat.mod_lt _ hp
  have hsucc : L = (L - 1) + 1 := by omega
  have hm : L % p = ((L - 1) % p + 1) % p := by
    conv_lhs => rw [hsucc]
    simp only [Nat.add_mod, Nat.mod_mod]
  simp only [residueCount, Nat.count_modEq_card L hp, Nat.zero_mod]
  by_cases htop : (L - 1) % p + 1 = p
  · rw [hm, htop, Nat.mod_self]
    simp only [Nat.not_lt_zero, if_false, true_iff]
    omega
  · have hsmall : (L - 1) % p + 1 < p := by omega
    rw [hm, Nat.mod_eq_of_lt hsmall]
    split_ifs <;> omega

/-- For a specified CRT root, the joint count has one exact rounding bit. -/
theorem pair_count_exact {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : p.Coprime q) (L a b r : ℕ) (hr : r < p * q)
    (hrp : r ≡ a [MOD p]) (hrq : r ≡ b [MOD q]) :
    Nat.count (fun n => n ≡ a [MOD p] ∧ n ≡ b [MOD q]) L =
      L / (p * q) + if r < L % (p * q) then 1 else 0 := by
  have heq : (fun n => n ≡ a [MOD p] ∧ n ≡ b [MOD q]) =
      (fun n => n ≡ r [MOD p * q]) := by
    funext n
    apply propext
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    exact and_congr ⟨fun h => h.trans hrp.symm, fun h => h.trans hrp⟩
      ⟨fun h => h.trans hrq.symm, fun h => h.trans hrq⟩
  simpa only [heq, Nat.mod_eq_of_lt hr] using
    (Nat.count_modEq_card L (Nat.mul_pos hp hq) r)

/-- A southwest prefix record of the CRT grid, expressed without choosing an
implementation of CRT. Bounds on `r` are separate hypotheses. -/
def IsRecord (p q r : ℕ) : Prop :=
  ∀ s : ℕ, s < p * q → s % p ≤ r % p → s % q ≤ r % q → s ≤ r

/-- On a nonzero proper tail of a period, every CRT root giving both singleton
ceilings must also give the joint ceiling. -/
def ForcingRemainder (p q t : ℕ) : Prop :=
  ∀ r : ℕ, r < p * q → r % p ≤ (t - 1) % p →
    r % q ≤ (t - 1) % q → r < t

lemma forcing_iff_record {p q t : ℕ} (ht : 0 < t) :
    ForcingRemainder p q t ↔ IsRecord p q (t - 1) := by
  unfold ForcingRemainder IsRecord
  constructor <;> intro h r hr hrp hrq <;> have := h r hr hrp hrq <;> omega

/-- This criterion is equivalent to the actual occurrence-count implication,
not merely a necessary numerical condition. The count at zero is the ceiling.
Here `0 < L < pq`; full periods can be removed using `pair_count_exact`. -/
theorem forcing_iff_maximal_counts {p q L : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (hL : 0 < L) (hLN : L < p * q) :
    ForcingRemainder p q L ↔
      (∀ a b : ℕ, residueCount L p a = residueCount L p 0 →
        residueCount L q b = residueCount L q 0 →
        Nat.count (fun n => n ≡ a [MOD p] ∧ n ≡ b [MOD q]) L = 1) := by
  constructor
  · intro hf a b ha hb
    let r := Nat.chineseRemainder hcop a b
    have hr : (r : ℕ) < p * q := Nat.chineseRemainder_lt_mul hcop a b hp.ne' hq.ne'
    have hrp := r.property.1
    have hrq := r.property.2
    have ha' := (residueCount_max_iff hL hp a).mp ha
    have hb' := (residueCount_max_iff hL hq b).mp hb
    have hrt : (r : ℕ) < L := hf r hr
      ((show (r : ℕ) % p = a % p from hrp).trans_le ha')
      ((show (r : ℕ) % q = b % q from hrq).trans_le hb')
    rw [pair_count_exact hp hq hcop L a b r hr hrp hrq,
      Nat.div_eq_of_lt hLN, Nat.mod_eq_of_lt hLN, if_pos hrt]
  · intro hf r hr hrp hrq
    have ha := (residueCount_max_iff hL hp r).mpr hrp
    have hb := (residueCount_max_iff hL hq r).mpr hrq
    have hc := hf r r ha hb
    rw [pair_count_exact hp hq hcop L r r r hr (Nat.ModEq.refl _) (Nat.ModEq.refl _),
      Nat.div_eq_of_lt hLN, Nat.mod_eq_of_lt hLN] at hc
    split_ifs at hc with h <;> omega

/-- A root congruent to `1 mod p` and `0 mod q` cannot be small when the
moduli are close. The gap assumption excludes the consecutive-moduli case. -/
lemma off_diagonal_10_bound {p q x : ℕ} (hp : 1 < p) (hpq : p + 2 ≤ q)
    (hxp : x % p = 1) (hxq : x % q = 0) :
    q * (p + 1) ≤ (q - p) * x := by
  obtain ⟨v, hv⟩ := Nat.dvd_of_mod_eq_zero hxq
  have hxpos : 0 < x := by
    by_contra h
    have : x = 0 := by omega
    simp [this] at hxp
  have hvpos : 1 ≤ v := by nlinarith
  have hd : 2 ≤ q - p := by omega
  have hq : q = p + (q - p) := by omega
  have hdiv := Nat.mod_add_div x p
  rw [hxp] at hdiv
  have hvw : v + 1 ≤ x / p := by
    by_contra h
    have hwv : x / p ≤ v := by omega
    have hmul := Nat.mul_le_mul_left p hwv
    have htwo : 2 ≤ (q - p) * v := by nlinarith
    nlinarith
  have hsmall : p + 1 ≤ (q - p) * v := by nlinarith
  have hmul := Nat.mul_le_mul_left q hsmall
  calc
    q * (p + 1) ≤ q * ((q - p) * v) := hmul
    _ = (q - p) * x := by rw [hv]; ring

lemma off_diagonal_01_bound {p q x : ℕ} (hp : 1 < p) (hpq : p + 2 ≤ q)
    (hxp : x % p = 0) (hxq : x % q = 1) :
    p * (q - 1) ≤ (q - p) * x := by
  obtain ⟨v, hv⟩ := Nat.dvd_of_mod_eq_zero hxp
  have hxpos : 0 < x := by
    by_contra h
    have : x = 0 := by omega
    simp [this] at hxq
  have hvpos : 1 ≤ v := by nlinarith
  have hd : 2 ≤ q - p := by omega
  have hq : q = p + (q - p) := by omega
  have hdiv := Nat.mod_add_div x q
  rw [hxq] at hdiv
  have hwv : x / q + 1 ≤ v := by
    by_contra h
    have hvw : v ≤ x / q := by omega
    have hmul := Nat.mul_le_mul_left q hvw
    nlinarith
  have hwv' := Nat.mul_le_mul_left q hwv
  have hprod : q * v = p * v + (q - p) * v := by
    conv_lhs => rw [hq]
    ring
  have hsmall : q - 1 ≤ (q - p) * v := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega)]
  have hmul := Nat.mul_le_mul_left p hsmall
  calc
    p * (q - 1) ≤ p * ((q - p) * v) := hmul
    _ = (q - p) * x := by rw [hv]; ring

/-- Every nonzero CRT prefix record satisfies a quantitative gap constraint. -/
theorem record_gap_bound {p q r : ℕ} (hp : 1 < p) (hpq : p + 2 ≤ q)
    (hcop : p.Coprime q) (hr0 : 0 < r) (hrN : r < p * q)
    (hrec : IsRecord p q r) :
    p * (q - 1) ≤ (q - p) * r := by
  have hq : 1 < q := by omega
  have hnot : r % p ≠ 0 ∨ r % q ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := hcop.mul_dvd_of_dvd_of_dvd
      (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_of_mod_eq_zero h.2)
    have hle := Nat.le_of_dvd hr0 hd
    omega
  rcases hnot with hrp | hrq
  · let x := Nat.chineseRemainder hcop 1 0
    have hxN : (x : ℕ) < p * q :=
      Nat.chineseRemainder_lt_mul hcop 1 0 (by omega) (by omega)
    have hxp : (x : ℕ) % p = 1 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp] using x.property.1
    have hxq : (x : ℕ) % q = 0 := by
      simpa only [Nat.ModEq, Nat.zero_mod] using x.property.2
    have hxr : (x : ℕ) ≤ r := hrec x hxN (by omega) (by omega)
    have hb := off_diagonal_10_bound hp hpq hxp hxq
    have hm := Nat.mul_le_mul_left (q - p) hxr
    calc
      p * (q - 1) ≤ p * q := Nat.mul_le_mul_left p (Nat.sub_le q 1)
      _ ≤ q * (p + 1) := by nlinarith
      _ ≤ (q - p) * r := hb.trans hm
  · let x := Nat.chineseRemainder hcop 0 1
    have hxN : (x : ℕ) < p * q :=
      Nat.chineseRemainder_lt_mul hcop 0 1 (by omega) (by omega)
    have hxp : (x : ℕ) % p = 0 := by
      simpa only [Nat.ModEq, Nat.zero_mod] using x.property.1
    have hxq : (x : ℕ) % q = 1 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hq] using x.property.2
    have hxr : (x : ℕ) ≤ r := hrec x hxN (by omega) (by omega)
    exact (off_diagonal_01_bound hp hpq hxp hxq).trans
      (Nat.mul_le_mul_left (q - p) hxr)

/-- Thus a nontrivial favorable length below `pq` is necessarily large compared
with `pq/(q-p)`. Moving the start of the interval cannot change this criterion. -/
theorem forcing_gap_bound {p q L : ℕ} (hp : 1 < p) (hpq : p + 2 ≤ q)
    (hcop : p.Coprime q) (hL : 2 ≤ L) (hLN : L < p * q)
    (hf : ForcingRemainder p q L) :
    p * (q - 1) ≤ (q - p) * (L - 1) := by
  exact record_gap_bound hp hpq hcop (by omega) (by omega)
    ((forcing_iff_record (by omega)).mp hf)

/-- A constructive-in-content counterpattern: under the small-gap inequality,
there exist two maximal residue columns with NO common point. This rules out
forcing joint overlap from singleton ceilings on that entire range of lengths. -/
theorem disjoint_maximal_columns_of_small_gap {p q L : ℕ}
    (hp : 1 < p) (hpq : p + 2 ≤ q) (hcop : p.Coprime q)
    (hL : 2 ≤ L) (hLN : L < p * q)
    (hgap : (q - p) * (L - 1) < p * (q - 1)) :
    ∃ a b : ℕ, residueCount L p a = residueCount L p 0 ∧
      residueCount L q b = residueCount L q 0 ∧
      Nat.count (fun n => n ≡ a [MOD p] ∧ n ≡ b [MOD q]) L = 0 := by
  classical
  have hf : ¬ ForcingRemainder p q L := fun h =>
    (Nat.not_le_of_gt hgap) (forcing_gap_bound hp hpq hcop hL hLN h)
  unfold ForcingRemainder at hf
  push_neg at hf
  obtain ⟨r, hr, hrp, hrq, hrL⟩ := hf
  refine ⟨r, r, (residueCount_max_iff (by omega) (by omega) r).mpr hrp,
    (residueCount_max_iff (by omega) (by omega) r).mpr hrq, ?_⟩
  rw [pair_count_exact (by omega) (by omega) hcop L r r r hr
    (Nat.ModEq.refl _) (Nat.ModEq.refl _), Nat.div_eq_of_lt hLN,
    Nat.mod_eq_of_lt hLN, if_neg (by omega)]

end IntegerSieve.CRTWindow

#print axioms IntegerSieve.CRTWindow.pair_count_exact
#print axioms IntegerSieve.CRTWindow.forcing_iff_maximal_counts
#print axioms IntegerSieve.CRTWindow.record_gap_bound
#print axioms IntegerSieve.CRTWindow.disjoint_maximal_columns_of_small_gap
