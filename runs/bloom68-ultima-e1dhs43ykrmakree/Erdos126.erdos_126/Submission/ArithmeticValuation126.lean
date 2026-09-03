import FormalConjecturesUtil
import Submission.Signature126

/-!
# Valuation algebra for the integer opposition model

The correction at two is made before constructing the trees.  All difference
valuations below are taken only for distinct positive inputs.  No asymptotic
conjecture, or declaration from `Submission.Spec`, is used.
-/

namespace E126.ArithmeticValuation126

/-- The exceptional first level at two. -/
def epsilon (p : ℕ) : ℕ := if p = 2 then 1 else 0

lemma factorization_two (p : ℕ) : (2 : ℕ).factorization p = epsilon p := by
  simp [Nat.prime_two.factorization, epsilon, Finsupp.single_apply, eq_comm]

/-- The common valuation, with the extra baseline at two when appropriate. -/
def base (p a b : ℕ) : ℕ :=
  min (a.factorization p) (b.factorization p) +
    if a.factorization p = b.factorization p then epsilon p else 0

lemma base_of_eq {p a b : ℕ} (he : a.factorization p = b.factorization p) :
    base p a b = a.factorization p + epsilon p := by
  simp only [base, ← he, min_self, if_true]

/-- The adjusted normalized-sum exponent. -/
def sumExp (p a b : ℕ) : ℕ := (a + b).factorization p - base p a b

/-- The nonnegative absolute difference, without truncated subtraction. -/
def diff (a b : ℕ) : ℕ := ((a : ℤ) - (b : ℤ)).natAbs

/-- The adjusted normalized-difference exponent. -/
def diffExp (p a b : ℕ) : ℕ := (diff a b).factorization p - base p a b

lemma diff_pos {a b : ℕ} (hab : a ≠ b) : 0 < diff a b := by
  apply Int.natAbs_sub_pos_iff.mpr
  exact_mod_cast hab

lemma diff_lt_sum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : diff a b < a + b := by
  unfold diff
  rcases le_total a b with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
    omega

lemma diff_mul (k a b : ℕ) : diff (k * a) (k * b) = k * diff a b := by
  simp [diff, Nat.cast_mul, ← mul_sub, Int.natAbs_mul]

lemma gcd_factorization {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
    (Nat.gcd a b).factorization p = min (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply]

lemma base_eq_gcd_add {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
    base p a b = (Nat.gcd a b).factorization p +
      if p = 2 ∧ a.factorization 2 = b.factorization 2 then 1 else 0 := by
  rw [gcd_factorization ha hb]
  by_cases hp : p = 2
  · subst p
    simp [base, epsilon]
  · simp [base, epsilon, hp]

lemma min_le_sum_factorization {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    min (a.factorization p) (b.factorization p) ≤ (a + b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (by omega : a + b ≠ 0)).mp
  exact Nat.dvd_add
    ((pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd a p))
    ((pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd b p))

lemma min_le_diff_factorization {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b) :
    min (a.factorization p) (b.factorization p) ≤ (diff a b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (diff_pos hab).ne').mp
  apply Int.natCast_dvd.mp
  apply dvd_sub
  · exact Int.natCast_dvd_natCast.mpr
      ((pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd a p))
  · exact Int.natCast_dvd_natCast.mpr
      ((pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd b p))

/-- The strict valuation dichotomy for a sum (the reverse inequality is automatic). -/
lemma factorization_add_le_of_lt {p a b : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hlt : a.factorization p < b.factorization p) :
    (a + b).factorization p ≤ a.factorization p := by
  have hs : a + b ≠ 0 := by omega
  by_contra h
  have hsdiv : p ^ (a.factorization p + 1) ∣ a + b :=
    (hp.pow_dvd_iff_le_factorization hs).2 (by omega)
  have hbdiv : p ^ (a.factorization p + 1) ∣ b :=
    (pow_dvd_pow p (by omega : a.factorization p + 1 ≤ b.factorization p)).trans
      (Nat.ordProj_dvd b p)
  exact Nat.pow_succ_factorization_not_dvd ha hp
    ((Nat.dvd_add_iff_left hbdiv).mpr hsdiv)

lemma add_eq_pow_mul_units {p a b : ℕ} (he : a.factorization p = b.factorization p) :
    a + b = p ^ (a.factorization p) * (ordCompl[p] a + ordCompl[p] b) := by
  calc
    a + b = p ^ (a.factorization p) * ordCompl[p] a +
        p ^ (b.factorization p) * ordCompl[p] b := by
      rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
    _ = _ := by rw [← he, mul_add]

lemma diff_eq_pow_mul_units {p a b : ℕ} (he : a.factorization p = b.factorization p) :
    diff a b = p ^ (a.factorization p) * diff (ordCompl[p] a) (ordCompl[p] b) := by
  calc
    diff a b = diff (p ^ (a.factorization p) * ordCompl[p] a)
        (p ^ (a.factorization p) * ordCompl[p] b) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self, he, Nat.ordProj_mul_ordCompl_eq_self]
    _ = _ := diff_mul _ _ _

lemma unit_sum_ne_zero {p a b : ℕ} (ha : 0 < a) :
    ordCompl[p] a + ordCompl[p] b ≠ 0 := by
  exact ne_of_gt (Nat.add_pos_left (Nat.ordCompl_pos p ha.ne') _)

lemma unit_diff_ne_zero {p a b : ℕ} (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    diff (ordCompl[p] a) (ordCompl[p] b) ≠ 0 := by
  intro hz
  have h := diff_pos hab
  rw [diff_eq_pow_mul_units he, hz, mul_zero] at h
  omega

lemma sum_factorization_of_eq {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (he : a.factorization p = b.factorization p) :
    (a + b).factorization p = a.factorization p +
      (ordCompl[p] a + ordCompl[p] b).factorization p := by
  conv_lhs => rw [add_eq_pow_mul_units he]
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (unit_sum_ne_zero ha),
    Finsupp.add_apply, Nat.factorization_pow_self hp]

lemma diff_factorization_of_eq {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    (diff a b).factorization p = a.factorization p +
      (diff (ordCompl[p] a) (ordCompl[p] b)).factorization p := by
  rw [diff_eq_pow_mul_units he,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (unit_diff_ne_zero hab he),
    Finsupp.add_apply, Nat.factorization_pow_self hp]

lemma two_dvd_add_of_odd {u v : ℕ} (hu : ¬2 ∣ u) (hv : ¬2 ∣ v) : 2 ∣ u + v := by
  have hu' : u % 2 ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hv' : v % 2 ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  apply Nat.dvd_of_mod_eq_zero
  omega

lemma two_dvd_diff_of_odd {u v : ℕ} (hu : ¬2 ∣ u) (hv : ¬2 ∣ v) : 2 ∣ diff u v := by
  have hu' : u % 2 ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hv' : v % 2 ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  have hm : (v : ℤ) ≡ (u : ℤ) [ZMOD (2 : ℕ)] := by
    apply Int.natCast_modEq_iff.mpr
    change v % 2 = u % 2
    omega
  exact Int.natCast_dvd.mp hm.dvd

lemma epsilon_le_unit_sum {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    epsilon p ≤ (ordCompl[p] a + ordCompl[p] b).factorization p := by
  by_cases hp : p = 2
  · subst p
    change 1 ≤ _
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (unit_sum_ne_zero ha)).mp
    simpa using two_dvd_add_of_odd
      (Nat.not_dvd_ordCompl Nat.prime_two ha.ne') (Nat.not_dvd_ordCompl Nat.prime_two hb.ne')
  · simp [epsilon, hp]

lemma epsilon_le_unit_diff {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    epsilon p ≤ (diff (ordCompl[p] a) (ordCompl[p] b)).factorization p := by
  by_cases hp : p = 2
  · subst p
    change 1 ≤ _
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (unit_diff_ne_zero hab he)).mp
    simpa using two_dvd_diff_of_odd
      (Nat.not_dvd_ordCompl Nat.prime_two ha.ne') (Nat.not_dvd_ordCompl Nat.prime_two hb.ne')
  · simp [epsilon, hp]

lemma base_le_sum {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    base p a b ≤ (a + b).factorization p := by
  by_cases he : a.factorization p = b.factorization p
  · rw [sum_factorization_of_eq hp ha he]
    have h := epsilon_le_unit_sum (p := p) ha hb
    rw [base_of_eq he]
    exact Nat.add_le_add_left h _
  · simpa [base, he] using min_le_sum_factorization hp ha hb

lemma base_le_diff {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    base p a b ≤ (diff a b).factorization p := by
  by_cases he : a.factorization p = b.factorization p
  · rw [diff_factorization_of_eq hp hab he]
    have h := epsilon_le_unit_diff ha hb hab he
    rw [base_of_eq he]
    exact Nat.add_le_add_left h _
  · simpa [base, he] using min_le_diff_factorization hp hab

lemma sumExp_of_ne {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (he : a.factorization p ≠ b.factorization p) : sumExp p a b = 0 := by
  unfold sumExp base
  rw [if_neg he, add_zero]
  apply Nat.sub_eq_zero_of_le
  rcases lt_or_gt_of_ne he with hlt | hgt
  · rw [min_eq_left hlt.le]
    exact factorization_add_le_of_lt hp ha.ne' hlt
  · rw [min_eq_right hgt.le, Nat.add_comm a b]
    exact factorization_add_le_of_lt hp hb.ne' hgt

lemma sumExp_of_eq {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (he : a.factorization p = b.factorization p) :
    sumExp p a b = (ordCompl[p] a + ordCompl[p] b).factorization p - epsilon p := by
  rw [sumExp, sum_factorization_of_eq hp ha he, base_of_eq he, Nat.add_sub_add_left]

lemma diffExp_of_eq {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    diffExp p a b = (diff (ordCompl[p] a) (ordCompl[p] b)).factorization p - epsilon p := by
  rw [diffExp, diff_factorization_of_eq hp hab he, base_of_eq he, Nat.add_sub_add_left]

/-- The threshold characterization, with levels numbered from zero. -/
lemma sumExp_threshold {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    n < sumExp p a b ↔ a.factorization p = b.factorization p ∧
      p ^ (n + 1 + epsilon p) ∣ ordCompl[p] a + ordCompl[p] b := by
  by_cases he : a.factorization p = b.factorization p
  · rw [sumExp_of_eq hp ha he, and_iff_right he,
      hp.pow_dvd_iff_le_factorization (unit_sum_ne_zero ha)]
    omega
  · simp [sumExp_of_ne hp ha hb he, he]

lemma same_color_sumExp_zero {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : Signature126.primeColor p a = Signature126.primeColor p b) :
    sumExp p a b = 0 := by
  by_cases he : a.factorization p = b.factorization p
  · rw [sumExp_of_eq hp ha he]
    apply Nat.sub_eq_zero_of_le
    rw [← factorization_two]
    exact Signature126.ordCompl_sum_factorization_le hp ha hb hc
  · exact sumExp_of_ne hp ha hb he

/-- Orient units once, using the global color rather than a new sign at each level. -/
def orient (s : Bool) (u : ℕ) : ℤ := if s then (u : ℤ) else -(u : ℤ)

lemma orient_mod_opposite (s t : Bool) (u v m : ℕ) (hst : s ≠ t) :
    orient s u % (m : ℤ) = orient t v % (m : ℤ) ↔ m ∣ u + v := by
  change Int.ModEq (m : ℤ) (orient s u) (orient t v) ↔ _
  rw [Int.modEq_iff_dvd]
  cases s <;> cases t
  · exact (hst rfl).elim
  · simp only [orient, Bool.false_eq_true, if_false, if_true]
    rw [show (v : ℤ) - -(u : ℤ) = ((u + v : ℕ) : ℤ) by push_cast; ring]
    exact Int.natCast_dvd_natCast
  · simp only [orient, Bool.false_eq_true, if_false, if_true]
    rw [show -(v : ℤ) - (u : ℤ) = -((u + v : ℕ) : ℤ) by push_cast; ring, dvd_neg]
    exact Int.natCast_dvd_natCast
  · exact (hst rfl).elim

lemma orient_mod_same (s : Bool) (u v m : ℕ) :
    orient s u % (m : ℤ) = orient s v % (m : ℤ) ↔ m ∣ diff u v := by
  change Int.ModEq (m : ℤ) (orient s u) (orient s v) ↔ _
  rw [Int.modEq_iff_dvd]
  cases s
  · simp only [orient, Bool.false_eq_true, if_false]
    rw [show -(v : ℤ) - -(u : ℤ) = (u : ℤ) - (v : ℤ) by ring]
    exact Int.natCast_dvd
  · simp only [orient, if_true]
    rw [show (v : ℤ) - (u : ℤ) = -((u : ℤ) - (v : ℤ)) by ring, dvd_neg]
    exact Int.natCast_dvd

/-- A signed unit residue together with its valuation tag. -/
def label (p n a : ℕ) : ℕ × ℤ :=
  (a.factorization p,
    orient (Signature126.primeColor p a) (ordCompl[p] a) % (p ^ (n + 1 + epsilon p) : ℕ))

lemma label_refines (p : ℕ) {n m : ℕ} (hnm : n ≤ m) {a b : ℕ}
    (he : label p m a = label p m b) : label p n a = label p n b := by
  obtain ⟨hv, hu⟩ := Prod.mk.inj he
  apply Prod.ext hv
  apply Int.ModEq.of_dvd _ hu
  exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))

lemma label_eq_opposite {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : Signature126.primeColor p a ≠ Signature126.primeColor p b) (n : ℕ) :
    label p n a = label p n b ↔ n < sumExp p a b := by
  rw [sumExp_threshold hp ha hb]
  simp only [label, Prod.mk.injEq]
  rw [orient_mod_opposite _ _ _ _ _ hc]

/-- Same-color members of a level have the corresponding adjusted difference valuation. -/
lemma label_eq_same_bound {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (hc : Signature126.primeColor p a = Signature126.primeColor p b) (n : ℕ)
    (he : label p n a = label p n b) : n < diffExp p a b := by
  obtain ⟨hv, hu⟩ := Prod.mk.inj he
  rw [diffExp_of_eq hp hab hv]
  have hd : p ^ (n + 1 + epsilon p) ∣ diff (ordCompl[p] a) (ordCompl[p] b) := by
    apply (orient_mod_same (Signature126.primeColor p a) _ _ _).mp
    simpa only [hc] using hu
  have ht := (hp.pow_dvd_iff_le_factorization (unit_diff_ne_zero hab hv)).mp hd
  omega

end E126.ArithmeticValuation126
