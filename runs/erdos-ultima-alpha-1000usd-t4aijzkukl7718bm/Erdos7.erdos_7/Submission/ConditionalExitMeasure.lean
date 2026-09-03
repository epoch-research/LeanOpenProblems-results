import FormalConjecturesUtil

/-! Conditional-exit measures on a finite digit tree. The stem digit continues
with probability1/p, and the selected exit digit takes all remaining mass.
After an exit, the remaining digits are uniform. These are finite probability
weights and exact cylinder identities, not a covering-system theorem. -/
namespace Erdos7ConditionalExitMeasure
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma sum_digits_succ {p E : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin (E+1) → Fin p) → M) :
    (∑ y, f y) = ∑ d : Fin p, ∑ z : Fin E → Fin p, f (Fin.cons d z) := by
  calc
    _ = ∑ z : Fin p × (Fin E → Fin p), f (Fin.cons z.1 z.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (E+1) => Fin p)).symm
      intro y
      simp
    _ = _ := Fintype.sum_prod_type _

/-- Unnormalized integer density. Its sum is p^E, while its values are
0,1,or p-1 according to the first non-stem digit. -/
def raw {p : ℕ} (stem exit : Fin p) : (E : ℕ) → (Fin E → Fin p) → ℕ
  | 0, _ => 1
  | E+1, y => if y 0 = stem then raw stem exit E (Fin.tail y)
      else if y 0 = exit then p-1 else 0

@[simp] lemma raw_cons {p E : ℕ} (stem exit d : Fin p) (z : Fin E → Fin p) :
    raw stem exit (E+1) (Fin.cons d z) =
      if d = stem then raw stem exit E z else if d = exit then p-1 else 0 := by
  simp [raw]

lemma raw_le {p E : ℕ} (hp : 2 ≤ p) (stem exit : Fin p) (y : Fin E → Fin p) :
    raw stem exit E y ≤ p-1 := by
  induction E with
  | zero => simp only [raw]; omega
  | succ E ih =>
    simp only [raw]
    split_ifs <;> first | exact ih _ | omega

lemma raw_sum {p : ℕ} (hp : 1 ≤ p) (stem exit : Fin p) (hne : exit ≠ stem) (E : ℕ) :
    (∑ y : Fin E → Fin p, raw stem exit E y) = p^E := by
  induction E with
  | zero => simp [raw]
  | succ E ih =>
    rw [sum_digits_succ]
    have he (d : Fin p) (z : Fin E → Fin p) :
        raw stem exit (E+1) (Fin.cons d z) =
          (if d = stem then raw stem exit E z else 0) + (if d = exit then p-1 else 0) := by
      rw [raw_cons]
      by_cases hs : d = stem
      · subst d
        simp [hne.symm]
      · simp [hs]
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_ite_irrel]
    simp [ih, pow_succ]
    have he : p-1+1 = p := by omega
    calc
      p^E + p^E*(p-1) = p^E*(p-1+1) := by ring
      _ = p^E*p := by rw [he]

/-- Exact matching of a shorter prefix. -/
def prefixMatch {p a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p) (y : Fin E → Fin p) : Prop :=
  ∀ i : Fin a, y (Fin.castLE ha i) = v i

instance {p a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p) (y : Fin E → Fin p) :
    Decidable (prefixMatch ha v y) := by unfold prefixMatch; infer_instance

@[simp] lemma prefixMatch_zero {p E : ℕ} (v : Fin 0 → Fin p) (y : Fin E → Fin p) :
    prefixMatch (Nat.zero_le E) v y := by intro i; exact i.elim0

lemma prefixMatch_cons {p a E : ℕ} (ha : a+1 ≤ E+1) (v : Fin (a+1) → Fin p)
    (d : Fin p) (z : Fin E → Fin p) :
    prefixMatch ha v (Fin.cons d z) ↔
      d = v 0 ∧ prefixMatch (Nat.le_of_succ_le_succ ha) (Fin.tail v) z := by
  unfold prefixMatch
  rw [Fin.forall_fin_succ]
  rfl

lemma sum_prefix_succ {p a E : ℕ} (ha : a+1 ≤ E+1) (v : Fin (a+1) → Fin p)
    (f : (Fin (E+1) → Fin p) → ℕ) :
    (∑ y, if prefixMatch ha v y then f y else 0) =
      ∑ z : Fin E → Fin p, if prefixMatch (Nat.le_of_succ_le_succ ha) (Fin.tail v) z
        then f (Fin.cons (v 0) z) else 0 := by
  rw [sum_digits_succ]
  simp_rw [prefixMatch_cons, ite_and, Finset.sum_ite_irrel]
  simp

lemma prefix_count {p a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p) :
    (∑ y : Fin E → Fin p, if prefixMatch ha v y then 1 else 0) = p^(E-a) := by
  induction a generalizing E with
  | zero => simp [prefixMatch]
  | succ a ih =>
    cases E with
    | zero => omega
    | succ E =>
      rw [sum_prefix_succ]
      simpa only [Nat.succ_sub_succ_eq_sub] using ih (Nat.le_of_succ_le_succ ha) (Fin.tail v)

/-- The density is consistent under every prefix projection. -/
theorem raw_prefix_sum {p : ℕ} (hp : 1 ≤ p) (stem exit : Fin p) (hne : exit ≠ stem)
    {a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p) :
    (∑ y : Fin E → Fin p, if prefixMatch ha v y then raw stem exit E y else 0) =
      raw stem exit a v * p^(E-a) := by
  induction a generalizing E with
  | zero => simpa [raw, prefixMatch] using raw_sum hp stem exit hne E
  | succ a ih =>
    cases E with
    | zero => omega
    | succ E =>
      rw [sum_prefix_succ]
      simp only [raw, Fin.cons_zero, Fin.tail_cons, Nat.succ_sub_succ_eq_sub]
      by_cases hs : v 0 = stem
      · simp only [if_pos hs]
        exact ih (Nat.le_of_succ_le_succ ha) (Fin.tail v)
      · simp only [if_neg hs]
        by_cases hx : v 0 = exit
        · simp only [if_pos hx]
          have he : (∑ z : Fin E → Fin p,
              if prefixMatch (Nat.le_of_succ_le_succ ha) (Fin.tail v) z then p-1 else 0) =
              (p-1) * ∑ z : Fin E → Fin p,
                if prefixMatch (Nat.le_of_succ_le_succ ha) (Fin.tail v) z then 1 else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            split_ifs <;> simp
          rw [he, prefix_count]
        · simp [hx]

/-- Rational probability density on the finite digit vectors. -/
def density {p E : ℕ} (stem exit : Fin p) (y : Fin E → Fin p) : ℚ :=
  (raw stem exit E y : ℚ) / (p : ℚ)^E

lemma density_nonneg {p E : ℕ} (stem exit : Fin p) (y : Fin E → Fin p) :
    0 ≤ density stem exit y := by unfold density; positivity

lemma density_mass {p : ℕ} (hp : 1 ≤ p) (stem exit : Fin p) (hne : exit ≠ stem) (E : ℕ) :
    (∑ y : Fin E → Fin p, density stem exit y) = 1 := by
  unfold density
  rw [← Finset.sum_div, ← Nat.cast_sum, raw_sum hp stem exit hne]
  rw [Nat.cast_pow]
  apply div_self
  positivity

/-- The first non-stem digit, if the finite word has one. This classification
is independent of which exit measure is subsequently used. -/
def firstExit {p : ℕ} (stem : Fin p) : (E : ℕ) → (Fin E → Fin p) → Option (Fin p)
  | 0, _ => none
  | E+1, y => if y 0 = stem then firstExit stem E (Fin.tail y) else some (y 0)

lemma raw_classified {p E : ℕ} (stem exit : Fin p) (y : Fin E → Fin p) :
    raw stem exit E y = match firstExit stem E y with
      | none => 1
      | some d => if d = exit then p-1 else 0 := by
  induction E with
  | zero => rfl
  | succ E ih =>
    by_cases h : y 0 = stem
    · simpa only [raw, firstExit, if_pos h] using ih (Fin.tail y)
    · simp only [raw, firstExit, if_neg h]

/-- A prescribed first non-stem digit determines the classification. -/
lemma firstExit_of_stop {p E : ℕ} (stem d : Fin p) (hd : d ≠ stem)
    (b : Fin E) (y : Fin E → Fin p)
    (hbefore : ∀ j : Fin E, j.val < b.val → y j = stem) (hstop : y b = d) :
    firstExit stem E y = some d := by
  induction E with
  | zero => exact b.elim0
  | succ E ih =>
    cases b using Fin.cases with
    | zero => simp only [firstExit, hstop, if_neg hd]
    | succ b =>
      have hzero : y 0 = stem := hbefore 0 (by simp)
      rw [firstExit, if_pos hzero]
      apply ih b (Fin.tail y)
      · intro j hj
        exact hbefore j.succ (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using hj)
      · exact hstop

lemma firstExit_stem {p : ℕ} (stem : Fin p) (E : ℕ) :
    firstExit stem E (fun _ => stem) = none := by
  induction E with
  | zero => rfl
  | succ E ih => simpa only [firstExit, if_pos rfl, Fin.tail] using ih

/-- Every finite cylinder has the claimed exact probability. -/
theorem density_prefix_sum {p : ℕ} (hp : 1 ≤ p) (stem exit : Fin p) (hne : exit ≠ stem)
    {a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p) :
    (∑ y : Fin E → Fin p, if prefixMatch ha v y then density stem exit y else 0) =
      (raw stem exit a v : ℚ) / (p : ℚ)^a := by
  have he : (∑ y : Fin E → Fin p,
      if prefixMatch ha v y then (raw stem exit E y : ℚ) else 0) =
      (raw stem exit a v : ℚ) * (p : ℚ)^(E-a) := by
    exact_mod_cast raw_prefix_sum hp stem exit hne ha v
  calc
    _ = (∑ y : Fin E → Fin p,
        if prefixMatch ha v y then (raw stem exit E y : ℚ) else 0) / (p : ℚ)^E := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : prefixMatch ha v y <;> simp [density, h]
    _ = (raw stem exit a v : ℚ) * (p : ℚ)^(E-a) / (p : ℚ)^E := by rw [he]
    _ = _ := by
      have hpow : (p : ℚ)^E = (p : ℚ)^(E-a) * (p : ℚ)^a := by
        rw [← pow_add, Nat.sub_add_cancel ha]
      rw [hpow]
      have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      field_simp

/-- A future prefix has one common classification for all conditioned
measures: a stem prefix has mass p^-a; an exit-d prefix has mass
(p-1)*p^-a in measure d and zero in every other conditioned measure. -/
theorem classified_cylinder {p : ℕ} (hp : 1 ≤ p) (stem exit : Fin p) (hne : exit ≠ stem)
    {a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p) :
    (∑ y : Fin E → Fin p, if prefixMatch ha v y then density stem exit y else 0) =
      match firstExit stem a v with
      | none => 1 / (p : ℚ)^a
      | some d => if d = exit then ((p-1 : ℕ) : ℚ) / (p : ℚ)^a else 0 := by
  rw [density_prefix_sum hp stem exit hne ha v, raw_classified]
  cases firstExit stem a v with
  | none => rfl
  | some d => by_cases h : d = exit <;> simp [h]

#print axioms raw_prefix_sum
#print axioms density_mass
#print axioms classified_cylinder
end Erdos7ConditionalExitMeasure
