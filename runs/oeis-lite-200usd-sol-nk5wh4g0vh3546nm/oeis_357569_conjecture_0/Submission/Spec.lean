import FormalConjectures.Util.ProblemImports
open Nat

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

open scoped BigOperators

namespace Work

/-- The positive integers at most `q` which are not divisible by `p`. -/
def punits (p q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter (fun k => ¬ p ∣ k)

def pmults (p q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter (fun k => p ∣ k)

lemma mem_punits {p q k : ℕ} : k ∈ punits p q ↔ 1 ≤ k ∧ k ≤ q ∧ ¬ p ∣ k := by
  simp [punits, and_assoc]

lemma mem_pmults {p q k : ℕ} : k ∈ pmults p q ↔ 1 ≤ k ∧ k ≤ q ∧ p ∣ k := by
  simp [pmults, and_assoc]

lemma cast_punit_isUnit {p q k M : ℕ} (hp : p.Prime) (hM : ∃ e, M = p ^ e)
    (hk : k ∈ punits p q) : IsUnit (k : ZMod M) := by
  rw [ZMod.isUnit_iff_coprime]
  obtain ⟨e, rfl⟩ := hM
  exact hp.coprime_pow_of_not_dvd (mem_punits.mp hk).2.2

lemma punit_lt {p q k : ℕ} (hpq : p ∣ q) (hk : k ∈ punits p q) : k < q := by
  have h := mem_punits.mp hk
  exact lt_of_le_of_ne h.2.1 (fun heq => h.2.2 (heq ▸ hpq))


lemma prod_pmults {R : Type*} [CommMonoid R] {p m : ℕ} (hp : 0 < p) (f : ℕ → R) :
    ∏ k ∈ pmults p (p * m), f k = ∏ j ∈ Finset.Icc 1 m, f (p * j) := by
  classical
  symm

  apply Finset.prod_bij (fun j _ => p * j)
  · intro j hj
    rw [mem_pmults]
    simp only [Finset.mem_Icc] at hj
    constructor
    · exact Nat.mul_pos hp hj.1
    constructor
    · exact Nat.mul_le_mul_left p hj.2
    · exact dvd_mul_right p j
  · intro a₁ ha₁ a₂ ha₂ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro b hb
    have hb' := mem_pmults.mp hb
    refine ⟨b / p, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      have heq : p * (b / p) = b := Nat.mul_div_cancel' hb'.2.2
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr (fun h => by rw [h, mul_zero] at heq; omega)
      · exact Nat.le_of_mul_le_mul_left (by rw [heq]; exact hb'.2.1) hp
    · exact Nat.mul_div_cancel' hb'.2.2
  · intros
    rfl

lemma prod_Icc_split {R : Type*} [CommMonoid R] (p q : ℕ) (f : ℕ → R) :
    (∏ k ∈ Finset.Icc 1 q, f k) =
      (∏ k ∈ pmults p q, f k) * (∏ k ∈ punits p q, f k) := by
  classical
  simpa [pmults, punits] using
    (Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 q) (fun k => p ∣ k) f).symm

lemma prod_Icc_eq_prod_range {R : Type*} [CommMonoid R] (q : ℕ) (f : ℕ → R) :
    ∏ k ∈ Finset.Icc 1 q, f k = ∏ i ∈ Finset.range q, f (i + 1) := by
  classical
  symm
  apply Finset.prod_bij (fun i _ => i + 1)
  · simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  · omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intros
    rfl

lemma prod_Icc_id (q : ℕ) : ∏ k ∈ Finset.Icc 1 q, k = q ! := by
  rw [prod_Icc_eq_prod_range, Finset.prod_range_add_one_eq_factorial]

lemma choose_mul_prod (c q : ℕ) :
    ((c + 1) * q).choose q * (∏ k ∈ Finset.Icc 1 q, k) =
      ∏ k ∈ Finset.Icc 1 q, (c * q + k) := by
  rw [prod_Icc_id, prod_Icc_eq_prod_range]
  have hprod : (∏ i ∈ Finset.range q, (c * q + (i + 1))) =
      ∏ i ∈ Finset.range q, ((c * q + 1) + i) := by
    apply Finset.prod_congr rfl
    intro i hi
    omega
  rw [hprod, ← Nat.ascFactorial_eq_prod_range]
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  rw [mul_comm]
  congr 2
  simp [Nat.add_mul]

def uden (p q : ℕ) : ℕ := ∏ k ∈ punits p q, k

def unum (c p q : ℕ) : ℕ := ∏ k ∈ punits p q, (c * q + k)

lemma binom_cross (c p m : ℕ) (hp : 0 < p) :
    ((c + 1) * (p * m)).choose (p * m) * uden p (p * m) =
      ((c + 1) * m).choose m * unum c p (p * m) := by
  let D : ℕ := ∏ j ∈ Finset.Icc 1 m, p
  let E : ℕ := ∏ j ∈ Finset.Icc 1 m, j
  let N : ℕ := ∏ j ∈ Finset.Icc 1 m, (c * m + j)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hdenmult : (∏ k ∈ pmults p (p * m), k) = D * E := by
    rw [prod_pmults hp]
    rw [← Finset.prod_mul_distrib]
  have hnummult : (∏ k ∈ pmults p (p * m), (c * (p * m) + k)) = D * N := by
    rw [prod_pmults hp]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    dsimp [D, N]
    ring
  have hsmall : ((c + 1) * m).choose m * E = N := by
    simpa [E, N] using choose_mul_prod c m
  have hbig := choose_mul_prod c (p * m)
  rw [prod_Icc_split p (p * m) (fun k => k)] at hbig
  rw [prod_Icc_split p (p * m) (fun k => c * (p * m) + k)] at hbig
  change ((c + 1) * (p * m)).choose (p * m) *
      ((∏ k ∈ pmults p (p * m), k) * uden p (p * m)) =
    (∏ k ∈ pmults p (p * m), (c * (p * m) + k)) * unum c p (p * m) at hbig
  rw [hdenmult, hnummult, ← hsmall] at hbig
  have hE : 0 < E := by
    dsimp [E]
    rw [prod_Icc_id]
    exact factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left (mul_pos hD hE)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hbig

def bratio (c p q M : ℕ) : ZMod M :=
  ∏ k ∈ punits p q, ((c * q + k : ℕ) : ZMod M) * (k : ZMod M)⁻¹

lemma cast_uden_isUnit {p q M : ℕ} (hp : p.Prime) (hM : ∃ e, M = p ^ e) :
    IsUnit (uden p q : ZMod M) := by
  rw [show (uden p q : ZMod M) = ∏ k ∈ punits p q, (k : ZMod M) by
    simp [uden]]
  exact IsUnit.prod_iff.mpr (fun k hk => cast_punit_isUnit hp hM hk)

lemma bratio_eq (c p q M : ℕ) (hp : p.Prime) (hM : ∃ e, M = p ^ e) :
    bratio c p q M = (unum c p q : ZMod M) * (uden p q : ZMod M)⁻¹ := by
  classical
  have h : bratio c p q M * (uden p q : ZMod M) = (unum c p q : ZMod M) := by
    simp only [bratio, unum, uden, Nat.cast_prod, Nat.cast_add, Nat.cast_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    rw [mul_assoc, ZMod.inv_mul_of_unit _ (cast_punit_isUnit hp hM hk), mul_one]
  calc
    bratio c p q M = (bratio c p q M * (uden p q : ZMod M)) *
        (uden p q : ZMod M)⁻¹ := by
      rw [mul_assoc, ZMod.mul_inv_of_unit _ (cast_uden_isUnit hp hM), mul_one]
    _ = (unum c p q : ZMod M) * (uden p q : ZMod M)⁻¹ := by rw [h]

lemma binom_ratio (c p m M : ℕ) (hp : p.Prime) (hM : ∃ e, M = p ^ e) :
    ((((c + 1) * (p * m)).choose (p * m) : ℕ) : ZMod M) =
      (((((c + 1) * m).choose m : ℕ) : ZMod M) * bratio c p (p * m) M) := by
  have h := congrArg (fun n : ℕ => (n : ZMod M)) (binom_cross c p m hp.pos)
  simp only [Nat.cast_mul] at h
  rw [bratio_eq c p (p * m) M hp hM]
  let D : ZMod M := (uden p (p * m) : ZMod M)
  let A : ZMod M := ((((c + 1) * (p * m)).choose (p * m) : ℕ) : ZMod M)
  let B : ZMod M := ((((c + 1) * m).choose m : ℕ) : ZMod M)
  let N : ZMod M := (unum c p (p * m) : ZMod M)
  change A * D = B * N at h
  change A = B * (N * D⁻¹)
  calc
    A = (A * D) * D⁻¹ := by
      rw [mul_assoc, ZMod.mul_inv_of_unit D (cast_uden_isUnit hp hM), mul_one]
    _ = (B * N) * D⁻¹ := by rw [h]
    _ = B * (N * D⁻¹) := by ring

def lowUnits (p q : ℕ) : Finset ℕ :=
  (punits p q).filter (fun k => k ≤ q / 2)

def highUnits (p q : ℕ) : Finset ℕ :=
  (punits p q).filter (fun k => q / 2 < k)

lemma mem_lowUnits {p q k : ℕ} :
    k ∈ lowUnits p q ↔ 1 ≤ k ∧ k ≤ q ∧ ¬p ∣ k ∧ k ≤ q / 2 := by
  simp only [lowUnits, Finset.mem_filter, mem_punits]
  aesop

lemma mem_highUnits {p q k : ℕ} :
    k ∈ highUnits p q ↔ 1 ≤ k ∧ k ≤ q ∧ ¬p ∣ k ∧ q / 2 < k := by
  simp only [highUnits, Finset.mem_filter, mem_punits]
  aesop

lemma prod_punits_low_high {R : Type*} [CommMonoid R] (p q : ℕ) (f : ℕ → R) :
    ∏ k ∈ punits p q, f k =
      (∏ k ∈ lowUnits p q, f k) * (∏ k ∈ highUnits p q, f k) := by
  classical
  simpa [lowUnits, highUnits] using
    (Finset.prod_filter_mul_prod_filter_not (punits p q) (fun k => k ≤ q / 2) f).symm

lemma odd_div_identity {q : ℕ} (hq : q % 2 = 1) : q = 2 * (q / 2) + 1 := by
  have := (Nat.mod_add_div q 2).symm
  omega

lemma prod_high_reflect {R : Type*} [CommMonoid R] {p q : ℕ}
    (hqodd : q % 2 = 1) (hpq : p ∣ q) (f : ℕ → R) :
    ∏ k ∈ highUnits p q, f k = ∏ k ∈ lowUnits p q, f (q - k) := by
  classical
  symm
  apply Finset.prod_bij (fun k _ => q - k)
  · intro k hk
    rw [mem_highUnits]
    rw [mem_lowUnits] at hk
    have hqid := odd_div_identity hqodd
    refine ⟨by omega, by omega, ?_, by omega⟩
    intro hd
    apply hk.2.2.1
    have hh := Nat.dvd_sub hpq hd
    simpa [Nat.sub_sub_self hk.2.1] using hh
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [mem_lowUnits] at ha₁ ha₂
    omega
  · intro b hb
    rw [mem_highUnits] at hb
    have hbq : b < q := lt_of_le_of_ne hb.2.1 (fun heq => hb.2.2.1 (heq ▸ hpq))
    refine ⟨q - b, ?_, ?_⟩
    · rw [mem_lowUnits]
      have hqid := odd_div_identity hqodd
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro hd
      apply hb.2.2.1
      have hh := Nat.dvd_sub hpq hd
      simpa [Nat.sub_sub_self hb.2.1] using hh
    · exact Nat.sub_sub_self hb.2.1
  · intros
    rfl

lemma bratio_pair (c p q M : ℕ) (hqodd : q % 2 = 1) (hpq : p ∣ q) :
    bratio c p q M = ∏ k ∈ lowUnits p q,
      ((((c * q + k : ℕ) : ZMod M) * (k : ZMod M)⁻¹) *
       (((c * q + (q - k) : ℕ) : ZMod M) * (q - k : ZMod M)⁻¹)) := by
  rw [bratio, prod_punits_low_high]
  rw [prod_high_reflect hqodd hpq]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.cast_sub (mem_lowUnits.mp hk).2.1]

def pairTerm (p q M k : ℕ) : ZMod M :=
  ((k : ZMod M) * (q - k : ZMod M))⁻¹

lemma pair_factor (c p q M k : ℕ) (hp : p.Prime) (hM : ∃ e, M = p ^ e)
    (hk : k ∈ lowUnits p q) (hpq : p ∣ q) (hqodd : q % 2 = 1) :
    ((((c * q + k : ℕ) : ZMod M) * (k : ZMod M)⁻¹) *
       (((c * q + (q - k) : ℕ) : ZMod M) * (q - k : ZMod M)⁻¹)) =
      1 + (c * (c + 1) * q ^ 2 : ℕ) * pairTerm p q M k := by
  have hku : IsUnit (k : ZMod M) :=
    cast_punit_isUnit hp hM (Finset.filter_subset _ _ hk)
  have hqkmem : q - k ∈ punits p q := by
    rw [mem_punits]
    have hkl := mem_lowUnits.mp hk
    have hqid := odd_div_identity hqodd
    refine ⟨by omega, by omega, ?_⟩
    intro hd
    apply hkl.2.2.1
    have hh := Nat.dvd_sub hpq hd
    simpa [Nat.sub_sub_self hkl.2.1] using hh
  have hqkuNat : IsUnit (((q - k : ℕ) : ZMod M)) := cast_punit_isUnit hp hM hqkmem
  have hcast : ((q - k : ℕ) : ZMod M) = (q : ZMod M) - k := by
    rw [Nat.cast_sub (mem_lowUnits.mp hk).2.1]
  have hqku : IsUnit ((q : ZMod M) - k) := hcast ▸ hqkuNat
  have hr1 : (((c * q + k : ℕ) : ZMod M) * (k : ZMod M)⁻¹) =
      1 + (c : ZMod M) * q * (k : ZMod M)⁻¹ := by
    push_cast
    rw [add_mul, ZMod.mul_inv_of_unit _ hku, add_comm]
  have hr2 : (((c * q + (q - k) : ℕ) : ZMod M) * ((q : ZMod M) - k)⁻¹) =
      1 + (c : ZMod M) * q * ((q : ZMod M) - k)⁻¹ := by
    push_cast
    rw [hcast, add_mul, ZMod.mul_inv_of_unit _ hqku, add_comm]
  rw [hr1, hr2]
  have hsum : (k : ZMod M) + ((q : ZMod M) - k) = q := by ring
  have hinvsum : (k : ZMod M)⁻¹ + ((q : ZMod M) - k)⁻¹ =
      (q : ZMod M) * ((k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹) := by
    calc
      (k : ZMod M)⁻¹ + ((q : ZMod M) - k)⁻¹ =
          ((k : ZMod M) * (k : ZMod M)⁻¹) * ((q : ZMod M) - k)⁻¹ +
          (((q : ZMod M) - k) * ((q : ZMod M) - k)⁻¹) * (k : ZMod M)⁻¹ := by
            rw [ZMod.mul_inv_of_unit _ hku, ZMod.mul_inv_of_unit _ hqku]
            ring
      _ = ((k : ZMod M) + ((q : ZMod M) - k)) *
          ((k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹) := by ring
      _ = (q : ZMod M) * ((k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹) := by rw [hsum]
  rw [show pairTerm p q M k = (k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹ by
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      (k : ZMod M) * ((q : ZMod M) - k) *
          ((k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹) =
        ((k : ZMod M) * (k : ZMod M)⁻¹) *
          (((q : ZMod M) - k) * ((q : ZMod M) - k)⁻¹) := by ring
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ hku, ZMod.mul_inv_of_unit _ hqku, one_mul]]
  push_cast
  calc
    (1 + (c : ZMod M) * q * (k : ZMod M)⁻¹) *
        (1 + (c : ZMod M) * q * ((q : ZMod M) - k)⁻¹) =
      1 + (c : ZMod M) * q * ((k : ZMod M)⁻¹ + ((q : ZMod M) - k)⁻¹) +
        (c : ZMod M)^2 * q^2 * ((k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹) := by ring
    _ = 1 + (c : ZMod M) * ((c : ZMod M) + 1) * q ^ 2 *
        ((k : ZMod M)⁻¹ * ((q : ZMod M) - k)⁻¹) := by rw [hinvsum]; ring

def esum2 {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) : R :=
  ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i

lemma esum2_empty {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (f : ι → R) : esum2 ∅ f = 0 := by
  rw [esum2, Finset.powersetCard_eq_empty.mpr (by simp)]
  simp

lemma esum2_insert {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    {a : ι} {s : Finset ι} (ha : a ∉ s) (f : ι → R) :
    esum2 (insert a s) f = esum2 s f + f a * ∑ i ∈ s, f i := by
  classical
  rw [esum2, Finset.powersetCard_succ_insert ha 1]
  rw [Finset.sum_union]
  · congr 1
    rw [Finset.sum_image]
    · rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := fun h => ha (h ▸ hi)
      simp [hai]
    · intro x hx y hy hxy
      have hax : a ∉ x := fun h => ha ((Finset.mem_powersetCard.mp hx).1 h)
      have hay : a ∉ y := fun h => ha ((Finset.mem_powersetCard.mp hy).1 h)
      simpa [hax, hay] using congrArg (fun t : Finset ι => t.erase a) hxy
  · rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    rw [Finset.mem_image] at ht₂
    obtain ⟨u, hu, rfl⟩ := ht₂
    exact ha ((Finset.mem_powersetCard.mp ht₁).1 (Finset.mem_insert_self _ _))

lemma prod_linear_quadratic {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : R) (f : ι → R) (hA : A ^ 3 = 0) :
    ∏ i ∈ s, (1 + A * f i) =
      1 + A * (∑ i ∈ s, f i) + A ^ 2 * esum2 s f := by
  classical
  induction s using Finset.induction with
  | empty => rw [esum2_empty]; simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, esum2_insert ha]
      ring_nf
      rw [hA]
      ring

lemma sum_punits_low_high {R : Type*} [AddCommMonoid R] (p q : ℕ) (f : ℕ → R) :
    ∑ k ∈ punits p q, f k =
      (∑ k ∈ lowUnits p q, f k) + (∑ k ∈ highUnits p q, f k) := by
  classical
  simpa [lowUnits, highUnits] using
    (Finset.sum_filter_add_sum_filter_not (punits p q) (fun k => k ≤ q / 2) f).symm

lemma sum_high_reflect {R : Type*} [AddCommMonoid R] {p q : ℕ}
    (hqodd : q % 2 = 1) (hpq : p ∣ q) (f : ℕ → R) :
    ∑ k ∈ highUnits p q, f k = ∑ k ∈ lowUnits p q, f (q - k) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => q - k)
  · intro k hk
    rw [mem_highUnits]
    rw [mem_lowUnits] at hk
    have hqid := odd_div_identity hqodd
    refine ⟨by omega, by omega, ?_, by omega⟩
    intro hd
    apply hk.2.2.1
    have hh := Nat.dvd_sub hpq hd
    simpa [Nat.sub_sub_self hk.2.1] using hh
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [mem_lowUnits] at ha₁ ha₂
    omega
  · intro b hb
    rw [mem_highUnits] at hb
    have hbq : b < q := lt_of_le_of_ne hb.2.1 (fun heq => hb.2.2.1 (heq ▸ hpq))
    refine ⟨q - b, ?_, ?_⟩
    · rw [mem_lowUnits]
      have hqid := odd_div_identity hqodd
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro hd
      apply hb.2.2.1
      have hh := Nat.dvd_sub hpq hd
      simpa [Nat.sub_sub_self hb.2.1] using hh
    · exact Nat.sub_sub_self hb.2.1
  · intros
    rfl

def ssq (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + 1) ^ 2

lemma sum_Icc_eq_sum_range {R : Type*} [AddCommMonoid R] (q : ℕ) (f : ℕ → R) :
    ∑ k ∈ Finset.Icc 1 q, f k = ∑ i ∈ Finset.range q, f (i + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  · omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intros
    rfl

lemma six_mul_ssq (n : ℕ) : 6 * ssq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp [ssq]
  | succ n ih =>
      rw [ssq, Finset.sum_range_succ]
      change 6 * (ssq n + (n + 1) ^ 2) = _
      rw [Nat.mul_add, ih]
      ring

lemma ssq_dvd_of_coprime_six {n : ℕ} (hcop : n.Coprime 6) : n ∣ ssq n := by
  apply hcop.dvd_of_dvd_mul_right
  rw [mul_comm, six_mul_ssq]
  exact ⟨(n + 1) * (2 * n + 1), by ring⟩

lemma div_three_dvd_ssq {n : ℕ} (hn3 : 3 ∣ n) (hnodd : n % 2 = 1) : n / 3 ∣ ssq n := by
  obtain ⟨d, rfl⟩ := hn3
  have heq := six_mul_ssq (3 * d)
  have htwo : 2 * ssq (3 * d) = d * ((3 * d + 1) * (2 * (3 * d) + 1)) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3)
    nlinarith
  have hd : d ∣ 2 * ssq (3 * d) := ⟨_, htwo⟩
  have hdcop : d.Coprime 2 := by
    rw [Nat.coprime_two_right]
    exact (Nat.odd_mul.mp (Nat.odd_iff.mpr hnodd)).2
  have hres := hdcop.dvd_of_dvd_mul_left hd
  convert hres using 1 <;> omega

lemma sum_pmults {R : Type*} [AddCommMonoid R] {p m : ℕ} (hp : 0 < p) (f : ℕ → R) :
    ∑ k ∈ pmults p (p * m), f k = ∑ j ∈ Finset.Icc 1 m, f (p * j) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => p * j)
  · intro j hj
    rw [mem_pmults]
    simp only [Finset.mem_Icc] at hj
    exact ⟨Nat.mul_pos hp hj.1, Nat.mul_le_mul_left p hj.2, dvd_mul_right p j⟩
  · intro a₁ ha₁ a₂ ha₂ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro b hb
    have hb' := mem_pmults.mp hb
    refine ⟨b / p, ?_, Nat.mul_div_cancel' hb'.2.2⟩
    simp only [Finset.mem_Icc]
    have heq : p * (b / p) = b := Nat.mul_div_cancel' hb'.2.2
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (fun h => by rw [h, mul_zero] at heq; omega)
    · exact Nat.le_of_mul_le_mul_left (by rw [heq]; exact hb'.2.1) hp
  · intros
    rfl

def unitSq (p q : ℕ) : ℕ := ∑ k ∈ punits p q, k ^ 2

lemma ssq_eq_p_sq_mul_ssq_add_unitSq (p m : ℕ) (hp : 0 < p) :
    ssq (p * m) = p ^ 2 * ssq m + unitSq p (p * m) := by
  rw [ssq, ← sum_Icc_eq_sum_range (p * m) (fun k : ℕ => k ^ 2)]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (p * m)) (fun k => p ∣ k) (fun k => k ^ 2)
  change (∑ k ∈ pmults p (p * m), k ^ 2) + unitSq p (p * m) = _ at hsplit
  rw [sum_pmults hp] at hsplit
  rw [sum_Icc_eq_sum_range] at hsplit
  change (∑ i ∈ Finset.range m, (p * (i + 1)) ^ 2) + unitSq p (p * m) = _ at hsplit
  rw [show (∑ i ∈ Finset.range m, (p * (i + 1)) ^ 2) = p ^ 2 * ssq m by
    rw [ssq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring] at hsplit
  exact hsplit.symm

lemma unitSq_dvd_of_coprime_six (p m : ℕ) (hp : 0 < p)
    (hm : m.Coprime 6) (hpm : (p * m).Coprime 6) :
    p * m ∣ unitSq p (p * m) := by
  have hbig : p * m ∣ ssq (p * m) := ssq_dvd_of_coprime_six hpm
  have hsmall : m ∣ ssq m := ssq_dvd_of_coprime_six hm
  obtain ⟨z, hz⟩ := hsmall
  have hfirst : p * m ∣ p ^ 2 * ssq m := by
    refine ⟨p * z, ?_⟩
    rw [hz]
    ring
  rw [ssq_eq_p_sq_mul_ssq_add_unitSq p m hp] at hbig
  exact (Nat.dvd_add_iff_right hfirst).mpr hbig

lemma unitSq_dvd_three (s : ℕ) :
    3 ^ s ∣ unitSq 3 (3 * 3 ^ s) := by
  let m := 3 ^ s
  have hmodd : (3 * m) % 2 = 1 := by
    dsimp [m]
    exact Nat.odd_iff.mp (Odd.mul (by decide : Odd (3 : ℕ)) ((by decide : Odd (3 : ℕ)).pow))
  have hbig : m ∣ ssq (3 * m) := by
    have h := div_three_dvd_ssq (n := 3 * m) (dvd_mul_right 3 m) hmodd
    convert h using 1 <;> omega
  have hfirst : m ∣ 3 ^ 2 * ssq m := by
    cases s with
    | zero => simp [m]
    | succ t =>
        have hm3 : 3 ∣ m := by simp [m, pow_succ]
        have hmoddm : m % 2 = 1 := by
          dsimp [m]
          exact Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow)
        obtain ⟨z, hz⟩ := div_three_dvd_ssq hm3 hmoddm
        refine ⟨3 * z, ?_⟩
        rw [hz]
        have hmpos : 0 < m := by positivity
        have heq : 3 * (m / 3) = m := Nat.mul_div_cancel' hm3
        nlinarith
  rw [ssq_eq_p_sq_mul_ssq_add_unitSq 3 m (by decide)] at hbig
  exact (Nat.dvd_add_iff_right hfirst).mpr hbig

lemma prime_pow_coprime_six {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p ^ r).Coprime 6 := by
  rw [Nat.coprime_comm]
  exact hp.coprime_pow_of_not_dvd (by
    intro hd
    have hd' : p ∣ 2 * 3 := by norm_num at hd ⊢; exact hd
    rcases hp.dvd_mul.mp hd' with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega)

lemma inv_inv_of_isUnit {M : ℕ} {x : ZMod M} (hx : IsUnit x) : x⁻¹⁻¹ = x := by
  apply ZMod.inv_eq_of_mul_eq_one
  exact ZMod.inv_mul_of_unit x hx

lemma isUnit_inv_zmod {M : ℕ} {x : ZMod M} (hx : IsUnit x) : IsUnit x⁻¹ := by
  rcases hx with ⟨u, rfl⟩
  rw [ZMod.inv_coe_unit]
  exact Units.isUnit _


lemma invVal_mem_punits {p q k : ℕ} (hp : p.Prime) (hqpos : 0 < q)
    (hpq : p ∣ q) (hqpow : ∃ r, q = p ^ r) (hk : k ∈ punits p q) :
    ((k : ZMod q)⁻¹).val ∈ punits p q := by
  let x : ZMod q := (k : ZMod q)⁻¹
  haveI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hku : IsUnit (k : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    obtain ⟨r, rfl⟩ := hqpow
    exact hp.coprime_pow_of_not_dvd (mem_punits.mp hk).2.2
  have hxu : IsUnit x := by
    change IsUnit ((k : ZMod q)⁻¹)
    exact isUnit_inv_zmod hku
  have hq1 : 1 < q := hp.one_lt.trans_le (Nat.le_of_dvd hqpos hpq)
  letI : Fact (1 < q) := ⟨hq1⟩

  have hxne : x.val ≠ 0 := by
    intro h
    have hx0 : x = 0 := by
      rw [← ZMod.natCast_zmod_val x, h]
      simp
    rw [hx0] at hxu
    exact not_isUnit_zero hxu
  rw [mem_punits]
  refine ⟨Nat.one_le_iff_ne_zero.mpr hxne, (ZMod.val_lt x).le, ?_⟩
  have hxuCast : IsUnit (x.val : ZMod q) := by
    rw [ZMod.natCast_zmod_val]
    exact hxu
  rw [ZMod.isUnit_iff_coprime] at hxuCast
  have hcop : x.val.Coprime p := Nat.Coprime.of_dvd_right hpq hxuCast
  exact hp.coprime_iff_not_dvd.mp hcop.symm

lemma sum_inv_sq_eq_unitSq {p q : ℕ} (hp : p.Prime) (hqpos : 0 < q) (hpq : p ∣ q)
    (hqpow : ∃ r, q = p ^ r) :
    (∑ k ∈ punits p q, ((k : ZMod q)⁻¹) ^ 2) = (unitSq p q : ZMod q) := by
  classical
  haveI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  rw [unitSq, Nat.cast_sum]
  simp only [Nat.cast_pow]
  symm
  apply Finset.sum_bij (s := punits p q) (t := punits p q)
    (f := fun k => (k : ZMod q) ^ 2) (g := fun k => ((k : ZMod q)⁻¹) ^ 2)
    (fun k _ => ((k : ZMod q)⁻¹).val)
  · exact fun k hk => invVal_mem_punits hp hqpos hpq hqpow hk
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 : IsUnit (a₁ : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      obtain ⟨r, rfl⟩ := hqpow
      exact hp.coprime_pow_of_not_dvd (mem_punits.mp ha₁).2.2
    have h2 : IsUnit (a₂ : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      obtain ⟨r, rfl⟩ := hqpow
      exact hp.coprime_pow_of_not_dvd (mem_punits.mp ha₂).2.2
    have hz : (a₁ : ZMod q)⁻¹ = (a₂ : ZMod q)⁻¹ := by
      rw [← ZMod.natCast_zmod_val ((a₁ : ZMod q)⁻¹),
        ← ZMod.natCast_zmod_val ((a₂ : ZMod q)⁻¹), heq]
    have hc : (a₁ : ZMod q) = (a₂ : ZMod q) := by
      have hz' := congrArg Inv.inv hz
      simpa [inv_inv_of_isUnit h1, inv_inv_of_isUnit h2] using hz'
    have hv := congrArg ZMod.val hc
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (punit_lt hpq ha₁),
      Nat.mod_eq_of_lt (punit_lt hpq ha₂)] using hv
  · intro b hb
    have hbu : IsUnit (b : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      obtain ⟨r, rfl⟩ := hqpow
      exact hp.coprime_pow_of_not_dvd (mem_punits.mp hb).2.2
    let a := (((b : ZMod q)⁻¹).val)
    have ha : a ∈ punits p q := invVal_mem_punits hp hqpos hpq hqpow hb
    refine ⟨a, ha, ?_⟩
    dsimp [a]
    rw [ZMod.natCast_zmod_val, inv_inv_of_isUnit hbu]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (punit_lt hpq hb)]
  · intro k hk
    rw [ZMod.natCast_zmod_val]
    have hku : IsUnit (k : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      obtain ⟨r, rfl⟩ := hqpow
      exact hp.coprime_pow_of_not_dvd (mem_punits.mp hk).2.2
    rw [inv_inv_of_isUnit hku]

def tsum (p q M : ℕ) : ZMod M := ∑ k ∈ lowUnits p q, pairTerm p q M k

lemma pairTerm_mod_self {p q k : ℕ} (hp : p.Prime) (hqpos : 0 < q)
    (hpq : p ∣ q) (hqpow : ∃ r, q = p ^ r) (hk : k ∈ punits p q) :
    pairTerm p q q k = -((k : ZMod q)⁻¹) ^ 2 := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hku : IsUnit (k : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    obtain ⟨r, rfl⟩ := hqpow
    exact hp.coprime_pow_of_not_dvd (mem_punits.mp hk).2.2
  rw [pairTerm]
  apply ZMod.inv_eq_of_mul_eq_one
  rw [ZMod.natCast_self, zero_sub]
  rw [show (k : ZMod q) * -k * (-((k : ZMod q)⁻¹) ^ 2) =
      (k * (k : ZMod q)⁻¹) ^ 2 by ring]
  rw [ZMod.mul_inv_of_unit _ hku, one_pow]

lemma pairTerm_reflect {p q M k : ℕ} (hkq : k ≤ q) :
    pairTerm p q M (q - k) = pairTerm p q M k := by
  rw [pairTerm, pairTerm]
  rw [Nat.cast_sub hkq]
  apply congrArg Inv.inv
  ring

lemma two_tsum_eq_neg_unitSq {p q : ℕ} (hp : p.Prime) (hqpos : 0 < q)
    (hpq : p ∣ q) (hqpow : ∃ r, q = p ^ r) (hqodd : q % 2 = 1) :
    (2 : ZMod q) * tsum p q q = -(unitSq p q : ZMod q) := by
  have hsplit := sum_punits_low_high p q (fun k => pairTerm p q q k)
  rw [sum_high_reflect hqodd hpq] at hsplit
  have hreflect : (∑ k ∈ lowUnits p q, pairTerm p q q (q - k)) = tsum p q q := by
    rw [tsum]
    apply Finset.sum_congr rfl
    intro k hk
    exact pairTerm_reflect (mem_lowUnits.mp hk).2.1
  rw [hreflect] at hsplit
  change (∑ k ∈ punits p q, pairTerm p q q k) = tsum p q q + tsum p q q at hsplit
  have hfull : (∑ k ∈ punits p q, pairTerm p q q k) = (2 : ZMod q) * tsum p q q := by
    rw [hsplit]
    ring
  rw [← hfull]
  rw [Finset.sum_congr rfl (fun k hk => pairTerm_mod_self hp hqpos hpq hqpow hk)]
  rw [Finset.sum_neg_distrib, sum_inv_sq_eq_unitSq hp hqpos hpq hqpow]

lemma sum_range_mul_periodic {R : Type*} [AddCommMonoid R] (p m : ℕ) (f : ℕ → R)
    (hper : ∀ n i, f (p * n + i) = f i) :
    ∑ i ∈ Finset.range (p * m), f i = m • ∑ i ∈ Finset.range p, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, add_nsmul]
      simp only [one_nsmul]
      congr 1

      apply Finset.sum_congr rfl
      intro i hi
      exact hper m i

lemma sum_punits_inv_pow_zero {p r d : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hd : 0 < d) :
    (∑ k ∈ punits p (p ^ r), ((k : ZMod p)⁻¹) ^ d) = 0 := by
  have hpow : p ^ r = p * p ^ (r - 1) := by
    calc
      p ^ r = p ^ (r - 1 + 1) := by congr 1; omega
      _ = p * p ^ (r - 1) := by rw [pow_succ']
  have hmult : (∑ k ∈ pmults p (p ^ r), ((k : ZMod p)⁻¹) ^ d) = 0 := by
    rw [hpow, sum_pmults hp.pos]
    apply Finset.sum_eq_zero
    intro j hj
    push_cast
    rw [ZMod.natCast_self, zero_mul, ZMod.inv_zero]
    exact zero_pow hd.ne'
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (p ^ r)) (fun k => p ∣ k) (fun k => ((k : ZMod p)⁻¹) ^ d)
  change (∑ k ∈ pmults p (p ^ r), ((k : ZMod p)⁻¹) ^ d) +
      (∑ k ∈ punits p (p ^ r), ((k : ZMod p)⁻¹) ^ d) = _ at hsplit
  rw [hmult, zero_add] at hsplit
  rw [hsplit, sum_Icc_eq_sum_range]
  rw [hpow, sum_range_mul_periodic p (p ^ (r - 1))]
  · rw [nsmul_eq_mul]
    have hpr : p ∣ p ^ (r - 1) := by
      apply dvd_pow_self
      omega
    rw [show ((p ^ (r - 1) : ℕ) : ZMod p) = 0 by
      rw [ZMod.natCast_eq_zero_iff]
      exact hpr, zero_mul]
  · intro n i
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]

lemma sum_sq_eq_sum_sq_add_two_esum2 {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ 2 = (∑ i ∈ s, (f i) ^ 2) + 2 * esum2 s f := by
  classical
  induction s using Finset.induction with
  | empty => rw [esum2_empty]; simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, esum2_insert ha]
      calc
        (f a + ∑ x ∈ s, f x) ^ 2 =
            f a ^ 2 + 2 * f a * (∑ x ∈ s, f x) + (∑ x ∈ s, f x) ^ 2 := by ring
        _ = f a ^ 2 + (∑ x ∈ s, f x ^ 2) +
            2 * (esum2 s f + f a * ∑ i ∈ s, f i) := by rw [ih]; ring

lemma pairTerm_mod_prime {p q k : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    (hk : k ∈ punits p q) :
    pairTerm p q p k = -((k : ZMod p)⁻¹) ^ 2 := by
  have hku : IsUnit (k : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd.mpr (mem_punits.mp hk).2.2).symm
  rw [pairTerm]
  apply ZMod.inv_eq_of_mul_eq_one
  rw [show (q : ZMod p) = 0 by rw [ZMod.natCast_eq_zero_iff]; exact hpq, zero_sub]
  rw [show (k : ZMod p) * -k * (-((k : ZMod p)⁻¹) ^ 2) =
      (k * (k : ZMod p)⁻¹) ^ 2 by ring]
  rw [ZMod.mul_inv_of_unit _ hku, one_pow]

lemma two_isUnit_mod_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    IsUnit (2 : ZMod p) := by
  change IsUnit ((2 : ℕ) : ZMod p)
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro h
  have := Nat.le_of_dvd (by decide : 0 < 2) h
  omega

lemma tsum_mod_prime_eq_zero {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    tsum p (p ^ r) p = 0 := by
  let q := p ^ r
  have hqodd : q % 2 = 1 := by
    dsimp [q]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hsplit := sum_punits_low_high p q (fun k => pairTerm p q p k)
  rw [sum_high_reflect hqodd hpq] at hsplit
  have hreflect : (∑ k ∈ lowUnits p q, pairTerm p q p (q - k)) = tsum p q p := by
    rw [tsum]
    apply Finset.sum_congr rfl
    intro k hk
    exact pairTerm_reflect (mem_lowUnits.mp hk).2.1
  rw [hreflect] at hsplit
  change (∑ k ∈ punits p q, pairTerm p q p k) = tsum p q p + tsum p q p at hsplit
  have hfullzero : (∑ k ∈ punits p q, pairTerm p q p k) = 0 := by
    rw [Finset.sum_congr rfl (fun k hk => pairTerm_mod_prime hp hpq hk)]
    rw [Finset.sum_neg_distrib, sum_punits_inv_pow_zero hp hr (by decide : 0 < 2), neg_zero]
  rw [hfullzero] at hsplit
  have htwo := two_isUnit_mod_prime hp hp3
  apply htwo.mul_left_cancel
  change (2 : ZMod p) * tsum p q p = 2 * 0
  rw [show (2 : ZMod p) * tsum p q p = tsum p q p + tsum p q p by ring,
    ← hsplit, mul_zero]

lemma sum_pairTerm_sq_mod_prime_eq_zero {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 2 ≤ r) :
    (∑ k ∈ lowUnits p (p ^ r), (pairTerm p (p ^ r) p k) ^ 2) = 0 := by
  let q := p ^ r
  have hqodd : q % 2 = 1 := by
    dsimp [q]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hsplit := sum_punits_low_high p q (fun k => (pairTerm p q p k) ^ 2)
  rw [sum_high_reflect hqodd hpq] at hsplit
  have hreflect : (∑ k ∈ lowUnits p q, (pairTerm p q p (q - k)) ^ 2) =
      ∑ k ∈ lowUnits p q, (pairTerm p q p k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [pairTerm_reflect (mem_lowUnits.mp hk).2.1]
  rw [hreflect] at hsplit
  let S : ZMod p := ∑ k ∈ lowUnits p q, (pairTerm p q p k) ^ 2
  change (∑ k ∈ punits p q, (pairTerm p q p k) ^ 2) = S + S at hsplit
  have hfullzero : (∑ k ∈ punits p q, (pairTerm p q p k) ^ 2) = 0 := by
    rw [Finset.sum_congr rfl (fun k hk => congrArg (fun x : ZMod p => x ^ 2)
      (pairTerm_mod_prime hp hpq hk))]
    simp only [neg_sq]
    have hz := sum_punits_inv_pow_zero hp hr (by decide : 0 < 4)
    rw [← hz]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have htwo := two_isUnit_mod_prime hp hp3
  apply htwo.mul_left_cancel
  change (2 : ZMod p) * S = 2 * 0
  rw [show (2 : ZMod p) * S = S + S by ring, ← hsplit, hfullzero, mul_zero]

lemma esum2_pairTerm_mod_prime_eq_zero {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 2 ≤ r) :
    esum2 (lowUnits p (p ^ r)) (pairTerm p (p ^ r) p) = 0 := by
  have hid := sum_sq_eq_sum_sq_add_two_esum2
    (lowUnits p (p ^ r)) (pairTerm p (p ^ r) p)
  rw [show (∑ i ∈ lowUnits p (p ^ r), pairTerm p (p ^ r) p i) = 0 by
      exact tsum_mod_prime_eq_zero hp hp3 hr,
    zero_pow (by decide : (2 : ℕ) ≠ 0),
    sum_pairTerm_sq_mod_prime_eq_zero hp hp3 hr, zero_add] at hid
  have htwo := two_isUnit_mod_prime hp hp3
  apply htwo.mul_left_cancel
  simpa using hid.symm

lemma exists_mul_of_cast_eq_zero {d M : ℕ} (hd : d ∣ M) (hMpos : 0 < M) (x : ZMod M)
    (h : (ZMod.cast x : ZMod d) = 0) :
    ∃ y : ZMod M, x = (d : ZMod M) * y := by
  haveI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩

  have hv : (x.val : ZMod d) = 0 := by
    rw [← ZMod.cast_eq_val x]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at hv
  obtain ⟨z, hz⟩ := hv
  refine ⟨(z : ZMod M), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hz]
  push_cast
  ring

lemma cast_inv_of_isUnit {d M : ℕ} (hd : d ∣ M) {x : ZMod M} (hx : IsUnit x) :
    (ZMod.cast x⁻¹ : ZMod d) = (ZMod.cast x : ZMod d)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  change (ZMod.castHom hd (ZMod d)) x * (ZMod.castHom hd (ZMod d)) x⁻¹ = 1
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

lemma cast_pairTerm {p q d M k : ℕ} (hd : d ∣ M) (hp : p.Prime)
    (hM : ∃ e, M = p ^ e) (hk : k ∈ lowUnits p q) (hpq : p ∣ q) (hqodd : q % 2 = 1) :
    (ZMod.cast (pairTerm p q M k) : ZMod d) = pairTerm p q d k := by
  have hku : IsUnit (k : ZMod M) :=
    cast_punit_isUnit hp hM (Finset.filter_subset _ _ hk)
  have hqkmem : q - k ∈ punits p q := by
    rw [mem_punits]
    have hkl := mem_lowUnits.mp hk
    have hqid := odd_div_identity hqodd
    refine ⟨by omega, by omega, ?_⟩
    intro hdiv
    apply hkl.2.2.1
    have hh := Nat.dvd_sub hpq hdiv
    simpa [Nat.sub_sub_self hkl.2.1] using hh
  have hqku : IsUnit (((q - k : ℕ) : ZMod M)) := cast_punit_isUnit hp hM hqkmem
  have hden : IsUnit ((k : ZMod M) * (q - k : ZMod M)) := by
    rw [show (q - k : ZMod M) = ((q - k : ℕ) : ZMod M) by
      rw [Nat.cast_sub (mem_lowUnits.mp hk).2.1]]
    exact hku.mul hqku
  rw [pairTerm, pairTerm, cast_inv_of_isUnit hd hden]
  congr 1
  change (ZMod.castHom hd (ZMod d)) ((k : ZMod M) * (q - k : ZMod M)) = _

  rw [map_mul, map_sub]
  simp only [ZMod.castHom_apply]
  rw [ZMod.cast_natCast hd]
  rw [ZMod.cast_natCast hd]


lemma cast_tsum {p q d M : ℕ} (hd : d ∣ M) (hp : p.Prime)
    (hM : ∃ e, M = p ^ e) (hpq : p ∣ q) (hqodd : q % 2 = 1) :
    (ZMod.cast (tsum p q M) : ZMod d) = tsum p q d := by
  rw [tsum, tsum]
  change (ZMod.castHom hd (ZMod d)) (∑ k ∈ lowUnits p q, pairTerm p q M k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact cast_pairTerm hd hp hM hk hpq hqodd

lemma cast_esum2_pairTerm {p q d M : ℕ} (hd : d ∣ M) (hp : p.Prime)
    (hM : ∃ e, M = p ^ e) (hpq : p ∣ q) (hqodd : q % 2 = 1) :
    (ZMod.cast (esum2 (lowUnits p q) (pairTerm p q M)) : ZMod d) =
      esum2 (lowUnits p q) (pairTerm p q d) := by
  rw [esum2, esum2]
  change (ZMod.castHom hd (ZMod d))
    (∑ t ∈ Finset.powersetCard 2 (lowUnits p q), ∏ i ∈ t, pairTerm p q M i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  exact cast_pairTerm hd hp hM ((Finset.mem_powersetCard.mp ht).1 hk) hpq hqodd


lemma two_isUnit_primePow {p s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    IsUnit (2 : ZMod (p ^ s)) := by
  change IsUnit ((2 : ℕ) : ZMod (p ^ s))
  rw [ZMod.isUnit_iff_coprime]
  exact hp.coprime_pow_of_not_dvd (by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega)

lemma tsum_cast_zero_of_dvd_unitSq {p q d M : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hqpos : 0 < q) (hpq : p ∣ q) (hqpow : ∃ r, q = p ^ r)
    (hdq : d ∣ q) (hdpow : ∃ s, d = p ^ s) (hdu : d ∣ unitSq p q)
    (hM : ∃ e, M = p ^ e) (hdM : d ∣ M) (hqodd : q % 2 = 1) :
    (ZMod.cast (tsum p q M) : ZMod d) = 0 := by
  have hbase := two_tsum_eq_neg_unitSq hp hqpos hpq hqpow hqodd
  have hcast := congrArg (ZMod.castHom hdq (ZMod d)) hbase
  have hqpow' : ∃ e, q = p ^ e := hqpow
  simp only [map_mul, map_neg, map_natCast] at hcast
  simp only [ZMod.castHom_apply] at hcast

  rw [show (ZMod.cast (tsum p q q) : ZMod d) = tsum p q d by
    exact cast_tsum hdq hp hqpow' hpq hqodd] at hcast
  have hunitzero : ((unitSq p q : ℕ) : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdu
  rw [show (ZMod.cast (2 : ZMod q) : ZMod d) = 2 by
    exact ZMod.cast_natCast hdq 2] at hcast
  have htwo : IsUnit (2 : ZMod d) := by
    obtain ⟨s, rfl⟩ := hdpow
    exact two_isUnit_primePow hp hp3
  have htd : tsum p q d = 0 := by
    apply htwo.mul_left_cancel
    change (2 : ZMod d) * tsum p q d = 2 * 0
    simpa [hunitzero] using hcast
  rw [cast_tsum hdM hp hM hpq hqodd, htd]

lemma tsum_factor_ge5 {p r K : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (hKr : r ≤ K) :
    ∃ y : ZMod (p ^ K), tsum p (p ^ r) (p ^ K) = (p ^ r : ZMod (p ^ K)) * y := by
  let q := p ^ r
  have hqfac : q = p * p ^ (r - 1) := by
    dsimp [q]
    calc
      p ^ r = p ^ (r - 1 + 1) := by congr 1; omega
      _ = p * p ^ (r - 1) := by rw [pow_succ']
  have hu : q ∣ unitSq p q := by
    rw [hqfac]
    exact unitSq_dvd_of_coprime_six p (p ^ (r - 1)) hp.pos
      (prime_pow_coprime_six hp hp5) (by rw [← hqfac]; exact prime_pow_coprime_six hp hp5)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hcast : (ZMod.cast (tsum p q (p ^ K)) : ZMod q) = 0 := by
    apply tsum_cast_zero_of_dvd_unitSq hp (by omega) (by positivity)
      (dvd_pow_self p (by omega)) ⟨r, rfl⟩ (dvd_refl q) ⟨r, rfl⟩ hu
      ⟨K, rfl⟩ (pow_dvd_pow p hKr) hqodd
  simpa [q, Nat.cast_pow] using
    (exists_mul_of_cast_eq_zero (pow_dvd_pow p hKr) (by positivity) _ hcast)

lemma tsum_factor_three {r K : ℕ} (hr : 2 ≤ r) (hKr : r - 1 ≤ K) :
    ∃ y : ZMod (3 ^ K), tsum 3 (3 ^ r) (3 ^ K) = (3 ^ (r - 1) : ZMod (3 ^ K)) * y := by
  let q := 3 ^ r
  let d := 3 ^ (r - 1)
  have hqfac : q = 3 * d := by
    dsimp [q, d]
    calc
      3 ^ r = 3 ^ (r - 1 + 1) := by congr 1; omega
      _ = 3 * 3 ^ (r - 1) := by rw [pow_succ']
  have hu : d ∣ unitSq 3 q := by
    rw [hqfac]
    exact unitSq_dvd_three (r - 1)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow)
  have hcast : (ZMod.cast (tsum 3 q (3 ^ K)) : ZMod d) = 0 := by
    apply tsum_cast_zero_of_dvd_unitSq Nat.prime_three (by decide) (by positivity)
      (dvd_pow_self 3 (by omega)) ⟨r, rfl⟩
      (pow_dvd_pow 3 (by omega)) ⟨r - 1, rfl⟩ hu
      ⟨K, rfl⟩ (pow_dvd_pow 3 hKr) hqodd
  simpa [q, d, Nat.cast_pow] using
    (exists_mul_of_cast_eq_zero (pow_dvd_pow 3 hKr) (by positivity) _ hcast)

lemma esum2_pairTerm_factor {p r K : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 2 ≤ r) (hK : 1 ≤ K) :
    ∃ y : ZMod (p ^ K),
      esum2 (lowUnits p (p ^ r)) (pairTerm p (p ^ r) (p ^ K)) = (p : ZMod (p ^ K)) * y := by
  have hpq : p ∣ p ^ r := dvd_pow_self p (by omega)
  have hqodd : p ^ r % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hcast :
      (ZMod.cast (esum2 (lowUnits p (p ^ r)) (pairTerm p (p ^ r) (p ^ K))) : ZMod p) = 0 := by
    rw [cast_esum2_pairTerm (dvd_pow_self p (by omega)) hp ⟨K, rfl⟩ hpq hqodd]
    exact esum2_pairTerm_mod_prime_eq_zero hp hp3 hr
  simpa using (exists_mul_of_cast_eq_zero (dvd_pow_self p (by omega)) (by positivity) _ hcast)

lemma bratio_expansion (c p r : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    let K := 3 * r + 3
    let q := p ^ r
    bratio c p q (p ^ K) = 1 +
      (c * (c + 1) * q ^ 2 : ℕ) * tsum p q (p ^ K) := by
  dsimp only
  let K := 3 * r + 3
  let q := p ^ r
  have hqodd : q % 2 = 1 := by
    dsimp [q]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hpq : p ∣ q := by
    dsimp [q]
    exact dvd_pow_self p (by omega)
  rw [bratio_pair c p q (p ^ K) hqodd hpq]
  have hpair : (∏ k ∈ lowUnits p q,
      ((((c * q + k : ℕ) : ZMod (p ^ K)) * (k : ZMod (p ^ K))⁻¹) *
       (((c * q + (q - k) : ℕ) : ZMod (p ^ K)) * (q - k : ZMod (p ^ K))⁻¹)) =
      ∏ k ∈ lowUnits p q,
        (1 + ((c * (c + 1) * q ^ 2 : ℕ) : ZMod (p ^ K)) * pairTerm p q (p ^ K) k)) := by
    apply Finset.prod_congr rfl
    intro k hk
    exact pair_factor c p q (p ^ K) k hp ⟨K, rfl⟩ hk hpq hqodd
  rw [hpair]
  let A : ZMod (p ^ K) := ((c * (c + 1) * q ^ 2 : ℕ) : ZMod (p ^ K))
  have hq6 : (q : ZMod (p ^ K)) ^ 6 = 0 := by
    have hz : (((q ^ 6 : ℕ) : ZMod (p ^ K))) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      dsimp [q, K]
      rw [← pow_mul]
      apply pow_dvd_pow p
      omega
    simpa using hz
  have hA : A ^ 3 = 0 := by
    dsimp [A]
    push_cast
    calc
      ((c : ZMod (p ^ K)) * (c + 1) * q ^ 2) ^ 3 =
          ((c : ZMod (p ^ K)) * (c + 1)) ^ 3 * q ^ 6 := by ring
      _ = 0 := by rw [hq6, mul_zero]
  rw [prod_linear_quadratic _ A _ hA]
  change 1 + A * tsum p q (p ^ K) + A ^ 2 *
      esum2 (lowUnits p q) (pairTerm p q (p ^ K)) = 1 + A * tsum p q (p ^ K)
  obtain ⟨y, hy⟩ := esum2_pairTerm_factor (p := p) (r := r) (K := K) hp hp3 hr (by dsimp [K]; omega)
  rw [hy]
  have hq4p : (q : ZMod (p ^ K)) ^ 4 * p = 0 := by
    have hz : (((q ^ 4 * p : ℕ) : ZMod (p ^ K))) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      dsimp [q, K]
      rw [← pow_mul, ← _root_.pow_succ]
      apply pow_dvd_pow p
      omega
    simpa using hz
  have hzero : A ^ 2 * ((p : ZMod (p ^ K)) * y) = 0 := by
    dsimp [A]
    push_cast
    rw [show (((c : ZMod (p ^ K)) * (c + 1) * q ^ 2) ^ 2) * (p * y) =
      ((c : ZMod (p ^ K)) * (c + 1)) ^ 2 * (q ^ 4 * p) * y by ring,
      hq4p, mul_zero, zero_mul]
  rw [hzero, add_zero]


lemma bratio_eq_one_ge5 (c p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    bratio c p (p ^ s) (p ^ 3) = 1 := by
  let q := p ^ s
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p (by omega)
  rw [bratio_pair c p q (p ^ 3) hqodd hpq]
  have hpair : (∏ k ∈ lowUnits p q,
      ((((c * q + k : ℕ) : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) *
       (((c * q + (q - k) : ℕ) : ZMod (p ^ 3)) * (q - k : ZMod (p ^ 3))⁻¹)) =
      ∏ k ∈ lowUnits p q,
        (1 + ((c * (c + 1) * q ^ 2 : ℕ) : ZMod (p ^ 3)) * pairTerm p q (p ^ 3) k)) := by
    apply Finset.prod_congr rfl
    intro k hk
    exact pair_factor c p q (p ^ 3) k hp ⟨3, rfl⟩ hk hpq hqodd
  rw [hpair]
  let A : ZMod (p ^ 3) := ((c * (c + 1) * q ^ 2 : ℕ) : ZMod (p ^ 3))
  have hq4 : (q : ZMod (p ^ 3)) ^ 4 = 0 := by
    have hz : ((q ^ 4 : ℕ) : ZMod (p ^ 3)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      dsimp [q]
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega)
    simpa using hz
  have hA2 : A ^ 2 = 0 := by
    dsimp [A]
    push_cast
    calc
      ((c : ZMod (p ^ 3)) * (c + 1) * q ^ 2) ^ 2 =
          ((c : ZMod (p ^ 3)) * (c + 1)) ^ 2 * q ^ 4 := by ring
      _ = 0 := by rw [hq4, mul_zero]
  have hA3 : A ^ 3 = 0 := by rw [show A ^ 3 = A ^ 2 * A by ring, hA2, zero_mul]
  rw [prod_linear_quadratic _ A _ hA3, hA2, zero_mul, add_zero]
  change 1 + A * tsum p q (p ^ 3) = 1
  by_cases hs1 : s = 1
  · subst s
    obtain ⟨y, hy⟩ := tsum_factor_ge5 (r := 1) (K := 3) hp hp5 (by omega) (by omega)
    have hy' : tsum p q (p ^ 3) = (q : ZMod (p ^ 3)) * y := by simpa [q] using hy
    rw [hy']
    have hq3 : (q : ZMod (p ^ 3)) ^ 3 = 0 := by
      have hz : ((q ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        dsimp [q]
        rw [← pow_mul]
      simpa using hz
    have : A * ((q : ZMod (p ^ 3)) * y) = 0 := by
      dsimp [A]
      push_cast
      rw [show ((c : ZMod (p ^ 3)) * (c + 1) * q ^ 2) * (q * y) =
        ((c : ZMod (p ^ 3)) * (c + 1)) * q ^ 3 * y by ring,
        hq3, mul_zero, zero_mul]
    rw [this, add_zero]
  · have hs2 : 2 ≤ s := by omega
    have hq2 : (q : ZMod (p ^ 3)) ^ 2 = 0 := by
      have hz : ((q ^ 2 : ℕ) : ZMod (p ^ 3)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        dsimp [q]
        rw [← pow_mul]
        exact pow_dvd_pow p (by omega)
      simpa using hz
    have hAzero : A = 0 := by
      dsimp [A]
      push_cast
      rw [hq2, mul_zero]
    rw [hAzero, zero_mul, add_zero]

lemma bratio_eq_one_three (c s : ℕ) (hs : 2 ≤ s) :
    bratio c 3 (3 ^ s) (3 ^ 4) = 1 := by
  let q := 3 ^ s
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow)
  have hpq : 3 ∣ q := by dsimp [q]; exact dvd_pow_self 3 (by omega)
  rw [bratio_pair c 3 q (3 ^ 4) hqodd hpq]
  have hpair : (∏ k ∈ lowUnits 3 q,
      ((((c * q + k : ℕ) : ZMod (3 ^ 4)) * (k : ZMod (3 ^ 4))⁻¹) *
       (((c * q + (q - k) : ℕ) : ZMod (3 ^ 4)) * (q - k : ZMod (3 ^ 4))⁻¹)) =
      ∏ k ∈ lowUnits 3 q,
        (1 + ((c * (c + 1) * q ^ 2 : ℕ) : ZMod (3 ^ 4)) * pairTerm 3 q (3 ^ 4) k)) := by
    apply Finset.prod_congr rfl
    intro k hk
    exact pair_factor c 3 q (3 ^ 4) k Nat.prime_three ⟨4, rfl⟩ hk hpq hqodd
  rw [hpair]
  let A : ZMod (3 ^ 4) := ((c * (c + 1) * q ^ 2 : ℕ) : ZMod (3 ^ 4))
  have hq4 : (q : ZMod (3 ^ 4)) ^ 4 = 0 := by
    have hz : ((q ^ 4 : ℕ) : ZMod (3 ^ 4)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      dsimp [q]
      rw [← pow_mul]
      exact Nat.pow_dvd_pow 3 (show 4 ≤ s * 4 by omega)
    simpa using hz
  have hA2 : A ^ 2 = 0 := by
    dsimp [A]
    push_cast
    calc
      ((c : ZMod (3 ^ 4)) * (c + 1) * q ^ 2) ^ 2 =
          ((c : ZMod (3 ^ 4)) * (c + 1)) ^ 2 * q ^ 4 := by ring
      _ = 0 := by rw [hq4, mul_zero]
  have hA3 : A ^ 3 = 0 := by rw [show A ^ 3 = A ^ 2 * A by ring, hA2, zero_mul]
  rw [prod_linear_quadratic _ A _ hA3, hA2, zero_mul, add_zero]
  change 1 + A * tsum 3 q (3 ^ 4) = 1
  by_cases hs2 : s = 2
  · subst s
    obtain ⟨y, hy⟩ := tsum_factor_three (r := 2) (K := 4) (by omega) (by omega)
    have hy' : tsum 3 q (3 ^ 4) = (3 : ZMod (3 ^ 4)) * y := by simpa [q] using hy
    rw [hy']
    have hqd : (q : ZMod (3 ^ 4)) ^ 2 * 3 = 0 := by
      have hz : ((q ^ 2 * 3 : ℕ) : ZMod (3 ^ 4)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        norm_num [q]
      push_cast at hz
      exact hz
    have : A * ((3 : ZMod (3 ^ 4)) * y) = 0 := by
      dsimp [A]
      push_cast
      rw [show ((c : ZMod (3 ^ 4)) * (c + 1) * q ^ 2) * (3 * y) =
        ((c : ZMod (3 ^ 4)) * (c + 1)) * (q ^ 2 * 3) * y by ring,
        hqd, mul_zero, zero_mul]
    rw [this, add_zero]
  · have hs3 : 3 ≤ s := by omega
    have hq2 : (q : ZMod (3 ^ 4)) ^ 2 = 0 := by
      have hz : ((q ^ 2 : ℕ) : ZMod (3 ^ 4)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        dsimp [q]
        rw [← pow_mul]
        exact Nat.pow_dvd_pow 3 (show 4 ≤ s * 2 by omega)
      simpa using hz
    have hAzero : A = 0 := by
      dsimp [A]
      push_cast
      rw [hq2, mul_zero]
    rw [hAzero, zero_mul, add_zero]


lemma binom_prime_pow_eq_base_ge5 (c p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((((c + 1) * p ^ s).choose (p ^ s) : ℕ) : ZMod (p ^ 3)) = c + 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have h := binom_ratio c p (p ^ s) (p ^ 3) hp ⟨3, rfl⟩
      have hr : bratio c p (p * p ^ s) (p ^ 3) = 1 := by
        rw [← pow_succ']
        exact bratio_eq_one_ge5 c p (s + 1) hp hp5 (by omega)
      rw [hr, mul_one] at h
      simpa [pow_succ'] using h.trans ih

lemma binom_three_pow_eq_first (c t : ℕ) :
    ((((c + 1) * 3 ^ (t + 1)).choose (3 ^ (t + 1)) : ℕ) : ZMod (3 ^ 4)) =
      ((((c + 1) * 3).choose 3 : ℕ) : ZMod (3 ^ 4)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h := binom_ratio c 3 (3 ^ (t + 1)) (3 ^ 4) Nat.prime_three ⟨4, rfl⟩
      have hr : bratio c 3 (3 * 3 ^ (t + 1)) (3 ^ 4) = 1 := by
        rw [← pow_succ']
        exact bratio_eq_one_three c (t + 2) (by omega)
      rw [hr, mul_one] at h
      simpa [pow_succ', Nat.add_assoc] using h.trans ih

lemma bracket_factor_ge5 {p r K : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hK : 3 ≤ K) :
    ∃ y : ZMod (p ^ K),
      (2 : ZMod (p ^ K)) *
          ((((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ K))) ^ 2 -
        9 * ((((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ K))) =
      (p ^ 3 : ZMod (p ^ K)) * y := by
  let x : ZMod (p ^ K) :=
    2 * ((((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ K))) ^ 2 -
      9 * ((((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ K)))
  have hcast : (ZMod.cast x : ZMod (p ^ 3)) = 0 := by
    dsimp [x]
    change (ZMod.castHom (pow_dvd_pow p hK) (ZMod (p ^ 3)))
      (2 * ((((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ K))) ^ 2 -
        9 * ((((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ K)))) = 0
    simp only [map_sub, map_mul, map_pow, map_natCast]
    have hC : ((((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ 3))) = 3 := by
      convert binom_prime_pow_eq_base_ge5 2 p (r - 1) hp hp5 using 1 <;> norm_num
    have hB : ((((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℕ) : ZMod (p ^ 3))) = 2 := by
      convert binom_prime_pow_eq_base_ge5 1 p (r - 1) hp hp5 using 1 <;> norm_num
    rw [hC, hB]
    simp only [map_ofNat]
    norm_num
  obtain ⟨y, hy⟩ := exists_mul_of_cast_eq_zero (pow_dvd_pow p hK) (by positivity) x hcast
  exact ⟨y, by simpa [x, Nat.cast_pow] using hy⟩

lemma bracket_factor_three {r K : ℕ} (hr : 2 ≤ r) (hK : 4 ≤ K) :
    ∃ y : ZMod (3 ^ K),
      (2 : ZMod (3 ^ K)) *
          ((((3 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℕ) : ZMod (3 ^ K))) ^ 2 -
        9 * ((((2 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℕ) : ZMod (3 ^ K))) =
      (3 ^ 4 : ZMod (3 ^ K)) * y := by
  let x : ZMod (3 ^ K) :=
    2 * ((((3 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℕ) : ZMod (3 ^ K))) ^ 2 -
      9 * ((((2 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℕ) : ZMod (3 ^ K)))
  have hcast : (ZMod.cast x : ZMod (3 ^ 4)) = 0 := by
    dsimp [x]
    change (ZMod.castHom (pow_dvd_pow 3 hK) (ZMod (3 ^ 4)))
      (2 * ((((3 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℕ) : ZMod (3 ^ K))) ^ 2 -
        9 * ((((2 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℕ) : ZMod (3 ^ K)))) = 0
    simp only [map_sub, map_mul, map_pow, map_natCast]
    have hrepr : r - 1 = (r - 2) + 1 := by omega
    rw [hrepr]
    have hC : ((((3 * 3 ^ ((r - 2) + 1)).choose (3 ^ ((r - 2) + 1)) : ℕ) : ZMod (3 ^ 4))) =
        ((((3 * 3).choose 3 : ℕ) : ZMod (3 ^ 4))) := by
      simpa using binom_three_pow_eq_first 2 (r - 2)
    have hB : ((((2 * 3 ^ ((r - 2) + 1)).choose (3 ^ ((r - 2) + 1)) : ℕ) : ZMod (3 ^ 4))) =
        ((((2 * 3).choose 3 : ℕ) : ZMod (3 ^ 4))) := by
      simpa using binom_three_pow_eq_first 1 (r - 2)
    rw [hC, hB]
    simp only [map_ofNat]
    norm_num [Nat.choose]
    decide

  obtain ⟨y, hy⟩ := exists_mul_of_cast_eq_zero (pow_dvd_pow 3 hK) (by positivity) x hcast
  refine ⟨y, ?_⟩
  change x = (3 ^ 4 : ZMod (3 ^ K)) * y
  rw [show (3 ^ 4 : ZMod (3 ^ K)) = (((3 ^ 4 : ℕ) : ZMod (3 ^ K))) by norm_num]
  exact hy

lemma main_zmod (p r : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    let K := 3 * r + 3
    let q := p ^ r
    let m := p ^ (r - 1)
    let R := ZMod (p ^ K)
    ((((3 * q).choose q : ℕ) : R)) ^ 2 - 27 * ((((2 * q).choose q : ℕ) : R)) =
      ((((3 * m).choose m : ℕ) : R)) ^ 2 - 27 * ((((2 * m).choose m : ℕ) : R)) := by
  dsimp only
  let K := 3 * r + 3
  let q := p ^ r
  let m := p ^ (r - 1)
  let R := ZMod (p ^ K)
  let Cq : R := ((((3 * q).choose q : ℕ) : R))
  let Bq : R := ((((2 * q).choose q : ℕ) : R))
  let Cm : R := ((((3 * m).choose m : ℕ) : R))
  let Bm : R := ((((2 * m).choose m : ℕ) : R))
  let T : R := tsum p q (p ^ K)
  let X : R := (q : R) ^ 2 * T
  have hqfac : q = p * m := by
    dsimp [q, m]
    calc
      p ^ r = p ^ (r - 1 + 1) := by congr 1; omega
      _ = p * p ^ (r - 1) := by rw [pow_succ']
  have hC := binom_ratio 2 p m (p ^ K) hp ⟨K, rfl⟩
  have hB := binom_ratio 1 p m (p ^ K) hp ⟨K, rfl⟩
  have hC' : Cq = Cm * bratio 2 p q (p ^ K) := by
    dsimp [Cq, Cm]
    simpa [← hqfac] using hC
  have hB' : Bq = Bm * bratio 1 p q (p ^ K) := by
    dsimp [Bq, Bm]
    simpa [← hqfac] using hB
  have hR2raw := bratio_expansion 2 p r hp hp3 hr
  have hR1raw := bratio_expansion 1 p r hp hp3 hr
  have hR2 : bratio 2 p q (p ^ K) = 1 + 6 * X := by
    dsimp [q, K, X, T] at hR2raw ⊢
    convert hR2raw using 1 <;> norm_num <;> ring
  have hR1 : bratio 1 p q (p ^ K) = 1 + 2 * X := by
    dsimp [q, K, X, T] at hR1raw ⊢
    convert hR1raw using 1 <;> norm_num <;> ring
  change Cq ^ 2 - 27 * Bq = Cm ^ 2 - 27 * Bm

  rw [hC', hB', hR2, hR1]
  change (Cm * (1 + 6 * X)) ^ 2 - 27 * (Bm * (1 + 2 * X)) = Cm ^ 2 - 27 * Bm
  have hzero : 6 * X * ((2 : R) * Cm ^ 2 - 9 * Bm) + 36 * Cm ^ 2 * X ^ 2 = 0 := by
    by_cases hp_eq : p = 3
    · subst p
      obtain ⟨y, hy⟩ := tsum_factor_three (r := r) (K := K) hr (by dsimp [K]; omega)
      have hy' : T = (3 ^ (r - 1) : R) * y := by simpa [T, q, R] using hy
      obtain ⟨z, hz⟩ := bracket_factor_three (r := r) (K := K) hr (by dsimp [K]; omega)
      have hz' : (2 : R) * Cm ^ 2 - 9 * Bm = (3 ^ 4 : R) * z := by simpa [Cm, Bm, m, R] using hz
      dsimp [X]
      rw [hy', hz']
      have hfirst : (3 : R) ^ (2 * r) * 3 ^ (r - 1) * 3 ^ 4 = 0 := by
        have hn : (((3 ^ (2 * r) * 3 ^ (r - 1) * 3 ^ 4 : ℕ) : R)) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          dsimp [R, K]
          have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
          rw [h81, ← pow_add, ← pow_add]
          exact pow_dvd_pow 3 (by omega)
        push_cast at hn
        convert hn using 1 <;> norm_num
      have hsecond : ((3 : R) ^ (2 * r) * 3 ^ (r - 1)) ^ 2 = 0 := by
        have hn : ((((3 ^ (2 * r) * 3 ^ (r - 1)) ^ 2 : ℕ) : R)) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          dsimp [R, K]
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_add]
          exact pow_dvd_pow 3 (by omega)
        push_cast at hn
        exact hn
      have hq2 : (q : R) ^ 2 = (3 : R) ^ (2 * r) := by
        dsimp [q]
        push_cast
        rw [← pow_mul]
        congr 1 <;> omega
      rw [hq2]
      have hv1 :
          ((3 : R) ^ (2 * r) * (3 ^ (r - 1) * y)) * (3 ^ 4 * z) = 0 := by
        calc
          _ = ((3 : R) ^ (2 * r) * 3 ^ (r - 1) * 3 ^ 4) * y * z := by ring
          _ = 0 := by rw [hfirst]; ring
      have hv2 :
          ((3 : R) ^ (2 * r) * (3 ^ (r - 1) * y)) ^ 2 = 0 := by
        calc
          _ = (((3 : R) ^ (2 * r) * 3 ^ (r - 1)) ^ 2) * y ^ 2 := by ring
          _ = 0 := by rw [hsecond]; ring
      calc
        _ = 6 * (((3 : R) ^ (2 * r) * (3 ^ (r - 1) * y)) * (3 ^ 4 * z)) +
            36 * Cm ^ 2 * ((3 : R) ^ (2 * r) * (3 ^ (r - 1) * y)) ^ 2 := by ring
        _ = 0 := by rw [hv1, hv2]; ring
    · have hp5 : 5 ≤ p := by
        have hpne4 : p ≠ 4 := by intro h; subst p; norm_num at hp
        omega
      obtain ⟨y, hy⟩ := tsum_factor_ge5 (r := r) (K := K) hp hp5 (by omega) (by dsimp [K]; omega)
      have hy' : T = (q : R) * y := by simpa [T, q, R] using hy
      obtain ⟨z, hz⟩ := bracket_factor_ge5 (r := r) (K := K) hp hp5 hr (by dsimp [K]; omega)
      have hz' : (2 : R) * Cm ^ 2 - 9 * Bm = (p ^ 3 : R) * z := by simpa [Cm, Bm, m, R] using hz
      dsimp [X]
      rw [hy', hz']
      have hfirst : (q : R) ^ 3 * p ^ 3 = 0 := by
        have hn : (((q ^ 3 * p ^ 3 : ℕ) : R)) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          dsimp [q, R, K]
          rw [← pow_mul, ← pow_add]
          exact pow_dvd_pow p (by omega)
        simpa using hn
      have hsecond : (q : R) ^ 6 = 0 := by
        have hn : (((q ^ 6 : ℕ) : R)) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          dsimp [q, R, K]
          rw [← pow_mul]
          exact pow_dvd_pow p (by omega)
        simpa using hn
      have hv1 :
          ((q : R) ^ 2 * (q * y)) * (p ^ 3 * z) = 0 := by
        calc
          _ = ((q : R) ^ 3 * p ^ 3) * y * z := by ring
          _ = 0 := by rw [hfirst]; ring
      have hv2 : ((q : R) ^ 2 * (q * y)) ^ 2 = 0 := by
        calc
          _ = (q : R) ^ 6 * y ^ 2 := by ring
          _ = 0 := by rw [hsecond]; ring
      calc
        _ = 6 * (((q : R) ^ 2 * (q * y)) * (p ^ 3 * z)) +
            36 * Cm ^ 2 * ((q : R) ^ 2 * (q * y)) ^ 2 := by ring
        _ = 0 := by rw [hv1, hv2]; ring
  calc
    (Cm * (1 + 6 * X)) ^ 2 - 27 * (Bm * (1 + 2 * X)) =
      (Cm ^ 2 - 27 * Bm) + (6 * X * (2 * Cm ^ 2 - 9 * Bm) + 36 * Cm ^ 2 * X ^ 2) := by ring
    _ = Cm ^ 2 - 27 * Bm := by rw [hzero, add_zero]


end Work

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by
  have hz := Work.main_zmod p r hp hp3 hr
  dsimp only at hz
  apply (ZMod.intCast_eq_intCast_iff (a (p ^ r)) (a (p ^ (r - 1))) (p ^ (3 * r + 3))).mp
  simpa [a] using hz
