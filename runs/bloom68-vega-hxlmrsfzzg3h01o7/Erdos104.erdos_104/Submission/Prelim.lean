import FormalConjecturesUtil

/-!
# Faithful counting preliminaries for Erdős Problem 104

The three counting definitions below are copied from `Submission/Spec.lean`, but live in
an independent namespace. This file does not import that specification.

A qualifying circle is determined by its incident subset of a finite configuration. This
proves that the set counted by `Set.ncard` is genuinely finite and ensures that the
natural-number supremum is an attained maximum. Double counting circle--point-pair
incidences gives the unconditional bound `3 * unitCircleCount P ≤ P.card * (P.card - 1)`
and the same bound for the maxima. This is only a quadratic bound, not little-o of the
square. The asymptotic results below remain conditional transfers, not a proof of the
required uniform subquadratic geometric bound.
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos104Prelim

open EuclideanGeometry

/-- The number of distinct unit circles containing at least three points of `P`. -/
noncomputable def unitCircleCount (P : Finset ℝ²) : ℕ :=
  Set.ncard {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}

/-- The set of unit-circle counts attained by configurations of `n` points in the plane. -/
noncomputable def possibleUnitCircleCounts (n : ℕ) : Set ℕ :=
  {k | ∃ P : Finset ℝ², P.card = n ∧ unitCircleCount P = k}

/-- The maximum number of qualifying unit circles attained by a configuration of `n` points. -/
noncomputable def maxUnitCircleCount (n : ℕ) : ℕ :=
  sSup (possibleUnitCircleCounts n)

/-- The finite subset of `P` incident with a circle. -/
noncomputable def incidentPoints (P : Finset ℝ²) (s : Sphere ℝ²) : Finset ℝ² := by
  classical
  exact P.filter (fun p => p ∈ s)

@[simp] theorem mem_incidentPoints (P : Finset ℝ²) (s : Sphere ℝ²) (p : ℝ²) :
    p ∈ incidentPoints P s ↔ p ∈ P ∧ p ∈ s := by
  classical
  simp [incidentPoints]

/-- Three distinct common points force two circles in the plane to coincide. -/
theorem sphere_eq_of_three_common_points {s₁ s₂ : Sphere ℝ²} {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha₁ : a ∈ s₁) (hb₁ : b ∈ s₁) (hc₁ : c ∈ s₁)
    (ha₂ : a ∈ s₂) (hb₂ : b ∈ s₂) (hc₂ : c ∈ s₂) : s₁ = s₂ := by
  by_contra hne
  rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (finrank_euclideanSpace_fin (𝕜 := ℝ)) hne hab ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ with h | h
  · exact hac h.symm
  · exact hbc h.symm

/-- The incident-subset map is injective on the set used in `unitCircleCount`. -/
theorem incidentPoints_injOn (P : Finset ℝ²) :
    Set.InjOn (incidentPoints P)
      {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard} := by
  intro s₁ hs₁ s₂ _ heq
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (P.finite_toSet.sep (fun p => p ∈ s₁))).mp
      (Nat.lt_of_succ_le hs₁.2)
  have hmem : ∀ p ∈ P, p ∈ s₁ ↔ p ∈ s₂ := by
    intro p hp
    simpa only [mem_incidentPoints, hp, true_and] using (Finset.ext_iff.mp heq p)
  exact sphere_eq_of_three_common_points hab hac hbc ha.2 hb.2 hc.2
    ((hmem a ha.1).mp ha.2) ((hmem b hb.1).mp hb.2) ((hmem c hc.1).mp hc.2)

/-- Every incident subset is an element of the finite powerset of `P`. -/
theorem incidentPoints_mem_powerset (P : Finset ℝ²) (s : Sphere ℝ²) :
    incidentPoints P s ∈ P.powerset := by
  classical
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ P)

/-- The qualifying circles form a finite set; `Set.ncard` is not using its infinite-set value. -/
theorem finite_qualifyingUnitCircles (P : Finset ℝ²) :
    Set.Finite {s : Sphere ℝ² |
      s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard} := by
  classical
  exact Set.Finite.of_injOn
    (fun s _ => incidentPoints_mem_powerset P s)
    (incidentPoints_injOn P) P.powerset.finite_toSet

/-- In particular, the count agrees with the cardinality of the actual finite set of circles. -/
theorem unitCircleCount_eq_card (P : Finset ℝ²) :
    unitCircleCount P = (finite_qualifyingUnitCircles P).toFinset.card := by
  exact Set.ncard_eq_toFinset_card _ (finite_qualifyingUnitCircles P)

/-- The incident-subset injection bounds the number of qualifying circles by `2 ^ P.card`. -/
theorem unitCircleCount_le_two_pow_card (P : Finset ℝ²) :
    unitCircleCount P ≤ 2 ^ P.card := by
  classical
  have h := Set.ncard_le_ncard_of_injOn (incidentPoints P)
    (t := (P.powerset : Set (Finset ℝ²)))
    (fun s _ => incidentPoints_mem_powerset P s)
    (incidentPoints_injOn P) P.powerset.finite_toSet
  simpa only [unitCircleCount, Set.ncard_coe_finset, Finset.card_powerset] using h

/-- The incident-point finset has the cardinality used in the definition of the count. -/
theorem card_incidentPoints (P : Finset ℝ²) (s : Sphere ℝ²) :
    (incidentPoints P s).card = {p ∈ (P : Set ℝ²) | p ∈ s}.ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp

open scoped Classical in
/-- Among any finite collection of unit circles, at most two contain a given distinct
pair of points. Their centers lie on both unit circles centered at those points. -/
theorem card_unitCircles_through_pair_le_two (S : Finset (Sphere ℝ²))
    (hS : ∀ s ∈ S, s.radius = 1) {a b : ℝ²} (hab : a ≠ b) :
    (S.filter (fun s => a ∈ s ∧ b ∈ s)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  simp only [Finset.mem_filter] at hs₁ hs₂ hs₃
  have hdual (s : Sphere ℝ²) (hs : s ∈ S) (p : ℝ²) (hp : p ∈ s) :
      s.center ∈ (⟨p, 1⟩ : Sphere ℝ²) := by
    simpa only [mem_sphere, Sphere.mk_center, Sphere.mk_radius, dist_comm, hS s hs]
      using hp
  have heq : (⟨a, 1⟩ : Sphere ℝ²) = ⟨b, 1⟩ :=
    sphere_eq_of_three_common_points
      ((Sphere.center_ne_iff_ne_of_mem hs₁.2.1 hs₂.2.1).mpr h₁₂)
      ((Sphere.center_ne_iff_ne_of_mem hs₁.2.1 hs₃.2.1).mpr h₁₃)
      ((Sphere.center_ne_iff_ne_of_mem hs₂.2.1 hs₃.2.1).mpr h₂₃)
      (hdual s₁ hs₁.1 a hs₁.2.1) (hdual s₂ hs₂.1 a hs₂.2.1)
      (hdual s₃ hs₃.1 a hs₃.2.1) (hdual s₁ hs₁.1 b hs₁.2.2)
      (hdual s₂ hs₂.1 b hs₂.2.2) (hdual s₃ hs₃.1 b hs₃.2.2)
  exact hab (congrArg Sphere.center heq)

open scoped Classical in
/-- Three or more incident points give at least six ordered distinct incident pairs. -/
theorem six_le_card_incidentPairs (P : Finset ℝ²) (s : Sphere ℝ²)
    (hs : 3 ≤ (incidentPoints P s).card) :
    6 ≤ (P.offDiag.filter (fun q : ℝ² × ℝ² => q.1 ∈ s ∧ q.2 ∈ s)).card := by
  classical
  have hpairs : P.offDiag.filter (fun q : ℝ² × ℝ² => q.1 ∈ s ∧ q.2 ∈ s) =
      (incidentPoints P s).offDiag := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_offDiag, mem_incidentPoints]
    tauto
  rw [hpairs, Finset.offDiag_card]
  apply Nat.le_sub_of_add_le
  nlinarith

/-- Unconditional quadratic bound, by double counting circle--ordered-pair incidences.
Each qualifying circle contributes at least six incidences, while each distinct input
pair belongs to at most two unit circles. -/
theorem three_mul_unitCircleCount_le_card_mul_pred (P : Finset ℝ²) :
    3 * unitCircleCount P ≤ P.card * (P.card - 1) := by
  classical
  let S := (finite_qualifyingUnitCircles P).toFinset
  have hS (s : Sphere ℝ²) (hs : s ∈ S) :
      s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard :=
    (finite_qualifyingUnitCircles P).mem_toFinset.mp hs
  have hcount := Finset.card_mul_le_card_mul
    (s := S) (t := P.offDiag) (m := 6) (n := 2)
    (fun (s : Sphere ℝ²) (q : ℝ² × ℝ²) => q.1 ∈ s ∧ q.2 ∈ s)
    (fun s hs => six_le_card_incidentPairs P s
      (by rw [card_incidentPoints]; exact (hS s hs).2))
    (fun q hq => card_unitCircles_through_pair_le_two S
      (fun s hs => (hS s hs).1) (Finset.mem_offDiag.mp hq).2.2)
  have hcard : S.card = unitCircleCount P := (unitCircleCount_eq_card P).symm
  rw [hcard, Finset.offDiag_card, ← Nat.mul_sub_one] at hcount
  omega

/-- In particular, the qualifying-circle count is at most the square of the number of points. -/
theorem unitCircleCount_le_card_sq (P : Finset ℝ²) :
    unitCircleCount P ≤ P.card ^ 2 := by
  have h := three_mul_unitCircleCount_le_card_mul_pred P
  have hpred : P.card * (P.card - 1) ≤ P.card * P.card :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith

/-- Every natural number occurs as the cardinality of a finite planar configuration. -/
theorem exists_finset_card (n : ℕ) : ∃ P : Finset ℝ², P.card = n :=
  Infinite.exists_subset_card_eq ℝ² n

/-- There is at least one possible count for each configuration size, including zero. -/
theorem possibleUnitCircleCounts_nonempty (n : ℕ) :
    (possibleUnitCircleCounts n).Nonempty := by
  obtain ⟨P, hP⟩ := exists_finset_card n
  exact ⟨unitCircleCount P, P, hP, rfl⟩

/-- All counts for configurations of size `n` are bounded by `2 ^ n`. -/
theorem possibleUnitCircleCounts_bddAbove (n : ℕ) :
    BddAbove (possibleUnitCircleCounts n) := by
  refine ⟨2 ^ n, ?_⟩
  rintro k ⟨P, hP, rfl⟩
  simpa only [hP] using unitCircleCount_le_two_pow_card P

/-- The natural-number supremum is itself a possible count. -/
theorem maxUnitCircleCount_mem (n : ℕ) :
    maxUnitCircleCount n ∈ possibleUnitCircleCounts n :=
  Nat.sSup_mem (possibleUnitCircleCounts_nonempty n) (possibleUnitCircleCounts_bddAbove n)

/-- An actual configuration attains the maximum, rather than a default value of `sSup`. -/
theorem maxUnitCircleCount_attained (n : ℕ) :
    ∃ P : Finset ℝ², P.card = n ∧ unitCircleCount P = maxUnitCircleCount n :=
  maxUnitCircleCount_mem n

/-- Each configuration's count is bounded by the maximum at its own cardinality. -/
theorem unitCircleCount_le_maxUnitCircleCount (P : Finset ℝ²) :
    unitCircleCount P ≤ maxUnitCircleCount P.card :=
  le_csSup (possibleUnitCircleCounts_bddAbove P.card) ⟨P, rfl, rfl⟩

/-- The attained maximum satisfies the same finite combinatorial bound. -/
theorem maxUnitCircleCount_le_two_pow (n : ℕ) : maxUnitCircleCount n ≤ 2 ^ n := by
  obtain ⟨P, hP, hmax⟩ := maxUnitCircleCount_attained n
  simpa only [hP, hmax] using unitCircleCount_le_two_pow_card P

/-- The attained maximum satisfies the unconditional circle--pair incidence bound. -/
theorem three_mul_maxUnitCircleCount_le_mul_pred (n : ℕ) :
    3 * maxUnitCircleCount n ≤ n * (n - 1) := by
  obtain ⟨P, hP, hmax⟩ := maxUnitCircleCount_attained n
  simpa only [hP, hmax] using three_mul_unitCircleCount_le_card_mul_pred P

/-- In particular, the attained maximum is at most quadratic. This does not assert little-o. -/
theorem maxUnitCircleCount_le_sq (n : ℕ) : maxUnitCircleCount n ≤ n ^ 2 := by
  obtain ⟨P, hP, hmax⟩ := maxUnitCircleCount_attained n
  simpa only [hP, hmax] using unitCircleCount_le_card_sq P

/-- At a fixed multiplier and threshold, uniform configuration bounds are exactly bounds
on the attained maxima. -/
theorem uniform_bound_iff_max_bound (K N : ℕ) :
    (∀ P : Finset ℝ², N ≤ P.card → K * unitCircleCount P ≤ P.card ^ 2) ↔
      ∀ n : ℕ, N ≤ n → K * maxUnitCircleCount n ≤ n ^ 2 := by
  constructor
  · intro h n hn
    obtain ⟨P, hP, hmax⟩ := maxUnitCircleCount_attained n
    simpa only [hP, hmax] using h P (by simpa only [hP] using hn)
  · intro h P hP
    exact (Nat.mul_le_mul_left K (unitCircleCount_le_maxUnitCircleCount P)).trans
      (h P.card hP)

/-- Little-o for the real-valued maxima is equivalent to eventual natural-number
multiplier bounds. -/
theorem maxUnitCircleCount_isLittleO_iff_nat_bound :
    ((fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2)) ↔
      ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * maxUnitCircleCount n ≤ n ^ 2 := by
  rw [Asymptotics.isLittleO_iff_nat_mul_le]
  simp only [Real.norm_natCast, ← Nat.cast_mul, ← Nat.cast_pow,
    Nat.cast_le, eventually_atTop]

/-- The asymptotic statement is equivalent to the uniform geometric estimate. This
establishes the transfer only; it does not assert that the uniform estimate holds. -/
theorem maxUnitCircleCount_isLittleO_iff_uniform_bound :
    ((fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2)) ↔
      ∀ K : ℕ, ∃ N : ℕ, ∀ P : Finset ℝ²,
        N ≤ P.card → K * unitCircleCount P ≤ P.card ^ 2 := by
  rw [maxUnitCircleCount_isLittleO_iff_nat_bound]
  simp_rw [uniform_bound_iff_max_bound]

/-- A uniform subquadratic estimate for all configurations implies little-o for the
maximum. The uniform estimate remains an explicit hypothesis. -/
theorem maxUnitCircleCount_isLittleO_of_uniform_bound
    (h : ∀ K : ℕ, ∃ N : ℕ, ∀ P : Finset ℝ²,
      N ≤ P.card → K * unitCircleCount P ≤ P.card ^ 2) :
    (fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2) :=
  maxUnitCircleCount_isLittleO_iff_uniform_bound.mpr h

/-- The exact counterfamily obligation for a disproof. This equivalence does not
assert that any such family exists. -/
theorem maxUnitCircleCount_not_isLittleO_iff_counterfamily :
    (¬ ((fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2))) ↔
      ∃ K : ℕ, ∀ N : ℕ, ∃ P : Finset ℝ²,
        N ≤ P.card ∧ P.card ^ 2 < K * unitCircleCount P := by
  classical
  rw [maxUnitCircleCount_isLittleO_iff_uniform_bound]
  push_neg
  rfl

/-- Multipliers at most three satisfy the required inequality at every cardinality.
The unbounded range of multipliers is the unsolved part of the little-o assertion. -/
theorem unitCircleCount_mul_le_sq_of_le_three (P : Finset ℝ²) (K : ℕ)
    (hK : K ≤ 3) : K * unitCircleCount P ≤ P.card ^ 2 := by
  calc
    K * unitCircleCount P ≤ 3 * unitCircleCount P := Nat.mul_le_mul_right _ hK
    _ ≤ P.card * (P.card - 1) := three_mul_unitCircleCount_le_card_mul_pred P
    _ ≤ P.card * P.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = P.card ^ 2 := (pow_two _).symm

/-- Any counterfamily must have a fixed reciprocal-density multiplier at least four.
Neither the existence nor the nonexistence of such a family is asserted here. -/
theorem maxUnitCircleCount_not_isLittleO_iff_counterfamily_ge_four :
    (¬ ((fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2))) ↔
      ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, ∃ P : Finset ℝ²,
        N ≤ P.card ∧ P.card ^ 2 < K * unitCircleCount P := by
  rw [maxUnitCircleCount_not_isLittleO_iff_counterfamily]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_, hK⟩
    by_contra h
    have hsmall : K ≤ 3 := by omega
    obtain ⟨P, _, hP⟩ := hK 0
    exact (not_lt_of_ge (unitCircleCount_mul_le_sq_of_le_three P K hsmall)) hP
  · rintro ⟨K, _, hK⟩
    exact ⟨K, hK⟩

end Erdos104Prelim
