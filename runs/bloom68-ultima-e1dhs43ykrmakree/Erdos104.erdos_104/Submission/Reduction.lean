import FormalConjecturesUtil

/-!
# Exact finite-configuration criteria for Erdős Problem 104

This standalone file copies the three definitions from `Submission/Spec.lean`
and the finiteness/attainment lemmas from `Submission/Counting.lean`.
It does not import the specification or use its conjecture or disproof declarations.

The final three theorems give equivalent uniform real-ε and natural-number
criteria for the conjecture and an exact criterion for its negation.
Neither criterion is asserted to hold: this file does not settle the conjecture.
-/

open scoped EuclideanGeometry

namespace Erdos104

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

/-- The finite trace of a sphere on a configuration. -/
noncomputable def unitCircleTrace (P : Finset ℝ²) (s : Sphere ℝ²) : Finset ℝ² := by
  classical
  exact P.filter (fun p => p ∈ s)

@[simp]
theorem mem_unitCircleTrace {P : Finset ℝ²} {s : Sphere ℝ²} {p : ℝ²} :
    p ∈ unitCircleTrace P s ↔ p ∈ P ∧ p ∈ s := by
  classical
  simp [unitCircleTrace]

theorem unitCircleTrace_subset (P : Finset ℝ²) (s : Sphere ℝ²) :
    unitCircleTrace P s ⊆ P := by
  intro p hp
  exact (mem_unitCircleTrace.mp hp).1

@[simp]
theorem coe_unitCircleTrace (P : Finset ℝ²) (s : Sphere ℝ²) :
    (unitCircleTrace P s : Set ℝ²) = {p ∈ (P : Set ℝ²) | p ∈ s} := by
  ext p
  simp

/-- The trace determines any sphere containing at least three configuration points. -/
theorem eq_of_unitCircleTrace_eq {P : Finset ℝ²} {s t : Sphere ℝ²}
    (hs : 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard)
    (htrace : unitCircleTrace P s = unitCircleTrace P t) : s = t := by
  have hfinite : {p ∈ (P : Set ℝ²) | p ∈ s}.Finite :=
    P.finite_toSet.subset (fun _ hp => hp.1)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff hfinite).mp (by omega)
  have hmem (p : ℝ²) (hp : p ∈ P ∧ p ∈ s) : p ∈ t := by
    have hp' : p ∈ unitCircleTrace P t := htrace ▸ mem_unitCircleTrace.mpr hp
    exact (mem_unitCircleTrace.mp hp').2
  by_contra hne
  rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := ℝ²) finrank_euclideanSpace_fin hne hab ha.2 hb.2 hc.2
      (hmem a ha) (hmem b hb) (hmem c hc) with hca | hcb
  · exact hac hca.symm
  · exact hbc hcb.symm

/-- Distinct qualifying unit circles have distinct finite traces. -/
theorem unitCircleTrace_injOn (P : Finset ℝ²) :
    Set.InjOn (unitCircleTrace P)
      {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard} := by
  intro s hs t _ht htrace
  exact eq_of_unitCircleTrace_eq hs.2 htrace

/-- The set counted by `unitCircleCount` really is finite. -/
theorem qualifyingUnitCircles_finite (P : Finset ℝ²) :
    {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}.Finite := by
  apply Set.Finite.of_injOn (f := unitCircleTrace P)
      (t := (P.powerset : Set (Finset ℝ²)))
  · intro s _hs
    exact Finset.mem_powerset.mpr (unitCircleTrace_subset P s)
  · exact unitCircleTrace_injOn P
  · exact P.powerset.finite_toSet

/-- A configuration has at most as many qualifying circles as subsets of its points. -/
theorem unitCircleCount_le_two_pow_card (P : Finset ℝ²) :
    unitCircleCount P ≤ 2 ^ P.card := by
  unfold unitCircleCount
  calc
    _ ≤ (P.powerset : Set (Finset ℝ²)).ncard :=
      Set.ncard_le_ncard_of_injOn (unitCircleTrace P)
        (fun s _hs => Finset.mem_powerset.mpr (unitCircleTrace_subset P s))
        (unitCircleTrace_injOn P) P.powerset.finite_toSet
    _ = 2 ^ P.card := by rw [Set.ncard_coe_finset, Finset.card_powerset]

/-- There is a configuration of every finite size in the Euclidean plane. -/
theorem possibleUnitCircleCounts_nonempty (n : ℕ) :
    (possibleUnitCircleCounts n).Nonempty := by
  obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := ℝ²) n
  exact ⟨unitCircleCount P, P, hP, rfl⟩

/-- Every attainable count for `n` points satisfies the same uniform bound. -/
theorem possibleUnitCircleCounts_le_two_pow {n k : ℕ}
    (hk : k ∈ possibleUnitCircleCounts n) : k ≤ 2 ^ n := by
  rcases hk with ⟨P, hP, rfl⟩
  simpa [hP] using unitCircleCount_le_two_pow_card P

theorem possibleUnitCircleCounts_bddAbove (n : ℕ) :
    BddAbove (possibleUnitCircleCounts n) := by
  exact ⟨2 ^ n, fun _ hk => possibleUnitCircleCounts_le_two_pow hk⟩

theorem possibleUnitCircleCounts_finite (n : ℕ) :
    (possibleUnitCircleCounts n).Finite := by
  exact (Set.finite_le_nat (2 ^ n)).subset
    (fun _ hk => possibleUnitCircleCounts_le_two_pow hk)

/-- The natural-number supremum is itself an attainable count. -/
theorem maxUnitCircleCount_mem (n : ℕ) :
    maxUnitCircleCount n ∈ possibleUnitCircleCounts n := by
  exact Nat.sSup_mem (possibleUnitCircleCounts_nonempty n)
    (possibleUnitCircleCounts_bddAbove n)

/-- In particular, some `n`-point configuration attains the defined maximum. -/
theorem maxUnitCircleCount_attained (n : ℕ) :
    ∃ P : Finset ℝ², P.card = n ∧ unitCircleCount P = maxUnitCircleCount n := by
  exact maxUnitCircleCount_mem n

/-- The defined maximum is an upper bound for every configuration of that size. -/
theorem unitCircleCount_le_maxUnitCircleCount (P : Finset ℝ²) :
    unitCircleCount P ≤ maxUnitCircleCount P.card := by
  exact le_csSup (possibleUnitCircleCounts_bddAbove P.card) ⟨P, rfl, rfl⟩

/-- The defined supremum is the actual greatest attainable count. -/
theorem maxUnitCircleCount_isGreatest (n : ℕ) :
    IsGreatest (possibleUnitCircleCounts n) (maxUnitCircleCount n) := by
  exact ⟨maxUnitCircleCount_mem n,
    fun _ hk => le_csSup (possibleUnitCircleCounts_bddAbove n) hk⟩

theorem maxUnitCircleCount_le_two_pow (n : ℕ) :
    maxUnitCircleCount n ≤ 2 ^ n := by
  exact possibleUnitCircleCounts_le_two_pow (maxUnitCircleCount_mem n)


/-- Exact uniform-configuration criterion for the conjecture.  This is a reduction,
not a proof of either side. -/
theorem littleO_maxUnitCircleCount_iff_uniform :
    (fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ P : Finset ℝ², N ≤ P.card →
        (unitCircleCount P : ℝ) ≤ ε * (P.card : ℝ) ^ 2 := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h hε)
    refine ⟨N, fun P hP => ?_⟩
    have hb := hN P.card hP
    simp only [Real.norm_natCast, Real.norm_of_nonneg (sq_nonneg _)] at hb
    exact (Nat.cast_le.mpr (unitCircleCount_le_maxUnitCircleCount P)).trans hb
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    obtain ⟨P, hP, hCount⟩ := maxUnitCircleCount_attained n
    have hp := hN P (by simpa only [hP] using hn)
    simp only [Real.norm_natCast, Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [hP, hCount] using hp

/-- An equivalent formulation using only natural-number inequalities in finite
configurations.  It makes no assertion that the criterion is satisfied. -/
theorem littleO_maxUnitCircleCount_iff_nat_uniform :
    (fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) ↔
      ∀ k : ℕ, ∃ N : ℕ, ∀ P : Finset ℝ², N ≤ P.card →
        k * unitCircleCount P ≤ P.card ^ 2 := by
  rw [Asymptotics.isLittleO_iff_nat_mul_le]
  constructor
  · intro h k
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h k)
    refine ⟨N, fun P hP => ?_⟩
    have hb := hN P.card hP
    simp only [Real.norm_natCast, Real.norm_of_nonneg (sq_nonneg _)] at hb
    have hc : k * maxUnitCircleCount P.card ≤ P.card ^ 2 := by
      exact_mod_cast hb
    exact (Nat.mul_le_mul_left k (unitCircleCount_le_maxUnitCircleCount P)).trans hc
  · intro h k
    obtain ⟨N, hN⟩ := h k
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    obtain ⟨P, hP, hCount⟩ := maxUnitCircleCount_attained n
    have hp : k * maxUnitCircleCount n ≤ n ^ 2 := by
      simpa only [hP, hCount] using hN P (by simpa only [hP] using hn)
    simp only [Real.norm_natCast, Real.norm_of_nonneg (sq_nonneg _)]
    exact_mod_cast hp

/-- Exact counterexample criterion.  A disproof must supply ONE fixed integer k
and configurations of unbounded size violating the corresponding inequality. -/
theorem not_littleO_maxUnitCircleCount_iff_nat_witness :
    ¬ (fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ 2) ↔
      ∃ k : ℕ, ∀ N : ℕ, ∃ P : Finset ℝ²,
        N ≤ P.card ∧ P.card ^ 2 < k * unitCircleCount P := by
  rw [littleO_maxUnitCircleCount_iff_nat_uniform]
  push_neg
  rfl

end Erdos104

#print axioms Erdos104.littleO_maxUnitCircleCount_iff_uniform
#print axioms Erdos104.littleO_maxUnitCircleCount_iff_nat_uniform
#print axioms Erdos104.not_littleO_maxUnitCircleCount_iff_nat_witness
