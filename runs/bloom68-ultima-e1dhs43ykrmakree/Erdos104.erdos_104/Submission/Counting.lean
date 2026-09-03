import FormalConjecturesUtil

/-!
# Finiteness and attainment for the counting definitions in Erdős Problem 104

This standalone file copies only the three definitions from `Submission/Spec.lean`.
It does not import that file or use its conjecture or disproof declarations.
The bound proved here is the elementary bound `2 ^ P.card`, not the main conjecture.
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

end Erdos104
