import FormalConjecturesUtil

/-!
# An elementary quadratic bound for Erdős Problem 104

This standalone file copies the definition of `unitCircleCount` from `Spec.lean`,
without importing that file.  A qualifying circle contains at least three
unordered pairs of configuration points, and each pair belongs to at most two
unit circles.  Double counting gives `3 * unitCircleCount P ≤ P.card * (P.card - 1)`.
This does not assert the little-o conjecture.
-/

open scoped EuclideanGeometry

namespace CircleQuadratic

open EuclideanGeometry

/-- The number of distinct unit circles containing at least three points of `P`. -/
noncomputable def unitCircleCount (P : Finset ℝ²) : ℕ :=
  Set.ncard {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}

/-- The finite set of configuration points on a circle. -/
noncomputable def circleTrace (P : Finset ℝ²) (s : Sphere ℝ²) : Finset ℝ² := by
  classical
  exact P.filter (fun p => p ∈ s)

@[simp]
theorem mem_circleTrace {P : Finset ℝ²} {s : Sphere ℝ²} {p : ℝ²} :
    p ∈ circleTrace P s ↔ p ∈ P ∧ p ∈ s := by
  classical
  simp [circleTrace]

theorem circleTrace_subset (P : Finset ℝ²) (s : Sphere ℝ²) : circleTrace P s ⊆ P := by
  intro p hp
  exact (mem_circleTrace.mp hp).1

@[simp]
theorem coe_circleTrace (P : Finset ℝ²) (s : Sphere ℝ²) :
    (circleTrace P s : Set ℝ²) = {p ∈ (P : Set ℝ²) | p ∈ s} := by
  ext p
  simp

/-- Three distinct common points determine a circle, so its trace determines it. -/
theorem eq_of_circleTrace_eq {P : Finset ℝ²} {s t : Sphere ℝ²}
    (hs : 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard)
    (htrace : circleTrace P s = circleTrace P t) : s = t := by
  have hfinite : {p ∈ (P : Set ℝ²) | p ∈ s}.Finite :=
    P.finite_toSet.subset (fun _ hp => hp.1)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff hfinite).mp (by omega)
  have hmem (p : ℝ²) (hp : p ∈ P ∧ p ∈ s) : p ∈ t := by
    have hp' : p ∈ circleTrace P t := htrace ▸ mem_circleTrace.mpr hp
    exact (mem_circleTrace.mp hp').2
  by_contra hne
  rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := ℝ²) finrank_euclideanSpace_fin hne hab ha.2 hb.2 hc.2
      (hmem a ha) (hmem b hb) (hmem c hc) with hca | hcb
  · exact hac hca.symm
  · exact hbc hcb.symm

/-- The qualifying circles form a finite set: their traces inject into the powerset of `P`. -/
theorem qualifyingUnitCircles_finite (P : Finset ℝ²) :
    {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}.Finite := by
  apply Set.Finite.of_injOn (f := circleTrace P)
      (t := (P.powerset : Set (Finset ℝ²)))
  · intro s _hs
    exact Finset.mem_powerset.mpr (circleTrace_subset P s)
  · intro s hs t _ht htrace
    exact eq_of_circleTrace_eq hs.2 htrace
  · exact P.powerset.finite_toSet

/-- Duality: a point on a unit circle has the circle's center on its own unit circle. -/
theorem center_mem_unitCircle {s : Sphere ℝ²} {p : ℝ²}
    (hs : s.radius = 1) (hp : p ∈ s) : s.center ∈ (⟨p, 1⟩ : Sphere ℝ²) := by
  change dist s.center p = 1
  exact (mem_sphere'.mp hp).trans hs

/-- Through two distinct points there are at most two unit circles.

Their centers lie in the intersection of the unit circles centered at the two points.
-/
theorem unitCircle_eq_or_eq {a b : ℝ²} (hab : a ≠ b) {s t u : Sphere ℝ²}
    (hs : s.radius = 1) (ht : t.radius = 1) (hu : u.radius = 1)
    (has : a ∈ s) (hbs : b ∈ s) (hat : a ∈ t) (hbt : b ∈ t)
    (hau : a ∈ u) (hbu : b ∈ u) (hst : s ≠ t) : u = s ∨ u = t := by
  have hdual : (⟨a, 1⟩ : Sphere ℝ²) ≠ ⟨b, 1⟩ := by
    intro h
    exact hab (congrArg Sphere.center h)
  have hcenters : s.center ≠ t.center := by
    intro h
    exact hst (Sphere.ext h (hs.trans ht.symm))
  rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := ℝ²) finrank_euclideanSpace_fin hdual hcenters
      (center_mem_unitCircle hs has) (center_mem_unitCircle ht hat)
      (center_mem_unitCircle hu hau) (center_mem_unitCircle hs hbs)
      (center_mem_unitCircle ht hbt) (center_mem_unitCircle hu hbu) with h | h
  · exact Or.inl (Sphere.ext h (hu.trans hs.symm))
  · exact Or.inr (Sphere.ext h (hu.trans ht.symm))

open scoped Classical in
/-- In a finite family of unit circles, a pair of distinct points has degree at most two. -/
theorem card_circles_through_pair_le_two (S : Finset (Sphere ℝ²)) {a b : ℝ²}
    (hab : a ≠ b) (hS : ∀ s ∈ S, s.radius = 1) :
    (S.filter (fun s => a ∈ s ∧ b ∈ s)).card ≤ 2 := by
  classical
  by_contra! h
  obtain ⟨s, t, u, hs, ht, hu, hst, hsu, htu⟩ := Finset.two_lt_card_iff.mp h
  rcases Finset.mem_filter.mp hs with ⟨hsS, has, hbs⟩
  rcases Finset.mem_filter.mp ht with ⟨htS, hat, hbt⟩
  rcases Finset.mem_filter.mp hu with ⟨huS, hau, hbu⟩
  rcases unitCircle_eq_or_eq hab (hS s hsS) (hS t htS) (hS u huS)
      has hbs hat hbt hau hbu hst with hus | hut
  · exact hsu hus.symm
  · exact htu hut.symm

open scoped Classical in
/-- The unordered pairs on a circle are exactly the two-element subsets of its trace. -/
theorem pairs_on_circle (P : Finset ℝ²) (s : Sphere ℝ²) :
    (P.powersetCard 2).filter (fun q => ∀ p ∈ q, p ∈ s) =
      (circleTrace P s).powersetCard 2 := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hqP, hqcard⟩, hqs⟩
    exact ⟨fun p hp => mem_circleTrace.mpr ⟨hqP hp, hqs p hp⟩, hqcard⟩
  · rintro ⟨hqt, hqcard⟩
    exact ⟨⟨fun p hp => (mem_circleTrace.mp (hqt hp)).1, hqcard⟩,
      fun p hp => (mem_circleTrace.mp (hqt hp)).2⟩

open scoped Classical in
/-- Each qualifying circle contains at least three unordered pairs. -/
theorem three_le_card_pairs_on_circle {P : Finset ℝ²} {s : Sphere ℝ²}
    (hs : 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard) :
    3 ≤ ((P.powersetCard 2).filter (fun q => ∀ p ∈ q, p ∈ s)).card := by
  classical
  have ht : 3 ≤ (circleTrace P s).card := by
    simpa only [← coe_circleTrace, Set.ncard_coe_finset] using hs
  rw [pairs_on_circle, Finset.card_powersetCard]
  simpa using Nat.choose_le_choose 2 ht

/-- Double counting incidences between qualifying circles and unordered point pairs. -/
theorem three_mul_unitCircleCount_le_two_mul_choose (P : Finset ℝ²) :
    3 * unitCircleCount P ≤ 2 * P.card.choose 2 := by
  classical
  let C := (qualifyingUnitCircles_finite P).toFinset
  have hC (s : Sphere ℝ²) : s ∈ C ↔
      s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard := by
    exact Set.Finite.mem_toFinset _
  have hCcard : C.card = unitCircleCount P :=
    (Set.ncard_eq_toFinset_card _ (qualifyingUnitCircles_finite P)).symm
  have hcount : C.card * 3 ≤ (P.powersetCard 2).card * 2 := by
    apply Finset.card_mul_le_card_mul (fun s q => ∀ p ∈ q, p ∈ s)
    · intro s hs
      exact three_le_card_pairs_on_circle ((hC s).mp hs).2
    · intro q hq
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
      simpa only [Finset.bipartiteBelow, Finset.mem_insert, Finset.mem_singleton,
        forall_eq_or_imp, forall_eq] using
        card_circles_through_pair_le_two C hab (fun s hs => ((hC s).mp hs).1)
  simpa only [hCcard, Finset.card_powersetCard, Nat.mul_comm] using hcount

/-- The elementary quadratic upper bound for the number of qualifying unit circles. -/
theorem three_mul_unitCircleCount_le_card_mul_pred (P : Finset ℝ²) :
    3 * unitCircleCount P ≤ P.card * (P.card - 1) := by
  calc
    3 * unitCircleCount P ≤ 2 * P.card.choose 2 :=
      three_mul_unitCircleCount_le_two_mul_choose P
    _ = (P.card * (P.card - 1) / 2) * 2 := by
      rw [Nat.choose_two_right, Nat.mul_comm]
    _ ≤ P.card * (P.card - 1) := Nat.div_mul_le_self _ _

/-- A slightly weaker form avoiding subtraction. -/
theorem three_mul_unitCircleCount_le_card_sq (P : Finset ℝ²) :
    3 * unitCircleCount P ≤ P.card ^ 2 := by
  calc
    3 * unitCircleCount P ≤ P.card * (P.card - 1) :=
      three_mul_unitCircleCount_le_card_mul_pred P
    _ ≤ P.card * P.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = P.card ^ 2 := (pow_two _).symm

/-- In particular the count is bounded by the square of the number of points. -/
theorem unitCircleCount_le_card_sq (P : Finset ℝ²) :
    unitCircleCount P ≤ P.card ^ 2 := by
  have h := three_mul_unitCircleCount_le_card_sq P
  omega

end CircleQuadratic

#print axioms CircleQuadratic.qualifyingUnitCircles_finite
#print axioms CircleQuadratic.three_mul_unitCircleCount_le_card_mul_pred
#print axioms CircleQuadratic.unitCircleCount_le_card_sq
