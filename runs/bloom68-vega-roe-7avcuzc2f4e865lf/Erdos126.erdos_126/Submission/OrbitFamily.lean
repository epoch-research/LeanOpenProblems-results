import FormalConjecturesUtil

/-!
# Mixed negation-orbits of a finite vertex set

The mixed orbits form a disjoint family. A Boolean labeling which separates
non-self-opposite residues is constant on each side of every mixed orbit.
This gives the cross-entry identity and same-side entry bound. The residual
self-opposite kernel is positive semidefinite, by a finite-image sum of squares.
Additive homomorphisms enlarge orbits and give one-way laminarity of the families.
No finiteness assumption on the residue groups is used.
-/

namespace Erdos126Orbit

open scoped BigOperators
open Finset

noncomputable section

variable {V G : Type*} [Fintype V] [AddCommGroup G] [DecidableEq G]

/-- The vertices whose values agree up to sign with the value at `i`. -/
def orbit (v : V → G) (i : V) : Finset V :=
  univ.filter (fun j => v j = v i ∨ v j = -v i)

/-- A support contains both sides of a non-self-opposite residue pair. -/
def mixed (v : V → G) (U : Finset V) : Prop :=
  ∃ i ∈ U, ∃ j ∈ U, v i = -v j ∧ v i ≠ -v i

/-- The distinct mixed negation-orbits. -/
def family (v : V → G) : Finset (Finset V) := by
  classical
  exact (univ.image (orbit v)).filter (mixed v)

section Orbits

variable (v : V → G)

@[simp] theorem mem_orbit {i j : V} :
    i ∈ orbit v j ↔ v i = v j ∨ v i = -v j := by
  simp [orbit]

@[simp] theorem self_mem_orbit (i : V) : i ∈ orbit v i :=
  (mem_orbit v).2 (Or.inl rfl)

theorem mem_orbit_symm {i j : V} (h : i ∈ orbit v j) : j ∈ orbit v i := by
  rcases (mem_orbit v).1 h with h | h
  · exact (mem_orbit v).2 (Or.inl h.symm)
  · apply (mem_orbit v).2
    right
    simpa only [neg_neg] using congrArg Neg.neg h.symm

/-- Any member can be used as the representative of an orbit. -/
theorem orbit_eq_of_mem {i j : V} (h : i ∈ orbit v j) :
    orbit v i = orbit v j := by
  ext k
  simp only [mem_orbit]
  rcases (mem_orbit v).1 h with h | h
  · rw [h]
  · rw [h, neg_neg]
    exact or_comm

theorem orbit_eq_of_common_mem {i j k : V}
    (hi : k ∈ orbit v i) (hj : k ∈ orbit v j) : orbit v i = orbit v j :=
  (orbit_eq_of_mem v hi).symm.trans (orbit_eq_of_mem v hj)

theorem orbit_eq_iff {i j : V} :
    orbit v i = orbit v j ↔ v i = v j ∨ v i = -v j := by
  constructor
  · intro h
    apply (mem_orbit v).1
    rw [← h]
    exact self_mem_orbit v i
  · intro h
    exact orbit_eq_of_mem v ((mem_orbit v).2 h)

theorem orbit_disjoint_or_eq (i j : V) :
    Disjoint (orbit v i) (orbit v j) ∨ orbit v i = orbit v j := by
  classical
  by_cases h : Disjoint (orbit v i) (orbit v j)
  · exact Or.inl h
  · obtain ⟨k, hi, hj⟩ := Finset.not_disjoint_iff.1 h
    exact Or.inr (orbit_eq_of_common_mem v hi hj)

/-- Being non-self-opposite is constant on an orbit. -/
theorem nonself_of_mem_orbit {i j : V} (hi : i ∈ orbit v j)
    (hj : v j ≠ -v j) : v i ≠ -v i := by
  rcases (mem_orbit v).1 hi with h | h
  · simpa only [h] using hj
  · rw [h, neg_neg]
    exact Ne.symm hj

end Orbits

section Families

variable (v : V → G)

@[simp] theorem mem_family {U : Finset V} :
    U ∈ family v ↔ (∃ i, orbit v i = U) ∧ mixed v U := by
  classical
  simp only [family, mem_filter, mem_image, mem_univ, true_and]

theorem mixed_of_mem_family {U : Finset V} (hU : U ∈ family v) : mixed v U :=
  ((mem_family v).1 hU).2

theorem exists_orbit_of_mem_family {U : Finset V} (hU : U ∈ family v) :
    ∃ i, orbit v i = U :=
  ((mem_family v).1 hU).1

/-- A family member is exactly the orbit of any of its vertices. -/
theorem eq_orbit_of_mem_family {U : Finset V} {i : V}
    (hU : U ∈ family v) (hi : i ∈ U) : U = orbit v i := by
  obtain ⟨k, rfl⟩ := exists_orbit_of_mem_family v hU
  exact (orbit_eq_of_mem v hi).symm

theorem value_eq_or_neg_of_mem_family {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) :
    v i = v j ∨ v i = -v j := by
  rw [eq_orbit_of_mem_family v hU hj] at hi
  exact (mem_orbit v).1 hi

theorem card_two_le_of_mem_family {U : Finset V} (hU : U ∈ family v) :
    2 ≤ U.card := by
  obtain ⟨i, hi, j, hj, hij, hni⟩ := mixed_of_mem_family v hU
  apply Finset.one_lt_card.2
  refine ⟨i, hi, j, hj, ?_⟩
  intro h
  subst j
  exact hni hij

theorem nonself_of_mem_family {U : Finset V} {i : V}
    (hU : U ∈ family v) (hi : i ∈ U) : v i ≠ -v i := by
  obtain ⟨a, ha, b, hb, hab, hna⟩ := mixed_of_mem_family v hU
  rw [eq_orbit_of_mem_family v hU ha] at hi
  exact nonself_of_mem_orbit v hi hna

/-- Every vertex in a mixed orbit has an opposite-valued witness in that orbit. -/
theorem exists_opposite_of_mem_family {U : Finset V} {i : V}
    (hU : U ∈ family v) (hi : i ∈ U) : ∃ j ∈ U, v i = -v j := by
  obtain ⟨a, ha, b, hb, hab, hna⟩ := mixed_of_mem_family v hU
  rcases value_eq_or_neg_of_mem_family v hU hi ha with h | h
  · exact ⟨b, hb, h.trans hab⟩
  · exact ⟨a, ha, h⟩

theorem family_disjoint_or_eq {U W : Finset V}
    (hU : U ∈ family v) (hW : W ∈ family v) : Disjoint U W ∨ U = W := by
  obtain ⟨i, rfl⟩ := exists_orbit_of_mem_family v hU
  obtain ⟨j, rfl⟩ := exists_orbit_of_mem_family v hW
  exact orbit_disjoint_or_eq v i j

/-- An opposite-valued non-self-opposite pair generates a member of the family. -/
theorem orbit_mem_family_of_opposite {i j : V}
    (hij : v i = -v j) (hni : v i ≠ -v i) : orbit v i ∈ family v := by
  apply (mem_family v).2
  refine ⟨⟨i, rfl⟩, i, self_mem_orbit v i, j, ?_, hij, hni⟩
  exact mem_orbit_symm v ((mem_orbit v).2 (Or.inr hij))

theorem orbit_mem_family_iff (i : V) :
    orbit v i ∈ family v ↔ v i ≠ -v i ∧ ∃ j, v i = -v j := by
  constructor
  · intro hi
    obtain ⟨j, hj, hij⟩ := exists_opposite_of_mem_family v hi (self_mem_orbit v i)
    exact ⟨nonself_of_mem_family v hi (self_mem_orbit v i), j, hij⟩
  · rintro ⟨hni, j, hij⟩
    exact orbit_mem_family_of_opposite v hij hni

end Families

section Signs

/-- In a two-element type, two elements different from a third one agree. -/
theorem bool_eq_of_ne_common {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

variable (v : V → G) (σ : V → Bool)
    (hσ : ∀ i j, v i = -v j → v i ≠ -v i → σ i ≠ σ j)

include hσ

/-- An opposite witness forces equal values in a mixed orbit to have equal signs. -/
theorem sign_eq_of_value_eq {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) (hij : v i = v j) :
    σ i = σ j := by
  obtain ⟨k, hk, hik⟩ := exists_opposite_of_mem_family v hU hi
  exact bool_eq_of_ne_common
    (hσ i k hik (nonself_of_mem_family v hU hi))
    (hσ j k (hij.symm.trans hik) (nonself_of_mem_family v hU hj))

theorem sign_ne_iff {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) :
    σ i ≠ σ j ↔ v i = -v j := by
  constructor
  · intro hne
    rcases value_eq_or_neg_of_mem_family v hU hi hj with h | h
    · exact False.elim (hne (sign_eq_of_value_eq v σ hσ hU hi hj h))
    · exact h
  · intro hij
    exact hσ i j hij (nonself_of_mem_family v hU hi)

theorem sign_eq_iff {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) :
    σ i = σ j ↔ v i = v j := by
  constructor
  · intro heq
    rcases value_eq_or_neg_of_mem_family v hU hi hj with h | h
    · exact h
    · exact False.elim (hσ i j h (nonself_of_mem_family v hU hi) heq)
  · exact sign_eq_of_value_eq v σ hσ hU hi hj

end Signs

section Entries

open scoped Classical

variable (v : V → G)

/-- Co-membership counts the unique mixed orbit, when that orbit exists. -/
theorem sum_members_eq (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0) =
      if orbit v i ∈ family v ∧ j ∈ orbit v i then 1 else 0 := by
  classical
  by_cases hi : orbit v i ∈ family v
  · rw [Finset.sum_eq_single (orbit v i)]
    · simp [hi]
    · intro U hU hne
      by_cases hiU : i ∈ U
      · exact False.elim (hne (eq_orbit_of_mem_family v hU hiU))
      · simp [hiU]
    · intro hnot
      exact False.elim (hnot hi)
  · rw [if_neg (fun h => hi h.1)]
    apply Finset.sum_eq_zero
    intro U hU
    have hiU : i ∉ U := by
      intro hit
      apply hi
      simpa only [← eq_orbit_of_mem_family v hU hit] using hU
    simp [hiU]

theorem sum_members_le_one (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_members_eq]
  split_ifs <;> norm_num

variable (σ : V → Bool)
    (hσ : ∀ i j, v i = -v j → v i ≠ -v i → σ i ≠ σ j)

include hσ

/-- Opposite-sign entries recover precisely the non-self-opposite pairs. -/
theorem sum_cross_entries (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i ≠ σ j then (1 : ℝ) else 0) =
      if v i = -v j ∧ v i ≠ -v i then 1 else 0 := by
  classical
  by_cases h : v i = -v j ∧ v i ≠ -v i
  · have hiF := orbit_mem_family_of_opposite v h.1 h.2
    have hj : j ∈ orbit v i := mem_orbit_symm v ((mem_orbit v).2 (Or.inr h.1))
    have hs := hσ i j h.1 h.2
    calc
      (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i ≠ σ j then (1 : ℝ) else 0) =
          ∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0 := by
            simp [hs]
      _ = 1 := by rw [sum_members_eq]; simp [hiF, hj]
      _ = if v i = -v j ∧ v i ≠ -v i then 1 else 0 := (if_pos h).symm
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro U hU
    apply if_neg
    rintro ⟨hi, hj, hne⟩
    exact h ⟨(sign_ne_iff v σ hσ hU hi hj).1 hne, nonself_of_mem_family v hU hi⟩

/-- Equal-sign entries are bounded by the non-self-opposite equal-value kernel. -/
theorem sum_same_entries_le (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i = σ j then (1 : ℝ) else 0) ≤
      if v i = v j ∧ v i ≠ -v i then 1 else 0 := by
  classical
  by_cases h : v i = v j ∧ v i ≠ -v i
  · rw [if_pos h]
    calc
      (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i = σ j then (1 : ℝ) else 0) ≤
          ∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro U hU
            by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;>
              by_cases hs : σ i = σ j <;> simp [hi, hj, hs]
      _ ≤ 1 := sum_members_le_one v i j
  · rw [if_neg h]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro U hU
    apply if_neg
    rintro ⟨hi, hj, heq⟩
    exact h ⟨(sign_eq_iff v σ hσ hU hi hj).1 heq, nonself_of_mem_family v hU hi⟩

end Entries

section PositiveSemidefinite

variable {A : Type*} [DecidableEq A]

/-- An equality kernel restricted to any collection of values is a sum of squares.
Only the finite image of the value map is used; the value type need not be finite. -/
theorem equality_kernel_eq_sum_sq (w : V → A) (p : A → Prop) [DecidablePred p]
    (z : V → ℝ) :
    (∑ i, ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0)) =
      ∑ a ∈ (univ.image w).filter p,
        (∑ i ∈ univ.filter (fun i => w i = a), z i) ^ 2 := by
  classical
  calc
    (∑ i, ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0)) =
        ∑ a ∈ univ.image w, ∑ i ∈ univ.filter (fun i => w i = a),
          ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i)) _).symm
    _ = ∑ a ∈ univ.image w,
        if p a then (∑ i ∈ univ.filter (fun i => w i = a), z i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hp : p a
      · rw [if_pos hp, pow_two, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hwi : w i = a := (Finset.mem_filter.1 hi).2
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hwj : w j = a
        · simp [hwi, hwj, hp]
        · simp [hwi, hp, hwj, Ne.symm hwj]
      · rw [if_neg hp]
        apply Finset.sum_eq_zero
        intro i hi
        have hwi : w i = a := (Finset.mem_filter.1 hi).2
        simp [hwi, hp]
    _ = ∑ a ∈ (univ.image w).filter p,
        (∑ i ∈ univ.filter (fun i => w i = a), z i) ^ 2 :=
      (Finset.sum_filter _ _).symm

theorem equality_kernel_nonneg (w : V → A) (p : A → Prop) [DecidablePred p]
    (z : V → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0) := by
  rw [equality_kernel_eq_sum_sq]
  exact Finset.sum_nonneg (fun a _ => sq_nonneg _)

/-- The baseline kernel groups into squares over self-opposite residue classes. -/
theorem baseline_eq_sum_sq (v : V → G) (z : V → ℝ) :
    (∑ i, ∑ j, z i * z j * (if v i = v j ∧ v i = -v i then (1 : ℝ) else 0)) =
      ∑ a ∈ (univ.image v).filter (fun a => a = -a),
        (∑ i ∈ univ.filter (fun i => v i = a), z i) ^ 2 :=
  equality_kernel_eq_sum_sq v (fun a => a = -a) z

/-- Positive semidefiniteness of the self-opposite baseline kernel. -/
theorem baseline_psd (v : V → G) (z : V → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * (if v i = v j ∧ v i = -v i then (1 : ℝ) else 0) :=
  equality_kernel_nonneg v (fun a => a = -a) z

end PositiveSemidefinite

section Maps

variable {H : Type*} [AddCommGroup H] [DecidableEq H]
    (v : V → G) (f : G →+ H)

/-- Mapping the residues by an additive homomorphism can only enlarge an orbit. -/
theorem orbit_subset_map (i : V) :
    orbit v i ⊆ orbit (fun x => f (v x)) i := by
  intro j hj
  rcases (mem_orbit v).1 hj with h | h
  · exact (mem_orbit (fun x => f (v x))).2 (Or.inl (congrArg f h))
  · apply (mem_orbit (fun x => f (v x))).2
    right
    simpa only [map_neg] using congrArg f h

/-- Intersecting mixed orbits at two mapped levels are nested in the map direction. -/
theorem family_map_subset_of_common_mem {U W : Finset V} {i : V}
    (hU : U ∈ family v) (hW : W ∈ family (fun x => f (v x)))
    (hiU : i ∈ U) (hiW : i ∈ W) : U ⊆ W := by
  rw [eq_orbit_of_mem_family v hU hiU,
    eq_orbit_of_mem_family (fun x => f (v x)) hW hiW]
  exact orbit_subset_map v f i

theorem family_map_disjoint_or_subset {U W : Finset V}
    (hU : U ∈ family v) (hW : W ∈ family (fun x => f (v x))) :
    Disjoint U W ∨ U ⊆ W := by
  classical
  by_cases hd : Disjoint U W
  · exact Or.inl hd
  · obtain ⟨i, hiU, hiW⟩ := Finset.not_disjoint_iff.1 hd
    exact Or.inr (family_map_subset_of_common_mem v f hU hW hiU hiW)

end Maps

end

end Erdos126Orbit
