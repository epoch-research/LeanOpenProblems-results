import Submission.ProgressionFiberEquivalence

/-! Relabel active cells of a finite partial partition by representative points.
This preserves every fiber, exceptional mass, and phase approximation exactly. -/
namespace Erdos3CanonicalPartialPartition
open Finset Erdos3FinitePartitionIncrement Erdos3ProgressionFiberEquivalence
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {V J I : Type*}

noncomputable def cellRepresentative (c : V → Option J) (j : J) : Option V :=
  if h : ∃ x, c x = some j then some h.choose else none

noncomputable def canonicalLabel (c : V → Option J) (x : V) : Option V :=
  (c x).bind (cellRepresentative c)

lemma representative_spec (c : V → Option J) {j : J} {y : V}
    (hy : cellRepresentative c j = some y) : c y = some j := by
  unfold cellRepresentative at hy
  split_ifs at hy with h
  · have hh := h.choose_spec
    rw [Option.some.inj hy] at hh
    exact hh

lemma representative_exists (c : V → Option J) {j : J} {x : V} (hx : c x = some j) :
    ∃ y, cellRepresentative c j = some y := by
  have h : ∃ x, c x = some j := ⟨x,hx⟩
  exact ⟨h.choose,by simp only [cellRepresentative,dif_pos h]⟩

lemma canonical_fiber_iff (c : V → Option J) {j : J} {y : V}
    (hy : cellRepresentative c j = some y) (x : V) :
    canonicalLabel c x = some y ↔ c x = some j := by
  rw [canonicalLabel,Option.bind_eq_some_iff]
  constructor
  · rintro ⟨j',hx,hj'⟩
    have hh := representative_spec c hy
    have hh' := representative_spec c hj'
    have hj : j' = j := Option.some.inj (hh'.symm.trans hh)
    simpa only [hj] using hx
  · intro hx
    exact ⟨j,hx,hy⟩

lemma canonical_none_iff (c : V → Option J) (x : V) :
    canonicalLabel c x = none ↔ c x = none := by
  cases hx : c x with
  | none => simp only [canonicalLabel,hx,Option.bind_none]
  | some j =>
    obtain ⟨y,hy⟩ := representative_exists c hx
    simp only [canonicalLabel,hx,Option.bind_some,hy,Option.some_ne_none]

lemma canonical_some_info (c : V → Option J) {x y : V}
    (hxy : canonicalLabel c x = some y) :
    ∃ j, c y = some j ∧ c x = some j ∧ ∀ z, canonicalLabel c z = some y ↔ c z = some j := by
  obtain ⟨j,hx,hj⟩ := Option.bind_eq_some_iff.mp hxy
  exact ⟨j,representative_spec c hj,hx,canonical_fiber_iff c hj⟩

lemma canonical_bad_mass [Fintype V] (c : V → Option J) :
    cellMass (canonicalLabel c) none = cellMass c none := by
  unfold cellMass
  apply expect_congr rfl
  intro x _
  rw [canonical_none_iff]

noncomputable def canonicalValue (c : V → Option J) (w : I → J → ℂ) (i : I) (y : V) : ℂ :=
  match c y with
  | none => 1
  | some j => w i j

lemma canonicalValue_norm (c : V → Option J) (w : I → J → ℂ)
    (hw : ∀ i j, ‖w i j‖ = 1) (i : I) (y : V) : ‖canonicalValue c w i y‖ = 1 := by
  unfold canonicalValue
  split <;> simp only [hw,norm_one]

lemma canonical_flat [Fintype V] (c : V → Option J) (w : I → J → ℂ)
    (f : I → V → ℂ) {ε : ℝ}
    (hflat : ∀ x j, c x = some j → ∀ i, ‖f i x-w i j‖ ≤ ε) :
    ∀ x y, canonicalLabel c x = some y → ∀ i, ‖f i x-canonicalValue c w i y‖ ≤ ε := by
  intro x y hxy i
  obtain ⟨j,hy,hx,_⟩ := canonical_some_info c hxy
  simpa only [canonicalValue,hy] using hflat x j hx i

/-- Arbitrary labels can be replaced by Fin N, uniformly in the original
label type. All good progression fibers and the exceptional mass are unchanged. -/
theorem canonical_progression_partition {N L D : ℕ} (c : Fin N → Option J)
    (w : I → J → ℂ) (f : I → Fin N → ℂ) {ε : ℝ}
    (hw : ∀ i j, ‖w i j‖ = 1)
    (hflat : ∀ x j, c x = some j → ∀ i, ‖f i x-w i j‖ ≤ ε)
    (hgeom : ∀ j, (cell c (some j)).Nonempty →
      ∃ a d : ℕ, 0 < d ∧ d ≤ D ∧ (∀ k < L, a+k*d < N) ∧
        ∀ x : Fin N, c x = some j ↔ ∃ k : Fin L, x.val = a+k.val*d) :
    ∃ c' : Fin N → Option (Fin N), ∃ w' : I → Fin N → ℂ,
      (∀ i j, ‖w' i j‖ = 1) ∧ cellMass c' none = cellMass c none ∧
      (∀ x j, c' x = some j → ∀ i, ‖f i x-w' i j‖ ≤ ε) ∧
      ∀ j, (cell c' (some j)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ D ∧ (∀ k < L, a+k*d < N) ∧
          ∀ x : Fin N, c' x = some j ↔ ∃ k : Fin L, x.val = a+k.val*d := by
  refine ⟨canonicalLabel c,canonicalValue c w,canonicalValue_norm c w hw,
    canonical_bad_mass c,canonical_flat c w f hflat,?_⟩
  intro y hy
  obtain ⟨x,hx⟩ := hy
  obtain ⟨j,hj,hxj,hfiber⟩ := canonical_some_info c ((mem_cell_iff _ _ _).mp hx)
  have hcell : (cell c (some j)).Nonempty := ⟨x,(mem_cell_iff _ _ _).mpr hxj⟩
  obtain ⟨a,d,hd,hdb,hpoints,hgeom'⟩ := hgeom j hcell
  exact ⟨a,d,hd,hdb,hpoints,fun z ↦ (hfiber z).trans (hgeom' z)⟩

#print axioms canonical_progression_partition
end Erdos3CanonicalPartialPartition
