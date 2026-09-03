import Submission.ClassThinning

/-!
Explicit special-unitary conjugators exhibit growing balanced bicliques in
another proposed class-graph host. This is an obstruction to that construction,
not a disproof of the extremal conjecture.
-/

open Matrix SimpleGraph Classical

set_option maxHeartbeats 2000000

namespace Erdos714SU3Class

variable {F : Type*} [Field F] [StarRing F]

abbrev SU3 (F : Type*) [Field F] [StarRing F] := Matrix.specialUnitaryGroup (Fin 3) F

lemma coe_unitary_ne_zero (t : unitary F) : (t : F) ≠ 0 :=
  (Unitary.isUnit_coe (U := t)).ne_zero

lemma star_unitary (t : unitary F) : star (t : F) = (t : F)⁻¹ := by
  exact Unitary.coe_inv t

/-- A convenient diagonal two-parameter subgroup of SU(3). -/
def diag (u v : unitary F) : SU3 F :=
  ⟨Matrix.diagonal ![(u : F), (v : F), (((u*v)⁻¹ : unitary F) : F)], by
    apply Matrix.mem_specialUnitaryGroup_iff.mpr
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      rw [Matrix.diagonal_eq_diagonal_iff]
      intro i
      fin_cases i
      · exact u.property.2
      · exact v.property.2
      · exact ((u*v)⁻¹).property.2
    · rw [Matrix.det_diagonal]
      simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Fin.prod_univ_zero, mul_one]
      change ((u : F) * ((v : F) * (((u*v)⁻¹ : unitary F) : F))) = 1
      rw [← mul_assoc, ← Submonoid.coe_mul, ← Submonoid.coe_mul, mul_inv_cancel]
      rfl⟩

/-- A unitary companion-type matrix with one fixed characteristic polynomial. -/
def center (a v : F) (hv : v*star v = 1-a*star a) : SU3 F :=
  ⟨!![0,-star a,v; 1,0,0; 0,star v,a], by
    apply Matrix.mem_specialUnitaryGroup_iff.mpr
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      all_goals first | ring1 | linear_combination hv
    · simp [Matrix.det_fin_three]
      linear_combination hv⟩

lemma norm_twist (a v : F) (hv : v*star v = 1-a*star a) (e : unitary F) :
    (v*(e:F)^3)*star (v*(e:F)^3) = 1-a*star a := by
  calc
    _ = (v*star v) * (((e:F)*star (e:F))^3) := by rw [StarMul.star_mul, star_pow]; ring
    _ = _ := by rw [e.property.2, one_pow, mul_one, hv]

def left (t : unitary F) : SU3 F := diag (t^3) ((t⁻¹)^3)

def right (a v : F) (hv : v*star v = 1-a*star a) (e : unitary F) : SU3 F :=
  center a (v*(e:F)^3) (norm_twist a v hv e)

def conjugator (t e : unitary F) : SU3 F := diag (e*(t⁻¹)^2) (e*t)

/-- The class membership is certified by an actual special-unitary conjugator. -/
theorem intertwining (a v : F) (hv : v*star v = 1-a*star a) (t e : unitary F) :
    left t * conjugator t e * center a v hv = right a v hv e * conjugator t e := by
  apply Subtype.ext
  change ((left t).val * (conjugator t e).val) * (center a v hv).val =
    (right a v hv e).val * (conjugator t e).val
  have ht := coe_unitary_ne_zero t
  have he := coe_unitary_ne_zero e
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [left, right, conjugator, center, diag, Unitary.coe_inv, StarMul.star_mul, star_pow, star_unitary]
  all_goals field_simp

/-- Distinct cubes give injective parameterizations on both sides of the grid. -/
theorem not_free (a v : F) (hv : v*star v = 1-a*star a) (hv0 : v ≠ 0)
    {r : ℕ} (t : Fin r → unitary F) (hc : Function.Injective (fun i => (t i : F)^3)) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714ClassGraph.graph (center a v hv)) := by
  let L : Fin r ↪ SU3 F := ⟨fun i => left (t i), by
    intro i j h
    apply hc
    have he := congrArg (fun g : SU3 F => g.val 0 0) h
    simpa [left, diag] using he⟩
  let R : Fin r ↪ SU3 F := ⟨fun i => right a v hv (t i), by
    intro i j h
    apply hc
    apply mul_left_cancel₀ hv0
    have he := congrArg (fun g : SU3 F => g.val 0 2) h
    exact he⟩
  apply Erdos714ClassGraph.not_free_of_intertwining (center a v hv) L R
    (fun i j => conjugator (t i) (t j))
  intro i j
  exact intertwining a v hv (t i) (t j)

/-- The same grid bounds every free edge thinning of the class host. -/
theorem thinning_bound [Fintype F] (a v : F) (hv : v*star v = 1-a*star a)
    (hv0 : v ≠ 0) (H : SimpleGraph (SU3 F ⊕ SU3 F)) (r s : ℕ)
    (t : Fin s → unitary F) (hc : Function.Injective (fun i => (t i : F)^3))
    (hHG : H ≤ Erdos714ClassGraph.graph (center a v hv))
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    s^2 * H.edgeFinset.card ≤
      extremalNumber (2*s) (completeBipartiteGraph (Fin r) (Fin r)) *
        (Erdos714ClassGraph.graph (center a v hv)).edgeFinset.card := by
  exact Erdos714ClassGraph.thinning_bound (center a v hv) H r s hHG hH
    (not_free a v hv hv0 t hc)

open Finset

/-- At most three unitary scalars have any prescribed cube. -/
lemma cube_fiber_bound [Fintype F] (c : F) :
    (univ.filter (fun t : unitary F => (t : F)^3=c)).card ≤ 3 := by
  apply (show _ ≤ (Polynomial.nthRoots 3 c).toFinset.card from ?_).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 c))
  apply Finset.card_le_card_of_injOn (fun t : unitary F => (t : F))
  · intro t ht
    change (t : F) ∈ (Polynomial.nthRoots 3 c).toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by decide : 0 < 3)]
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu h
    exact Subtype.ext h

/-- Cubing loses at most a factor of three in the number of parameters. -/
lemma cube_count [Fintype F] :
    Fintype.card (unitary F) ≤
      3 * (univ.image (fun t : unitary F => (t : F)^3)).card := by
  simpa only [Finset.card_univ] using
    Finset.card_le_mul_card_image (univ : Finset (unitary F)) 3
      (fun c _ => cube_fiber_bound c)

/-- A cardinality-only criterion for a balanced grid in the special-unitary host. -/
theorem not_free_of_card [Fintype F] (a v : F)
    (hv : v*star v = 1-a*star a) (hv0 : v ≠ 0) (r : ℕ)
    (hcard : 3*(r-1) < Fintype.card (unitary F)) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714ClassGraph.graph (center a v hv)) := by
  let C : Finset F := univ.image (fun t : unitary F => (t : F)^3)
  have hC : r ≤ C.card := by
    have h := cube_count (F := F)
    change Fintype.card (unitary F) ≤ 3*C.card at h
    omega
  obtain ⟨g : Fin r ↪ F, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := C) (by simpa using hC)
  have hex : ∀ i, ∃ t : unitary F, (t : F)^3 = g i := by
    intro i
    have hi := hg ⟨i,rfl⟩
    obtain ⟨t,ht,he⟩ := mem_image.mp hi
    exact ⟨t,he⟩
  choose t ht using hex
  apply not_free a v hv hv0 t
  intro i j hij
  apply g.injective
  simpa only [ht] using hij

/-- Every free edge thinning is controlled by the number of unitary scalars. -/
theorem thinning_bound_of_card [Fintype F] (a v : F)
    (hv : v*star v = 1-a*star a) (hv0 : v ≠ 0)
    (H : SimpleGraph (SU3 F ⊕ SU3 F)) (r s : ℕ)
    (hcard : 3*(s-1) < Fintype.card (unitary F))
    (hHG : H ≤ Erdos714ClassGraph.graph (center a v hv))
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    s^2 * H.edgeFinset.card ≤
      extremalNumber (2*s) (completeBipartiteGraph (Fin r) (Fin r)) *
        (Erdos714ClassGraph.graph (center a v hv)).edgeFinset.card := by
  exact Erdos714ClassGraph.thinning_bound (center a v hv) H r s hHG hH
    (not_free_of_card a v hv hv0 s hcard)

end Erdos714SU3Class

#print axioms Erdos714SU3Class.intertwining

#print axioms Erdos714SU3Class.not_free
#print axioms Erdos714SU3Class.thinning_bound

#print axioms Erdos714SU3Class.cube_count
#print axioms Erdos714SU3Class.not_free_of_card
#print axioms Erdos714SU3Class.thinning_bound_of_card
