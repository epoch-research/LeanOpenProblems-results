import FormalConjecturesUtil

/-! Conditioning away a complete, disjoint pure-power family preserves a
lower mass bound for every present cylinder disjoint from the lower pure
classes. This is an auxiliary finite-measure lemma, not an odd-cover theorem. -/
namespace Erdos7PureProjectionLower
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def mass {Ω : Type*} (μ : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ x ∈ S, μ x
noncomputable def geom (r : ℝ) (E : ℕ) : ℝ := ∑ j ∈ Finset.range E, r^(j+1)

def pureUnion {Ω : Type*} [DecidableEq Ω] (B : ℕ → Finset Ω) (E : ℕ) : Finset Ω :=
  (Finset.range E).biUnion (fun j => B (j+1))

lemma mass_mono {Ω : Type*} (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    {S T : Finset Ω} (hST : S ⊆ T) : mass μ S ≤ mass μ T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun x _ _ => hμ x)

lemma geom_nonneg (r : ℝ) (hr : 0 ≤ r) (E : ℕ) : 0 ≤ geom r E :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg hr _)

lemma geom_mono (r : ℝ) (hr : 0 ≤ r) : Monotone (geom r) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun _ _ _ => pow_nonneg hr _)

lemma geometric_tail (r : ℝ) (a E : ℕ) :
    (∑ j ∈ Finset.range E, r^(a+j+1)) = r^a*geom r E := by
  simp only [geom, Finset.mul_sum, ← pow_add]
  apply Finset.sum_congr rfl
  intro j _
  congr 1

lemma pureUnion_mass {Ω : Type*} [DecidableEq Ω] (μ : Ω → ℝ)
    (B : ℕ → Finset Ω) (E : ℕ) (r : ℝ)
    (hB : ∀ j, 1 ≤ j → j ≤ E → mass μ (B j) = r^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j → Disjoint (B i) (B j)) :
    mass μ (pureUnion B E) = geom r E := by
  unfold mass pureUnion
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro j hj
    exact hB (j+1) (by omega) (by have := Finset.mem_range.mp hj; omega)
  · intro i hi j hj hij
    apply hdis (i+1) (j+1) (by omega) (by have := Finset.mem_range.mp hi; omega)
      (by omega) (by have := Finset.mem_range.mp hj; omega) (by omega)

lemma pure_complement_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (hm : (∑ x, μ x) = 1) (B : ℕ → Finset Ω) (E : ℕ) (r : ℝ)
    (hB : ∀ j, 1 ≤ j → j ≤ E → mass μ (B j) = r^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j → Disjoint (B i) (B j)) :
    mass μ (Finset.univ \ pureUnion B E) = 1-geom r E := by
  unfold mass
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _),hm]
  rw [show (∑ x ∈ pureUnion B E, μ x) = geom r E from pureUnion_mass μ B E r hB hdis]

/-- Only pure powers strictly above the cylinder's own exponent can remove
part of an allowable cylinder. Their finite geometric tail is explicit. -/
theorem surviving_cylinder_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (B : ℕ → Finset Ω) (E a : ℕ) (haE : a ≤ E) (r : ℝ)
    (hB : ∀ j, 1 ≤ j → j ≤ E → mass μ (B j) = r^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j → Disjoint (B i) (B j))
    (C : Finset Ω) (hC : mass μ C = r^a)
    (havoid : ∀ j, 1 ≤ j → j ≤ a → Disjoint C (B j)) :
    r^a*(1-geom r (E-a)) ≤ mass μ (C ∩ (Finset.univ \ pureUnion B E)) := by
  let T := (Finset.range (E-a)).biUnion (fun j => B (a+j+1))
  have hsub : C ∩ pureUnion B E ⊆ T := by
    intro x hx
    obtain ⟨hxC,hxB⟩ := Finset.mem_inter.mp hx
    obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hxB
    have hjE := Finset.mem_range.mp hj
    have haj : a ≤ j := by
      by_contra hh
      exact Finset.disjoint_left.mp (havoid (j+1) (by omega) (by omega)) hxC hxj
    apply Finset.mem_biUnion.mpr
    refine ⟨j-a,Finset.mem_range.mpr (by omega),?_⟩
    simpa only [Nat.add_sub_of_le haj] using hxj
  have hT : mass μ T = r^a*geom r (E-a) := by
    unfold mass T
    rw [Finset.sum_biUnion]
    · calc
        _ = ∑ j ∈ Finset.range (E-a), r^(a+j+1) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hB _ (by omega) (by have := Finset.mem_range.mp hj; omega)
        _ = _ := geometric_tail r a (E-a)
    · intro i hi j hj hij
      apply hdis (a+i+1) (a+j+1) (by omega) (by have := Finset.mem_range.mp hi; omega)
        (by omega) (by have := Finset.mem_range.mp hj; omega) (by omega)
  have hb := mass_mono μ hμ hsub
  rw [hT] at hb
  have he : mass μ (C ∩ (Finset.univ \ pureUnion B E)) = mass μ C-mass μ (C ∩ pureUnion B E) := by
    rw [← Finset.inter_sdiff_assoc,Finset.inter_univ]
    rw [← Finset.sdiff_inter_self_left C (pureUnion B E)]
    exact Finset.sum_sdiff_eq_sub Finset.inter_subset_left
  rw [he,hC]
  nlinarith

/-- Conditioning on the pure-power complement cannot lower the probability
of a present allowable cylinder below its original geometric mass. -/
theorem conditional_cylinder_lower_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (B : ℕ → Finset Ω) (E a : ℕ) (haE : a ≤ E) (r : ℝ) (hr : 0 ≤ r)
    (hB : ∀ j, 1 ≤ j → j ≤ E → mass μ (B j) = r^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j → Disjoint (B i) (B j))
    (C : Finset Ω) (hC : mass μ C = r^a)
    (havoid : ∀ j, 1 ≤ j → j ≤ a → Disjoint C (B j))
    (hU : 0 < mass μ (Finset.univ \ pureUnion B E)) :
    r^a ≤ mass μ (C ∩ (Finset.univ \ pureUnion B E)) /
      mass μ (Finset.univ \ pureUnion B E) := by
  apply (le_div_iff₀ hU).mpr
  have hh := surviving_cylinder_mass μ hμ B E a haE r hB hdis C hC havoid
  have hg := geom_mono r hr (show E-a ≤ E by omega)
  have hp := mul_le_mul_of_nonneg_left hg (pow_nonneg hr a)
  rw [pure_complement_mass μ hm B E r hB hdis]
  nlinarith

lemma geom_strictMono (r : ℝ) (hr : 0 < r) : StrictMono (geom r) := by
  apply strictMono_nat_of_lt_succ
  intro E
  have hh : geom r (E+1) = geom r E+r^(E+1) := Finset.sum_range_succ _ _
  rw [hh]
  exact lt_add_of_pos_right _ (pow_pos hr _)

/-- A finite pure-power family gives a strict improvement whenever the
present cylinder has positive exponent. No uniform gap as E grows is claimed. -/
theorem conditional_cylinder_strict_lower_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (B : ℕ → Finset Ω) (E a : ℕ) (ha : 0 < a) (haE : a ≤ E) (r : ℝ) (hr : 0 < r)
    (hB : ∀ j, 1 ≤ j → j ≤ E → mass μ (B j) = r^j)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j → Disjoint (B i) (B j))
    (C : Finset Ω) (hC : mass μ C = r^a)
    (havoid : ∀ j, 1 ≤ j → j ≤ a → Disjoint C (B j))
    (hU : 0 < mass μ (Finset.univ \ pureUnion B E)) :
    r^a < mass μ (C ∩ (Finset.univ \ pureUnion B E)) /
      mass μ (Finset.univ \ pureUnion B E) := by
  apply (lt_div_iff₀ hU).mpr
  have hh := surviving_cylinder_mass μ hμ B E a haE r hB hdis C hC havoid
  have hg := geom_strictMono r hr (show E-a < E by omega)
  have hp := mul_lt_mul_of_pos_left hg (pow_pos hr a)
  rw [pure_complement_mass μ hm B E r hB hdis]
  nlinarith

#print axioms surviving_cylinder_mass
#print axioms conditional_cylinder_lower_bound
#print axioms conditional_cylinder_strict_lower_bound
end Erdos7PureProjectionLower
