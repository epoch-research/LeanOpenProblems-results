import Submission.PresentCylinderLower
import Submission.ArithmeticReduction

/-! Arithmetic application of the uniform conditioning lower bound to
present, non-pure classes of an irredundant covering system. This is a
necessary geometric property, not a noncoverage theorem. -/
namespace Erdos7PresentCylinderArithmetic
open scoped BigOperators
open Erdos7PresentCylinderLower Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 3000000

def cylinder (p E a : ℕ) [NeZero p] (b : ℤ) : Finset (ZMod (p^E)) :=
  Finset.univ.filter (fun x => (x.val : ZMod (p^a)) = (b : ZMod (p^a)))

lemma mem_cylinder (p E a : ℕ) [NeZero p] (b : ℤ) (x : ZMod (p^E)) :
    x ∈ cylinder p E a b ↔ ((p^a : ℕ) : ℤ) ∣ (x.val : ℤ)-b := by
  simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [eq_comm]
  simpa only [Int.cast_natCast] using
    ZMod.intCast_eq_intCast_iff_dvd_sub b (x.val : ℤ) (p^a)

lemma cylinder_card (p E a : ℕ) [NeZero p] (ha : a ≤ E) (b : ℤ) :
    ((cylinder p E a b).card : ℚ) =
      Fintype.card (ZMod (p^E)) * ((p : ℚ)⁻¹)^a := by
  let f := ZMod.castHom (pow_dvd_pow p ha) (ZMod (p^a))
  have hf (x : ZMod (p^E)) : f x = (x.val : ZMod (p^a)) := by
    calc
      f x = f (x.val : ZMod (p^E)) := congrArg f (ZMod.natCast_zmod_val x).symm
      _ = _ := map_natCast f x.val
  have he : cylinder p E a b = Finset.univ.filter (fun x => f x = (b : ZMod (p^a))) := by
    ext x
    simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and, hf]
  rw [he]
  have h := Erdos7StarSieve.surjective_fiber_card_rat f.toAddMonoidHom
    (ZMod.castHom_surjective (pow_dvd_pow p ha)) (b : ZMod (p^a))
  simpa only [ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow] using h

lemma cylinders_disjoint (p E a b : ℕ) [NeZero p] (hab : a ≤ b)
    (u v : ℤ) (hnot : ¬ ((p^a : ℕ) : ℤ) ∣ v-u) :
    Disjoint (cylinder p E a u) (cylinder p E b v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hu := (mem_cylinder p E a u x).mp hx
  have hv := (mem_cylinder p E b v x).mp hy
  have hd : ((p^a : ℕ) : ℤ) ∣ ((p^b : ℕ) : ℤ) := by exact_mod_cast pow_dvd_pow p hab
  have h := dvd_sub hu (hd.trans hv)
  apply hnot
  convert h using 1
  ring

/-- Pure moduli have distinct indices when their exponents differ. -/
lemma pure_indices_injective {I : Type*} (m : I → ℕ) (p E : ℕ) (hp : 1 < p)
    (pure : Fin E → I) (hmod : ∀ j, m (pure j) = p^(j.val+1)) :
    Function.Injective pure := by
  intro i j hij
  have h := congrArg m hij
  rw [hmod i, hmod j] at h
  have he := (Nat.pow_right_inj hp).mp h
  exact Fin.ext (by omega)

/-- An actual non-pure class, after uniform deletion of all pure powers,
retains at least its original p-adic projection mass. All pure powers up to E
must be present; a missing/padded class does not satisfy these hypotheses. -/
theorem present_projection_lower {I : Type*}
    (m : I → ℕ) (b : I → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x-b j)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-b i)
    (p E : ℕ) [NeZero p] (hp : 2 ≤ p)
    (pure : Fin E → I) (hmod : ∀ j, m (pure j) = p^(j.val+1))
    (i : I) (a : ℕ) (ha : a ≤ E) (hdiv : p^a ∣ m i)
    (hnpure : ∀ j, pure j ≠ i) :
    let B := fun j : ℕ => if hj : j < E then
      cylinder p E (j+1) (b (pure ⟨j,hj⟩)) else ∅
    let U := Finset.univ \ (Finset.range E).biUnion B
    ((p : ℚ)⁻¹)^a ≤ ((U ∩ cylinder p E a (b i)).card : ℚ) / U.card := by
  classical
  dsimp only
  let B := fun j : ℕ => if hj : j < E then
    cylinder p E (j+1) (b (pure ⟨j,hj⟩)) else ∅
  have hp1 : 1 < p := by omega
  have hpq : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have hr : (0 : ℚ) < (p : ℚ)⁻¹ := inv_pos.mpr hpq
  have hhalf : (p : ℚ)⁻¹ ≤ 1/2 := by
    have hh : (2 : ℚ) ≤ p := by exact_mod_cast hp
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) hh
  have hinj := pure_indices_injective m p E hp1 pure hmod
  have hpair (j k : Fin E) (hjk : j < k) :
      Disjoint (cylinder p E (j.val+1) (b (pure j)))
        (cylinder p E (k.val+1) (b (pure k))) := by
    apply cylinders_disjoint p E _ _ (by exact Nat.add_le_add_right (Nat.le_of_lt hjk) 1)
    have hne : pure j ≠ pure k := fun h => (ne_of_lt hjk) (hinj h)
    have hd : m (pure j) ∣ m (pure k) := by
      rw [hmod j, hmod k]
      exact pow_dvd_pow p (by exact Nat.add_le_add_right (Nat.le_of_lt hjk) 1)
    have h := residue_not_congruent_of_proper_modulus_divisor m b hpriv hcover hne hd
    simpa only [hmod j] using h
  have hd : (↑(Finset.range E) : Set ℕ).PairwiseDisjoint B := by
    intro j hj k hk hne
    have hjE := Finset.mem_range.mp hj
    have hkE := Finset.mem_range.mp hk
    change Disjoint (B j) (B k)
    simp only [B, dif_pos hjE, dif_pos hkE]
    rcases lt_or_gt_of_ne hne with h | h
    · exact hpair ⟨j,hjE⟩ ⟨k,hkE⟩ h
    · exact (hpair ⟨k,hkE⟩ ⟨j,hjE⟩ h).symm
  have hsize (j : ℕ) (hj : j < E) :
      ((B j).card : ℚ) = Fintype.card (ZMod (p^E)) * ((p : ℚ)⁻¹)^(j+1) := by
    simp only [B, dif_pos hj]
    exact cylinder_card p E (j+1) (by omega) _
  have havoid (j : ℕ) (hj : j < E) (hja : j < a) :
      Disjoint (cylinder p E a (b i)) (B j) := by
    simp only [B, dif_pos hj]
    apply Disjoint.symm
    apply cylinders_disjoint p E (j+1) a (by omega)
    have hdiv' : m (pure ⟨j,hj⟩) ∣ m i := by
      rw [hmod]
      exact (pow_dvd_pow p (by omega : j+1 ≤ a)).trans hdiv
    have h := residue_not_congruent_of_proper_modulus_divisor m b hpriv hcover
      (hnpure ⟨j,hj⟩) hdiv'
    simpa only [hmod] using h
  exact conditioned_cylinder_lower ((p : ℚ)⁻¹) hr.le a E B
    (cylinder p E a (b i)) hd hsize (cylinder_card p E a ha _) havoid
    (pure_complement_nonempty _ hr hhalf E B hd hsize)

#print axioms cylinder_card
#print axioms present_projection_lower
end Erdos7PresentCylinderArithmetic
