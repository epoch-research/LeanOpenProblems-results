import Submission.SymmetricPureAvoidance
import Submission.PresentCylinderArithmetic

/-! Opposite unit residues avoiding one class at every pure prime-power level.
This is a finite arithmetic preparation, not an odd-covering obstruction. -/
namespace Erdos7SymmetricPureArithmetic
open Erdos7PresentCylinderArithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma mem_cylinder_neg (p E e : ℕ) [NeZero p] (he : e ≤ E)
    (a : ℤ) (x : ZMod (p^E)) :
    -x ∈ cylinder p E e a ↔ x ∈ cylinder p E e (-a) := by
  let f := ZMod.castHom (pow_dvd_pow p he) (ZMod (p^e))
  have hf (y : ZMod (p^E)) : f y = (y.val : ZMod (p^e)) := by
    calc
      f y = f (y.val : ZMod (p^E)) := congrArg f (ZMod.natCast_zmod_val y).symm
      _ = _ := map_natCast f y.val
  simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hf (-x), map_neg, hf x, Int.cast_neg]
  exact neg_eq_iff_eq_neg

/-- For p≥3, uniformly in E, one can choose opposite units avoiding every
class a_e modulo p^e for 2≤e≤E. The class modulo p has been normalized to zero.
The preceding finite-space theorem even leaves at least one third of the
whole p^E residue space available. -/
theorem exists_unit_opposite_pair (p E : ℕ) [NeZero p]
    (hp : 3 ≤ p) (hE : 1 ≤ E) (a : ℕ → ℤ) :
    ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      ∀ e, 2 ≤ e → e ≤ E →
        ¬ ((p^e : ℕ) : ℤ) ∣ u-a e ∧ ¬ ((p^e : ℕ) : ℤ) ∣ -u-a e := by
  classical
  let Z := cylinder p E 1 0
  let B := fun j => cylinder p E (j+2) (a (j+2))
  let r : ℚ := (p : ℚ)⁻¹
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr3 : r ≤ 1/3 := by
    have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
    simpa only [r, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) hpq
  have hZ : ((Z.card : ℕ) : ℚ) ≤ Fintype.card (ZMod (p^E))*r := by
    have hh := cylinder_card p E 1 hE 0
    simpa only [pow_one, Z, r] using hh.le
  have hB : ∀ j < E-1, ((B j).card : ℚ) ≤
      Fintype.card (ZMod (p^E))*r^(j+2) := by
    intro j hj
    exact (cylinder_card p E (j+2) (by omega) (a (j+2))).le
  have hstable : ∀ x : ZMod (p^E), x ∈ Z → -x ∈ Z := by
    intro x hx
    have hh := (mem_cylinder_neg p E 1 hE 0 x).mpr
    apply hh
    simpa only [neg_zero] using hx
  obtain ⟨x, hxZ, _, hxB⟩ := Erdos7SymmetricPureAvoidance.exists_avoiding_pair
    (fun x : ZMod (p^E) => -x) neg_neg Z hstable B (E-1) r hr hr3 hZ hB
  refine ⟨(x.val : ℤ), ?_, ?_⟩
  · intro h
    apply hxZ
    apply (mem_cylinder p E 1 0 x).mpr
    simpa only [pow_one, sub_zero] using h
  · intro e he heE
    have hej : e-2 < E-1 := by omega
    have heq : e-2+2 = e := by omega
    have hh := hxB (e-2) hej
    simp only [B, heq] at hh
    constructor
    · exact fun hd => hh.1 ((mem_cylinder p E e (a e) x).mpr hd)
    · intro hd
      apply hh.2
      apply (mem_cylinder_neg p E e heE (a e) x).mpr
      apply (mem_cylinder p E e (-a e) x).mpr
      convert dvd_neg.mpr hd using 1 <;> ring

#print axioms mem_cylinder_neg
#print axioms exists_unit_opposite_pair
end Erdos7SymmetricPureArithmetic
