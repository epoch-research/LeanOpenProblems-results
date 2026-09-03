import Submission.PrimeOrbitForest
import Submission.UnitOrbitPhaseProbability

/-! Exact arithmetic intersection weights for the unit-period forest edges.
These formulas justify the residue-sensitive correction; they do not supply
a universally small forest-corrected budget. -/
namespace Erdos7PrimeOrbitForestProbability
open Erdos7UnitOrbitProbability Erdos7UnitOrbitPhaseProbability
open Erdos7UnitOrbitDescent Erdos7PrimeOrbitForest
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

lemma meets_of_order_one {G H : Type*} [Group G] [Group H]
    (f : G →* H) (u v : G) (a : H) (hu : orderOf (f u) = 1) :
    Meets f u a v ↔ f v = a := by
  have he := orderOf_eq_one_iff.mp hu
  simp [Meets,map_mul,map_zpow,he]

lemma unit_event_iff {G I : Type} [Group G] [Fintype G] [Fintype I]
    (H : I → Type) [∀ i, Group (H i)] (π : (i : I) → G →* H i)
    (a : (i : I) → H i) (u v : G) (i : I) (hi : orderOf (π i u) = 1) :
    UnitEvent H π a u i v ↔ π i v = a i := by
  have he := orderOf_eq_one_iff.mp hi
  simp [UnitEvent,Active,map_mul,map_zpow,he]

variable {N m n : ℕ} [NeZero N]

/-- Ordinary unit fibers intersect with probability 1/phi(lcm) precisely
when their residues agree modulo the gcd. -/
theorem fiber_intersection_probability (hm : m ∣ N) (hn : n ∣ N)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (Nat.card {v : (ZMod N)ˣ // ZMod.unitsMap hm v = a ∧ ZMod.unitsMap hn v = b}:ℚ) /
      N.totient = if CRTCompatible a b then 1/((m.lcm n).totient:ℚ) else 0 := by
  simpa only [CoMeets,one_zpow,mul_one,exists_const,map_one,orderOf_one,Nat.cast_one]
    using common_phase_probability hm hn 1 a b

/-- In a pair of unit-period events, orbit meetings are just ordinary fibers. -/
theorem unit_intersection_probability (hm : m ∣ N) (hn : n ∣ N)
    (u : (ZMod N)ˣ) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ)
    (hum : orderOf (ZMod.unitsMap hm u) = 1)
    (hun : orderOf (ZMod.unitsMap hn u) = 1) :
    (Nat.card {v : (ZMod N)ˣ // Meets (ZMod.unitsMap hm) u a v ∧
      Meets (ZMod.unitsMap hn) u b v}:ℚ) / N.totient =
        if CRTCompatible a b then 1/((m.lcm n).totient:ℚ) else 0 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v =>
    and_congr (meets_of_order_one _ u v a hum) (meets_of_order_one _ u v b hun)))]
  exact fiber_intersection_probability hm hn a b

lemma compatible_int_iff (a b : ℤ) (ha : IsUnit (a : ZMod m)) (hb : IsUnit (b : ZMod n)) :
    CRTCompatible ha.unit hb.unit ↔ ((m.gcd n:ℕ):ℤ) ∣ b-a := by
  unfold CRTCompatible
  rw [Units.ext_iff,ZMod.unitsMap_val,ZMod.unitsMap_val,ha.unit_spec,hb.unit_spec,
    ZMod.cast_intCast (Nat.gcd_dvd_left m n),ZMod.cast_intCast (Nat.gcd_dvd_right m n)]
  exact ZMod.intCast_eq_intCast_iff_dvd_sub a b (m.gcd n)

/-- Integer residues give the usual exact CRT compatibility test. -/
theorem integer_unit_intersection_probability (hm : m ∣ N) (hn : n ∣ N)
    (u : (ZMod N)ˣ) (a b : ℤ) (ha : IsUnit (a : ZMod m)) (hb : IsUnit (b : ZMod n))
    (hum : orderOf (ZMod.unitsMap hm u) = 1)
    (hun : orderOf (ZMod.unitsMap hn u) = 1) :
    (Nat.card {v : (ZMod N)ˣ // Meets (ZMod.unitsMap hm) u ha.unit v ∧
      Meets (ZMod.unitsMap hn) u hb.unit v}:ℚ) / N.totient =
        if ((m.gcd n:ℕ):ℤ) ∣ b-a then 1/((m.lcm n).totient:ℚ) else 0 := by
  rw [unit_intersection_probability hm hn u ha.unit hb.unit hum hun]
  simp only [compatible_int_iff]

/-- For coprime moduli of the same prime induced order, the normalized
unordered-pair charge is exactly twice the product of their unit densities.
In particular, changing their residues cannot eliminate this contribution. -/
theorem coprime_pair_charge (hm : m ∣ N) (hn : n ∣ N) (hcop : m.Coprime n)
    (u : (ZMod N)ˣ) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ)
    (p : ℕ) (hp : 2 ≤ p)
    (hum : orderOf (ZMod.unitsMap hm u) = p)
    (hun : orderOf (ZMod.unitsMap hn u) = p) :
    ((Nat.card {v : (ZMod N)ˣ //
      (Meets (ZMod.unitsMap hm) u a v ∧ Meets (ZMod.unitsMap hn) u b v) ∧
        ¬ CoMeets hm hn u a b v}:ℚ) / N.totient) /
      (((p*(p-1):ℕ):ℚ)/2) = 2/((m.totient:ℚ)*n.totient) := by
  letI : Subsingleton (ZMod (m.gcd n))ˣ := by rw [hcop.gcd_eq_one]; infer_instance
  have hcrt : CRTCompatible a b := Subsingleton.elim _ _
  have hcomp : Erdos7UnitOrbitKernel.Compatible hm hn u a b := by
    unfold Erdos7UnitOrbitKernel.Compatible
    rw [Subsingleton.elim
      ((ZMod.unitsMap (Nat.gcd_dvd_left m n) a)⁻¹ * ZMod.unitsMap (Nat.gcd_dvd_right m n) b) 1]
    exact Subgroup.one_mem _
  have hg : orderOf (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) = 1 := by
    rw [Subsingleton.elim (ZMod.unitsMap ((Nat.gcd_dvd_left m n).trans hm) u) 1,orderOf_one]
  have hl : orderOf (ZMod.unitsMap (Nat.lcm_dvd hm hn) u) = p := by
    rw [order_lcm hm hn u,hum,hun,Nat.lcm_self]
  rw [distinct_phase_probability hm hn u a b,if_pos hcomp,if_pos hcrt,
    hum,hun,hg,hl,hcop.lcm_eq_mul,Nat.totient_mul hcop]
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hpq1 : (p:ℚ)-1 ≠ 0 := by
    have hp' : (2:ℚ) ≤ p := by exact_mod_cast hp
    linarith
  have hmpos := Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hm (NeZero.pos N))
  have hnpos := Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hn (NeZero.pos N))
  have hmt : (m.totient:ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hnt : (n.totient:ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
  simp only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one,one_mul]
  field_simp
  <;> ring

#print axioms coprime_pair_charge
#print axioms unit_event_iff
#print axioms integer_unit_intersection_probability
end
end Erdos7PrimeOrbitForestProbability
