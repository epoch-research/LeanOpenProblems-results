import Submission.UnitOrbitDescent

/-! Arithmetic input to the conditional unit-orbit descent. Minimality still
has to be combined with a useful bound on collisions. -/
namespace Erdos7UnitOrbitArithmetic
open Erdos7Reduction Erdos7UnitOrbitDescent
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {I : Type} [Fintype I]

abbrev UnitIndex (m : I → ℕ) (a : I → ℤ) := {i : I // IsUnit (a i : ZMod (m i))}

def unitMap (N : ℕ) (m : I → ℕ) (hd : ∀ i, m i ∣ N) (i : I) :
    (ZMod N)ˣ →* (ZMod (m i))ˣ :=
  Units.map (ZMod.castHom (hd i) (ZMod (m i))).toMonoidHom

def unitResidue (m : I → ℕ) (a : I → ℤ) (i : UnitIndex m a) :
    (ZMod (m i.val))ˣ := i.property.unit

/-- The classes with nonunit residues cannot meet a unit; all other classes
become actual fibers of group homomorphisms. -/
theorem unit_cover (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ)
    (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) :
    ∀ v : (ZMod N)ˣ, ∃ i : UnitIndex m a,
      unitMap N m hd i.val v = unitResidue m a i := by
  intro v
  let x : ℤ := (v.val.val : ℕ)
  obtain ⟨k,hk⟩ := hc x
  have hproj : ((unitMap N m hd k v : (ZMod (m k))ˣ) : ZMod (m k)) =
      (x : ZMod (m k)) := by
    change (ZMod.castHom (hd k) (ZMod (m k))) (v : ZMod N) = (x : ZMod (m k))
    rw [← ZMod.natCast_zmod_val (v : ZMod N)]
    simp [x]
  have hres : (a k : ZMod (m k)) = (x : ZMod (m k)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) x (m k)).mpr hk
  have hu : IsUnit (a k : ZMod (m k)) := by
    rw [hres, ← hproj]
    exact (unitMap N m hd k v).isUnit
  refine ⟨⟨k,hu⟩, ?_⟩
  apply Units.ext
  change (unitMap N m hd k v : ZMod (m k)) = (hu.unit : ZMod (m k))
  rw [hu.unit_spec]
  exact hproj.trans hres.symm

lemma order_lt_period (N : ℕ) [NeZero N] (hN : 1 < N) (u : (ZMod N)ˣ) :
    orderOf u < N := by
  have hle : orderOf u ≤ Fintype.card (ZMod N)ˣ :=
    Nat.le_of_dvd Fintype.card_pos orderOf_dvd_card
  rw [ZMod.card_units_eq_totient] at hle
  exact hle.trans_lt (Nat.totient_lt N hN)

lemma no_smaller_unit_cover (N : ℕ) [NeZero N] (hN : 1 < N)
    (m : I → ℕ) (a : I → ℤ)
    (hmin : ∀ D, D < N → ¬ HasOddArithmeticCover D (Fintype.card I))
    (u : (ZMod N)ˣ) :
    ¬ HasOddArithmeticCover (orderOf u) (Fintype.card (UnitIndex m a)) := by
  intro h
  obtain ⟨hD,J,fJ,d,b,hdi,hd,hc,hdD,hcard⟩ := h
  exact hmin _ (order_lt_period N hN u)
    ⟨hD,J,fJ,d,b,hdi,hd,hc,hdD,hcard.trans (Fintype.card_subtype_le _)⟩

/-- Every translated odd-order unit orbit of a period-minimal odd cover has
an active unit period or two distinct classes with the same induced period. -/
theorem minimal_period_orbit_collision (N : ℕ) [NeZero N] (hN : 1 < N)
    (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (hmin : ∀ D, D < N → ¬ HasOddArithmeticCover D (Fintype.card I))
    (u : (ZMod N)ˣ) (hu : Odd (orderOf u)) (v : (ZMod N)ˣ) :
    let H (i : UnitIndex m a) := (ZMod (m i.val))ˣ
    let π (i : UnitIndex m a) := unitMap N m hd i.val
    (∃ i, Active H π (unitResidue m a) u v i ∧ orderOf (π i u) = 1) ∨
    (∃ i j, i ≠ j ∧ Active H π (unitResidue m a) u v i ∧
      Active H π (unitResidue m a) u v j ∧ orderOf (π i u) = orderOf (π j u)) := by
  dsimp only
  exact every_orbit_bad _ _ _ (unit_cover N m a hd hc) u hu
    (no_smaller_unit_cover N hN m a hmin u) v


/-- An arithmetic necessary bound on the actual unit-period and repeated-period
collision sets. Its missing ingredient for Erdős 7 is a strict universal upper
bound for a suitable odd-order generator. -/
theorem minimal_period_collision_budget [LinearOrder I]
    (N : ℕ) [NeZero N] (hN : 1 < N)
    (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (hmin : ∀ D, D < N → ¬ HasOddArithmeticCover D (Fintype.card I))
    (u : (ZMod N)ˣ) (hu : Odd (orderOf u)) :
    let J := UnitIndex m a
    let H (i : J) := (ZMod (m i.val))ˣ
    let π (i : J) := unitMap N m hd i.val
    N.totient ≤
      (∑ i : J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m a) u v i ∧ orderOf (π i u) = 1)).card) +
      (∑ ij : PairIndex (I := J), ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m a) u v ij.val.1 ∧
        Active H π (unitResidue m a) u v ij.val.2 ∧
        orderOf (π ij.val.1 u) = orderOf (π ij.val.2 u))).card) := by
  dsimp only
  have hh := collision_count_bound _ _ _ (unit_cover N m a hd hc) u hu
    (no_smaller_unit_cover N hN m a hmin u)
  simpa only [ZMod.card_units_eq_totient] using hh

#print axioms minimal_period_collision_budget

#print axioms unit_cover
#print axioms order_lt_period
#print axioms minimal_period_orbit_collision
end
end Erdos7UnitOrbitArithmetic
