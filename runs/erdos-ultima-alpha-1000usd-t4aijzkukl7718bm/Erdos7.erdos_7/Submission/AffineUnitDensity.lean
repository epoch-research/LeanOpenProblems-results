import Submission.PrimeOrbitArithmetic
import Submission.UnitOrbitProbability

/-! Unit-density and prime-orbit conditions at an arbitrary affine centre.
No universally successful choice of centre is asserted. -/
namespace Erdos7AffineUnitDensity
open Erdos7UnitOrbitArithmetic Erdos7UnitOrbitProbability
open Erdos7UnitOrbitDescent Erdos7PrimeOrbitMoment Erdos7PrimeOrbitArithmetic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I]

lemma translated_cover (m : I → ℕ) (a : I → ℤ) (c : ℤ)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) :
    ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-(a i-c) := by
  intro x
  obtain ⟨i,hi⟩ := hc (x+c)
  refine ⟨i, ?_⟩
  convert hi using 1 <;> ring

lemma unit_fiber_probability {N d : ℕ} [NeZero N] (hd : d ∣ N) (a : (ZMod d)ˣ) :
    ((((Finset.univ : Finset (ZMod N)ˣ).filter (fun v => ZMod.unitsMap hd v = a)).card : ℚ) /
      N.totient) = 1/(d.totient : ℚ) := by
  letI : NeZero d := ⟨(Nat.pos_of_dvd_of_pos hd (NeZero.pos N)).ne'⟩
  have h := single_probability (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd) 1 a
  simpa only [Meets, one_zpow, mul_one, exists_const, map_one, orderOf_one,
    Nat.card_eq_fintype_card, Fintype.card_subtype, ZMod.card_units_eq_totient,
    Nat.cast_one] using h

lemma unit_density (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ)
    (hd : ∀ i, m i ∣ N) (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) :
    (1 : ℚ) ≤ ∑ i : UnitIndex m a, 1/((m i.val).totient : ℚ) := by
  let J := UnitIndex m a
  let B (i : J) : Finset (ZMod N)ˣ := Finset.univ.filter (fun v =>
    unitMap N m hd i.val v = unitResidue m a i)
  have hcover : (Finset.univ : Finset (ZMod N)ˣ) ⊆ Finset.univ.biUnion B := by
    intro v _
    obtain ⟨i,hi⟩ := unit_cover N m a hd hc v
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hcount : N.totient ≤ ∑ i : J, (B i).card := by
    rw [← ZMod.card_units_eq_totient N, ← Finset.card_univ]
    exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hpos : (0 : ℚ) < N.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have hrat : (N.totient : ℚ) ≤ ∑ i : J, ((B i).card : ℚ) := by exact_mod_cast hcount
  have hdiv := (div_le_div_iff_of_pos_right hpos).mpr hrat
  rw [div_self hpos.ne', Finset.sum_div] at hdiv
  convert hdiv using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (unit_fiber_probability (hd i.val) (unitResidue m a i)).symm

/-- Every affine centre gives a necessary totient-weighted density condition. -/
theorem centered_unit_density (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ)
    (hd : ∀ i, m i ∣ N) (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) (c : ℤ) :
    (1 : ℚ) ≤ ∑ i : UnitIndex m (fun i => a i-c), 1/((m i.val).totient : ℚ) :=
  unit_density N m _ hd (translated_cover m a c hc)

/-- The sharper prime-orbit inequality also applies at every affine centre. -/
theorem centered_prime_moment {p : ℕ} (hp : p.Prime)
    (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (u : (ZMod N)ˣ) (hu : orderOf u = p) (c : ℤ) :
    let b (i : I) := a i-c
    let J := UnitIndex m b
    let H (i : J) := (ZMod (m i.val))ˣ
    let π (i : J) := unitMap N m hd i.val
    p*(p-1)*N.totient ≤
      p*(p-1)*(∑ i : J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m b) u v i ∧ orderOf (π i u) = 1)).card) +
      ∑ ij : J × J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Conflict H π (unitResidue m b) u v ij.1 ij.2)).card :=
  arithmetic_prime_moment hp N m _ hd (translated_cover m a c hc) u hu

#print axioms centered_unit_density
#print axioms centered_prime_moment
end
end Erdos7AffineUnitDensity
