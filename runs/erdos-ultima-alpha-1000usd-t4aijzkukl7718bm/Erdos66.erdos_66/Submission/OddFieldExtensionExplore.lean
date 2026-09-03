import Submission.ParabolaRepairExplore

/-! Odd-degree extension preserves square classes. A parabola over a larger
field has its exact old-field slice, and new parameters miss nonzero old
points. These are finite field statements, not integer-prefix estimates. -/
namespace Erdos66OddFieldExtension
open Erdos66ParabolaRepair
open scoped Classical
set_option maxHeartbeats 1600000

lemma isSquare_of_odd_power {F : Type*} [Field F] (x : F) (d : ℕ)
    (hd : Odd d) (hx : IsSquare (x^d)) : IsSquare x := by
  obtain ⟨k,hk⟩ := hd
  obtain ⟨b,hb⟩ := hx
  by_cases hx0 : x=0
  · subst x; exact ⟨0,by simp⟩
  refine ⟨b/x^k,?_⟩
  rw [hk,show 2*k=k*2 by omega,pow_add,pow_one,pow_mul] at hb
  field_simp [pow_ne_zero _ hx0]
  linear_combination hb

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

lemma isSquare_algebraMap_iff (hd : Odd (Module.finrank F K)) (x : F) :
    IsSquare (algebraMap F K x) ↔ IsSquare x := by
  constructor
  · intro hx
    have hh := hx.map (Algebra.norm F)
    rw [Algebra.norm_algebraMap] at hh
    exact isSquare_of_odd_power x _ hd hh
  · exact IsSquare.map (algebraMap F K)

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

lemma quadraticChar_algebraMap (hd : Odd (Module.finrank F K)) (x : F) :
    quadraticChar K (algebraMap F K x)=quadraticChar F x := by
  simp only [quadraticChar_apply,quadraticCharFun,
    map_eq_zero,isSquare_algebraMap_iff hd]

lemma curve_old_slice (u : F) (x y : F) :
    ((algebraMap F K x,algebraMap F K y):K×K)∈curve (algebraMap F K u) ↔
      (x,y)∈curve u := by
  rw [mem_curve,mem_curve]
  simp only [←map_pow,←map_div₀]
  exact (algebraMap F K).injective.eq_iff

/-- A parameter outside the old field introduces no nonzero point into its
old coordinate-plane slice. -/
lemma outside_parameter_old_slice (u : K) (hu : u∉Set.range (algebraMap F K))
    (x y : F) :
    ((algebraMap F K x,algebraMap F K y):K×K)∈curve u ↔ x=0 ∧ y=0 := by
  rw [mem_curve]
  dsimp only
  have hu0 : u≠0 := by
    intro h
    apply hu
    exact ⟨0,by simpa using h.symm⟩
  constructor
  · intro he
    by_cases hy0 : y=0
    · have hh : (algebraMap F K x)^2=0 := by simpa [hy0,hu0] using he.symm
      have hx0 : x=0 := (algebraMap F K).injective (by simpa using eq_zero_of_pow_eq_zero hh)
      exact ⟨hx0,hy0⟩
    · have hyK : algebraMap F K y≠0 := (map_ne_zero (algebraMap F K)).mpr hy0
      exfalso
      apply hu
      refine ⟨x^2/y,?_⟩
      simp only [map_div₀,map_pow]
      have hh := (eq_div_iff hu0).mp he
      apply (div_eq_iff hyK).mpr
      linear_combination -hh
  · rintro ⟨rfl,rfl⟩
    simp

end Erdos66OddFieldExtension
