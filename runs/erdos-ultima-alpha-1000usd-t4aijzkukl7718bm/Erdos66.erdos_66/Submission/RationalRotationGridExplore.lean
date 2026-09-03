import Submission.HermiteFloorExplore

/-! Exact floor differences along a full reduced rational rotation orbit. -/
namespace Erdos66RationalRotationGrid
open Erdos66HermiteFloor
open scoped Classical
set_option maxHeartbeats 1800000

lemma sum_zmod_range {R : Type*} [AddCommMonoid R] (n : ℕ) [NeZero n] (f : ZMod n → R) :
    (∑ a : ZMod n, f a) = ∑ k ∈ Finset.range n, f (k : ZMod n) := by
  have he : (Finset.range n).image (fun k : ℕ ↦ (k : ZMod n)) = Finset.univ := by
    ext a
    simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,iff_true]
    exact ⟨a.val,ZMod.val_lt a,ZMod.natCast_zmod_val a⟩
  rw [← he,Finset.sum_image]
  intro i hi j hj hij
  have hval := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hi),
    ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)] using hval

lemma rat_mul_mod_decomposition (r : ℚ) (k : ℕ) :
    (k : ℝ)*(r : ℝ) =
      ((((r.num*(k : ℤ) : ℤ) : ZMod r.den).val : ℝ)/(r.den : ℝ)) +
        ((r.num*(k : ℤ)/(r.den : ℤ) : ℤ) : ℝ) := by
  letI : NeZero r.den := ⟨r.den_nz⟩
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hv := ZMod.val_intCast (n := r.den) (r.num*(k : ℤ))
  have hv' : ((((r.num*(k : ℤ) : ℤ) : ZMod r.den).val : ℝ)) =
      ((r.num*(k : ℤ)%(r.den : ℤ) : ℤ) : ℝ) := by exact_mod_cast hv
  rw [hv',Rat.cast_def]
  have he := Int.emod_add_mul_ediv (r.num*(k : ℤ)) (r.den : ℤ)
  have he' := congrArg (fun z : ℤ ↦ (z : ℝ)) he
  push_cast at he'
  field_simp
  nlinarith only [he']

lemma rational_orbit_sum (r : ℚ) (f : ℝ → ℤ)
    (hf : ∀ x : ℝ, ∀ z : ℤ, f (x+z)=f x) :
    (∑ k ∈ Finset.range r.den, f ((k : ℝ)*(r : ℝ))) =
      ∑ k ∈ Finset.range r.den, f ((k : ℝ)/r.den) := by
  letI : NeZero r.den := ⟨r.den_nz⟩
  have hu : IsUnit (r.num : ZMod r.den) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime,Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]
    exact r.reduced.symm
  obtain ⟨u,hu⟩ := hu
  have he (k : ℕ) : f ((k : ℝ)*(r : ℝ)) =
      f ((((r.num : ZMod r.den)*(k : ZMod r.den)).val : ℝ)/r.den) := by
    rw [rat_mul_mod_decomposition,hf]
    congr 2
    simp only [Int.cast_mul,Int.cast_natCast]
  simp_rw [he]
  have hs := Equiv.sum_comp u.mulLeft (fun a : ZMod r.den ↦ f ((a.val : ℝ)/r.den))
  rw [sum_zmod_range,sum_zmod_range] at hs
  simp only [Units.mulLeft_apply,hu] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)]

/-- Exact full-block identity; no distribution or error estimate is used. -/
theorem rational_floor_difference (r : ℚ) (x y : ℝ) :
    (∑ k ∈ Finset.range r.den,
      (⌊x+(k : ℝ)*(r : ℝ)⌋-⌊y+(k : ℝ)*(r : ℝ)⌋)) =
        ⌊(r.den : ℝ)*x⌋-⌊(r.den : ℝ)*y⌋ := by
  have h := rational_orbit_sum r (fun s ↦ ⌊x+s⌋-⌊y+s⌋) (by
    intro s z
    simp only [← add_assoc,Int.floor_add_intCast]
    omega)
  rw [h,Finset.sum_sub_distrib,sum_floor_grid r.den r.pos,sum_floor_grid r.den r.pos]

end Erdos66RationalRotationGrid
