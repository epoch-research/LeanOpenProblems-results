import Submission.BohrArithmeticProgressions

/-! Uniformly bounded flat arithmetic progressions through inner Bohr points.
The theorem controls membership and phase oscillation, not the density of a set
on the selected progression. -/
namespace Erdos3BohrQuadraticFlattening
open Finset Erdos3BohrArithmeticProgressions Erdos3LocalQuadraticFlattening
  Erdos3SimultaneousQuadraticRecurrence Erdos3LocalQuadraticInverse Erdos3FiniteBohr
  Erdos3BohrCovering
open scoped BigOperators Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G] {I : Type*} [Fintype I]

lemma flat_progression_of_mesh (C : Finset (AddChar G ℂ)) (q : I → G → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) {R η : ℝ}
    (hquad : ∀ i, IsLocallyQuadratic (bohr C (R+η) : Set G) (q i))
    (a h : G) (ha : a ∈ bohr C R) (L t n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (hmesh : 2*((L*recurrenceBound (2*Fintype.card I) t : ℕ) : ℝ)/(n : ℝ) ≤ η) :
    ∃ d : ℕ, 0 < d ∧ d ≤ recurrenceBound (2*Fintype.card I) t*(2*n+1)^(2*C.card) ∧
      ∀ j ≤ L, a+(j*d) • h ∈ bohr C (R+η) ∧
        ∀ i, ‖q i (a+(j*d) • h)-q i a‖ ≤ 2*(L : ℝ)^2*(1/2 : ℝ)^t := by
  let B := recurrenceBound (2*Fintype.card I) t
  obtain ⟨d₀,hd₀,hd₀bound,hinside⟩ := progression_in_enlarged_bohr C a h ha (L*B) n hn
  have hR : ∀ j ≤ L*B, a+j • (d₀ • h) ∈ (bohr C (R+η) : Set G) := by
    intro j hj
    rw [smul_smul]
    exact bohr_mono C (add_le_add le_rfl hmesh) (hinside j hj)
  obtain ⟨d₁,hd₁,hd₁bound,hflat⟩ := simultaneous_local_quadratic_flattening
    (bohr C (R+η) : Set G) q hq hquad a (d₀ • h) L t hL hR
  refine ⟨d₁*d₀,Nat.mul_pos hd₁ hd₀,Nat.mul_le_mul hd₁bound.le hd₀bound,?_⟩
  intro j hj
  have he : (j*(d₁*d₀)) • h = (j*d₁) • (d₀ • h) := by rw [smul_smul,Nat.mul_assoc]
  rw [he]
  exact ⟨hR (j*d₁) (Nat.mul_le_mul hj hd₁bound.le),fun i ↦ hflat i j hj⟩

def flattenAccuracy (L s : ℕ) : ℕ := 2*Nat.clog 2 L+s+1
noncomputable def flattenMesh (m L s : ℕ) (η : ℝ) : ℕ :=
  ⌈2*((L*recurrenceBound (2*m) (flattenAccuracy L s) : ℕ) : ℝ)/η⌉₊+1
noncomputable def flattenStrideBound (rank m L s : ℕ) (η : ℝ) : ℕ :=
  recurrenceBound (2*m) (flattenAccuracy L s)*(2*flattenMesh m L s η+1)^(2*rank)

lemma flattenAccuracy_error (L s : ℕ) :
    2*(L : ℝ)^2*(1/2 : ℝ)^(flattenAccuracy L s) ≤ (1/2 : ℝ)^s := by
  have hL : (L : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 L) := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) L
  have hLs : (L : ℝ)^2 ≤ (2 : ℝ)^(2*Nat.clog 2 L) := by
    convert pow_le_pow_left₀ (Nat.cast_nonneg L) hL 2 using 1
    rw [← pow_mul,mul_comm]
  calc
    _ ≤ 2*(2 : ℝ)^(2*Nat.clog 2 L)*(1/2 : ℝ)^(flattenAccuracy L s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLs (by norm_num)) (by positivity)
    _ = _ := by
      simp only [flattenAccuracy,div_pow,one_pow,pow_add,pow_one]
      field_simp

lemma flattenMesh_pos (m L s : ℕ) (η : ℝ) : 0 < flattenMesh m L s η := by
  unfold flattenMesh
  omega

lemma flattenMesh_bound (m L s : ℕ) {η : ℝ} (hη : 0 < η) :
    2*((L*recurrenceBound (2*m) (flattenAccuracy L s) : ℕ) : ℝ)/(flattenMesh m L s η : ℝ) ≤ η := by
  have hn : (0 : ℝ) < flattenMesh m L s η := by exact_mod_cast flattenMesh_pos m L s η
  have hh : 2*((L*recurrenceBound (2*m) (flattenAccuracy L s) : ℕ) : ℝ)/η ≤
      (flattenMesh m L s η : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [flattenMesh,Nat.cast_add,Nat.cast_one]
    exact le_add_of_nonneg_right (by norm_num)
  have hh' := (div_le_iff₀ hη).mp hh
  apply (div_le_iff₀ hn).mpr
  nlinarith only [hh']

/-- Every inner Bohr point has a uniformly bounded positive natural stride
along which all the prescribed local quadratics are nearly constant for L steps.
The initial generator h may have torsion; this theorem does not assert distinctness. -/
theorem flat_progression_in_bohr (C : Finset (AddChar G ℂ)) (q : I → G → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) {R η : ℝ} (hη : 0 < η)
    (hquad : ∀ i, IsLocallyQuadratic (bohr C (R+η) : Set G) (q i))
    (a h : G) (ha : a ∈ bohr C R) (L s : ℕ) (hL : 0 < L) :
    ∃ d : ℕ, 0 < d ∧ d ≤ flattenStrideBound C.card (Fintype.card I) L s η ∧
      ∀ j ≤ L, a+(j*d) • h ∈ bohr C (R+η) ∧ ∀ i, ‖q i (a+(j*d) • h)-q i a‖ ≤ (1/2 : ℝ)^s := by
  obtain ⟨d,hd,hbound,hflat⟩ := flat_progression_of_mesh C q hq hquad a h ha L
    (flattenAccuracy L s) (flattenMesh (Fintype.card I) L s η) hL
    (flattenMesh_pos _ _ _ _) (flattenMesh_bound (Fintype.card I) L s hη)
  exact ⟨d,hd,hbound,fun j hj ↦ ⟨(hflat j hj).1,
    fun i ↦ ((hflat j hj).2 i).trans (flattenAccuracy_error L s)⟩⟩

lemma nat_stride_injective_zmod (p L D d : ℕ) [NeZero p] (hd : 0 < d) (hdD : d ≤ D)
    (hbudget : L*D < p) (a : ZMod p) :
    Function.Injective (fun j : Fin (L+1) ↦ a+(j.val*d) • (1 : ZMod p)) := by
  intro i j hij
  have hi : i.val*d < p := (Nat.mul_le_mul (by omega : i.val ≤ L) hdD).trans_lt hbudget
  have hj : j.val*d < p := (Nat.mul_le_mul (by omega : j.val ≤ L) hdD).trans_lt hbudget
  have he : ((i.val*d : ℕ) : ZMod p) = ((j.val*d : ℕ) : ZMod p) := by
    simpa only [nsmul_eq_mul,mul_one] using add_left_cancel hij
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] at hv
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd hv)

/-- The same construction gives DISTINCT points when the modulus exceeds the
explicit length-times-stride budget. Thus torsion cannot make this conclusion
vacuous. The theorem still does not assert density preservation. -/
theorem proper_flat_progression_zmod (p : ℕ) [NeZero p]
    (C : Finset (AddChar (ZMod p) ℂ)) (q : I → ZMod p → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) {R η : ℝ} (hη : 0 < η)
    (hquad : ∀ i, IsLocallyQuadratic (bohr C (R+η) : Set (ZMod p)) (q i))
    (a : ZMod p) (ha : a ∈ bohr C R) (L s : ℕ) (hL : 0 < L)
    (hbudget : L*flattenStrideBound C.card (Fintype.card I) L s η < p) :
    ∃ d : ℕ, 0 < d ∧ d ≤ flattenStrideBound C.card (Fintype.card I) L s η ∧
      Function.Injective (fun j : Fin (L+1) ↦ a+(j.val*d) • (1 : ZMod p)) ∧
      ∀ j ≤ L, a+(j*d) • (1 : ZMod p) ∈ bohr C (R+η) ∧
        ∀ i, ‖q i (a+(j*d) • (1 : ZMod p))-q i a‖ ≤ (1/2 : ℝ)^s := by
  obtain ⟨d,hd,hbound,hflat⟩ := flat_progression_in_bohr C q hq hη hquad a (1 : ZMod p) ha L s hL
  exact ⟨d,hd,hbound,nat_stride_injective_zmod p L _ d hd hbound hbudget a,hflat⟩

#print axioms flat_progression_in_bohr
#print axioms proper_flat_progression_zmod
end Erdos3BohrQuadraticFlattening
