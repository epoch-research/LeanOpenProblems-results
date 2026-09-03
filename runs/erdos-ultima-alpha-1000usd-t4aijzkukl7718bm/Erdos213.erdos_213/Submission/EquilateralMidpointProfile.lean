import Submission.CommonFaceClass

/-! A local obstruction for the square-class profile arising from one
three-torsion y-projection. This is not a bound for arbitrary point sets. -/
namespace Erdos213.EquilateralMidpointProfile
open TetrahedralArithmetic CommonFaceClass

/-- Homogenized squared norms, with the required factors of 3 included.
For t=(U+V√(-3))/(2T), entry zero is 4T² N(t), and the other six
entries are 12T² N(t-r), where r ranges over the vertices and side
midpoints of an equilateral triangle. -/
def forms {R : Type*} [CommRing R] (U V T : R) : Fin 7 → R :=
  ![U^2+3*V^2,
    3*((U-2*T)^2+3*V^2),
    3*((U+T)^2+3*(V-T)^2),
    3*((U+T)^2+3*(V+T)^2),
    3*((U+4*T)^2+3*V^2),
    3*((U-2*T)^2+3*(V-2*T)^2),
    3*((U-2*T)^2+3*(V+2*T)^2)]

lemma forms_scale {R : Type*} [CommRing R] (r U V T : R) (i : Fin 7) :
    forms (r*U) (r*V) (r*T) i = r^2*forms U V T i := by
  fin_cases i <;> simp [forms] <;> ring

lemma forms_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (U V T : R) (i : Fin 7) :
    f (forms U V T i) = forms (f U) (f V) (f T) i := by
  fin_cases i <;> simp [forms,map_ofNat]

set_option synthInstance.maxSize 10000 in
lemma mod_five_profile : ∀ U V T : ZMod 5,
    (∀ i : Fin 7, IsSquare (forms U V T i)) → U=0 ∧ V=0 ∧ T=0 := by
  decide

lemma primitive_not_profile (U V T : ℤ) (hp : Primitive U V T) :
    ¬ ∀ i : Fin 7, IsSquare (forms U V T i) := by
  intro h
  have hm (i : Fin 7) : IsSquare (forms (U : ZMod 5) (V : ZMod 5) (T : ZMod 5) i) := by
    have hi := (h i).map (Int.castRingHom (ZMod 5))
    simpa only [forms_map] using hi
  obtain ⟨hU,hV,hT⟩ := mod_five_profile _ _ _ hm
  obtain ⟨r,s,t,hp⟩ := hp
  have he : (r : ZMod 5)*U+(s : ZMod 5)*V+(t : ZMod 5)*T=1 := by
    have hh := congrArg ((↑) : ℤ → ZMod 5) hp
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_one] using hh
  rw [hU,hV,hT] at he
  exact (show (0 : ZMod 5) ≠ 1 by decide) (by simpa using he)

/-- The profile has no rational affine parameter at all, including the loci
where some of the displayed norms vanish. The proof is a primitive integer
reduction followed by the complete kernel-checked modulus-five calculation. -/
theorem no_rational_profile (x y : ℚ) :
    ¬ ∀ i : Fin 7, IsSquare (forms (2*x) (2*y) 1 i) := by
  intro h
  obtain ⟨r,U,T,V,hr,hU,hT,hV,hp⟩ :=
    rational_primitive_scale (2*x) 1 (2*y) (by positivity)
  have hp' : Primitive U V T := by
    obtain ⟨a,b,c,hp⟩ := hp
    exact ⟨a,c,b,by linarith only [hp]⟩
  apply primitive_not_profile U V T hp'
  intro i
  have hi := h i
  rw [hU,hV,hT,forms_scale] at hi
  have hi' := hi.div (IsSquare.sq r)
  have he : r^2*forms (U : ℚ) (V : ℚ) (T : ℚ) i /r^2 =
      forms (U : ℚ) (V : ℚ) (T : ℚ) i := by field_simp
  rw [he] at hi'
  apply Rat.isSquare_intCast_iff.mp
  have hf := forms_map (Int.castRingHom ℚ) U V T i
  change ((forms U V T i : ℤ) : ℚ) = forms (U : ℚ) (V : ℚ) (T : ℚ) i at hf
  rw [hf]
  exact hi'

#print axioms mod_five_profile
#print axioms no_rational_profile
end Erdos213.EquilateralMidpointProfile
