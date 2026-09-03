import FormalConjecturesUtil
import Submission.WengerRestrictionGeometry

/-! A translation-pair obstruction to scalar group voltages on the affine
three-coordinate quadrangle graph. It includes quadratic-extension classes,
but does not address arbitrary projective permutation lifts or settle Erdős 713. -/
open SimpleGraph
namespace Erdos713C8QuadraticClassVoltage
variable {K W : Type*} [Field K] [CharP K 2] [CommGroup W]
set_option maxHeartbeats 2000000

abbrev Vertex (K W : Type*) := (Fin 3 → K) × W

def Inc (f : K → W) (p l : Vertex K W) : Prop :=
  p.1 1+l.1 1=l.1 0*p.1 0 ∧
  p.1 2+l.1 2=l.1 1*p.1 0 ∧
  l.2=f (l.1 0*p.1 0)*p.2

abbrev graph (f : K → W) := Erdos713C6.bipGraph (Inc f)

/-- Only one nontrivial translation pair is needed. Its octagon has four
distinct base points and four distinct base lines, regardless of the sheets. -/
theorem contains_of_pair (f : K → W) (u : K) (hu : u ≠ 0) (hu1 : u ≠ 1)
    (hpair : f u*f (u+1)=f 0*f 1) : cycleGraph 8 ⊑ graph f := by
  have htwo : (2 : K)=0 := CharP.cast_eq_zero K 2
  have huu : u+u=0 := by linear_combination u*htwo
  have hu' : u+1 ≠ 0 := by
    intro he
    apply hu1
    linear_combination he-htwo
  have hu1' : u+1 ≠ 1 := by intro he; apply hu; linear_combination he
  have hun : u ≠ u+1 := by intro he; exact one_ne_zero (by linear_combination -he)
  have hlast : f (u+1)*((f 1)⁻¹*f u)=f 0 := by
    calc
      _ = (f u*f (u+1))*(f 1)⁻¹ := by ac_rfl
      _ = _ := by rw [hpair]; simp
  let p : Fin 4 → Vertex K W :=
    ![(![0,0,0],1),(![1,0,0],1),(![0,u,u],(f 0)⁻¹*f u),
      (![1,u+1,0],(f 1)⁻¹*f u)]
  let l : Fin 4 → Vertex K W :=
    ![(![0,0,0],f 0),(![u,u,u],f u),(![1,u,u],f u),(![u+1,0,0],f 0)]
  have hp : Function.Injective p := by
    intro i j he
    have h0 := congrArg (fun z : Vertex K W => z.1 0) he
    have h1 := congrArg (fun z : Vertex K W => z.1 1) he
    fin_cases i <;> fin_cases j <;> dsimp [p] at h0 h1
    all_goals first | rfl | exact (zero_ne_one h0).elim | exact (one_ne_zero h0).elim |
      exact (hu h1).elim | exact (hu h1.symm).elim |
      exact (hu' h1).elim | exact (hu' h1.symm).elim
  have hl : Function.Injective l := by
    intro i j he
    have h0 := congrArg (fun z : Vertex K W => z.1 0) he
    fin_cases i <;> fin_cases j <;> dsimp [l] at h0
    all_goals first | rfl | exact (zero_ne_one h0).elim | exact (one_ne_zero h0).elim |
      exact (hu h0).elim | exact (hu h0.symm).elim |
      exact (hu1 h0).elim | exact (hu1 h0.symm).elim |
      exact (hu' h0).elim | exact (hu' h0.symm).elim |
      exact (hu1' h0).elim | exact (hu1' h0.symm).elim |
      exact (hun h0).elim | exact (hun h0.symm).elim
  have hshift : u+1+u=1 := by linear_combination huu
  apply Erdos713WengerRestriction.contains_of_octagon (Inc f) p l hp hl
  · intro i
    fin_cases i <;> simp [Inc,p,l,huu,hlast]
  · intro i
    fin_cases i <;> simp [Inc,p,l,huu,hshift]

/-- A constant product on every translation pair is incompatible with C8-freeness. -/
theorem contains_translation_pairs [Fintype K] (f : K → W)
    (hpair : ∀ u, f u*f (u+1)=f 0*f 1) (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ graph f := by
  classical
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1} : Finset K)) (t := Finset.univ) (by simpa using hq)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu
  exact contains_of_pair f u hu.1 hu.2 (hpair u)

section QuadraticClasses
variable {L : Type*} [Field L]

omit [CharP K 2] in
lemma translated_ne_zero (φ : K →+* L) (j : L) (hOutside : ∀ t, j ≠ φ t) (t : K) :
    j+φ t ≠ 0 := by
  intro he
  apply hOutside (-t)
  rw [map_neg]
  linear_combination he

def quadraticVoltage (φ : K →+* L) (j : L) (hOutside : ∀ t, j ≠ φ t)
    (χ : Lˣ →* W) (t : K) : W :=
  χ (Units.mk0 (j+φ t) (translated_ne_zero φ j hOutside t))

omit [CharP K 2] in
/-- The two translated factors multiply to a nonzero base-field element. -/
lemma quadratic_pair [CharP L 2] (φ : K →+* L) (j : L) (δ : K)
    (hj : j^2+j=φ δ) (hOutside : ∀ t, j ≠ φ t)
    (χ : Lˣ →* W) (hχ : ∀ a : Kˣ, χ (Units.map φ.toMonoidHom a)=1) (t : K) :
    quadraticVoltage φ j hOutside χ t * quadraticVoltage φ j hOutside χ (t+1) = 1 := by
  have he : (j+φ t)*(j+φ (t+1))=φ (δ+t^2+t) := by
    simp only [map_add,map_one,map_pow]
    linear_combination hj + (j*φ t)*(CharP.cast_eq_zero L 2)
  have hn : δ+t^2+t ≠ 0 := by
    intro hh
    apply mul_ne_zero (translated_ne_zero φ j hOutside t) (translated_ne_zero φ j hOutside (t+1))
    rw [he,hh,map_zero]
  have hu : Units.mk0 (j+φ t) (translated_ne_zero φ j hOutside t) *
      Units.mk0 (j+φ (t+1)) (translated_ne_zero φ j hOutside (t+1)) =
      Units.map φ.toMonoidHom (Units.mk0 (δ+t^2+t) hn) := by
    apply Units.ext
    exact he
  simp only [quadraticVoltage,← map_mul,hu,hχ]

/-- Every multiplicative class map annihilating base-field units gives the
same obstruction. In particular the issue is not a choice of coordinates
for the quadratic extension or its norm-one group. -/
theorem contains_quadratic_classes [Fintype K] [CharP L 2]
    (φ : K →+* L) (j : L) (δ : K) (hj : j^2+j=φ δ)
    (hOutside : ∀ t, j ≠ φ t) (χ : Lˣ →* W)
    (hχ : ∀ a : Kˣ, χ (Units.map φ.toMonoidHom a)=1)
    (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (quadraticVoltage φ j hOutside χ) := by
  apply contains_translation_pairs _ ?_ hq
  intro t
  rw [quadratic_pair φ j δ hj hOutside χ hχ]
  have hh := quadratic_pair φ j δ hj hOutside χ hχ 0
  simpa only [zero_add] using hh.symm

end QuadraticClasses

#print axioms contains_of_pair
#print axioms contains_translation_pairs
#print axioms quadratic_pair
#print axioms contains_quadratic_classes
end Erdos713C8QuadraticClassVoltage
