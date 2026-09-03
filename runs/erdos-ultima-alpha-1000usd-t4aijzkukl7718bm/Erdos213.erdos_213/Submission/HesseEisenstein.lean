import Submission.HesseSplitSeven
import Submission.RationalEisenstein

/-! Transfer of the split-prime obstruction to Q(sqrt(-3)). No parameter
integrality or denominator restriction is imposed. This is not a solution
of the arbitrary-cardinality integral-distance conjecture. -/
namespace Erdos213.HesseEisenstein
open RationalEisenstein HesseSplitSeven
open scoped QuadraticAlgebra
noncomputable section
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- One of the two split embeddings; its conjugate uses -r. -/
def embedding (r : ℚ_[7]) (hr : r^2=-3) : G →+* ℚ_[7] where
  toFun z := (z.re : ℚ_[7])+(z.im : ℚ_[7])*r
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,Rat.cast_add]
    ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
    push_cast
    ring_nf
    rw [hr]
    ring

lemma neg_root {r : ℚ_[7]} (hr : r^2=-3) : (-r)^2=-3 := by simpa using hr

lemma embedding_rr (r : ℚ_[7]) (hr : r^2=-3) : embedding r hr rr=r := by
  simp [embedding,rr]

lemma norm_split (r : ℚ_[7]) (hr : r^2=-3) (z : G) :
    (norm z : ℚ_[7])=embedding r hr z*embedding (-r) (neg_root hr) z := by
  rw [norm_components]
  simp only [embedding,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]
  push_cast
  linear_combination (z.im : ℚ_[7])^2*hr

/-- The six conditions omit the unit vertex 1 from the old seven-condition
center/equilateral-midpoint profile. Two atoms are scaled by 2. -/
def sixProfile (t : G) : Fin 6 → ℚ :=
  ![norm t,3*norm (2*t+1-rr),3*norm (2*t+1+rr),
    3*norm (t-1+rr),3*norm (t+2),3*norm (t-1-rr)]

lemma profile_split (r : ℚ_[7]) (hr : r^2=-3) (t : G) (i : Fin 6) :
    (sixProfile t i : ℚ_[7])=
      profile r (embedding r hr t) 1 (embedding (-r) (neg_root hr) t) 1 i := by
  fin_cases i <;> dsimp [sixProfile,profile]
  all_goals push_cast
  all_goals rw [norm_split r hr]
  all_goals simp only [map_add,map_sub,map_mul,map_ofNat,map_one,embedding_rr]
  all_goals ring

def parameter (s : G) : G := (s^3+2)/(3*s)

lemma embedding_parameter (r : ℚ_[7]) (hr : r^2=-3) (s : G) :
    embedding r hr (parameter s)=hesse (embedding r hr s) := by
  simp only [parameter,hesse,map_div₀,map_pow,map_add,map_mul,map_ofNat]

/-- The six norm values cannot even share a square class on this base change.
The proof uses a genuine split 7-adic embedding and handles both independently
nonintegral local components by projective normalization. -/
theorem no_six_profile (s : G) (hs : s≠0) :
    ¬(∀ i j : Fin 6, IsSquare (sixProfile (parameter s) i*sixProfile (parameter s) j)) := by
  intro h
  obtain ⟨r,hr,hr2⟩ := root_lift
  have hrQ : (r : ℚ_[7])^2=-3 := congrArg (fun z : ℤ_[7] => (z : ℚ_[7])) hr
  apply no_padic_profile r hr2 (embedding r hrQ s) (embedding (-(r : ℚ_[7])) (neg_root hrQ) s)
    (by simpa only [map_zero] using (embedding r hrQ).injective.ne hs)
    (by simpa only [map_zero] using (embedding (-(r : ℚ_[7])) (neg_root hrQ)).injective.ne hs)
  intro i j
  have hh := (h i j).map (Rat.castHom ℚ_[7])
  change IsSquare (((sixProfile (parameter s) i : ℚ) : ℚ_[7])*
    ((sixProfile (parameter s) j : ℚ) : ℚ_[7])) at hh
  rw [profile_split r hrQ _ i,profile_split r hrQ _ j,embedding_parameter,embedding_parameter] at hh
  exact hh

#print axioms norm_split
#print axioms profile_split
#print axioms no_six_profile
end
end Erdos213.HesseEisenstein
