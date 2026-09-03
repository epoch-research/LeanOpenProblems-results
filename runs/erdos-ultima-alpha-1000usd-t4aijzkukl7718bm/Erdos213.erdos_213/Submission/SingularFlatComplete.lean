import Submission.SingularFlatGram

/-! Completeness of the singular flat-Gram parametrization under its
nondegeneracy assumptions. This does not classify arbitrary integral point
sets and does not settle Erdős 213. -/
namespace Erdos213.SingularFlatGram
set_option maxHeartbeats 2000000

lemma shifted_determinant (p q r a b : ℚ) :
    gramDet (p^2+a) (q^2+b) (r^2-a-b) (p*q) (p*r) (q*r) =
      r^2*a*b-(a+b)*(a*b+p^2*b+q^2*a) := by
  dsimp [gramDet]
  ring

lemma shifted_diagB (p q r t : ℚ) (ht : t≠0) (ht1 : 1+t≠0) :
    diagB p q r t-q^2=t*(diagA p q r t-p^2) := by
  dsimp [diagA,diagB]
  field_simp
  ring

/-- Every nondegenerate real-plane member of the trace-fixed, rank-one
 off-diagonal family is covered. No assertion about rational square lengths
 is part of this parametrization theorem. -/
theorem parametrization_complete {p q r A B C : ℚ}
    (hp : p≠0) (hq : q≠0) (hr : r≠0)
    (htrace : A+B+C=p^2+q^2+r^2)
    (hdet : gramDet A B C (p*q) (p*r) (q*r)=0)
    (hminor : 0<A*B-(p*q)^2) :
    ∃ t : ℚ, t≠0 ∧ 1+t≠0 ∧
      A=diagA p q r t ∧ B=diagB p q r t ∧ C=diagC p q r t := by
  let a := A-p^2
  let b := B-q^2
  have hA : A=p^2+a := by dsimp [a]; ring
  have hB : B=q^2+b := by dsimp [b]; ring
  have hC : C=r^2-a-b := by dsimp [a,b]; linarith only [htrace]
  have hd : r^2*a*b=(a+b)*(a*b+p^2*b+q^2*a) := by
    rw [hA,hB,hC,shifted_determinant] at hdet
    exact sub_eq_zero.mp hdet
  have ha : a≠0 := by
    intro ha
    have hpb : (p*b)^2=0 := by rw [ha] at hd; nlinarith only [hd]
    have hb : b=0 := (mul_eq_zero.mp (eq_zero_of_pow_eq_zero hpb)).resolve_left hp
    rw [hA,hB,ha,hb] at hminor
    nlinarith only [hminor]
  have hb : b≠0 := by
    intro hb
    have hqa : (q*a)^2=0 := by rw [hb] at hd; nlinarith only [hd]
    exact ha ((mul_eq_zero.mp (eq_zero_of_pow_eq_zero hqa)).resolve_left hq)
  have hab : a+b≠0 := by
    intro hab
    rw [hab,zero_mul] at hd
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hr) ha) hb) hd
  let t := b/a
  have ht : t≠0 := div_ne_zero hb ha
  have hbt : b=t*a := by dsimp [t]; field_simp
  have ht1 : 1+t≠0 := by
    intro hz
    apply hab
    rw [hbt]
    linear_combination a*hz
  have hlin : r^2*t=(1+t)*(a*t+p^2*t+q^2) := by
    have hz : a^2*(r^2*t-(1+t)*(a*t+p^2*t+q^2))=0 := by
      rw [hbt] at hd
      linear_combination hd
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 ha))
  have heA : A=diagA p q r t := by
    rw [hA]
    change p^2+a = -q^2/t+r^2/(1+t)
    field_simp
    linear_combination -hlin
  have heB : B=diagB p q r t := by
    have hh := shifted_diagB p q r t ht ht1
    rw [← heA,hA] at hh
    rw [hB,hbt]
    linear_combination -hh
  refine ⟨t,ht,ht1,heA,heB,?_⟩
  have hh := trace_eq p q r t ht ht1
  rw [← heA,← heB] at hh
  linarith only [htrace,hh]

/-- The face-branch obstruction holds for every nondegenerate flat Gram
matrix in this family, without assuming the formulas as input. -/
theorem no_positive_face_branch_of_flat {p q r A B C : ℚ}
    (hp : p≠0) (hq : q≠0) (hr : r≠0)
    (htrace : A+B+C=p^2+q^2+r^2)
    (hdet : gramDet A B C (p*q) (p*r) (q*r)=0)
    (hminor : 0<A*B-(p*q)^2)
    (hbranch : r^2=4*p*q ∨ r^2= -4*p*q)
    (hplus : IsSquare (A+B+2*p*q))
    (hminus : IsSquare (A+B-2*p*q)) : False := by
  obtain ⟨t,ht,ht1,hA,hB,hC⟩ := parametrization_complete hp hq hr htrace hdet hminor
  rw [hA,hB] at hminor hplus hminus
  exact no_positive_face_branch hp hq ht ht1 hbranch hminor hplus hminus

/-- Positive pairwise Gram minors rule out vanishing source parameters. -/
theorem parameters_nonzero_of_minors {p q r A B C : ℚ}
    (hdet : gramDet A B C (p*q) (p*r) (q*r)=0)
    (hAB : 0<A*B-(p*q)^2) (hAC : 0<A*C-(p*r)^2)
    (hBC : 0<B*C-(q*r)^2) : p≠0 ∧ q≠0 ∧ r≠0 := by
  refine ⟨?_,?_,?_⟩
  · intro hp
    have hz : A*(B*C-(q*r)^2)=0 := by
      dsimp [gramDet] at hdet
      rw [hp] at hdet
      nlinarith only [hdet]
    have hA := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hBC)
    rw [hA,hp] at hAB
    norm_num at hAB
  · intro hq
    have hz : B*(A*C-(p*r)^2)=0 := by
      dsimp [gramDet] at hdet
      rw [hq] at hdet
      nlinarith only [hdet]
    have hB := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hAC)
    rw [hB,hq] at hAB
    norm_num at hAB
  · intro hr
    have hz : C*(A*B-(p*q)^2)=0 := by
      dsimp [gramDet] at hdet
      rw [hr] at hdet
      nlinarith only [hdet]
    have hC := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hAB)
    rw [hC,hr] at hAC
    norm_num at hAC

/-- A signed additive relation among the four body lengths reconstructs
exactly the trace and the rank-one off-diagonal source. -/
theorem body_relation_reconstruction {T d e f l₀ l₁ l₂ l₃ : ℚ}
    (h₀ : T+2*d+2*e+2*f=l₀^2)
    (h₁ : T+2*d-2*e-2*f=l₁^2)
    (h₂ : T-2*d+2*e-2*f=l₂^2)
    (h₃ : T-2*d-2*e+2*f=l₃^2)
    (hrel : l₀+l₃=l₁+l₂) :
    T=((l₀+l₃)/2)^2+((l₀-l₂)/2)^2+((l₀-l₁)/2)^2 ∧
    d=((l₀+l₃)/2)*((l₀-l₂)/2) ∧
    e=((l₀+l₃)/2)*((l₀-l₁)/2) ∧
    f=((l₀-l₂)/2)*((l₀-l₁)/2) := by
  have he : l₃=l₁+l₂-l₀ := by linarith only [hrel]
  rw [he] at h₃ ⊢
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (h₀+h₁+h₂+h₃)/4
  · linear_combination (h₀+h₁-h₂-h₃)/8
  · linear_combination (h₀-h₁+h₂-h₃)/8
  · linear_combination (h₀-h₁-h₂+h₃)/8

/-- Completeness for flat cubes whose signed body lengths have the displayed
additive relation. All three positive pairwise minors supply nondegeneracy.
The nine other length-square conditions are NOT resolved by this theorem. -/
theorem signed_body_parametrization_complete {A B C d e f l₀ l₁ l₂ l₃ : ℚ}
    (h₀ : A+B+C+2*d+2*e+2*f=l₀^2)
    (h₁ : A+B+C+2*d-2*e-2*f=l₁^2)
    (h₂ : A+B+C-2*d+2*e-2*f=l₂^2)
    (h₃ : A+B+C-2*d-2*e+2*f=l₃^2)
    (hrel : l₀+l₃=l₁+l₂)
    (hdet : gramDet A B C d e f=0)
    (hAB : 0<A*B-d^2) (hAC : 0<A*C-e^2) (hBC : 0<B*C-f^2) :
    let p := (l₀+l₃)/2
    let q := (l₀-l₂)/2
    let r := (l₀-l₁)/2
    ∃ t : ℚ, t≠0 ∧ 1+t≠0 ∧
      A=diagA p q r t ∧ B=diagB p q r t ∧ C=diagC p q r t := by
  obtain ⟨hT,hd,he,hf⟩ := body_relation_reconstruction h₀ h₁ h₂ h₃ hrel
  rw [hd,he,hf] at hdet
  rw [hd] at hAB
  rw [he] at hAC
  rw [hf] at hBC
  obtain ⟨hp,hq,hr⟩ := parameters_nonzero_of_minors hdet hAB hAC hBC
  exact parametrization_complete hp hq hr hT hdet hAB

#print axioms parametrization_complete
#print axioms no_positive_face_branch_of_flat
#print axioms parameters_nonzero_of_minors
#print axioms body_relation_reconstruction
#print axioms signed_body_parametrization_complete
end Erdos213.SingularFlatGram
