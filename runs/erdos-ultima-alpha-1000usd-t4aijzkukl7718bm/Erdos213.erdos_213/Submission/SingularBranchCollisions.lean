import Submission.SingularFlatComplete

/-! Two branch-collision loci cannot occur simultaneously at nonzero rational
parameters. This is a restricted arithmetic statement, not an Erdős-213
settlement or a rational-point nonexistence theorem for the full cover. -/
namespace Erdos213.SingularFlatGram
set_option maxHeartbeats 2000000
open Polynomial

lemma collision_sextic_ne_zero (x : ℚ) :
    x^6-6*x^5-7*x^4+6*x^3+12*x^2+6*x+1≠0 := by
  intro hx
  let P : ℤ[X] := X^6-6*X^5-7*X^4+6*X^3+12*X^2+6*X+1
  have hm : P.Monic := by dsimp [P]; monicity!
  have hh : aeval x P=0 := by simpa [P,map_ofNat] using hx
  obtain ⟨k,hk,hkd⟩ := exists_integer_of_is_root_of_monic hm hh
  have hd : k ∣ (1 : ℤ) := by simpa [P] using hkd
  have hu : IsUnit k := isUnit_iff_dvd_one.mpr hd
  rcases Int.isUnit_iff.mp hu with h | h <;>
    simp [h] at hk <;> rw [hk] at hx <;> norm_num at hx

lemma no_normalized_double_collision {p r : ℚ} (hp : p≠0)
    (hF : (p+1)^2-r^2*(2*p+1)=0)
    (hG : (2-r)*p^2+r*(r-1)^2=0) : False := by
  have hz : 4*p^2*(p^6-6*p^5-7*p^4+6*p^3+12*p^2+6*p+1)=0 := by
    linear_combination
      2*(2*p^6-2*p^4*r^2-p^3*r^2+4*p^2*r^2-4*p^2*r+
        4*p*r^2-4*p*r+r^2-r)*hF -
      2*(2*p+1)^2*(p^3*r+2*p^3-2*p*r-2*p-r-1)*hG
  exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))
    (collision_sextic_ne_zero p)) hz

def edgeFaceF (p q r : ℚ) : ℚ := q*(p+q)^2-r^2*(2*p+q)
def edgeFaceG (p q r : ℚ) : ℚ := (2*q-r)*p^2+r*(q-r)^2

/-- The two displayed cubic collision loci have no common nonzero rational
point, even without the positivity assumptions used in the branch audit. -/
theorem no_double_edge_face_collision {p q r : ℚ} (hp : p≠0) (hq : q≠0)
    (hF : edgeFaceF p q r=0) (hG : edgeFaceG p q r=0) : False := by
  have hF' : (p/q+1)^2-(r/q)^2*(2*(p/q)+1)=0 := by
    dsimp [edgeFaceF] at hF
    field_simp
    linear_combination hF
  have hG' : (2-r/q)*(p/q)^2+(r/q)*(r/q-1)^2=0 := by
    dsimp [edgeFaceG] at hG
    field_simp
    linear_combination hG
  exact no_normalized_double_collision (div_ne_zero hp hq) hF' hG'

lemma edgeFaceF_order {p q r : ℚ} (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hF : edgeFaceF p q r=0) : q<r := by
  have he : (r^2-q^2)*(2*p+q)=q*p^2 := by
    dsimp [edgeFaceF] at hF
    linear_combination -hF
  have hpos : 0<(r^2-q^2)*(2*p+q) := by
    rw [he]
    exact mul_pos hq (sq_pos_of_pos hp)
  have hs : 0<r^2-q^2 := (mul_pos_iff_of_pos_right (by linarith : 0<2*p+q)).mp hpos
  nlinarith only [hs,hq,hr]

lemma edgeFaceG_order {p q r : ℚ} (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hG : edgeFaceG p q r=0) : q<r := by
  by_contra h
  have hrq : r≤q := le_of_not_gt h
  have hpos : 0<(2*q-r)*p^2 := mul_pos (by linarith) (sq_pos_of_pos hp)
  have hnonneg : 0≤r*(q-r)^2 := mul_nonneg (le_of_lt hr) (sq_nonneg _)
  dsimp [edgeFaceG] at hG
  linarith only [hG,hpos,hnonneg]

def edgeFaceCollisions (p q r : ℚ) : Fin 4 → ℚ :=
  ![edgeFaceF p q r,edgeFaceF p r q,edgeFaceG p q r,edgeFaceG p r q]

/-- Of the four cubic loci left by the dominant positive-chamber branch
factorization, at most one vanishes at positive rational parameters. -/
theorem at_most_one_edge_face_collision {p q r : ℚ}
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (i j : Fin 4)
    (hi : edgeFaceCollisions p q r i=0)
    (hj : edgeFaceCollisions p q r j=0) : i=j := by
  have h01 : ¬(edgeFaceF p q r=0 ∧ edgeFaceF p r q=0) := by
    rintro ⟨h0,h1⟩
    exact lt_asymm (edgeFaceF_order hp hq hr h0) (edgeFaceF_order hp hr hq h1)
  have h02 : ¬(edgeFaceF p q r=0 ∧ edgeFaceG p q r=0) := by
    rintro ⟨h0,h2⟩
    exact no_double_edge_face_collision (ne_of_gt hp) (ne_of_gt hq) h0 h2
  have h03 : ¬(edgeFaceF p q r=0 ∧ edgeFaceG p r q=0) := by
    rintro ⟨h0,h3⟩
    exact lt_asymm (edgeFaceF_order hp hq hr h0) (edgeFaceG_order hp hr hq h3)
  have h12 : ¬(edgeFaceF p r q=0 ∧ edgeFaceG p q r=0) := by
    rintro ⟨h1,h2⟩
    exact lt_asymm (edgeFaceF_order hp hr hq h1) (edgeFaceG_order hp hq hr h2)
  have h13 : ¬(edgeFaceF p r q=0 ∧ edgeFaceG p r q=0) := by
    rintro ⟨h1,h3⟩
    exact no_double_edge_face_collision (ne_of_gt hp) (ne_of_gt hr) h1 h3
  have h23 : ¬(edgeFaceG p q r=0 ∧ edgeFaceG p r q=0) := by
    rintro ⟨h2,h3⟩
    exact lt_asymm (edgeFaceG_order hp hq hr h2) (edgeFaceG_order hp hr hq h3)
  fin_cases i <;> fin_cases j <;> simp_all [edgeFaceCollisions]

/-- All six quadratic face discriminants are nonzero whenever the six
face lengths are rational in a positive flat Gram matrix of this family. -/
theorem all_face_discriminants_nonzero {p q r A B C : ℚ}
    (htrace : A+B+C=p^2+q^2+r^2)
    (hdet : gramDet A B C (p*q) (p*r) (q*r)=0)
    (hAB : 0<A*B-(p*q)^2) (hAC : 0<A*C-(p*r)^2)
    (hBC : 0<B*C-(q*r)^2)
    (hABp : IsSquare (A+B+2*p*q)) (hABm : IsSquare (A+B-2*p*q))
    (hACp : IsSquare (A+C+2*p*r)) (hACm : IsSquare (A+C-2*p*r))
    (hBCp : IsSquare (B+C+2*q*r)) (hBCm : IsSquare (B+C-2*q*r)) :
    (r^2≠4*p*q ∧ r^2≠ -4*p*q) ∧
    (q^2≠4*p*r ∧ q^2≠ -4*p*r) ∧
    (p^2≠4*q*r ∧ p^2≠ -4*q*r) := by
  obtain ⟨hp,hq,hr⟩ := parameters_nonzero_of_minors hdet hAB hAC hBC
  have hR : ¬(r^2=4*p*q ∨ r^2= -4*p*q) := by
    intro h
    exact no_positive_face_branch_of_flat hp hq hr htrace hdet hAB h hABp hABm
  have hQ : ¬(q^2=4*p*r ∨ q^2= -4*p*r) := by
    intro h
    have hT : A+C+B=p^2+r^2+q^2 := by linear_combination htrace
    have hD : gramDet A C B (p*r) (p*q) (r*q)=0 := by
      dsimp [gramDet] at hdet ⊢
      linear_combination hdet
    exact no_positive_face_branch_of_flat hp hr hq hT hD hAC h hACp hACm
  have hP : ¬(p^2=4*q*r ∨ p^2= -4*q*r) := by
    intro h
    have hT : B+C+A=q^2+r^2+p^2 := by linear_combination htrace
    have hD : gramDet B C A (q*r) (q*p) (r*p)=0 := by
      dsimp [gramDet] at hdet ⊢
      linear_combination hdet
    exact no_positive_face_branch_of_flat hq hr hp hT hD hBC h hBCp hBCm
  exact ⟨not_or.mp hR,not_or.mp hQ,not_or.mp hP⟩

lemma minor_factorization (p q r t : ℚ) (ht : t≠0) (ht1 : 1+t≠0) :
    (diagA p q r t*diagB p q r t-(p*q)^2)*(1+t)^2 =
      -r^2*(p^2*t^2+(p^2+q^2-r^2)*t+q^2) := by
  dsimp [diagA,diagB]
  field_simp
  ring

/-- Positive source parameters for a nondegenerate flat Gram matrix cannot
satisfy all three triangle inequalities. After a permutation, the family
therefore lies in the dominant chamber p>q+r. -/
theorem positive_source_dominant {p q r A B C : ℚ}
    (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (htrace : A+B+C=p^2+q^2+r^2)
    (hdet : gramDet A B C (p*q) (p*r) (q*r)=0)
    (hminor : 0<A*B-(p*q)^2) :
    q+r<p ∨ p+r<q ∨ p+q<r := by
  obtain ⟨t,ht,ht1,hA,hB,hC⟩ := parametrization_complete
    (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hr) htrace hdet hminor
  have he := minor_factorization p q r t ht ht1
  rw [← hA,← hB] at he
  have hs : 0< -r^2*(p^2*t^2+(p^2+q^2-r^2)*t+q^2) := by
    rw [← he]
    exact mul_pos hminor (sq_pos_of_ne_zero ht1)
  have hf : p^2*t^2+(p^2+q^2-r^2)*t+q^2<0 := by
    have hn : r^2*(p^2*t^2+(p^2+q^2-r^2)*t+q^2)<0 := by linarith only [hs]
    by_contra! hz
    exact (not_lt_of_ge (mul_nonneg (sq_nonneg r) hz)) hn
  have hpf : 4*p^2*(p^2*t^2+(p^2+q^2-r^2)*t+q^2)<0 :=
    mul_neg_of_pos_of_neg (by positivity) hf
  have hd : 0<(p^2+q^2-r^2)^2-4*p^2*q^2 := by
    nlinarith only [hpf,sq_nonneg (2*p^2*t+(p^2+q^2-r^2))]
  by_contra! h
  have hl : 0≤r^2-(p-q)^2 := by
    have hm := mul_nonneg (show 0≤r-p+q by linarith only [h.1])
      (show 0≤r+p-q by linarith only [h.2.1])
    nlinarith only [hm]
  have hu : 0≤(p+q)^2-r^2 := by
    have hm := mul_nonneg (show 0≤p+q-r by linarith only [h.2.2])
      (show 0≤p+q+r by linarith only [hp,hq,hr])
    nlinarith only [hm]
  have hh := mul_nonneg hl hu
  nlinarith only [hh,hd]

#print axioms collision_sextic_ne_zero
#print axioms no_double_edge_face_collision
#print axioms at_most_one_edge_face_collision
#print axioms all_face_discriminants_nonzero
#print axioms positive_source_dominant
end Erdos213.SingularFlatGram
