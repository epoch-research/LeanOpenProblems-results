import FormalConjecturesUtil

/-! A generic polynomial obstruction for one quartic extension class.
This does not exclude isolated arithmetic specializations, nor does it settle
Erdős 213. The conclusion is a failure to be a split polynomial times a square. -/
namespace Erdos213.PythagoreanQuarticObstruction
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000

def denom (k : ℝ) : ℝ[X] := C (k^2)*X^2+(X+1)^2
def quad (k : ℝ) : ℝ[X] := denom k+C (2*k)*(X+1)
def numerator (k : ℝ) : ℝ[X] := X^2*quad k*quad (-k)
def pointNumerator (k : ℝ) : ℝ[X] := C (2*k)*X*(X+1)

lemma numerator_identity (k : ℝ) :
    pointNumerator k^2-X^2*denom k^2 = -numerator k := by
  simp only [pointNumerator, numerator, quad, denom, map_neg, map_mul, map_pow,
    map_ofNat]
  ring

lemma quad_eval (k x : ℝ) :
    (quad k).eval x = (k^2+1)*x^2+2*(1+k)*x+(1+2*k) := by
  simp only [quad,denom,eval_add,eval_mul,eval_C,eval_pow,eval_X,eval_one]
  ring

lemma quad_positive {k : ℝ} (hk : 0<k) (x : ℝ) : 0<(quad k).eval x := by
  have hid : 4*(k^2+1)*(quad k).eval x =
      (2*(k^2+1)*x+2*(1+k))^2+8*k^3 := by
    rw [quad_eval]
    ring
  have hcube : 0<k^3 := pow_pos hk _
  have hlead : 0<k^2+1 := by positivity
  nlinarith [sq_nonneg (2*(k^2+1)*x+2*(1+k))]

lemma quad_natDegree (k : ℝ) : (quad k).natDegree=2 := by
  apply Nat.le_antisymm
  · unfold quad denom
    compute_degree
  · apply le_natDegree_of_ne_zero
    have hpoly : quad k = C (k^2+1)*X^2+C (2*(1+k))*X+C (1+2*k) := by
      simp only [quad,denom,map_add,map_mul,map_pow,map_ofNat,map_one]
      ring
    have he : (quad k).coeff 2=k^2+1 := by
      rw [hpoly]
      simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
      norm_num
    rw [he]
    positivity

lemma quad_irreducible {k : ℝ} (hk : 0<k) : Irreducible (quad k) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [quad_natDegree]
  · intro x hx
    exact (ne_of_gt (quad_positive hk x)) hx

lemma quad_not_dvd_X (k : ℝ) : ¬quad k ∣ (X : ℝ[X]) := by
  intro h
  have he := natDegree_le_of_dvd h (show (X : ℝ[X])≠0 by simp)
  simp [quad_natDegree] at he

lemma quad_not_dvd_X_add_one (k : ℝ) : ¬quad k ∣ (X+1 : ℝ[X]) := by
  intro h
  have hdeg : (X+1 : ℝ[X]).natDegree=1 := by compute_degree; norm_num
  have hz : (X+1 : ℝ[X])≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hdeg
    contradiction
  have he := natDegree_le_of_dvd h hz
  rw [quad_natDegree,hdeg] at he
  omega

lemma quad_not_dvd_opposite {k : ℝ} (hk : 0<k) : ¬quad k ∣ quad (-k) := by
  intro h
  have hid : quad k-quad (-k)=C (4*k)*(X+1) := by
    simp only [quad,denom,map_neg,map_mul,map_pow,map_ofNat]
    ring
  have hd : quad k ∣ C (4*k)*(X+1) := hid ▸ dvd_sub (dvd_refl _) h
  rcases (quad_irreducible hk).prime.dvd_or_dvd hd with hc | hl
  · have hz : (C (4*k) : ℝ[X])≠0 := by
      simp only [ne_eq,C_eq_zero]
      positivity
    have he := natDegree_le_of_dvd hc hz
    simp only [quad_natDegree,natDegree_C] at he
    omega
  · exact quad_not_dvd_X_add_one k hl

/-- An irreducible factor with no real root cannot occur to odd order in a
split polynomial times a square. The proof uses exact divisibility only. -/
lemma not_split_times_square (q r : ℝ[X]) (hq : Irreducible q)
    (hd : 0<q.natDegree) (hn : ∀ x : ℝ, q.eval x≠0) (hr : ¬q ∣ r) :
    ¬∃ S H : ℝ[X], S.Splits ∧ q*r=S*H^2 := by
  rintro ⟨S,H,hS,he⟩
  have hr0 : r≠0 := by
    intro hz
    exact hr (hz ▸ dvd_zero q)
  have hS0 : S≠0 := by
    intro hz
    rw [hz,zero_mul] at he
    exact (mul_ne_zero hq.ne_zero hr0) he
  have hqS : ¬q ∣ S := by
    intro hdiv
    have hsplit := hS.of_dvd hS0 hdiv
    have hdegree : q.degree≠0 := degree_ne_of_natDegree_ne (show q.natDegree≠0 from Nat.ne_of_gt hd)
    obtain ⟨x,hx⟩ := hsplit.exists_eval_eq_zero hdegree
    exact hn x hx
  have hqHH : q ∣ H^2 := by
    have hdiv : q ∣ S*H^2 := he ▸ dvd_mul_right q r
    exact (hq.prime.dvd_or_dvd hdiv).resolve_left hqS
  obtain ⟨T,hT⟩ := hq.prime.dvd_of_dvd_pow hqHH
  have hc : r=q*(S*T^2) := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [he,hT]
    ring
  exact hr ⟨S*T^2,hc⟩

lemma numerator_not_split_square_of_pos {k : ℝ} (hk : 0<k) :
    ¬∃ S H : ℝ[X], S.Splits ∧ numerator k=S*H^2 := by
  have hq := quad_irreducible hk
  have hrem : ¬quad k ∣ X^2*quad (-k) :=
    hq.prime.not_dvd_mul (fun h => quad_not_dvd_X k (hq.prime.dvd_of_dvd_pow h))
      (quad_not_dvd_opposite hk)
  have hn := not_split_times_square (quad k) (X^2*quad (-k)) hq
    (by rw [quad_natDegree]; norm_num) (fun x => ne_of_gt (quad_positive hk x)) hrem
  rintro ⟨S,H,hS,he⟩
  apply hn
  refine ⟨S,H,hS,?_⟩
  calc
    quad k*(X^2*quad (-k)) = numerator k := by unfold numerator; ring
    _ = S*H^2 := he

lemma numerator_neg (k : ℝ) : numerator (-k)=numerator k := by
  simp only [numerator,neg_neg]
  ring

/-- Uniform in every nonzero real parameter. This is a statement about the
polynomial identity, not about the square status of any one evaluated norm. -/
theorem numerator_not_split_square {k : ℝ} (hk : k≠0) :
    ¬∃ S H : ℝ[X], S.Splits ∧ numerator k=S*H^2 := by
  rcases lt_or_gt_of_ne hk with hn | hp
  · have he := numerator_not_split_square_of_pos (neg_pos.mpr hn)
    simpa only [numerator_neg] using he
  · exact numerator_not_split_square_of_pos hp

#print axioms numerator_identity
#print axioms quad_irreducible
#print axioms not_split_times_square
#print axioms numerator_not_split_square

end
end Erdos213.PythagoreanQuarticObstruction
