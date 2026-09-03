import Submission.ObliqueMedianBridge
import Submission.IsoscelesCurve

/-! Arithmetic restrictions on concyclic quadruples in a rational-distance
oblique 3-by-3 grid. No existence of such a grid is asserted. -/
namespace Erdos213.GridCircleResonance
open ObliqueMedianBridge MedianFlipClosure
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

lemma medians_unequal {x : Triple} (hh : heron x ≠ 0) (hq : RationalMedians x) :
    x 0 ≠ x 1 := by
  intro he
  obtain ⟨a,ha⟩ := hq.1 0
  obtain ⟨b,hb⟩ := hq.1 1
  obtain ⟨c,hc⟩ := hq.1 2
  have ha' : x 0=a^2 := by simpa only [pow_two] using ha
  have hb' : x 1=b^2 := by simpa only [pow_two] using hb
  have hc' : x 2=c^2 := by simpa only [pow_two] using hc
  have h₁ : IsSquare (2*b^2+2*c^2-a^2) := by
    convert hq.2 0 using 1
    simp [median,total,Fin.sum_univ_three,ha',hb',hc']
    ring
  have h₂ : IsSquare (2*a^2+2*b^2-c^2) := by
    convert hq.2 2 using 1
    simp [median,total,Fin.sum_univ_three,ha',hb',hc']
    ring
  have hz := IsoscelesCurve.isosceles_heron_zero (by simpa [ha',hb'] using he) h₁ h₂
  apply hh
  simpa only [heron_expanded,ha',hb',hc',← pow_mul] using hz

lemma medians_forbidden {x : Triple} (hh : heron x ≠ 0) (hq : RationalMedians x)
    (p : Equiv.Perm (Fin 3)) :
    x (p 0) ≠ x (p 1) ∧ x (p 2) ≠ x (p 0)+x (p 1) := by
  have hp : heron (x ∘ p) ≠ 0 := by rwa [heron_permute]
  exact ⟨medians_unequal hp (hq.permuting p),
    fun he => right_impossible hp (hq.permuting p) he⟩

lemma directions_neg {A B H : ℚ} (h : Directions A B H) : Directions A B (-H) := by
  unfold Directions at h ⊢
  simp only [mul_neg,sub_neg_eq_add]
  simp only [← sub_eq_add_neg]
  tauto

lemma directions_swap {A B H : ℚ} (h : Directions A B H) : Directions B A H := by
  unfold Directions at h ⊢
  ring_nf at h ⊢
  tauto

lemma positive_diagonal {A B H : ℚ} (hp : 0<A*B-H^2) (h : Directions A B H) :
    0<A ∧ 0<B := by
  obtain ⟨a,ha⟩ := h.1
  obtain ⟨b,hb⟩ := h.2.1
  constructor <;> nlinarith [sq_nonneg H,sq_nonneg a,sq_nonneg b]

lemma median_relations {A B H : ℚ} (hp : 0<A*B-H^2) (h : Directions A B H) :
    A ≠ B ∧ H ≠ 0 ∧ A+2*H ≠ 0 ∧ B+2*H ≠ 0 ∧ A+H ≠ 0 ∧ B+H ≠ 0 := by
  have hq := (grid_iff_two_median_triangles A B H).mp ((grid_iff_directions A B H).mpr h)
  have hh : heron (triangle A B H) ≠ 0 := by
    rw [heron_triangle]
    exact ne_of_gt (mul_pos (by norm_num) hp)
  have h₀ := medians_forbidden hh hq.1 (Equiv.refl _)
  have h₁ := medians_forbidden hh hq.1 (Equiv.swap 0 2)
  have h₂ := medians_forbidden hh hq.1 (Equiv.swap 1 2)
  norm_num [triangle,Matrix.cons_val_two,Equiv.swap_apply_def] at h₀ h₁ h₂
  simp only [show ¬((1 : Fin 3)=2) from by decide,
    show ¬((0 : Fin 3)=2) from by decide, ↓reduceIte,
    Matrix.cons_val_zero,Matrix.cons_val_one] at h₁ h₂
  refine ⟨h₀.1,?_,?_,?_,?_,?_⟩ <;> intro he
  · apply h₀.2; linarith
  · apply h₁.1; linarith
  · apply h₂.1; linarith
  · apply h₂.2; linarith
  · apply h₁.2; linarith

lemma nonsquare_ratio {x y c : ℚ} (hx : IsSquare x) (hy : IsSquare y)
    (h0 : x ≠ 0) (hc : ¬IsSquare c) (he : y=c*x) : False := by
  apply hc
  convert hy.div hx using 1
  rw [he]
  field_simp

lemma sum_four_ne {A B H : ℚ} (hp : 0<A*B-H^2) (h : Directions A B H) :
    A+B-4*H ≠ 0 := by
  intro he
  have hab := positive_diagonal hp h
  apply nonsquare_ratio h.2.2.2.1 h.2.2.1
    (show A+B-2*H ≠ 0 by linarith) (by decide +kernel : ¬IsSquare (3 : ℚ))
  linarith

lemma mixed_two_ne {A B H : ℚ} (hp : 0<A*B-H^2) (h : Directions A B H) :
    A-2*B-2*H ≠ 0 := by
  intro he
  have hab := positive_diagonal hp h
  apply nonsquare_ratio h.2.1 h.2.2.2.1 (ne_of_gt hab.2)
    (by decide +kernel : ¬IsSquare (3 : ℚ))
  linarith

lemma mixed_four_ne {A B H : ℚ} (hp : 0<A*B-H^2) (h : Directions A B H) :
    A-2*B-4*H ≠ 0 := by
  intro he
  have hab := positive_diagonal hp h
  apply nonsquare_ratio h.2.2.2.2.2.2.1 h.2.2.2.2.2.1
    (show A+4*B+4*H ≠ 0 by linarith)
    (by decide +kernel : ¬IsSquare (3/2 : ℚ))
  linarith

def gx : Fin 9 → ℚ := ![0,0,0,1,1,1,2,2,2]
def gy : Fin 9 → ℚ := ![0,1,2,0,1,2,0,1,2]

def circle (A B H : ℚ) (i j k l : Fin 9) : ℚ :=
  let x := fun q => gx q-gx i
  let y := fun q => gy q-gy i
  let n := fun q => norm A B H (x q) (y q)
  x j*(y k*n l-n k*y l)-y j*(x k*n l-n k*x l)+n j*(x k*y l-y k*x l)

/-- The only circle-degeneracy hyperplanes not already excluded by the
arithmetic and positivity are the four quarter-metric resonances. -/
theorem sorted_circle_ne {A B H : ℚ} (hp : 0<A*B-H^2) (h : Directions A B H)
    (haP : A+4*H ≠ 0) (haM : A-4*H ≠ 0)
    (hbP : B+4*H ≠ 0) (hbM : B-4*H ≠ 0)
    (i j k l : Fin 9) (hij : i<j) (hjk : j<k) (hkl : k<l) :
    circle A B H i j k l ≠ 0 := by
  have hn := directions_neg h
  have hs := directions_swap h
  have hsn := directions_neg hs
  have hpn : 0<A*B-(-H)^2 := by nlinarith only [hp]
  have hps : 0<B*A-H^2 := by nlinarith only [hp]
  have hpsn : 0<B*A-(-H)^2 := by nlinarith only [hp]
  obtain ⟨hA,hB⟩ := positive_diagonal hp h
  have hplus : 0<A+B+2*H := by
    by_contra! he
    have hm := mul_nonpos_of_nonneg_of_nonpos hA.le he
    nlinarith [sq_nonneg (A+H)]
  have hminus : 0<A+B-2*H := by
    by_contra! he
    have hm := mul_nonpos_of_nonneg_of_nonpos hA.le he
    nlinarith [sq_nonneg (A-H)]
  obtain ⟨hab,hH,ha2,hb2,ha1,hb1⟩ := median_relations hp h
  obtain ⟨_,_,han2,hbn2,han1,hbn1⟩ := median_relations hpn hn
  have hs4 := sum_four_ne hp h
  have hsn4 := sum_four_ne hpn hn
  have hm2 := mixed_two_ne hp h
  have hmn2 := mixed_two_ne hpn hn
  have hms2 := mixed_two_ne hps hs
  have hmsn2 := mixed_two_ne hpsn hsn
  have hm4 := mixed_four_ne hp h
  have hmn4 := mixed_four_ne hpn hn
  have hms4 := mixed_four_ne hps hs
  have hmsn4 := mixed_four_ne hpsn hsn
  clear h hn hs hsn hp hpn hps hpsn
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals fin_cases k <;> norm_num at hjk
  all_goals fin_cases l <;> norm_num at hkl
  all_goals norm_num [circle,gx,gy,ObliqueMedianBridge.norm]
  all_goals intro he
  all_goals first
    | linarith only [he,hA,hB,hplus,hminus]
    | exact hab (by linarith only [he])
    | exact hH (by linarith only [he])
    | exact ha2 (by linarith only [he])
    | exact hb2 (by linarith only [he])
    | exact ha1 (by linarith only [he])
    | exact hb1 (by linarith only [he])
    | exact han2 (by linarith only [he])
    | exact hbn2 (by linarith only [he])
    | exact han1 (by linarith only [he])
    | exact hbn1 (by linarith only [he])
    | exact hs4 (by linarith only [he])
    | exact hsn4 (by linarith only [he])
    | exact hm2 (by linarith only [he])
    | exact hmn2 (by linarith only [he])
    | exact hms2 (by linarith only [he])
    | exact hmsn2 (by linarith only [he])
    | exact hm4 (by linarith only [he])
    | exact hmn4 (by linarith only [he])
    | exact hms4 (by linarith only [he])
    | exact hmsn4 (by linarith only [he])
    | exact haP (by linarith only [he])
    | exact haM (by linarith only [he])
    | exact hbP (by linarith only [he])
    | exact hbM (by linarith only [he])

#print axioms sorted_circle_ne
#print axioms medians_forbidden
#print axioms median_relations
#print axioms sum_four_ne
#print axioms mixed_two_ne
#print axioms mixed_four_ne
end Erdos213.GridCircleResonance
