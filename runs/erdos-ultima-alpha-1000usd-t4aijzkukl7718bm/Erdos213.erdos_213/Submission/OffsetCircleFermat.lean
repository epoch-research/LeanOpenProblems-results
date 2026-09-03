import Submission.OffsetCircle
import Submission.FermatArea

/-! Two Fermat obstructions within the offset-circle construction.
Neither is an obstruction to arbitrary rational-distance configurations. -/
namespace Erdos213.OffsetCircle

lemma one_add_four_fourth_not_square {t : ℚ} (ht : t ≠ 0) :
    ¬ IsSquare (1+4*t^4) := by
  rintro ⟨u,hu⟩
  have htpos : 0<t^2 := sq_pos_of_ne_zero ht
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz] at hu
    nlinarith only [hu,sq_nonneg (t^2)]
  apply FermatArea.no_rational_square_area (x := 1) (y := 2*t^2) (z := |u|)
    (by norm_num) (by positivity) (abs_pos.mpr hu0)
    (show (1 : ℚ)^2+(2*t^2)^2=|u|^2 by
      rw [sq_abs]
      linear_combination hu)
  convert IsSquare.sq t using 1
  ring

/-- The two endpoint conditions cannot hold at the top of a noncentered circle. -/
lemma top_anchor_obstruction (c : ℚ) (hc : c ≠ 0)
    (h0 : IsSquare (kernel c 1 0 1))
    (h1 : IsSquare (c^2+(c-1)^2)) : False := by
  apply one_add_four_fourth_not_square hc
  convert h0.mul h1 using 1
  dsimp [kernel]
  ring

/-- A nontrivial three-square progression cannot have square common difference. -/
lemma two_anchor_squares_obstruction (c : ℚ) (hc : c^2 ≠ 1)
    (ha : IsSquare (c^2-1)) (hb : IsSquare (2*c^2-1)) : False := by
  obtain ⟨r,hr⟩ := ha
  obtain ⟨s,hs⟩ := hb
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hr
    apply hc
    nlinarith only [hr]
  have hcpos : 1<c^2 := by nlinarith only [hr,sq_pos_of_ne_zero hr0]
  have hspos : 1 < |s| := by nlinarith only [hs,sq_abs s,abs_nonneg s,hcpos]
  have hc0 : c ≠ 0 := by intro hz; rw [hz] at hcpos; norm_num at hcpos
  apply FermatArea.no_rational_square_area (x := |s|+1) (y := |s|-1) (z := 2*|c|)
    (by positivity) (by linarith only [hspos]) (by exact mul_pos (by norm_num) (abs_pos.mpr hc0))
    (show (|s|+1)^2+(|s|-1)^2=(2*|c|)^2 by
      nlinarith only [hs,sq_abs s,sq_abs c])
  refine ⟨r,?_⟩
  nlinarith only [hr,hs,sq_abs s]

/-- The torsion-partner involution cannot fix a nonzero rational parameter
satisfying the finite endpoint condition. -/
lemma fixed_partner_obstruction (c t : ℚ) (hc : c ≠ 1) (ht : t ≠ 0)
    (hfix : (c-1)*t^2=c+1)
    (hend : IsSquare (c^2+(c-1)^2*t^2)) : False := by
  have hr : c^2-1=((c-1)*t)^2 := by linear_combination -(c-1)*hfix
  have hrpos : 0<((c-1)*t)^2 := sq_pos_of_ne_zero (mul_ne_zero (sub_ne_zero.mpr hc) ht)
  have hcn : c^2 ≠ 1 := by rw [← hr] at hrpos; linarith only [hrpos]
  have he : c^2+(c-1)^2*t^2=2*c^2-1 := by linear_combination (c-1)*hfix
  rw [he] at hend
  exact two_anchor_squares_obstruction c hcn ⟨(c-1)*t,by simpa only [pow_two] using hr⟩ hend

#print axioms one_add_four_fourth_not_square
#print axioms top_anchor_obstruction
#print axioms two_anchor_squares_obstruction
#print axioms fixed_partner_obstruction
end Erdos213.OffsetCircle
