import Submission.CentralCircumcenters
import Submission.NonsplitHyperbola

/-! Several restricted phase alignments are impossible for the central mixed
construction. This is not a classification of its square inputs, much less
of arbitrary integral-distance configurations. -/
namespace Erdos213.CentralCircumcenterPhases
open CentralCircumcenters
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

private lemma norm_three_mod9 : ∀ a b c : ZMod 9,
    a^2+b^2=3*c^2 → a.val%3=0 ∧ b.val%3=0 ∧ c.val%3=0 := by decide +kernel

private lemma three_dvd_of_mod9 {a : ℤ} (h : (a : ZMod 9).val%3=0) : (3 : ℤ)∣a := by
  have he : (((a : ZMod 9).val : ℤ)%3)=0 := by exact_mod_cast h
  rw [ZMod.val_intCast] at he
  norm_num only [Nat.cast_ofNat] at he
  rw [Int.emod_emod_of_dvd _ (by norm_num : (3 : ℤ)∣9)] at he
  exact Int.dvd_of_emod_eq_zero he

lemma integer_norm_three_zero (N : ℕ) : ∀ a b c : ℤ, c.natAbs=N →
    a^2+b^2=3*c^2 → c=0 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b c hN he
    by_cases hc : c=0
    · exact hc
    have hz : (a : ZMod 9)^2+(b : ZMod 9)^2=3*(c : ZMod 9)^2 := by
      have hh := congrArg (fun z : ℤ => (z : ZMod 9)) he
      push_cast at hh
      exact hh
    obtain ⟨ha,hb,hc'⟩ := norm_three_mod9 _ _ _ hz
    obtain ⟨u,rfl⟩ := three_dvd_of_mod9 ha
    obtain ⟨v,rfl⟩ := three_dvd_of_mod9 hb
    obtain ⟨w,rfl⟩ := three_dvd_of_mod9 hc'
    have hw : w≠0 := by intro hw; apply hc; simp [hw]
    have hsmall : u^2+v^2=3*w^2 := by nlinarith only [he]
    have hlt : w.natAbs<N := by
      rw [← hN,Int.natAbs_mul]
      have hpos : 0<w.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hw)
      norm_num
      omega
    exact False.elim (hw (ih w.natAbs hlt u v w rfl hsmall))

lemma rational_sum_sq_ne_three (r p : ℚ) : r^2+p^2≠3 := by
  intro h
  let D : ℤ := r.den*p.den
  let A : ℤ := r.num*p.den
  let B : ℤ := p.num*r.den
  have hnum (q : ℚ) : (q.num : ℚ)=q*q.den := by
    exact (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  have hA : (A : ℚ)=r*D := by dsimp [A,D]; push_cast; rw [hnum]; ring
  have hB : (B : ℚ)=p*D := by dsimp [B,D]; push_cast; rw [hnum]; ring
  have hI : A^2+B^2=3*D^2 := by
    have hQ : (A : ℚ)^2+(B : ℚ)^2=3*(D : ℚ)^2 := by
      rw [hA,hB]
      linear_combination (D : ℚ)^2*h
    exact_mod_cast hQ
  have hzero := integer_norm_three_zero D.natAbs A B D rfl hI
  have hD : (0 : ℤ)<D := by dsimp [D]; positivity
  omega

/-- The congruent-number-two cubic has no affine point with nonzero ordinate.
This follows from the already proved rational fourth-power obstruction. -/
lemma congruent_two_ordinate_zero {X Y : ℚ} (h : Y^2=X*(X^2-4)) : Y=0 := by
  by_contra hy
  have hx4 : X^2-4≠0 := by
    intro he
    rw [he,mul_zero] at h
    exact hy (sq_eq_zero_iff.mp h)
  have ht : (X^2-4)/(2*Y)≠0 := div_ne_zero hx4 (mul_ne_zero (by norm_num) hy)
  apply NonsplitHyperbola.rational_one_add_fourth_not_square ht
    ((X^2+4)*(X^2-4)/(4*Y^2))
  have h4 : Y^4=(X*(X^2-4))^2 := by
    rw [show Y^4=(Y^2)^2 by ring,h]
  field_simp
  nlinarith only [h4]

/-- Alignment with the original radial direction leads to the
congruent-number-two cubic and is impossible away from the real axis. -/
lemma radial_phase_ne_zero {x y : ℚ} (hy : y≠0)
    (hr : IsSquare (radiusSq x y)) :
    2*radiusSq x y*y^2-radiusSq x y-4*y^2+1≠0 := by
  intro hF
  obtain ⟨r,hr⟩ := hr
  have hr' : r^2=radiusSq x y := by nlinarith only [hr]
  have hr0 : r≠0 := by
    intro he
    rw [he] at hr'
    dsimp [radiusSq] at hr'
    nlinarith [sq_pos_of_ne_zero hy,sq_nonneg x]
  have hR2 : radiusSq x y-2≠0 := by
    intro he
    have hR : radiusSq x y=2 := by linarith
    rw [hR] at hF
    ring_nf at hF
    norm_num at hF
  have hE : (4*r*y*(radiusSq x y-2))^2=
      (2*radiusSq x y-2)*((2*radiusSq x y-2)^2-4) := by
    calc
      (4*r*y*(radiusSq x y-2))^2 = 16*r^2*y^2*(radiusSq x y-2)^2 := by ring
      _ = _ := by
        rw [hr']
        linear_combination 8*radiusSq x y*(radiusSq x y-2)*hF
  have hz := congruent_two_ordinate_zero hE
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ)≠0) hr0) hy) hR2) hz

/-- A second low-degree phase relation would require the rational tilt to
have square equal to three. -/
lemma cubic_tilt_phase_ne_zero {x y : ℚ} (hy : y≠0) :
    (radiusSq x y-1)^2-12*y^2≠0 := by
  intro hF
  have he : tilt x y^2=3 := by
    dsimp [tilt]
    field_simp
    nlinarith only [hF]
  have hn : ¬IsSquare (3 : ℚ) := by norm_num
  exact hn ⟨tilt x y,by nlinarith only [he]⟩

/-- Orthogonality of the two residual vectors would give a rational
representation of three as a sum of two squares. -/
lemma orthogonal_phase_ne_zero {x y : ℚ} (hy : y≠0)
    (hr : IsSquare (radiusSq x y))
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    (radiusSq x y-1)^2+4*y^2*(radiusSq x y-2)≠0 := by
  intro hF
  have hk : tilt x y^2=2-radiusSq x y := by
    dsimp [tilt]
    field_simp
    nlinarith only [hF]
  obtain ⟨r,hr⟩ := hr
  obtain ⟨p,hp⟩ := pythagorean_tilt hy hp hm
  apply rational_sum_sq_ne_three r p
  nlinarith only [hr,hp,hk]

private lemma opposite_two_squares {r a b : ℚ} (hr : r≠0)
    (ha : a^2=r^2+2) (hb : b^2=2-r^2) : False := by
  have he : (r*a*b)^2=(-r^2)*((-r^2)^2-4) := by
    rw [mul_pow,mul_pow,ha,hb]
    ring
  have hz := congruent_two_ordinate_zero he
  have ha0 : a≠0 := by intro h; rw [h] at ha; nlinarith [sq_nonneg r]
  have hb0 : b≠0 := by
    intro h
    have hn : ¬IsSquare (2 : ℚ) := by norm_num
    apply hn
    exact ⟨r,by rw [h] at hb; nlinarith only [hb]⟩
  exact (mul_ne_zero (mul_ne_zero hr ha0) hb0) hz

private lemma symmetric_two_squares {r a b : ℚ} (hr : r≠0)
    (ha : a^2=2*r^2+1) (hb : b^2=2*r^2-1) : False := by
  have he : (4*r*a*b)^2=(4*r^2)*((4*r^2)^2-4) := by
    rw [mul_pow,mul_pow,mul_pow,ha,hb]
    ring
  have hz := congruent_two_ordinate_zero he
  have ha0 : a≠0 := by intro h; rw [h] at ha; nlinarith [sq_nonneg r]
  have hb0 : b≠0 := by
    intro h
    have hn : ¬IsSquare (1/2 : ℚ) := by decide +kernel
    apply hn
    exact ⟨r,by rw [h] at hb; nlinarith only [hb]⟩
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ)≠0) hr) ha0) hb0) hz

/-- One of the two genus-two phase profiles is excluded by the same
congruent-number-two obstruction after using the source square conditions. -/
lemma first_sextic_phase_ne_zero {x y : ℚ} (hy : y≠0)
    (hr : IsSquare (radiusSq x y))
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    (radiusSq x y-1)^2*(radiusSq x y+2)+4*y^2*(radiusSq x y-2)≠0 := by
  intro hF
  have hk : tilt x y^2*(radiusSq x y+2)=2-radiusSq x y := by
    dsimp [tilt]
    field_simp
    nlinarith only [hF]
  obtain ⟨r,hr⟩ := hr
  have hr' : r^2=radiusSq x y := by nlinarith only [hr]
  have hr0 : r≠0 := by
    intro he
    rw [he] at hr'
    dsimp [radiusSq] at hr'
    nlinarith [sq_pos_of_ne_zero hy,sq_nonneg x]
  obtain ⟨p,hp⟩ := pythagorean_tilt hy hp hm
  have hp' : p^2=1+tilt x y^2 := by nlinarith only [hp]
  have hp0 : p≠0 := by intro he; rw [he] at hp'; nlinarith [sq_nonneg (tilt x y)]
  have hpa : p^2*(radiusSq x y+2)=4 := by
    linear_combination (radiusSq x y+2)*hp'+hk
  have ha : (2/p)^2=radiusSq x y+2 := by
    field_simp
    nlinarith only [hpa]
  have hb : (2*tilt x y/p)^2=2-radiusSq x y := by
    calc
      _ = tilt x y^2*(2/p)^2 := by ring
      _ = tilt x y^2*(radiusSq x y+2) := by rw [ha]
      _ = _ := hk
  exact opposite_two_squares hr0 (by simpa [hr'] using ha) (by simpa [hr'] using hb)

/-- The reciprocal genus-two profile is likewise excluded. -/
lemma second_sextic_phase_ne_zero {x y : ℚ} (hy : y≠0)
    (hr : IsSquare (radiusSq x y))
    (hp : IsSquare ((x+1)^2+y^2)) (hm : IsSquare ((x-1)^2+y^2)) :
    (radiusSq x y-1)^2*(2*radiusSq x y+1)-4*y^2*(2*radiusSq x y-1)≠0 := by
  intro hF
  have hk : tilt x y^2*(2*radiusSq x y+1)=2*radiusSq x y-1 := by
    dsimp [tilt]
    field_simp
    nlinarith only [hF]
  obtain ⟨r,hr⟩ := hr
  have hr' : r^2=radiusSq x y := by nlinarith only [hr]
  have hr0 : r≠0 := by
    intro he
    rw [he] at hr'
    dsimp [radiusSq] at hr'
    nlinarith [sq_pos_of_ne_zero hy,sq_nonneg x]
  obtain ⟨p,hp⟩ := pythagorean_tilt hy hp hm
  have hp' : p^2=1+tilt x y^2 := by nlinarith only [hp]
  have hp0 : p≠0 := by intro he; rw [he] at hp'; nlinarith [sq_nonneg (tilt x y)]
  have hpa : p^2*(2*radiusSq x y+1)=4*radiusSq x y := by
    linear_combination (2*radiusSq x y+1)*hp'+hk
  have ha : (2*r/p)^2=2*radiusSq x y+1 := by
    field_simp
    nlinarith only [hpa,hr']
  have hb : (2*r*tilt x y/p)^2=2*radiusSq x y-1 := by
    calc
      _ = tilt x y^2*(2*r/p)^2 := by ring
      _ = tilt x y^2*(2*radiusSq x y+1) := by rw [ha]
      _ = _ := hk
  exact symmetric_two_squares hr0 (by simpa [hr'] using ha) (by simpa [hr'] using hb)

#print axioms rational_sum_sq_ne_three
#print axioms congruent_two_ordinate_zero
#print axioms radial_phase_ne_zero
#print axioms cubic_tilt_phase_ne_zero
#print axioms orthogonal_phase_ne_zero
#print axioms first_sextic_phase_ne_zero
#print axioms second_sextic_phase_ne_zero
end Erdos213.CentralCircumcenterPhases
