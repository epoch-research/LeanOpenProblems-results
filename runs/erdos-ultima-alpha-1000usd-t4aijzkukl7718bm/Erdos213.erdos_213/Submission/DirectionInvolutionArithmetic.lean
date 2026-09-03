import Submission.DirectionInvolutions
import Submission.IsoscelesCurve

/-! Arithmetic restrictions on the old six-direction support.
These are not a classification of arbitrary rational-distance configurations. -/
namespace Erdos213.DirectionInvolutions
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma one_nine_squares_zero {q : ℚ} (h₁ : IsSquare (q^2+1))
    (h₉ : IsSquare (q^2+9)) : q=0 := by
  obtain ⟨u,hu⟩ := h₁
  obtain ⟨v,hv⟩ := h₉
  have hu' : u^2=q^2+1 := by nlinarith only [hu]
  have hv' : v^2=q^2+9 := by nlinarith only [hv]
  have he : (q*u*v)^2=q^2*(q^2+1)*(q^2+9) := by
    calc
      _ = q^2*u^2*v^2 := by ring
      _ = _ := by rw [hu',hv']
  rcases IsoscelesCurve.plus_curve_abscissa he with h | h | h | h | h
  · nlinarith only [h]
  · nlinarith [sq_nonneg q]
  · nlinarith [sq_nonneg q]
  · have hh : IsSquare (3 : ℚ) := ⟨q,by nlinarith only [h]⟩
    norm_num at hh
  · nlinarith [sq_nonneg q]

/-- None of the three split involutions preserving the six old directions
can preserve an admissible positive rational norm form. -/
theorem old_norm_excludes_symmetry {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    x≠ -(1/2) ∧ r≠1 ∧ r≠ -2*x := by
  obtain ⟨a,ha⟩ := hsq 1
  obtain ⟨b,hb⟩ := hsq 2
  obtain ⟨c,hc⟩ := hsq 3
  obtain ⟨d,hd⟩ := hsq 4
  obtain ⟨e,he⟩ := hsq 5
  change (0 : ℚ)^2-2*x*0*1+r*1^2=a*a at ha
  change (-1 : ℚ)^2-2*x*(-1)*1+r*1^2=b*b at hb
  change (1 : ℚ)^2-2*x*1*1+r*1^2=c*c at hc
  change (-1 : ℚ)^2-2*x*(-1)*2+r*2^2=d*d at hd
  change (-2 : ℚ)^2-2*x*(-2)*1+r*1^2=e*e at he
  norm_num at ha hb hc hd he
  refine ⟨?_,?_,?_⟩
  · intro hx
    subst x
    have h₁ : IsSquare (d^2+1) := ⟨2*a,by nlinarith only [hd,ha]⟩
    have h₉ : IsSquare (d^2+9) := ⟨2*c,by nlinarith only [hd,hc]⟩
    have hh := one_nine_squares_zero h₁ h₉
    nlinarith only [hh,hd,hr]
  · intro hR
    rw [hR] at hr hb hc hd he
    have h₁ : d^2=1+2*b^2 := by nlinarith only [hd,hb]
    have h₂ : c^2=4-b^2 := by nlinarith only [hc,hb]
    rcases IsoscelesCurve.normalized_isosceles h₁ h₂ with h | h
    · nlinarith only [h,hb,hr,sq_nonneg (x+1)]
    · nlinarith only [h,hb,hr,sq_nonneg (x-1)]
  · intro hR
    have h₁ : c^2=1+2*a^2 := by nlinarith only [hc,ha,hR]
    have h₂ : e^2=4-a^2 := by nlinarith only [he,ha,hR]
    rcases IsoscelesCurve.normalized_isosceles h₁ h₂ with h | h
    · nlinarith only [h,ha,hr,sq_nonneg x]
    · nlinarith only [h,ha,hR,hr,sq_nonneg (x+2)]

/-- Three midpoint slices are excluded by the existing elementary descents.
The other midpoint slices are not classified here. -/
theorem old_norm_excludes_midpoints {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i))) :
    x≠0 ∧ x≠ -1 ∧ x≠ -(1/2) := by
  obtain ⟨a,ha⟩ := hsq 1
  obtain ⟨b,hb⟩ := hsq 2
  obtain ⟨c,hc⟩ := hsq 3
  obtain ⟨e,he⟩ := hsq 5
  change (0 : ℚ)^2-2*x*0*1+r*1^2=a*a at ha
  change (-1 : ℚ)^2-2*x*(-1)*1+r*1^2=b*b at hb
  change (1 : ℚ)^2-2*x*1*1+r*1^2=c*c at hc
  change (-2 : ℚ)^2-2*x*(-2)*1+r*1^2=e*e at he
  norm_num at ha hb hc he
  refine ⟨?_,?_,(old_norm_excludes_symmetry hr hsq).1⟩
  · intro hx
    have hn : a≠0 := by intro hz; nlinarith only [hr,ha,hx,hz]
    apply OrthogonalGlobal.no_simultaneous_squares hn
    exact ⟨⟨c,by nlinarith only [hc,ha,hx]⟩,⟨e,by nlinarith only [he,ha,hx]⟩⟩
  · intro hx
    have hn : b≠0 := by intro hz; nlinarith only [hr,hb,hx,hz]
    apply OrthogonalGlobal.no_simultaneous_squares hn
    exact ⟨⟨a,by nlinarith only [ha,hb,hx]⟩,⟨c,by nlinarith only [hc,hb,hx]⟩⟩

def splitShape (m : Coeff) : Prop :=
  (m.b=m.a ∧ m.c=0) ∨ (m.a=0 ∧ m.b=m.c) ∨ (m.b=0 ∧ m.c= -m.a)

lemma finite_split_shapes : ∀ i j k l : Fin 6,
    i≠j → i≠k → i≠l → j≠k → j≠l → k≠l →
    IsSquare (multiplier (twoPairs i j k l)) → splitShape (twoPairs i j k l) := by
  unfold splitShape
  decide +kernel

lemma splitShape_scale (v : ℚ) (m : Coeff) (h : splitShape m) : splitShape (scale v m) := by
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · left; dsimp [scale]; constructor <;> simp [h₁,h₂]
  · right; left; dsimp [scale]; constructor <;> simp [h₁,h₂]
  · right; right; dsimp [scale]; constructor <;> simp [h₁,h₂]

lemma two_old_pairs_splitShape (m : Coeff) (hm : multiplier m≠0)
    (hsq : IsSquare (multiplier m)) (i j k l : Fin 6)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
    (hij' : pair m (oldRoot i) (oldRoot j)=0)
    (hkl' : pair m (oldRoot k) (oldRoot l)=0) : splitShape m := by
  obtain ⟨hne,_⟩ := finite_split_certificate i j k l hij hik hil hjk hjl hkl
  rw [pair_eq_dot] at hij' hkl'
  obtain ⟨v,hv⟩ := proportional_of_two_rows _ _ m hij' hkl' hne
  change m=scale v (twoPairs i j k l) at hv
  have he : multiplier m=v^2*multiplier (twoPairs i j k l) := by rw [hv,multiplier_scale]
  have hv0 : v≠0 := by
    intro h; apply hm; rw [he,h]; ring
  have hmult : IsSquare (multiplier (twoPairs i j k l)) := by
    have hh := hsq.div (IsSquare.sq v)
    rw [he,mul_div_cancel_left₀ _ (pow_ne_zero 2 hv0)] at hh
    exact hh
  rw [hv]
  exact splitShape_scale v _ (finite_split_shapes i j k l hij hik hil hjk hjl hkl hmult)

lemma splitShape_phase {x r : ℚ} (m : Coeff) (hm : multiplier m≠0)
    (h : splitShape m) (hphase : m.c*r-2*m.a*x-m.b=0) :
    x= -(1/2) ∨ r=1 ∨ r= -2*x := by
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · have hn : m.a≠0 := by intro he; apply hm; simp [multiplier,h₂,he]
    left
    have hz : m.a*(2*x+1)=0 := by rw [h₁,h₂] at hphase; nlinarith only [hphase]
    have hh := (mul_eq_zero.mp hz).resolve_left hn
    linarith
  · have hn : m.c≠0 := by intro he; apply hm; simp [multiplier,h₁,he]
    right; left
    have hz : m.c*(r-1)=0 := by rw [h₁,h₂] at hphase; nlinarith only [hphase]
    have hh := (mul_eq_zero.mp hz).resolve_left hn
    linarith
  · have hn : m.a≠0 := by intro he; apply hm; simp [multiplier,h₁,he]
    right; right
    have hz : m.a*(r+2*x)=0 := by rw [h₁,h₂] at hphase; nlinarith only [hphase]
    have hh := (mul_eq_zero.mp hz).resolve_left hn
    linarith

/-- No admissible norm-preserving projective involution can pair two disjoint
pairs of the old six directions. No fixed-point-free assumption is used. -/
theorem norm_no_two_old_pairs {x r : ℚ} (hr : x^2<r)
    (hsq : ∀ i : Fin 6, IsSquare (form x r (oldRoot i)))
    (m : Coeff) (hm : multiplier m≠0) (hphase : m.c*r-2*m.a*x-m.b=0)
    (i j k l : Fin 6) (hij : i≠j) (hik : i≠k) (hil : i≠l)
    (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
    (hij' : pair m (oldRoot i) (oldRoot j)=0)
    (hkl' : pair m (oldRoot k) (oldRoot l)=0) : False := by
  have hnonzero : ∀ a : Fin 6, (oldRoot a).u≠0 ∨ (oldRoot a).v≠0 := by decide +kernel
  have hmapped := square_form_of_wedge x r _ _ (hnonzero j) hij' (hsq j)
  have hmult := multiplier_square hr m hphase (oldRoot i) (hnonzero i) (hsq i) hmapped
  have hs := two_old_pairs_splitShape m hm hmult i j k l hij hik hil hjk hjl hkl hij' hkl'
  obtain ⟨hx,hR,hR'⟩ := old_norm_excludes_symmetry hr hsq
  exact (splitShape_phase m hm hs hphase).elim hx (fun h => h.elim hR hR')

#print axioms one_nine_squares_zero
#print axioms old_norm_excludes_symmetry
#print axioms old_norm_excludes_midpoints
#print axioms finite_split_shapes
#print axioms norm_no_two_old_pairs
end Erdos213.DirectionInvolutions
