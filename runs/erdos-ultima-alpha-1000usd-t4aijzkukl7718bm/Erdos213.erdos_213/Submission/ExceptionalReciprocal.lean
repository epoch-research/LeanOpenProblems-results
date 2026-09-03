import Submission.OffsetCircleExceptional
import Submission.NonsplitHyperbola

/-! A reciprocal extension on the exceptional squared circle cannot produce a
three-point rational-distance set. This is only a restricted-family theorem. -/
namespace Erdos213.OffsetCircle.Exceptional

def invSource (x y : ℚ) : ℚ × ℚ := (-x/(2*x+1),y/(2*x+1))

lemma invSource_on_circle (D x y : ℚ) (hn : 2*x+1 ≠ 0)
    (hc : (x-1)^2+D*y^2=2) :
    ((invSource x y).1-1)^2+D*(invSource x y).2^2=2 := by
  have hn' : x*2+1 ≠ 0 := by simpa only [mul_comm] using hn
  dsimp [invSource]
  field_simp [hn,hn']
  linear_combination hc

lemma invSource_fst_ne_zero (x y : ℚ) (hx : x ≠ 0) (hn : 2*x+1 ≠ 0) :
    (invSource x y).1 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx) hn

lemma invSource_hyperbola (x y : ℚ) (hx : x ≠ 0) (hn : 2*x+1 ≠ 0) :
    hyperbolaPoint (invSource x y).1 (invSource x y).2 = -hyperbolaPoint x y := by
  have hn' : x*2+1 ≠ 0 := by simpa only [mul_comm] using hn
  apply Prod.ext <;> dsimp [invSource,hyperbolaPoint]
  all_goals field_simp [hn,hn']
  all_goals ring

lemma invSource_squared_reciprocal (D x y : ℚ) (hn : 2*x+1 ≠ 0)
    (hc : (x-1)^2+D*y^2=2) :
    squarePoint D (invSource x y).1 (invSource x y).2 =
      ((squarePoint D x y).1/normSq D (squarePoint D x y),
       -(squarePoint D x y).2/normSq D (squarePoint D x y)) := by
  rw [(source_circle_identities D x y hc).1]
  apply Prod.ext <;> dsimp [invSource,squarePoint]
  all_goals field_simp

lemma hyperbolaPoint_injective (x y u v : ℚ) (hx : x ≠ 0) (hu : u ≠ 0)
    (he : hyperbolaPoint x y=hyperbolaPoint u v) : (x,y)=(u,v) := by
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  dsimp [hyperbolaPoint] at hf hs
  have hxu : x=u := by field_simp at hf; nlinarith only [hf]
  subst u
  apply Prod.ext
  · rfl
  · dsimp
    field_simp at hs
    exact hs

lemma square_distance_transfers (D x y u v : ℚ) (hx : x ≠ 0) (hu : u ≠ 0)
    (hp : (x-1)^2+D*y^2=2) (hq : (u-1)^2+D*v^2=2)
    (hs : IsSquare (distSq D (squarePoint D x y) (squarePoint D u v))) :
    IsSquare (distSq D (hyperbolaPoint x y) (hyperbolaPoint u v)) := by
  rw [exceptional_distance_factor D x y u v hx hu hp hq]
  exact hs.div (IsSquare.sq (4*x*u))

/-- The pole of the Mobius chart cannot be joined to a non-pole squared source
point by a rational distance; its squared distance has square class 2. -/
lemma pole_distance_not_square (D x y : ℚ) (hx : x ≠ 0)
    (hc : (x-1)^2+D*y^2=2) :
    ¬ IsSquare (distSq D (squarePoint D x y) (-1,0)) := by
  have he : distSq D (squarePoint D x y) (-1,0)=8*x^2 := by
    convert (source_circle_identities D x y hc).2.1 using 1
    dsimp [distSq,normSq,squarePoint]
    ring
  rw [he]
  intro h
  have hn : ¬ IsSquare (2 : ℚ) := by decide +kernel
  apply hn
  obtain ⟨r,hr⟩ := h
  refine ⟨r/(2*x),?_⟩
  field_simp
  linear_combination hr

lemma source_norm_pos (D x y : ℚ) (hD : 0<D) (hc : (x-1)^2+D*y^2=2) :
    0<2*x+1 := by
  nlinarith only [hc,sq_nonneg x,mul_nonneg (le_of_lt hD) (sq_nonneg y)]

lemma zero_source_is_pole (D y : ℚ) (hc : (0-1 : ℚ)^2+D*y^2=2) :
    squarePoint D 0 y=(-1,0) := by
  apply Prod.ext <;> dsimp [squarePoint] <;> nlinarith only [hc]

/-- An existing rational edge cannot be extended by adjoining the reciprocal
of one endpoint while remaining in this squared-source-circle family. -/
lemma no_reciprocal_triple (D x y u v : ℚ) (hD : 0<D)
    (hx : x ≠ 0) (hu : u ≠ 0)
    (hp : (x-1)^2+D*y^2=2) (hq : (u-1)^2+D*v^2=2)
    (hne : (u,v) ≠ (x,y)) (hne' : (u,v) ≠ invSource x y)
    (h1 : IsSquare (distSq D (squarePoint D u v) (squarePoint D x y)))
    (h2 : IsSquare (distSq D (squarePoint D u v)
      (squarePoint D (invSource x y).1 (invSource x y).2)))
    (h3 : IsSquare (distSq D (squarePoint D x y)
      (squarePoint D (invSource x y).1 (invSource x y).2))) : False := by
  have hn : 2*x+1 ≠ 0 := ne_of_gt (source_norm_pos D x y hD hp)
  have hi := invSource_on_circle D x y hn hp
  have hix := invSource_fst_ne_zero x y hx hn
  have he := invSource_hyperbola x y hx hn
  apply NonsplitHyperbola.no_antipodal_triple D hD (hyperbolaPoint u v) (hyperbolaPoint x y)
  · exact image_on_hyperbola D u v hu hq
  · exact image_on_hyperbola D x y hx hp
  · intro hh
    exact hne (hyperbolaPoint_injective u v x y hu hx hh)
  · intro hh
    rw [← he] at hh
    exact hne' (hyperbolaPoint_injective u v _ _ hu hix hh)
  · exact square_distance_transfers D u v x y hu hx hq hp h1
  · rw [← he]
    exact square_distance_transfers D u v _ _ hu hix hq hi h2
  · rw [← he]
    exact square_distance_transfers D x y _ _ hx hix hp hi h3

lemma reciprocal_pair_control :
    invSource (1/2) (1/2)=(-1/4,1/4) ∧
    squarePoint 7 (1/2) (1/2)=(-3/2,1/2) ∧
    squarePoint 7 (-1/4) (1/4)=(-3/8,-1/8) ∧
    distSq 7 (squarePoint 7 (1/2) (1/2)) (squarePoint 7 (-1/4) (1/4))=2^2 := by
  decide +kernel

#print axioms invSource_squared_reciprocal
#print axioms hyperbolaPoint_injective
#print axioms pole_distance_not_square
#print axioms no_reciprocal_triple
#print axioms reciprocal_pair_control
end Erdos213.OffsetCircle.Exceptional
