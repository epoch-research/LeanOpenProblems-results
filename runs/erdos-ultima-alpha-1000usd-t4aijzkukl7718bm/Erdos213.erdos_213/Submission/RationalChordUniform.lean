import Submission.RationalChordCircle
import Submission.PolynomialSquareValues

/-! A uniform rational-function growth rule is confined to a line or circle.
Selected sparse parameter sets and n-dependent formulas are not covered. -/
namespace Erdos213.RationalChordUniform
open Polynomial EuclideanGeometry RationalChordPencil RationalChordCircle
noncomputable section
set_option maxHeartbeats 2000000

lemma integer_roots_finite {f : ℂ[X]} (hf : f≠0) :
    Set.Finite {n : ℤ | f.eval (n : ℂ)=0} := by
  exact (finite_setOf_isRoot hf).preimage (Int.cast_injective (α := ℂ)).injOn

lemma constant_curve_of_pencil_zero {a b : ℂ[X]} {u : ℂ} (h : pencil a b u=0) :
    Collinear ℝ (curve a b) := by
  have ha : a=C u*b := sub_eq_zero.mp h
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨u,(0 : ℂ),?_⟩
  rintro z ⟨t,ht,rfl⟩
  refine ⟨0,?_⟩
  change a.eval (t : ℂ)/b.eval (t : ℂ)=_
  rw [ha,eval_mul,eval_C,mul_div_cancel_right₀ _ ht]
  simp

lemma infinite_integer_values (a b : ℂ[X]) (hb : b≠0) (N : ℤ)
    (hconst : ∀ u : ℂ, pencil a b u≠0) :
    Set.Infinite ((fun n : ℤ => a.eval (n : ℂ)/b.eval (n : ℂ)) ''
      {n : ℤ | N≤n ∧ b.eval (n : ℂ)≠0}) := by
  let T : Set ℤ := {n | N≤n ∧ b.eval (n : ℂ)≠0}
  let U : Set ℂ := (fun n : ℤ => a.eval (n : ℂ)/b.eval (n : ℂ)) '' T
  have hT : T.Infinite := by
    have h := (Set.Ici_infinite N).diff (integer_roots_finite hb)
    exact h
  intro hU
  have hf : (⋃ u∈U, {n : ℤ | (pencil a b u).eval (n : ℂ)=0}).Finite :=
    hU.biUnion fun u _ => integer_roots_finite (hconst u)
  apply hT
  apply hf.subset
  intro n hn
  let u := a.eval (n : ℂ)/b.eval (n : ℂ)
  have hu : u∈U := ⟨n,hn,rfl⟩
  refine Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,?_⟩⟩
  change (pencil a b u).eval (n : ℂ)=0
  simp only [pencil,eval_sub,eval_mul,eval_C,u]
  rw [div_mul_cancel₀ _ hn.2,sub_self]

lemma algebraMap_rat (q : ℚ) : algebraMap ℚ ℂ q=(q : ℂ) := rfl

abbrev mapQ (f : ℚ[X]) : ℂ[X] := f.map (algebraMap ℚ ℂ)
def unitD (D : ℚ) : ℂ := (Real.sqrt (D : ℝ) : ℂ)*Complex.I
def lift (D : ℚ) (x y : ℚ[X]) : ℂ[X] := mapQ x+C (unitD D)*mapQ y

lemma bar_mapQ (f : ℚ[X]) : bar (mapQ f)=mapQ f := by
  ext n
  simp

lemma bar_unitD (D : ℚ) : starRingEnd ℂ (unitD D)= -unitD D := by
  simp [unitD]

lemma unitD_sq (D : ℚ) (hD : 0≤D) : (unitD D)^2= -(D : ℂ) := by
  unfold unitD
  rw [mul_pow,Complex.I_sq]
  have hh : ((Real.sqrt (D : ℝ) : ℂ))^2=(D : ℂ) := by
    have h := Real.sq_sqrt (show (0 : ℝ)≤D by exact_mod_cast hD)
    exact_mod_cast h
  rw [hh]
  ring

lemma bar_lift (D : ℚ) (x y : ℚ[X]) :
    bar (lift D x y)=mapQ x-C (unitD D)*mapQ y := by
  simp only [lift,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
    bar_mapQ,bar_unitD,map_neg]
  ring

lemma lift_norm (D : ℚ) (hD : 0≤D) (x y : ℚ[X]) :
    lift D x y*bar (lift D x y)=mapQ (x^2+C D*y^2) := by
  have hs : (C (unitD D) : ℂ[X])^2= -C (D : ℂ) := by
    rw [← C_pow,unitD_sq D hD,C_neg]
  rw [bar_lift]
  simp only [lift,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_mul,
    Polynomial.map_C]
  change (_+C (unitD D)*_)*(_-C (unitD D)*_) = _
  calc
    _=(mapQ x)^2-(C (unitD D))^2*(mapQ y)^2 := by ring
    _=_ := by rw [hs]; simp only [algebraMap_rat]; ring

lemma lift_pencil (D α β : ℚ) (x y d : ℚ[X]) :
    pencil (lift D x y) (mapQ d) ((α : ℂ)+unitD D*(β : ℂ)) =
      lift D (x-C α*d) (y-C β*d) := by
  simp only [pencil,lift,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
    C_add,C_mul,algebraMap_rat]
  ring

lemma eval_mapQ (f : ℚ[X]) (n : ℤ) : (mapQ f).eval (n : ℂ)=((f.eval (n : ℚ) : ℚ) : ℂ) := by
  simpa using eval_map_apply (algebraMap ℚ ℂ) (p := f) (n : ℚ)

lemma lift_value (D : ℚ) (x y d : ℚ[X]) (n : ℤ) :
    (lift D x y).eval (n : ℂ)/(mapQ d).eval (n : ℂ) =
      ((x.eval (n : ℚ)/d.eval (n : ℚ) : ℚ) : ℂ)+
        unitD D*((y.eval (n : ℚ)/d.eval (n : ℚ) : ℚ) : ℂ) := by
  simp only [lift,eval_add,eval_mul,eval_C,eval_mapQ,Rat.cast_div]
  rw [add_div,mul_div_assoc]

lemma denominator_eventually_nonzero (d : ℚ[X]) (hd : d≠0) :
    ∃ N : ℤ, ∀ n : ℤ, N≤n → d.eval (n : ℚ)≠0 := by
  obtain ⟨r,hr⟩ := exists_max_root d hd
  obtain ⟨N,hN⟩ := exists_int_gt r
  refine ⟨N,?_⟩
  intro n hn hz
  have := hr (n : ℚ) hz
  have hn' : (N : ℚ)≤n := by exact_mod_cast hn
  linarith

lemma rational_anchor_square (D : ℚ) (x y d : ℚ[X]) (hd : d≠0) (N n : ℤ)
    (hdn : d.eval (n : ℚ)≠0)
    (h : ∀ m : ℤ, N≤m → d.eval (m : ℚ)≠0 →
      IsSquare ((x.eval (m : ℚ)/d.eval (m : ℚ)-x.eval (n : ℚ)/d.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)/d.eval (m : ℚ)-y.eval (n : ℚ)/d.eval (n : ℚ))^2)) :
    IsSquare ((x-C (x.eval (n : ℚ)/d.eval (n : ℚ))*d)^2+
      C D*(y-C (y.eval (n : ℚ)/d.eval (n : ℚ))*d)^2) := by
  obtain ⟨M,hM⟩ := denominator_eventually_nonzero d hd
  apply PolynomialSquareValues.isSquare_of_eventually_int_eval
  refine ⟨max N M,?_⟩
  intro m hm
  have hdm := hM m ((le_max_right _ _).trans hm)
  have hs := (h m ((le_max_left _ _).trans hm) hdm).mul (IsSquare.sq (d.eval (m : ℚ)))
  convert hs using 1
  simp only [eval_add,eval_pow,eval_mul,eval_sub,eval_C]
  field_simp

lemma complex_anchor_square (D : ℚ) (hD : 0≤D) (x y d : ℚ[X]) (α β : ℚ)
    (hs : IsSquare ((x-C α*d)^2+C D*(y-C β*d)^2)) :
    IsSquare (pencil (lift D x y) (mapQ d) ((α : ℂ)+unitD D*(β : ℂ))*
      bar (pencil (lift D x y) (mapQ d) ((α : ℂ)+unitD D*(β : ℂ)))*mapQ d*bar (mapQ d)) := by
  rw [lift_pencil,lift_norm D hD,bar_mapQ]
  have hh : IsSquare (mapQ ((x-C α*d)^2+C D*(y-C β*d)^2)) :=
    hs.map (Polynomial.mapRingHom (algebraMap ℚ ℂ))
  convert hh.mul (IsSquare.sq (mapQ d)) using 1; ring

/-- A fixed rational-function path with rational square chord values for every
pair of sufficiently large integer parameters lies on a line or a circle.
The conclusion covers all real parameters where the denominator is nonzero.
No conclusion is asserted for sparse subsets of integers or changing paths. -/
theorem uniform_square_chords_line_or_circle (D : ℚ) (hD : 0≤D)
    (x y d : ℚ[X]) (hd : d≠0) (N : ℤ)
    (h : ∀ m n : ℤ, N≤m → N≤n → d.eval (m : ℚ)≠0 → d.eval (n : ℚ)≠0 →
      IsSquare ((x.eval (m : ℚ)/d.eval (m : ℚ)-x.eval (n : ℚ)/d.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)/d.eval (m : ℚ)-y.eval (n : ℚ)/d.eval (n : ℚ))^2)) :
    Collinear ℝ (curve (lift D x y) (mapQ d)) ∨
      Cospherical (curve (lift D x y) (mapQ d)) := by
  let a := lift D x y
  let b := mapQ d
  have hb : b≠0 := Polynomial.map_ne_zero hd
  by_cases hc : ∃ u : ℂ, pencil a b u=0
  · obtain ⟨u,hu⟩ := hc
    exact Or.inl (constant_curve_of_pencil_zero hu)
  push_neg at hc
  let U : Set ℂ := (fun n : ℤ => a.eval (n : ℂ)/b.eval (n : ℂ)) ''
    {n : ℤ | N≤n ∧ b.eval (n : ℂ)≠0}
  have hU : U.Infinite := infinite_integer_values a b hb N hc
  apply symbolic_square_anchors_line_or_circle_general a b hb U hU
  rintro u ⟨n,⟨hn,hdn⟩,rfl⟩
  have hdnQ : d.eval (n : ℚ)≠0 := by
    intro he
    apply hdn
    change (mapQ d).eval (n : ℂ)=0
    rw [eval_mapQ,he]
    simp
  change IsSquare (pencil (lift D x y) (mapQ d)
    ((lift D x y).eval (n : ℂ)/(mapQ d).eval (n : ℂ))*
    bar (pencil (lift D x y) (mapQ d)
      ((lift D x y).eval (n : ℂ)/(mapQ d).eval (n : ℂ)))*mapQ d*bar (mapQ d))
  rw [lift_value]
  apply complex_anchor_square D hD x y d
  exact rational_anchor_square D x y d hd N n hdnQ (fun m hm hdm => h m n hm hn hdm hdnQ)

lemma coordinate_dist_sq (D : ℚ) (hD : 0≤D) (α β γ δ : ℚ) :
    dist ((α : ℂ)+unitD D*(β : ℂ)) ((γ : ℂ)+unitD D*(δ : ℂ))^2 =
      (((α-γ)^2+D*(β-δ)^2 : ℚ) : ℝ) := by
  rw [dist_eq_norm,← Complex.normSq_eq_norm_sq]
  simp [unitD,Complex.normSq_apply]
  linear_combination ((β : ℝ)-δ)^2 *
    (Real.sq_sqrt (show (0 : ℝ)≤D by exact_mod_cast hD))

lemma integer_value_dist_sq (D : ℚ) (hD : 0≤D) (x y d : ℚ[X]) (m n : ℤ) :
    dist (value (lift D x y) (mapQ d) (m : ℝ))
      (value (lift D x y) (mapQ d) (n : ℝ))^2 =
      (((x.eval (m : ℚ)/d.eval (m : ℚ)-x.eval (n : ℚ)/d.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)/d.eval (m : ℚ)-y.eval (n : ℚ)/d.eval (n : ℚ))^2 : ℚ) : ℝ) := by
  simp only [value,Complex.ofReal_intCast,lift_value]
  exact coordinate_dist_sq D hD _ _ _ _

/-- Metric version: rational distances at every sufficiently large integer pair
force the whole real-parameter image, apart from poles, onto a line or circle. -/
theorem uniform_rational_distances_line_or_circle (D : ℚ) (hD : 0≤D)
    (x y d : ℚ[X]) (hd : d≠0) (N : ℤ)
    (h : ∀ m n : ℤ, N≤m → N≤n → d.eval (m : ℚ)≠0 → d.eval (n : ℚ)≠0 →
      ∃ q : ℚ, (q : ℝ)=dist (value (lift D x y) (mapQ d) (m : ℝ))
        (value (lift D x y) (mapQ d) (n : ℝ))) :
    Collinear ℝ (curve (lift D x y) (mapQ d)) ∨
      Cospherical (curve (lift D x y) (mapQ d)) := by
  apply uniform_square_chords_line_or_circle D hD x y d hd N
  intro m n hm hn hdm hdn
  obtain ⟨q,hq⟩ := h m n hm hn hdm hdn
  have he := integer_value_dist_sq D hD x y d m n
  rw [← hq] at he
  refine ⟨q,?_⟩
  have heQ : q^2=(x.eval (m : ℚ)/d.eval (m : ℚ)-x.eval (n : ℚ)/d.eval (n : ℚ))^2+
      D*(y.eval (m : ℚ)/d.eval (m : ℚ)-y.eval (n : ℚ)/d.eval (n : ℚ))^2 := by
    exact_mod_cast he
  simpa only [pow_two] using heQ.symm

/-- No four points drawn from such a uniform path can simultaneously have a
noncollinear first triple and a noncospherical four-point set. -/
theorem no_general_position_four (D : ℚ) (hD : 0≤D)
    (x y d : ℚ[X]) (hd : d≠0) (N : ℤ)
    (h : ∀ m n : ℤ, N≤m → N≤n → d.eval (m : ℚ)≠0 → d.eval (n : ℚ)≠0 →
      IsSquare ((x.eval (m : ℚ)/d.eval (m : ℚ)-x.eval (n : ℚ)/d.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)/d.eval (m : ℚ)-y.eval (n : ℚ)/d.eval (n : ℚ))^2))
    (a b c e : ℂ) (ha : a∈curve (lift D x y) (mapQ d))
    (hb : b∈curve (lift D x y) (mapQ d)) (hc : c∈curve (lift D x y) (mapQ d))
    (he : e∈curve (lift D x y) (mapQ d)) :
    ¬ (¬Collinear ℝ {a,b,c} ∧ ¬Cospherical {a,b,c,e}) := by
  rintro ⟨htri,hcir⟩
  rcases uniform_square_chords_line_or_circle D hD x y d hd N h with hline | hcircle
  · apply htri
    exact Collinear.subset (by simp [Set.insert_subset_iff,ha,hb,hc]) hline
  · apply hcir
    exact Cospherical.subset (by simp [Set.insert_subset_iff,ha,hb,hc,he]) hcircle

#print axioms uniform_rational_distances_line_or_circle
#print axioms no_general_position_four
#print axioms rational_anchor_square
#print axioms uniform_square_chords_line_or_circle
end
end Erdos213.RationalChordUniform
