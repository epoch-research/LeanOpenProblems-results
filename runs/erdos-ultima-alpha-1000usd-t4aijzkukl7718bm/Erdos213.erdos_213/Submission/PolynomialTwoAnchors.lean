import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Submission.PolynomialSquareValues

/-! Rigidity for arbitrary-degree polynomial paths. Uniform integer-parameter
square values are essential; sparse parameter subsets are not covered. -/
namespace Erdos213.PolynomialTwoAnchors
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000

lemma degrees_zero_of_product_one {K : Type*} [Field K] (p q : K[X])
    (h : p*q=1) : p.natDegree=0 ∧ q.natDegree=0 := by
  have hp : p ≠ 0 := by intro hz; simp [hz] at h
  have hq : q ≠ 0 := by intro hz; simp [hz] at h
  have hh := congrArg natDegree h
  rw [natDegree_mul hp hq,natDegree_one] at hh
  omega

/-- The polynomial Pell equation with a nonzero constant coefficient has only
constant solutions. The coefficient may be complex. -/
lemma complex_constant_pell (u v : ℂ[X]) (a : ℂ) (ha : a ≠ 0)
    (h : u^2-C a*v^2=1) : u.natDegree=0 ∧ v.natDegree=0 := by
  obtain ⟨c,hc⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < (2 : ℕ))
  have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc; exact ha hc.symm
  let p := u-C c*v
  let q := u+C c*v
  have hpq : p*q=1 := by
    calc
      _ = u^2-C (c^2)*v^2 := by dsimp [p,q]; rw [map_pow]; ring
      _ = 1 := by rw [hc,h]
  obtain ⟨hp,hq⟩ := degrees_zero_of_product_one p q hpq
  have hp' := eq_C_of_natDegree_eq_zero hp
  have hq' := eq_C_of_natDegree_eq_zero hq
  have hu : C (2 : ℂ)*u=C (p.coeff 0+q.coeff 0) := by
    calc
      _ = p+q := by dsimp [p,q]; norm_num only [map_ofNat]; ring
      _ = _ := by rw [hp',hq',map_add]; simp
  have hv : C (2*c)*v=C (q.coeff 0-p.coeff 0) := by
    calc
      _ = q-p := by dsimp [p,q]; rw [map_mul]; norm_num only [map_ofNat]; ring
      _ = _ := by rw [hp',hq',map_sub]; simp
  have hu' := congrArg natDegree hu
  have hv' := congrArg natDegree hv
  rw [natDegree_C_mul (by norm_num),natDegree_C] at hu'
  rw [natDegree_C_mul (mul_ne_zero (by norm_num) hc0),natDegree_C] at hv'
  exact ⟨hu',hv'⟩

lemma real_constant_pell (u v : ℝ[X]) (a : ℝ) (ha : a ≠ 0)
    (h : u^2-C a*v^2=1) : u.natDegree=0 ∧ v.natDegree=0 := by
  have hm := congrArg (Polynomial.map Complex.ofRealHom) h
  simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_mul,map_C,Polynomial.map_one] at hm
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  obtain ⟨hu,hv⟩ := complex_constant_pell _ _ _ ha' hm
  simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective] using And.intro hu hv

lemma constant_conic (u v : ℝ[X]) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : C a*u^2+C b*v^2=C a) : u.natDegree=0 ∧ v.natDegree=0 := by
  have he : C a*C (-b/a) = -C b := by
    rw [← map_mul,← map_neg]
    congr 1
    field_simp
  apply real_constant_pell u v (-b/a) (div_ne_zero (neg_ne_zero.mpr hb) ha)
  apply mul_left_cancel₀ (show C a ≠ (0 : ℝ[X]) from C_ne_zero.mpr ha)
  calc
    C a*(u^2-C (-b/a)*v^2) = C a*u^2+C b*v^2 := by
      linear_combination -v^2*he
    _ = C a*1 := by simpa using h

open Filter in
lemma heron_one_constant (u v y : ℝ[X]) (D : ℝ) (hD : 0 < D)
    (h : C (4*D)*y^2=(u^2-1)*(1-v^2)) :
    u.natDegree=0 ∨ v.natDegree=0 := by
  by_contra hh
  have hu : 0 < u.degree := natDegree_pos_iff_degree_pos.mp
    (Nat.pos_of_ne_zero (fun h0 => hh (Or.inl h0)))
  have hv : 0 < v.degree := natDegree_pos_iff_degree_pos.mp
    (Nat.pos_of_ne_zero (fun h0 => hh (Or.inr h0)))
  have hU := (u.abs_tendsto_atTop hu).eventually (eventually_ge_atTop (2 : ℝ))
  have hV := (v.abs_tendsto_atTop hv).eventually (eventually_ge_atTop (2 : ℝ))
  obtain ⟨t,htU,htV⟩ := (hU.and hV).exists
  have hu' : 0 < (u.eval t)^2-1 := by nlinarith [sq_abs (u.eval t)]
  have hv' : 0 < (v.eval t)^2-1 := by nlinarith [sq_abs (v.eval t)]
  have he := congrArg (Polynomial.eval t) h
  simp only [eval_mul,eval_C,eval_pow,eval_sub,eval_one] at he
  have hy : 0 ≤ D*(y.eval t)^2 := mul_nonneg hD.le (sq_nonneg _)
  nlinarith [mul_pos hu' hv']

lemma heron_classification (u v y : ℝ[X]) (D : ℝ) (hD : 0 < D)
    (h : C (4*D)*y^2=(u^2-1)*(1-v^2)) :
    y=0 ∨ (u.natDegree=0 ∧ v.natDegree=0 ∧ y.natDegree=0) := by
  have h4D : 4*D ≠ 0 := by positivity
  rcases heron_one_constant u v y D hD h with hu | hv
  · have hu' := eq_C_of_natDegree_eq_zero hu
    let c := u.coeff 0
    have he : C (4*D)*y^2=C (c^2-1)*(1-v^2) := by
      rw [hu'] at h
      simpa only [c,map_sub,map_pow,map_one] using h
    by_cases hc : c^2-1=0
    · left
      rw [hc,map_zero,zero_mul] at he
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he).resolve_left (C_ne_zero.mpr h4D))
    · right
      have hh : C (c^2-1)*v^2+C (4*D)*y^2=C (c^2-1) := by linear_combination he
      obtain ⟨hv,hy⟩ := constant_conic v y (c^2-1) (4*D) hc h4D hh
      exact ⟨hu,hv,hy⟩
  · have hv' := eq_C_of_natDegree_eq_zero hv
    let c := v.coeff 0
    have he : C (4*D)*y^2=(u^2-1)*C (1-c^2) := by
      rw [hv'] at h
      simpa only [c,map_sub,map_pow,map_one] using h
    by_cases hc : 1-c^2=0
    · left
      rw [hc,map_zero,mul_zero] at he
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he).resolve_left (C_ne_zero.mpr h4D))
    · right
      have hh : C (1-c^2)*u^2+C (-4*D)*y^2=C (1-c^2) := by
        rw [show -4*D=-(4*D) by ring,map_neg]
        linear_combination -he
      obtain ⟨hu,hy⟩ := constant_conic u y (1-c^2) (-4*D) hc (by positivity) hh
      exact ⟨hu,hv,hy⟩

/-- No degree bound and no incidence with either anchor is assumed. A
polynomial path at symbolic rational distance from two fixed anchors is
constant or lies on their line. -/
theorem two_anchor_classification (x y : ℝ[X]) (D : ℝ) (hD : 0 < D)
    (h0 : IsSquare (x^2+C D*y^2))
    (h1 : IsSquare ((x-1)^2+C D*y^2)) :
    y=0 ∨ (x.natDegree=0 ∧ y.natDegree=0) := by
  obtain ⟨r,hr⟩ := h0
  obtain ⟨s,hs⟩ := h1
  rw [← pow_two] at hr hs
  have he : C (4*D)*y^2=((r+s)^2-1)*(1-(r-s)^2) := by
    rw [map_mul]
    norm_num only [map_ofNat]
    linear_combination (2-(r^2-s^2+2*x-1))*hr + (2+(r^2-s^2+2*x-1))*hs
  rcases heron_classification (r+s) (r-s) y D hD he with hy | ⟨hu,hv,hy⟩
  · exact Or.inl hy
  right
  refine ⟨?_,hy⟩
  have hx : C (2 : ℝ)*x=(r+s)*(r-s)+1 := by norm_num only [map_ofNat]; linear_combination hr-hs
  have hh : (r+s)*(r-s)+1=C ((r+s).coeff 0*(r-s).coeff 0+1) := by
    rw [eq_C_of_natDegree_eq_zero hu,eq_C_of_natDegree_eq_zero hv]
    simp only [map_add,map_mul,map_one,coeff_C,ite_true]
  rw [hh] at hx
  have hd := congrArg natDegree hx
  simpa only [natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0),natDegree_C] using hd

/-- Rational-coefficient version of the symbolic classification. -/
theorem rational_two_anchor_classification (x y : ℚ[X]) (D : ℚ) (hD : 0 < D)
    (h0 : IsSquare (x^2+C D*y^2))
    (h1 : IsSquare ((x-1)^2+C D*y^2)) :
    y=0 ∨ (x.natDegree=0 ∧ y.natDegree=0) := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  have h0' := h0.map (Polynomial.mapRingHom f)
  have h1' := h1.map (Polynomial.mapRingHom f)
  change IsSquare ((x^2+C D*y^2).map f) at h0'
  change IsSquare (((x-1)^2+C D*y^2).map f) at h1'
  simp only [Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_one,map_C] at h0' h1'
  have hD' : 0 < f D := by change 0 < (D : ℝ); exact_mod_cast hD
  rcases two_anchor_classification (x.map f) (y.map f) (f D) hD' h0' h1' with hy | hdeg
  · left
    apply Polynomial.map_injective f f.injective
    simpa only [Polynomial.map_zero] using hy
  · right
    simpa only [natDegree_map_eq_of_injective f.injective] using hdeg

/-- Uniform rational distances at every sufficiently large integer parameter
force a rational polynomial path to be constant or to lie on the anchor line.
The degree is arbitrary, and the two thresholds can differ. -/
theorem eventual_two_anchor_classification (x y : ℚ[X]) (D : ℚ) (hD : 0 < D)
    (h0 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((x.eval (n : ℚ))^2+D*(y.eval (n : ℚ))^2))
    (h1 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((x.eval (n : ℚ)-1)^2+D*(y.eval (n : ℚ))^2)) :
    y=0 ∨ (x.natDegree=0 ∧ y.natDegree=0) := by
  apply rational_two_anchor_classification x y D hD
  · apply PolynomialSquareValues.isSquare_of_eventually_int_eval
    simpa only [eval_add,eval_pow,eval_mul,eval_C] using h0
  · apply PolynomialSquareValues.isSquare_of_eventually_int_eval
    simpa only [eval_add,eval_pow,eval_mul,eval_C,eval_sub,eval_one] using h1

/-- A nonconstant path in this uniform model must lie on the anchor line. -/
theorem eventual_two_anchor_line (x y : ℚ[X]) (D : ℚ) (hD : 0 < D)
    (hn : x.natDegree ≠ 0 ∨ y.natDegree ≠ 0)
    (h0 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((x.eval (n : ℚ))^2+D*(y.eval (n : ℚ))^2))
    (h1 : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsSquare ((x.eval (n : ℚ)-1)^2+D*(y.eval (n : ℚ))^2)) : y=0 := by
  rcases eventual_two_anchor_classification x y D hD h0 h1 with hy | ⟨hx,hy⟩
  · exact hy
  · rcases hn with hn | hn
    · exact (hn hx).elim
    · exact (hn hy).elim

#print axioms complex_constant_pell
#print axioms two_anchor_classification
#print axioms eventual_two_anchor_classification
#print axioms eventual_two_anchor_line
end
end Erdos213.PolynomialTwoAnchors
