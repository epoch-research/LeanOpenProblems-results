import FormalConjecturesUtil

/-! Rigidity of a proposed universal quadratic-map construction.
This does not bound arbitrary rational-distance configurations. -/

open Polynomial EuclideanGeometry
namespace Erdos213.QuadraticRigidity
noncomputable section

lemma isSquare_ratFunc_iff {K : Type*} [Field K] (p : K[X]) :
    IsSquare (algebraMap K[X] (RatFunc K) p) ↔ IsSquare p := by
  constructor
  · rintro ⟨r, hr⟩
    have hint : IsIntegral K[X] (r^2) := by
      rw [pow_two, ← hr]
      exact isIntegral_algebraMap
    obtain ⟨q,hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := K[X]) (K := RatFunc K) (by norm_num : 0 < (2 : ℕ)) hint
    refine ⟨q, ?_⟩
    apply IsFractionRing.injective K[X] (RatFunc K)
    simpa [map_mul, hq] using hr
  · rintro ⟨q,hq⟩
    exact ⟨algebraMap K[X] (RatFunc K) q, by simp [hq]⟩

def quad (A B C₀ : ℝ) : ℝ[X] := C A*X^2+C B*X+C C₀

lemma discr_zero_of_isSquare {A B C₀ : ℝ} (h : IsSquare (quad A B C₀)) :
    B^2-4*A*C₀ = 0 := by
  obtain ⟨p,hp⟩ := h
  have hdeg : (quad A B C₀).natDegree ≤ 2 := by
    unfold quad
    compute_degree!
  have hpdeg : p.natDegree ≤ 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [hp, natDegree_mul hp0 hp0] at hdeg
      omega
  obtain ⟨a,b,hab⟩ := exists_eq_X_add_C_of_natDegree_le_one hpdeg
  have he : quad A B C₀ = C (a*a)*X^2+C (2*a*b)*X+C (b*b) := by
    rw [hp, hab]
    simp only [map_mul, map_ofNat]
    ring
  have hA := congrArg (fun f : ℝ[X] => f.coeff 2) he
  have hB := congrArg (fun f : ℝ[X] => f.coeff 1) he
  have hC := congrArg (fun f : ℝ[X] => f.coeff 0) he
  simp only [quad, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at hA hB hC
  norm_num at hA hB hC
  rw [hA, hB, hC]
  ring

lemma discr_zero_of_ratFunc_square {A B C₀ : ℝ}
    (h : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (quad A B C₀))) :
    B^2-4*A*C₀ = 0 :=
  discr_zero_of_isSquare ((isSquare_ratFunc_iff _).mp h)

def gramPolynomial (a b : ℝ²) : ℝ[X] :=
  quad ((a 0)^2+(a 1)^2) (2*(a 0*b 0+a 1*b 1)) ((b 0)^2+(b 1)^2)

lemma det_zero_of_gram_square (a b : ℝ²)
    (h : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (gramPolynomial a b))) :
    a 0*b 1-a 1*b 0 = 0 := by
  have hd := discr_zero_of_ratFunc_square h
  change (2*(a 0*b 0+a 1*b 1))^2-
    4*((a 0)^2+(a 1)^2)*((b 0)^2+(b 1)^2) = 0 at hd
  have he : (a 0*b 1-a 1*b 0)^2 = 0 := by
    linear_combination -hd/4
  exact eq_zero_of_pow_eq_zero he

noncomputable def point (a b c : ℝ²) (t : ℝ) : ℝ² := t^2 • a + t • b + c

lemma chord_factorization (a b c : ℝ²) (s t : ℝ) :
    dist (point a b c s) (point a b c t)^2 =
      (s-t)^2 * (gramPolynomial a b).eval (s+t) := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq,
    point, gramPolynomial, quad]
  ring

private lemma vector_dependent {a b : ℝ²} (ha : a ≠ 0)
    (hdet : a 0*b 1-a 1*b 0 = 0) : ∃ r : ℝ, b = r • a := by
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro hh
      apply ha
      ext i
      fin_cases i <;> simp [h0, hh]
    refine ⟨b 1/a 1, ?_⟩
    have hb0 : b 0 = 0 := by
      rw [h0] at hdet
      have he : a 1*b 0 = 0 := by linarith
      exact (mul_eq_zero.mp he).resolve_left h1
    ext i
    fin_cases i
    · simp [h0, hb0]
    · simp [h1]
  · refine ⟨b 0/a 0, ?_⟩
    ext i
    fin_cases i
    · simp [h0]
    · change b 1 = (b 0/a 0)*a 1
      field_simp
      nlinarith [hdet]

lemma range_collinear_of_gram_square (a b c : ℝ²)
    (h : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (gramPolynomial a b))) :
    Collinear ℝ (Set.range (point a b c)) := by
  have hd := det_zero_of_gram_square a b h
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases ha : a = 0
  · refine ⟨c,b, ?_⟩
    rintro _ ⟨t,rfl⟩
    exact ⟨t, by simp [point, ha]⟩
  · obtain ⟨r,hr⟩ := vector_dependent ha hd
    refine ⟨c,a, ?_⟩
    rintro _ ⟨t,rfl⟩
    refine ⟨t^2+t*r, ?_⟩
    simp [point, hr, add_smul, smul_smul]

/-- A nondegenerate quadratic image of a line cannot have its universal chord
factor be a rational-function square. Pairwise rationality at selected
parameters is a separate Diophantine condition. -/
lemma no_universal_square {a b : ℝ²} (hdet : a 0*b 1-a 1*b 0 ≠ 0) :
    ¬ IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (gramPolynomial a b)) := by
  intro h
  exact hdet (det_zero_of_gram_square a b h)

open Filter in
private lemma one_polynomial_constant (A B : ℝ[X])
    (h : ∀ t : ℝ, ((A.eval t)^2-1)*((B.eval t)^2-1) ≤ 0) :
    A.natDegree = 0 ∨ B.natDegree = 0 := by
  by_contra hh
  have hA : 0 < A.degree := natDegree_pos_iff_degree_pos.mp
    (Nat.pos_of_ne_zero (fun h0 => hh (Or.inl h0)))
  have hB : 0 < B.degree := natDegree_pos_iff_degree_pos.mp
    (Nat.pos_of_ne_zero (fun h0 => hh (Or.inr h0)))
  have heA := (A.abs_tendsto_atTop hA).eventually (eventually_ge_atTop (2 : ℝ))
  have heB := (B.abs_tendsto_atTop hB).eventually (eventually_ge_atTop (2 : ℝ))
  obtain ⟨t,htA,htB⟩ := (heA.and heB).exists
  have hpA : 0 < (A.eval t)^2-1 := by
    nlinarith [sq_abs (A.eval t)]
  have hpB : 0 < (B.eval t)^2-1 := by
    nlinarith [sq_abs (B.eval t)]
  exact (not_lt_of_ge (h t)) (mul_pos hpA hpB)

/-- Any polynomial path through the first anchor whose distances to both
`(0,0)` and `(1,0)` are rational functions must lie on the anchor line.
This is a symbolic identity theorem, not a bound for selected parameter values. -/
lemma two_anchor_polynomial_rigidity (x y : ℝ[X])
    (hx0 : x.eval 0 = 0) (hy0 : y.eval 0 = 0)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (x^2+y^2)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) ((x-1)^2+y^2))) : y = 0 := by
  obtain ⟨r,hr⟩ := (isSquare_ratFunc_iff _).mp h0
  obtain ⟨s,hs⟩ := (isSquare_ratFunc_iff _).mp h1
  rw [← pow_two] at hr hs
  have he : (4 : ℝ[X])*y^2 = ((r+s)^2-1)*(1-(r-s)^2) := by
    linear_combination (2-(r^2-s^2+2*x-1))*hr + (2+(r^2-s^2+2*x-1))*hs
  have heval := fun t => congrArg (Polynomial.eval t) he
  have hc : (r+s).natDegree = 0 ∨ (r-s).natDegree = 0 := by
    apply one_polynomial_constant
    intro t
    have hh := heval t
    simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_one, eval_ofNat] at hh
    simp only [eval_add, eval_sub]
    nlinarith [sq_nonneg (y.eval t)]
  have hr0 : r.eval 0 = 0 := by
    have hh := congrArg (Polynomial.eval 0) hr
    simpa [hx0, hy0] using hh.symm
  have hs0 : (s.eval 0)^2 = 1 := by
    have hh := congrArg (Polynomial.eval 0) hs
    simpa [hx0, hy0] using hh.symm
  have hrc : r.coeff 0 = 0 := by
    simpa only [coeff_zero_eq_eval_zero] using hr0
  have hsc : (s.coeff 0)^2 = 1 := by
    simpa only [coeff_zero_eq_eval_zero] using hs0
  have hplus : ((r+s).coeff 0)^2 = 1 := by
    simpa only [coeff_add, hrc, zero_add] using hsc
  have hminus : ((r-s).coeff 0)^2 = 1 := by
    simpa only [coeff_sub, hrc, zero_sub, neg_sq] using hsc
  rcases hc with hc | hc
  · have hplus' : (r+s)^2 = 1 := by
      rw [eq_C_of_natDegree_eq_zero hc, ← map_pow, hplus, map_one]
    rw [hplus'] at he
    norm_num at he
    exact he
  · have hminus' : (r-s)^2 = 1 := by
      rw [eq_C_of_natDegree_eq_zero hc, ← map_pow, hminus, map_one]
    rw [hminus'] at he
    norm_num at he
    exact he

#print axioms two_anchor_polynomial_rigidity
#print axioms isSquare_ratFunc_iff
#print axioms range_collinear_of_gram_square
#print axioms no_universal_square

end
end Erdos213.QuadraticRigidity
