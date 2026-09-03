import FormalConjecturesUtil

/-! Three-term Tits kernels: coefficient normalization and a checked quartic
bound on each row's zero set. These facts do not establish K44-freeness. -/
noncomputable section
open Classical Polynomial Finset
set_option maxHeartbeats 2000000
namespace Erdos714TitsThreeTerm
variable {E : Type*} [Field E]

def kernel (σ : E →+* E) (c x y : E) : E :=
  x*y^2+x^2*y+c*σ x*σ y

def scale (σ : E →+* E) (c : E) : E := c^3*(σ c)^2

lemma scale_ne_zero (σ : E →+* E) (c : E) (hc : c ≠ 0) : scale σ c ≠ 0 :=
  mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 2 ((_root_.map_ne_zero σ).mpr hc))

/-- An explicit inverse exponent eliminates every nonzero coefficient parameter. -/
lemma scale_identity (σ : E →+* E) (c : E) (hσ : σ (σ c) = c^2) :
    (scale σ c)^3 = c*(σ (scale σ c))^2 := by
  simp only [scale,map_mul,map_pow,hσ]
  ring

lemma kernel_scale (σ : E →+* E) (c : E) (hσ : σ (σ c) = c^2) (x y : E) :
    kernel σ c (scale σ c*x) (scale σ c*y) =
      (scale σ c)^3*kernel σ 1 x y := by
  simp only [kernel,map_mul]
  have he := scale_identity σ c hσ
  linear_combination -σ x*σ y*he

/-- A quartic obtained by applying sigma once and eliminating sigma(y).
Its leading coefficient is nonzero whenever the row coordinate is nonzero. -/
def rowPolynomial (σ : E →+* E) (c x : E) : E[X] :=
  C (σ x*x^2)*X^4+C (2*σ x*x^3)*X^3+
    C (σ x*x^4-(σ x)^2*(c*σ x)*x+σ (c*σ x)*(c*σ x)^2)*X^2-
    C ((σ x)^2*(c*σ x)*x^2)*X

lemma rowPolynomial_degree (σ : E →+* E) (c x : E) :
    (rowPolynomial σ c x).natDegree ≤ 4 := by
  unfold rowPolynomial
  compute_degree!

lemma rowPolynomial_coeff (σ : E →+* E) (c x : E) :
    (rowPolynomial σ c x).coeff 4 = σ x*x^2 := by
  simp only [rowPolynomial,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

lemma rowPolynomial_ne_zero (σ : E →+* E) (c x : E) (hx : x ≠ 0) :
    rowPolynomial σ c x ≠ 0 := by
  intro hz
  have he := congrArg (fun p : E[X] => p.coeff 4) hz
  change (rowPolynomial σ c x).coeff 4 = (0 : E[X]).coeff 4 at he
  rw [rowPolynomial_coeff,coeff_zero] at he
  exact mul_ne_zero ((_root_.map_ne_zero σ).mpr hx) (pow_ne_zero 2 hx) he

/-- The kernel equation produces an actual root, without cancelling an unproved factor. -/
lemma rowPolynomial_root (σ : E →+* E) (c x y : E)
    (hσ : σ (σ y) = y^2) (h : kernel σ c x y = 0) :
    (rowPolynomial σ c x).eval y = 0 := by
  have hs := congrArg σ h
  simp only [kernel,map_add,map_mul,map_pow,map_zero,hσ] at hs
  dsimp [kernel] at h
  simp only [rowPolynomial,eval_sub,eval_add,eval_mul,eval_C,eval_pow,eval_X,map_mul]
  linear_combination (c*σ x)^2*hs-
    (σ x*((c*σ x)*σ y-(x*y^2+x^2*y))+(σ x)^2*(c*σ x))*h

/-- Every nonzero row has at most four zero entries, uniformly in c. -/
theorem row_zeros_card_le_four (σ : E →+* E) (hσ : ∀ y, σ (σ y) = y^2)
    (c x : E) (hx : x ≠ 0) (S : Finset E)
    (hS : ∀ y ∈ S, kernel σ c x y = 0) : S.card ≤ 4 := by
  have hp := rowPolynomial_ne_zero σ c x hx
  have hs : S ⊆ (rowPolynomial σ c x).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset,Polynomial.mem_roots hp]
    exact rowPolynomial_root σ c x y (hσ y) (hS y hy)
  exact (card_le_card hs).trans <| (Multiset.toFinset_card_le _).trans <|
    (Polynomial.card_roots' _).trans (rowPolynomial_degree _ _ _)

/-- Hence excluding zero norm values costs at most four possible column points. -/
theorem nonzero_entries_card [Fintype E] (σ : E →+* E) (hσ : ∀ y, σ (σ y) = y^2)
    (c x : E) (hx : x ≠ 0) :
    Fintype.card E ≤ (univ.filter (fun y => kernel σ c x y ≠ 0)).card+4 := by
  have hb := row_zeros_card_le_four σ hσ c x hx
    (univ.filter (fun y => kernel σ c x y = 0)) (by simp)
  have he := card_filter_add_card_filter_not (s := (univ : Finset E)) (fun y => kernel σ c x y = 0)
  change (univ.filter (fun y => kernel σ c x y = 0)).card+
    (univ.filter (fun y => kernel σ c x y ≠ 0)).card = Fintype.card E at he
  omega

/-- Scaling transfers every actual weighted norm rectangle from coefficient 1
to any nonzero coefficient, preserving injectivity and nonzero row weights. -/
theorem scaled_norm_rectangle {F I J : Type*} [Field F] [Algebra F E]
    [FiniteDimensional F E] (σ : E →+* E) (c : E) (hc : c ≠ 0)
    (hσ : σ (σ c) = c^2) (x : I → E) (y : J → E)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (a : I → F) (b : J → F) (ha : ∀ i, a i ≠ 0)
    (h : ∀ i j, Algebra.norm F (kernel σ 1 (x i) (y j)) = a i*b j) :
    ∃ x' : I → E, ∃ y' : J → E, ∃ a' : I → F,
      Function.Injective x' ∧ Function.Injective y' ∧ (∀ i, a' i ≠ 0) ∧
        ∀ i j, Algebra.norm F (kernel σ c (x' i) (y' j)) = a' i*b j := by
  let u := scale σ c
  have hu : u ≠ 0 := scale_ne_zero σ c hc
  have hN : Algebra.norm F u ≠ 0 := Algebra.norm_ne_zero_iff.mpr hu
  refine ⟨(fun i => u*x i), (fun j => u*y j), (fun i => (Algebra.norm F u)^3*a i),
    ?_, ?_, (fun i => mul_ne_zero (pow_ne_zero 3 hN) (ha i)), ?_⟩
  · intro i j he
    exact hx (mul_left_cancel₀ hu he)
  · intro i j he
    exact hy (mul_left_cancel₀ hu he)
  · intro i j
    rw [kernel_scale σ c hσ,map_mul,map_pow,h]
    ring

#print axioms kernel_scale
#print axioms rowPolynomial_root
#print axioms row_zeros_card_le_four
#print axioms nonzero_entries_card
#print axioms scaled_norm_rectangle
end Erdos714TitsThreeTerm
