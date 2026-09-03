import FormalConjecturesUtil

/-! A parametric obstruction to Frobenius-twisted norm graphs with square weights.
This is not a proof or disproof of the balanced Zarankiewicz conjecture.
-/

open SimpleGraph Polynomial Classical

set_option maxHeartbeats 3000000

namespace Erdos714TwistedWeights

variable {F : Type*} [Field F] [CharP F 3]

/-- Coordinate norm for `theta^3-theta=d`. -/
def normForm (d : F) (v : F × F × F) : F :=
  v.1 ^ 3 + 2 * v.1 ^ 2 * v.2.2 + v.1 * v.2.2 ^ 2 - v.1 * v.2.1 ^ 2 +
    d * v.2.1 ^ 3 - d * v.2.1 * v.2.2 ^ 2 -
    3 * d * v.1 * v.2.1 * v.2.2 + d ^ 2 * v.2.2 ^ 3

/-- The displayed cubic really is the determinant of the multiplication matrix. -/
theorem normForm_eq_det (d : F) (v : F × F × F) :
    normForm d v = Matrix.det
      !![v.1, d*v.2.2, d*v.2.1;
         v.2.1, v.1+v.2.2, v.2.1+d*v.2.2;
         v.2.2, v.2.1, v.1+v.2.2] := by
  rw [Matrix.det_fin_three]
  change normForm d v =
    v.1 * (v.1 + v.2.2) * (v.1 + v.2.2) - v.1 * (v.2.1 + d*v.2.2) * v.2.1 -
    (d*v.2.2) * v.2.1 * (v.1+v.2.2) + (d*v.2.2) * (v.2.1+d*v.2.2) * v.2.2 +
    (d*v.2.1) * v.2.1 * v.2.1 - (d*v.2.1) * (v.1+v.2.2) * v.2.2
  unfold normForm
  ring

/-- The symmetric product associated with a field endomorphism. -/
def twist (sigma : F →+* F) (a b : F) : F := sigma a * b + a * sigma b

lemma twist_comm (sigma : F →+* F) (a b : F) : twist sigma a b = twist sigma b a := by
  unfold twist
  ring

lemma twist_self (sigma : F →+* F) (a : F) : twist sigma a a = -a * sigma a := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  unfold twist
  linear_combination a * sigma a * h3

/-- The proposed weighted graph. -/
def graph (sigma : F →+* F) (d : F) :
    SimpleGraph (Bool × ((F × F × F) × Fˣ)) where
  Adj u v := u.1 ≠ v.1 ∧
    normForm d (u.2.1 + v.2.1) = twist sigma (u.2.2 : F) (v.2.2 : F)
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    simpa only [add_comm, twist_comm sigma (v.2.2 : F)] using h.2
  loopless := by intro u h; exact h.1 rfl

/-- Restrict to square unit weights, rather than duplicate square-root labels. -/
def squareGraph (sigma : F →+* F) (d : F) :=
  (graph sigma d).induce {v | IsSquare (v.2.2 : F)}

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have : (1 : F) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

/-- A symmetric two-weight configuration, stated independently of how its parameters
are obtained. Its two sides use the same weight pattern `a,a,a,A`. -/
theorem symmetric_copy (sigma : F →+* F) (a A d v : F)
    (ha : a ≠ 0) (hA : A ≠ 0) (hsa : IsSquare a) (hsA : IsSquare A)
    (hd : twist sigma a a = d)
    (hv : v ^ 3 - v - d = twist sigma a A)
    (hAA : twist sigma A A = -v ^ 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (squareGraph sigma d) := by
  let aU : Fˣ := Units.mk0 a ha
  let AU : Fˣ := Units.mk0 A hA
  let L : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(false, (0, 0, 0), aU), (false, (1, 0, 0), aU),
      (false, (-1, 0, 0), aU), (false, (v, 1, 0), AU)]
  let R : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(true, (0, 1, 0), aU), (true, (1, 1, 0), aU),
      (true, (-1, 1, 0), aU), (true, (v, -1, 0), AU)]
  have hL : Function.Injective L := by
    intro i j hij
    have hp := congrArg (fun z : Bool × ((F × F × F) × Fˣ) => z.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [L, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg (fun z : Bool × ((F × F × F) × Fˣ) => z.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [R, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hleft : ∀ i, (L i).1 = false := by intro i; fin_cases i <;> rfl
  have hright : ∀ i, (R i).1 = true := by intro i; fin_cases i <;> rfl
  have hSL : ∀ i, IsSquare ((L i).2.2 : F) := by
    intro i; fin_cases i <;> first | exact hsa | exact hsA
  have hSR : ∀ i, IsSquare ((R i).2.2 : F) := by
    intro i; fin_cases i <;> first | exact hsa | exact hsA
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h4 : (4 : F) = 1 := by linear_combination h3
  have h6 : (6 : F) = 0 := by linear_combination 2*h3
  have h8 : (8 : F) = -1 := by linear_combination 3*h3
  have hp : (v+1)^3 = v^3+1 := by simpa using add_pow_char v (1:F) 3
  have hm : (v-1)^3 = v^3-1 := by simpa using sub_pow_char v (1:F)
  have hAa : twist sigma A a = twist sigma a A := twist_comm sigma A a
  have hE : ∀ i j, (graph sigma d).Adj (L i) (R j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L, R, graph, normForm, aU, AU, hd, hAa, hAA, hp, hm,
        show (-1:F)+v=v-1 by ring, show (1:F)+v=v+1 by ring] <;>
      ring_nf <;> (try simp [h2, h3, h4, h6, h8]) <;>
      (first | (linear_combination hv) | ring)
  let LL (i : Fin 4) : {z : Bool × ((F × F × F) × Fˣ) | IsSquare (z.2.2 : F)} :=
    ⟨L i, hSL i⟩
  let RR (i : Fin 4) : {z : Bool × ((F × F × F) × Fˣ) | IsSquare (z.2.2 : F)} :=
    ⟨R i, hSR i⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim LL RR, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => simp at hxy
      | inr j => exact hE i j
    | inr i =>
      cases y with
      | inl j => exact (hE j i).symm
      | inr j => simp at hxy
  · intro x y hxy
    have hval := congrArg Subtype.val hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hL hval)
      | inr j =>
        have h : (L i).1 = (R j).1 := congrArg Prod.fst hval
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
    | inr i =>
      cases y with
      | inl j =>
        have h : (L j).1 = (R i).1 := (congrArg Prod.fst hval).symm
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
      | inr j => exact congrArg Sum.inr (hR hval)

/-- The symbolic parameters work for every field endomorphism, not only a fixed
Frobenius exponent. The hypotheses ensure both weights are nonzero squares. -/
theorem parameter_obstruction (sigma : F →+* F) (w : F)
    (hw : w ≠ 0) (hw1 : w ^ 2 - 1 ≠ 0)
    (hsw : IsSquare w) (hsw1 : IsSquare (w ^ 2 - 1)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (squareGraph sigma (-(w ^ 3 - w) * sigma (w ^ 3 - w))) := by
  let c := w ^ 3 - w
  have hc : c = w * (w^2-1) := by dsimp [c]; ring
  have hcn : c ≠ 0 := by rw [hc]; exact mul_ne_zero hw hw1
  have hcs : IsSquare c := by rw [hc]; exact hsw.mul hsw1
  apply symmetric_copy sigma c (w^3) (-c * sigma c) (w * sigma w)
    hcn (pow_ne_zero 3 hw) hcs (hsw.pow 3) (twist_self sigma c)
  · have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    dsimp [c, twist]
    simp only [map_sub, map_pow]
    ring
  · rw [twist_self, map_pow]
    ring

namespace Example27

noncomputable def basePolynomial : (ZMod 3)[X] := X^3-X+1

lemma basePolynomial_degree : basePolynomial.natDegree = 3 := by
  unfold basePolynomial
  compute_degree!

lemma basePolynomial_monic : basePolynomial.Monic := by
  unfold basePolynomial
  monicity!

lemma basePolynomial_irreducible : Irreducible basePolynomial := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [basePolynomial_degree]
    decide
  · intro x hx
    have hc : x^3 = x := by simpa using FiniteField.pow_card x
    simpa [Polynomial.IsRoot, basePolynomial, hc] using hx

instance : Fact (Irreducible basePolynomial) := ⟨basePolynomial_irreducible⟩

abbrev K := AdjoinRoot basePolynomial

instance : CharP K 3 := charP_of_injective_algebraMap (algebraMap (ZMod 3) K).injective 3

noncomputable instance : Fintype K :=
  Fintype.ofEquiv (Fin basePolynomial.natDegree → ZMod 3)
    (AdjoinRoot.powerBasis basePolynomial_monic.ne_zero).basis.equivFun.symm.toEquiv

lemma card_K : Fintype.card K = 27 := by
  have h := Fintype.card_congr
    (AdjoinRoot.powerBasis basePolynomial_monic.ne_zero).basis.equivFun.toEquiv
  simpa [basePolynomial_degree] using h

noncomputable def t : K := AdjoinRoot.root basePolynomial

lemma t_spec : t^3-t+1 = 0 := by
  have h := AdjoinRoot.eval₂_root basePolynomial
  simpa [basePolynomial, t] using h

noncomputable def d : K := -t^2+t

lemma trace_d : d+d^3+d^9 = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have ht3 : t^3 = t-1 := by linear_combination t_spec
  have ht6 : t^6 = t^2+t+1 := by
    rw [show (6:ℕ)=3*2 by omega, pow_mul, ht3]
    linear_combination -t*h3
  have ht9 : t^9 = t+1 := by
    rw [show (9:ℕ)=3*3 by omega, pow_mul, ht3, sub_pow_char]
    linear_combination t_spec-h3
  have hd3 : d^3 = -t^2+1 := by
    dsimp [d]
    rw [add_pow_char _ _ 3, neg_pow, ← pow_mul, ht6, ht3]
    linear_combination -h3
  have hd9 : d^9 = -t^2-t := by
    change (iterateFrobenius K 3 2) (-t^2+t) = -t^2-t
    rw [map_add, map_neg, map_pow]
    simp only [iterateFrobenius_def]
    norm_num only [Nat.reducePow]
    rw [ht9]
    ring
  rw [hd3, hd9]
  dsimp [d]
  linear_combination -t^2*h3

lemma parameter_irreducible : Irreducible ((X^3-X-C d) : K[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X^3-X-C d) : K[X]).natDegree = 3 := by compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    have hx' : x^3-x = d := by
      simpa [Polynomial.IsRoot, sub_eq_zero] using hx
    have hx3 : x^9-x^3 = d^3 := by
      have h := congrArg (iterateFrobenius K 3 1) hx'
      simpa only [map_sub, map_pow, iterateFrobenius_def, Nat.reducePow, ← pow_mul,
        Nat.reduceMul] using h
    have hx9 : x^27-x^9 = d^9 := by
      have h := congrArg (iterateFrobenius K 3 2) hx'
      simpa only [map_sub, map_pow, iterateFrobenius_def, Nat.reducePow, ← pow_mul,
        Nat.reduceMul] using h
    have hx27 : x^27 = x := by simpa [card_K] using FiniteField.pow_card x
    have h10 : (1 : K) = 0 := by linear_combination -hx' - hx3 - hx9 - trace_d + hx27
    exact one_ne_zero h10

/-- An explicit, kernel-checked failure over a genuine field of order 27.
The endomorphism is the ninth-power Frobenius and all weights are squares. -/
theorem square_twisted_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (squareGraph (iterateFrobenius K 3 2) d) := by
  let w : K := -t^2+t+1
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hc : w^3-w = 1-t := by
    dsimp [w]
    linear_combination (-t^3+3*t^2-t-1)*t_spec+(-t^2+t)*h3
  have hcn : w^3-w ≠ 0 := by
    rw [hc]
    intro h
    have ht : t = 1 := by linear_combination -h
    have hs := t_spec
    rw [ht] at hs
    norm_num at hs
  have hw : w ≠ 0 := by intro h; apply hcn; simp [h]
  have hw1 : w^2-1 ≠ 0 := by
    intro h
    apply hcn
    calc
      w^3-w = w*(w^2-1) := by ring
      _ = 0 := by rw [h, mul_zero]
  have hsw : IsSquare w := by
    refine ⟨t^2+t, ?_⟩
    dsimp [w]
    linear_combination -((t+2)*t_spec+(t^2-1)*h3)
  have hsw1 : IsSquare (w^2-1) := by
    refine ⟨t^2+t-1, ?_⟩
    dsimp [w]
    linear_combination -(4*t_spec-h3)
  have ht3 : t^3 = t-1 := by linear_combination t_spec
  have ht9 : t^9 = t+1 := by
    rw [show (9:ℕ)=3*3 by omega, pow_mul, ht3, sub_pow_char]
    linear_combination t_spec-h3
  have hd : -(w^3-w) * (iterateFrobenius K 3 2) (w^3-w) = d := by
    rw [hc, map_sub, map_one]
    simp only [iterateFrobenius_def]
    norm_num only [Nat.reducePow]
    rw [ht9]
    dsimp [d]
    ring
  rw [← hd]
  exact parameter_obstruction _ w hw hw1 hsw hsw1

end Example27

end Erdos714TwistedWeights

#print axioms Erdos714TwistedWeights.symmetric_copy
#print axioms Erdos714TwistedWeights.parameter_obstruction

#print axioms Erdos714TwistedWeights.Example27.parameter_irreducible
#print axioms Erdos714TwistedWeights.Example27.square_twisted_not_free
