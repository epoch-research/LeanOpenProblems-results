import Submission.PositiveNormOrientation

/-! Semantic interpretation of the positive-orientation certificate. -/
noncomputable section
open Polynomial SimpleGraph
namespace Erdos714PositiveNormSemantics
open Erdos714OrdinarySquarePoints (K V d normForm trace_d card_K parameter_irreducible)
open Erdos714PositiveNorm

def extensionPolynomial : K[X] := X^3-X-C d

lemma extension_monic : extensionPolynomial.Monic := by
  unfold extensionPolynomial
  monicity!

lemma extension_degree : extensionPolynomial.natDegree = 3 := by
  unfold extensionPolynomial
  compute_degree!

instance extension_irreducible : Fact (Irreducible extensionPolynomial) := ⟨parameter_irreducible⟩
abbrev L := AdjoinRoot extensionPolynomial
noncomputable instance : Field L := AdjoinRoot.instField
instance : CharP L 3 := charP_of_injective_algebraMap (algebraMap K L).injective 3

def theta : L := AdjoinRoot.root extensionPolynomial
lemma theta_spec : theta^3-theta-algebraMap K L d = 0 := by
  have h := AdjoinRoot.eval₂_root extensionPolynomial
  simpa [extensionPolynomial, theta] using h

lemma theta_frobenius : theta^27 = theta-1 := by
  have h3 := theta_spec
  have h9 := congrArg (fun x : L => x^3) h3
  have h27 := congrArg (fun x : L => x^9) h3
  simp only [sub_pow_char, zero_pow (by decide : 3 ≠ 0)] at h9
  have hpow (a b : L) : (a-b)^9 = a^9-b^9 := sub_pow_char_pow a b 2 (p := 3)
  simp only [hpow, zero_pow (by decide : 9 ≠ 0)] at h27
  have ht := congrArg (algebraMap K L) trace_d
  simp only [map_add, map_pow, map_neg, map_one] at ht
  linear_combination h3+h9+h27+ht

lemma coeff_frobenius (a : K) : (algebraMap K L a)^27 = algebraMap K L a := by
  rw [← map_pow]
  congr 1
  simpa only [card_K] using FiniteField.pow_card a

def eval (v : V) (t : L) : L :=
  algebraMap K L (v 0) + algebraMap K L (v 1)*t + algebraMap K L (v 2)*t^2

lemma eval_frobenius (v : V) (t : L) : (eval v t)^27 = eval v (t^27) := by
  have ha (a b : L) : (a+b)^27 = a^27+b^27 := add_pow_char_pow a b 3 3
  simp only [eval, ha, mul_pow, coeff_frobenius]
  rw [← pow_mul, ← pow_mul]

lemma eval_frobenius_once (v : V) : (eval v theta)^27 = eval v (theta-1) := by
  rw [eval_frobenius, theta_frobenius]

lemma eval_frobenius_twice (v : V) : (eval v theta)^729 = eval v (theta+1) := by
  have h3 : (3 : L) = 0 := CharP.cast_eq_zero L 3
  change (eval v theta)^(27*27) = _
  rw [pow_mul, eval_frobenius_once, eval_frobenius]
  have hs : (theta-1)^27 = theta+1 := by
    rw [show (27 : ℕ) = 3^3 from rfl, sub_pow_char_pow, one_pow]
    rw [show (3 : ℕ)^3 = 27 from rfl, theta_frobenius]
    linear_combination -h3
  rw [hs]

lemma orientation_identity {F : Type*} [CommRing F] [CharP F 3]
    (a b c t D : F) (h : t^3-t-D = 0) :
    ((a+b*t+c*t^2)-(a+b*(t-1)+c*(t-1)^2)) *
    ((a+b*(t-1)+c*(t-1)^2)-(a+b*(t+1)+c*(t+1)^2)) *
    ((a+b*(t+1)+c*(t+1)^2)-(a+b*t+c*t^2)) = b^3-b*c^2-D*c^3 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  linear_combination -16*c^3*h +
    (-b^3-4*b^2*c*t-8*b*c^2*t^2+b*c^2-4*c^3*t-5*D*c^3)*h3

lemma norm_identity {F : Type*} [CommRing F] [CharP F 3]
    (a b c t D : F) (h : t^3-t-D = 0) :
    (a+b*t+c*t^2)*(a+b*(t-1)+c*(t-1)^2)*(a+b*(t+1)+c*(t+1)^2) =
      a^3+2*a^2*c+a*c^2-a*b^2+D*b^3-D*b*c^2-3*D*a*b*c+D^2*c^3 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  linear_combination
    (D*c^3+6*a*b*c+3*a*c^2*t+b^3+3*b^2*c*t+3*b*c^2*t^2-b*c^2+c^3*t^3-c^3*t)*h +
    (3*D*a*b*c+D*a*c^2*t+D*b^2*c*t+D*b*c^2*t^2+a^2*b*t+a^2*c*t^2+
      a*b^2*t^2+2*a*b*c*t+a*c^2*t^2)*h3

/-- The coordinate orientation is the actual ordered Frobenius Vandermonde product. -/
theorem orientation_eq_vandermonde (v : V) :
    algebraMap K L (orientation v) =
      (eval v theta-(eval v theta)^27)*((eval v theta)^27-(eval v theta)^729)*
        ((eval v theta)^729-eval v theta) := by
  rw [eval_frobenius_once, eval_frobenius_twice]
  simp only [orientation, eval, map_sub, map_pow, map_mul]
  exact (orientation_identity _ _ _ _ _ theta_spec).symm

/-- The coordinate norm is the product of all three relative Frobenius conjugates. -/
theorem norm_eq_conjugate_product (v : V) :
    algebraMap K L (normForm d v) = eval v theta*(eval v theta)^27*(eval v theta)^729 := by
  rw [eval_frobenius_once, eval_frobenius_twice]
  simp only [normForm, eval, map_add, map_sub, map_pow, map_mul, map_ofNat]
  exact (norm_identity _ _ _ _ _ theta_spec).symm

lemma eval_add (v w : V) : eval (v+w) theta = eval v theta+eval w theta := by
  simp only [eval, Pi.add_apply, map_add]
  ring

lemma eval_injective : Function.Injective (fun v : V => eval v theta) := by
  intro v w hvw
  change eval v theta = eval w theta at hvw
  let p : K[X] := C (v 0-w 0)+C (v 1-w 1)*X+C (v 2-w 2)*X^2
  have hp : aeval theta p = 0 := by
    have he : aeval theta p = eval v theta-eval w theta := by
      simp [p, eval]
      ring
    rw [he, hvw, sub_self]
  have hd : extensionPolynomial ∣ p := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [← AdjoinRoot.aeval_eq]
    exact hp
  have hp0 : p = 0 := by
    by_contra hn
    have hle := Polynomial.natDegree_le_of_dvd hd hn
    rw [extension_degree] at hle
    have hlt : p.natDegree ≤ 2 := by
      dsimp [p]
      compute_degree!
    omega
  funext i
  fin_cases i
  · have h := congrArg (fun p : K[X] => p.coeff 0) hp0
    simpa [p, sub_eq_zero] using h
  · have h := congrArg (fun p : K[X] => p.coeff 1) hp0
    simp only [p, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow] at h
    norm_num at h
    exact sub_eq_zero.mp h
  · have h := congrArg (fun p : K[X] => p.coeff 2) hp0
    simp only [p, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow] at h
    norm_num at h
    exact sub_eq_zero.mp h

noncomputable instance : Fintype L :=
  Fintype.ofEquiv (Fin extensionPolynomial.natDegree → K)
    (AdjoinRoot.powerBasis extension_monic.ne_zero).basis.equivFun.symm.toEquiv

lemma card_L : Fintype.card L = 19683 := by
  have h := Fintype.card_congr
    (AdjoinRoot.powerBasis extension_monic.ne_zero).basis.equivFun.toEquiv
  simpa [extension_degree, card_K] using h

def fieldNorm (x : L) : L := x*x^27*x^729
def fieldOrientation (x : L) : L := (x-x^27)*(x^27-x^729)*(x^729-x)
def basePositive (x : L) : Prop := x ≠ 0 ∧ ∃ a : K, x = algebraMap K L (a^2)

/-- The graph defined directly with Frobenius conjugates, rather than coordinate forms. -/
def fieldGraph : SimpleGraph (Bool × (L × K)) where
  Adj u v := u.1 ≠ v.1 ∧ fieldNorm (u.2.1+v.2.1) = algebraMap K L (u.2.2*v.2.2) ∧
    basePositive (fieldOrientation (u.2.1+v.2.1))
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

def fieldAllowed (v : Bool × (L × K)) : Prop :=
  v.2.2 ≠ 0 ∧ IsSquare v.2.2 ∧ basePositive (fieldNorm v.2.1)

def restrictedFieldGraph : SimpleGraph {v // fieldAllowed v} := fieldGraph.induce _

lemma map_basePositive (x : K) (hx : x ≠ 0) (hs : IsSquare x) :
    basePositive (algebraMap K L x) := by
  obtain ⟨a, ha⟩ := hs
  refine ⟨(map_ne_zero (algebraMap K L)).mpr hx, a, ?_⟩
  rw [ha, pow_two]

/-- Injective edge-preserving transfer of the already checked coordinate graph. -/
def coordinateCopy : Copy restrictedGraph restrictedFieldGraph where
  toHom := {
    toFun v := ⟨(v.val.1, eval v.val.2.1 theta, v.val.2.2), by
      obtain ⟨hw, hsw, hn, hsn⟩ := v.property
      exact ⟨hw, hsw, by
        change basePositive (eval _ theta*(eval _ theta)^27*(eval _ theta)^729)
        rw [← norm_eq_conjugate_product]
        exact map_basePositive _ hn hsn⟩⟩
    map_rel' := by
      intro u v huv
      obtain ⟨htag, hn, ho, hso⟩ := huv
      refine ⟨htag, ?_, ?_⟩
      · change fieldNorm (eval _ theta+eval _ theta) = _
        rw [← eval_add]
        change eval _ theta*(eval _ theta)^27*(eval _ theta)^729 = _
        rw [← norm_eq_conjugate_product]
        exact congrArg (algebraMap K L) hn
      · change basePositive (fieldOrientation (eval _ theta+eval _ theta))
        rw [← eval_add]
        change basePositive ((eval _ theta-(eval _ theta)^27)*
          ((eval _ theta)^27-(eval _ theta)^729)*((eval _ theta)^729-eval _ theta))
        rw [← orientation_eq_vandermonde]
        exact map_basePositive _ ho hso }
  injective' := by
    intro u v huv
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x => x.val.1) huv
    · apply Prod.ext
      · apply eval_injective
        exact congrArg (fun x => x.val.2.1) huv
      · exact congrArg (fun x => x.val.2.2) huv

/-- The finite-field graph itself contains a K₄,₄, even with both square restrictions. -/
theorem restrictedFieldGraph_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free restrictedFieldGraph := by
  intro hfree
  exact restrictedGraph_not_free (fun h => hfree (h.trans ⟨coordinateCopy⟩))

#print axioms eval_injective
#print axioms card_L
#print axioms restrictedFieldGraph_not_free
#print axioms orientation_eq_vandermonde
#print axioms norm_eq_conjugate_product
end Erdos714PositiveNormSemantics
