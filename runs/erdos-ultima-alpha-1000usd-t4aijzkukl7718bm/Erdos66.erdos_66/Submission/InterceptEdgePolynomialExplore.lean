import FormalConjecturesUtil

/-! Polynomial square-class separation for distinct collision edges. It
will certify that a triple-concurrency condition excludes only finitely
many translations. -/
namespace Erdos66InterceptEdgePolynomial
open Polynomial
open scoped Polynomial Classical
set_option maxHeartbeats 2200000
variable {F : Type*} [Field F]

def SameEdge (e f : F × F) : Prop :=
  (e.1=f.1 ∧ e.2=f.2) ∨ (e.1=f.2 ∧ e.2=f.1)

def edgeSum (e : F × F) : F := e.1+e.2
def edgeProd (e : F × F) : F := e.1*e.2
noncomputable def linearFactor (u : F) : F[X] := X-C (-u)
noncomputable def edgePolynomial (e : F × F) : F[X] := linearFactor e.1*linearFactor e.2

lemma linearFactor_ne_zero (u : F) : linearFactor u≠0 := X_sub_C_ne_zero _

lemma edgePolynomial_ne_zero (e : F × F) : edgePolynomial e≠0 :=
  mul_ne_zero (linearFactor_ne_zero _) (linearFactor_ne_zero _)

lemma linearFactor_eval (u a : F) : (linearFactor u).eval a=a+u := by simp [linearFactor]

lemma edgePolynomial_eval (e : F × F) (a : F) :
    (edgePolynomial e).eval a=(a+e.1)*(a+e.2) := by
  simp [edgePolynomial,linearFactor_eval]

lemma sameEdge_of_sum_prod (e f : F × F)
    (hs : edgeSum e=edgeSum f) (hp : edgeProd e=edgeProd f) : SameEdge e f := by
  have hz : (e.1-f.1)*(e.1-f.2)=0 := by
    dsimp [edgeSum] at hs
    dsimp [edgeProd] at hp
    linear_combination e.1*hs-hp
  rcases mul_eq_zero.mp hz with h | h
  · have he := sub_eq_zero.mp h
    exact Or.inl ⟨he,by dsimp [edgeSum] at hs; linear_combination hs-he⟩
  · have he := sub_eq_zero.mp h
    exact Or.inr ⟨he,by dsimp [edgeSum] at hs; linear_combination hs-he⟩

omit [Field F] in
lemma exclusive_endpoint (e f : F × F) (he : e.1≠e.2) (h : ¬SameEdge e f) :
    (e.1≠f.1 ∧ e.1≠f.2) ∨ (e.2≠f.1 ∧ e.2≠f.2) := by
  by_contra! hn
  have h1 : e.1=f.1 ∨ e.1=f.2 := by tauto
  have h2 : e.2=f.1 ∨ e.2=f.2 := by tauto
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact he (h1.trans h2.symm)
  · exact h (Or.inl ⟨h1,h2⟩)
  · exact h (Or.inr ⟨h1,h2⟩)
  · exact he (h1.trans h2.symm)

lemma rootMultiplicity_edge_product (u v s t : F) (huv : u≠v) (hus : u≠s) (hut : u≠t) :
    (edgePolynomial (u,v)*edgePolynomial (s,t)).rootMultiplicity (-u)=1 := by
  rw [rootMultiplicity_mul (mul_ne_zero (edgePolynomial_ne_zero (u,v))
    (edgePolynomial_ne_zero (s,t)))]
  simp only [edgePolynomial]
  rw [rootMultiplicity_mul (mul_ne_zero (linearFactor_ne_zero u) (linearFactor_ne_zero v)),
    rootMultiplicity_mul (mul_ne_zero (linearFactor_ne_zero s) (linearFactor_ne_zero t))]
  simp only [linearFactor,rootMultiplicity_X_sub_C,neg_inj,huv,hus,hut,if_true,if_false,
    add_zero]

lemma edge_product_has_simple_root (e f : F × F) (he : e.1≠e.2)
    (h : ¬SameEdge e f) : ∃r : F, (edgePolynomial e*edgePolynomial f).rootMultiplicity r=1 := by
  rcases exclusive_endpoint e f he h with h | h
  · exact ⟨-e.1,rootMultiplicity_edge_product e.1 e.2 f.1 f.2 he h.1 h.2⟩
  · have hx := rootMultiplicity_edge_product e.2 e.1 f.1 f.2 he.symm h.1 h.2
    have heq : edgePolynomial (e.2,e.1)=edgePolynomial e := by simp only [edgePolynomial]; ring
    rw [heq] at hx
    exact ⟨-e.2,hx⟩

lemma square_ne_square_times_edges (e f : F × F) (he : e.1≠e.2)
    (hef : ¬SameEdge e f) (P Q : F[X]) (hQ : Q≠0) :
    P^2≠Q^2*(edgePolynomial e*edgePolynomial f) := by
  intro heq
  have hE := mul_ne_zero (edgePolynomial_ne_zero e) (edgePolynomial_ne_zero f)
  have hR := mul_ne_zero (pow_ne_zero 2 hQ) hE
  have hP : P≠0 := fun hp ↦ by rw [hp,zero_pow (by norm_num)] at heq; exact hR heq.symm
  obtain ⟨r,hr⟩ := edge_product_has_simple_root e f he hef
  have hh := congrArg (fun W : F[X] ↦ W.rootMultiplicity r) heq
  dsimp only at hh
  rw [rootMultiplicity_mul hR,hr] at hh
  simp only [pow_two,rootMultiplicity_mul (mul_ne_zero hP hP),
    rootMultiplicity_mul (mul_ne_zero hQ hQ)] at hh
  omega

/-- A norm eliminating three square roots. -/
noncomputable def tripleNorm (e f g : F × F) (A B C' : F[X]) : F[X] :=
  (A^2*edgePolynomial e+B^2*edgePolynomial f-C'^2*edgePolynomial g)^2-
    (C (2 : F)*A*B)^2*(edgePolynomial e*edgePolynomial f)

lemma tripleNorm_ne_zero (h2 : (2 : F)≠0) (e f g : F × F)
    (he : e.1≠e.2) (hef : ¬SameEdge e f) (A B C' : F[X]) (hA : A≠0) (hB : B≠0) :
    tripleNorm e f g A B C'≠0 := by
  intro hh
  apply square_ne_square_times_edges e f he hef
    (A^2*edgePolynomial e+B^2*edgePolynomial f-C'^2*edgePolynomial g)
    (C (2 : F)*A*B) (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h2) hA) hB)
  exact sub_eq_zero.mp hh

lemma norm_vanish_of_relation (a b c x y z e f g : F)
    (hx : x^2=e) (hy : y^2=f) (hz : z^2=g) (h : a*x+b*y+c*z=0) :
    (a^2*e+b^2*f-c^2*g)^2-(2*a*b)^2*(e*f)=0 := by
  rw [←hx,←hy,←hz,←mul_pow c z 2]
  have he : c*z=-(a*x+b*y) := by linear_combination h
  rw [he]
  ring

lemma tripleNorm_eval_zero (e f g : F × F) (A B C' : F[X]) (a x y z : F)
    (hx : x^2=(edgePolynomial e).eval a) (hy : y^2=(edgePolynomial f).eval a)
    (hz : z^2=(edgePolynomial g).eval a)
    (h : A.eval a*x+B.eval a*y+C'.eval a*z=0) :
    (tripleNorm e f g A B C').eval a=0 := by
  simp only [tripleNorm,eval_sub,eval_pow,eval_mul,eval_add,eval_C]
  exact norm_vanish_of_relation _ _ _ _ _ _ _ _ _ hx hy hz h

end Erdos66InterceptEdgePolynomial
