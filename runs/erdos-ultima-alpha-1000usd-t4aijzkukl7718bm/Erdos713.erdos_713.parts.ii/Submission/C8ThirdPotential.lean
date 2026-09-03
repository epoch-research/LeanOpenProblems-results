import FormalConjecturesUtil
import Submission.C8RootPotential

/-! Third-line-coordinate potentials: auxiliary C8 construction obstructions.
These results do not settle the extremal-exponent conjecture. -/
open SimpleGraph
namespace Erdos713C8ThirdPotential
open Erdos713C8FiniteQuadratic
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

def Inc (Q : K → K → K → K) (p l : Vertex K) : Prop :=
  p.2 0 + l.2 0 = l.1*p.1 ∧
  p.2 1 + l.2 1 = l.2 0*p.1 ∧
  p.2 2 + l.2 2 = Q l.1 (l.2 0) (l.2 1)*p.1

def Octagon (Q : K → K → K → K) : Prop :=
  ∃ p l : Fin 4 → Vertex K, Function.Injective p ∧ Function.Injective l ∧
    (∀ i, Inc Q (p i) (l i)) ∧ (∀ i, Inc Q (p (i+1)) (l i))

def pointShift (t : K) (p : Vertex K) : Vertex K :=
  (p.1+t, ![p.2 0, p.2 1+t*p.2 0, p.2 2])

def lineShift (Q : K → K → K → K) (t : K) (l : Vertex K) : Vertex K :=
  (l.1, ![l.2 0+t*l.1, l.2 1+2*t*l.2 0+t^2*l.1, l.2 2+t*Q l.1 (l.2 0) (l.2 1)])

lemma pointShift_injective (t : K) : Function.Injective (pointShift t) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex K => v.2 0) h
  have h1 := congrArg (fun v : Vertex K => v.2 1) h
  have h2 := congrArg (fun v : Vertex K => v.2 2) h
  dsimp [pointShift] at hx h0 h1 h2
  refine Prod.ext (by linear_combination hx) ?_
  funext i
  fin_cases i
  · exact h0
  · change p.2 1 = q.2 1
    linear_combination h1 - t*h0
  · exact h2

lemma lineShift_injective (Q : K → K → K → K) (t : K) :
    Function.Injective (lineShift Q t) := by
  intro l m h
  have ha := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex K => v.2 0) h
  have h1 := congrArg (fun v : Vertex K => v.2 1) h
  have h2 := congrArg (fun v : Vertex K => v.2 2) h
  dsimp [lineShift] at ha h0 h1 h2
  have hb : l.2 0 = m.2 0 := by linear_combination h0 - t*ha
  have hc : l.2 1 = m.2 1 := by linear_combination h1-2*t*hb-t^2*ha
  rw [ha,hb,hc] at h2
  refine Prod.ext ha ?_
  funext i
  fin_cases i
  · exact hb
  · change l.2 1 = m.2 1
    exact hc
  · change l.2 2 = m.2 2
    linear_combination h2

lemma shift_inc {Q R : K → K → K → K} (t : K)
    (hQ : ∀ a b c, R a (b+t*a) (c+2*t*b+t^2*a) = Q a b c) {p l : Vertex K} (h : Inc Q p l) :
    Inc R (pointShift t p) (lineShift Q t l) := by
  rcases h with ⟨h0,h1,h2⟩
  dsimp [Inc,pointShift,lineShift]
  rw [hQ]
  refine ⟨?_,?_,?_⟩
  · linear_combination h0
  · linear_combination h1 + t*h0
  · linear_combination h2

lemma shift_octagon {Q R : K → K → K → K} (t : K)
    (hQ : ∀ a b c, R a (b+t*a) (c+2*t*b+t^2*a) = Q a b c) (h : Octagon Q) : Octagon R := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  exact ⟨pointShift t ∘ p, lineShift Q t ∘ l,
    (pointShift_injective t).comp hp, (lineShift_injective Q t).comp hl,
    fun i => shift_inc t hQ (hA i), fun i => shift_inc t hQ (hB i)⟩

def graph (Q : K → K → K → K) : SimpleGraph (Vertex K ⊕ Vertex K) where
  Adj v w := match v,w with
    | .inl p,.inr l => Inc Q p l
    | .inr l,.inl p => Inc Q p l
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

set_option maxHeartbeats 1000000 in
lemma contains_of_octagon {Q : K → K → K → K} (h : Octagon Q) :
    SimpleGraph.cycleGraph 8 ⊑ graph Q := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  let f : Fin 8 → Vertex K ⊕ Vertex K :=
    ![Sum.inl (p 0),Sum.inr (l 0),Sum.inl (p 1),Sum.inr (l 1),
      Sum.inl (p 2),Sum.inr (l 2),Sum.inl (p 3),Sum.inr (l 3)]
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try (exfalso; revert hij; decide)
    all_goals dsimp [f,graph]
    all_goals first | exact hA 0 | exact hA 1 | exact hA 2 | exact hA 3 | exact hB 0 | exact hB 1 | exact hB 2 | exact hB 3
  · intro i j hij
    change f i = f j at hij
    fin_cases i <;> fin_cases j <;> dsimp [f] at hij
    all_goals first | rfl | (have he := hp (Sum.inl.inj hij); exfalso; revert he; decide) | (have he := hl (Sum.inr.inj hij); exfalso; revert he; decide) | cases hij

def moment (u v r t : K) (Q : K → K → K → K) : K :=
  let s := (1-v)*r-(1-u)*t
  Q 0 0 0*s + Q u (u*s) (u*s^2)*t +
    Q 1 ((1-v)*r) ((1-v)*r*(s+t)-u*s*t)*(v*r-u*t) - Q v 0 0*r

lemma octagon_of_moment (Q : K → K → K → K) (u v r t : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) (hM : moment u v r t Q = 0) :
    Octagon Q := by
  dsimp [moment] at hM
  let s := (1-v)*r-(1-u)*t
  have hs : s ≠ 0 := by
    intro he
    have hprod : t^2*(1-u)*(v-u) = 0 := by
      dsimp [s] at he
      linear_combination (1-v)*hB-v*((1-v)*r+(1-u)*t)*he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht) (sub_ne_zero.mpr hu1.symm))
      (sub_ne_zero.mpr huv.symm)) hprod
  have hs2 : v*r-u*t ≠ 0 := by
    intro he
    have hprod : t^2*u*(u-v) = 0 := by
      linear_combination v*hB-(1-v)*(v*r+u*t)*he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht) hu) (sub_ne_zero.mpr huv)) hprod
  have hut : u*t ≠ 0 := mul_ne_zero hu ht
  have hvr : v*r ≠ 0 := mul_ne_zero hv hr
  let p : Fin 4 → Vertex K :=
    ![(0,![0,0,0]), (s,![0,0,Q 0 0 0*s]),
      (s+t,![u*t,u*s*t,Q 0 0 0*s+Q u (u*s) (u*s^2)*t]), (r,![v*r,0,Q v 0 0*r])]
  let l : Fin 4 → Vertex K :=
    ![(0,![0,0,0]), (u,![u*s,u*s^2,Q u (u*s) (u*s^2)*s-Q 0 0 0*s]),
      (1,![(1-v)*r,(1-v)*r*(s+t)-u*s*t,Q 1 ((1-v)*r) ((1-v)*r*(s+t)-u*s*t)*(s+t)-Q 0 0 0*s-Q u (u*s) (u*s^2)*t]),
      (v,![0,0,0])]
  refine ⟨p,l,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    have hy := congrArg (fun w : Vertex K => w.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at hx hy
      first | exact (hs hx).elim | exact (hs hx.symm).elim |
        exact (hr hx).elim | exact (hr hx.symm).elim |
        exact (hut hy).elim | exact (hut hy.symm).elim |
        exact (hvr hy).elim | exact (hvr hy.symm).elim |
        (exfalso; apply ht; linear_combination hx) |
        (exfalso; apply ht; linear_combination -hx) |
        (exfalso; apply hs2; dsimp [s] at hx; linear_combination hx) |
        (exfalso; apply hs2; dsimp [s] at hx; linear_combination -hx))
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    fin_cases i <;> fin_cases j <;> dsimp [l] at hx <;> simp_all
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals solve | ring | linear_combination hB | linear_combination -hB | linear_combination hM | linear_combination -hM

lemma fourth_add [CharP K 2] (x y : K) : (x+y)^4 = x^4+y^4 := by
  have he (z : K) : z^4 = (z^2)^2 := by ring
  simp only [he,CharTwo.add_sq]

lemma noncube_linearized_surjective [Finite K] [CharP K 2] (δ : K)
    (hδ : ∀ z : K, z^3 ≠ δ) : Function.Surjective (fun τ : K => τ^4+δ*τ) := by
  apply Finite.surjective_of_injective
  intro x y hxy
  have he : (x+y)^4+δ*(x+y) = 0 := by
    rw [fourth_add]
    linear_combination hxy+(y^4+δ*y)*(CharTwo.two_eq_zero (R := K))
  have hf : (x+y)*((x+y)^3+δ) = 0 := by linear_combination he
  rcases mul_eq_zero.mp hf with h | h
  · simpa only [← CharTwo.sub_eq_add,sub_eq_zero] using h
  · have hz : (x+y)^3 = δ := by
      simpa only [← CharTwo.sub_eq_add,sub_eq_zero] using h
    exact (hδ _ hz).elim

lemma square_third_shift [CharP K 2] (δ : K) (f : K → K) (u v r t τ : K) :
    moment u v r t (fun a b c =>
      (c+2*τ*b+τ^2*a)^2+δ*a*(b+τ*a)+f a) =
    moment u v r t (fun a b c => c^2+δ*a*b+f a)+
      (τ^4+δ*τ)*Erdos713C8FiniteQuadratic.D u v r t := by
  simp only [CharTwo.two_eq_zero,zero_mul,add_zero,CharTwo.add_sq,mul_pow]
  dsimp [moment,Erdos713C8FiniteQuadratic.D]
  ring

/-- A noncube does not protect this third-coordinate construction:
the available point shift cancels its octagon voltage. -/
theorem square_third_noncube [Fintype K] [CharP K 2] (δ : K) (f : K → K)
    (hδ : ∀ z : K, z^3 ≠ δ) (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b c => c^2+δ*a*b+f a) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hD,_⟩ :=
    parameters_char_two (K := K) hq
  let M := moment u v r t (fun a b c => c^2+δ*a*b+f a)
  obtain ⟨τ,hτ⟩ := noncube_linearized_surjective δ hδ
    (-M/Erdos713C8FiniteQuadratic.D u v r t)
  change τ^4+δ*τ = -M/Erdos713C8FiniteQuadratic.D u v r t at hτ
  apply contains_of_octagon
  apply shift_octagon τ (Q := fun a b c =>
    (c+2*τ*b+τ^2*a)^2+δ*a*(b+τ*a)+f a)
  · intro a b c; rfl
  · apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
    rw [square_third_shift,hτ]
    change M+(-M/Erdos713C8FiniteQuadratic.D u v r t)*
      Erdos713C8FiniteQuadratic.D u v r t = 0
    rw [div_mul_cancel₀ _ hD]
    ring

lemma root_third_shift [CharP K 2] (σ : K →+* K) (hσ : ∀ a, (σ a)^2 = a)
    (δ : K) (f : K → K) (u v r t τ : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a b c => σ (c+2*τ*b+τ^2*a)+δ*a*(b+τ*a)+f a) =
      moment u v r t (fun a b c => σ c+δ*a*b+f a)+
        δ*τ*Erdos713C8FiniteQuadratic.D u v r t := by
  have he (a b c : K) : σ (c+2*τ*b+τ^2*a)+δ*a*(b+τ*a)+f a =
      (σ c+δ*a*b+f a)+τ*σ a+δ*τ*a^2 := by
    simp only [CharTwo.two_eq_zero,zero_mul,add_zero,map_add,map_mul,map_pow,hσ]
    ring
  simp_rw [he]
  have hz := Erdos713C8RootPotential.root_moment_zero σ hσ u v r t hB
  dsimp [moment,Erdos713C8FiniteCubic.moment,Erdos713C8FiniteQuadratic.D] at hz ⊢
  simp only [map_zero,map_one,zero_mul,one_mul,zero_add] at hz ⊢
  linear_combination τ*hz

/-- An inverse-Frobenius third-coordinate term also fails, even with
an arbitrary additional slope function and any nonzero mixed coefficient. -/
theorem root_third_mixed [Fintype K] [CharP K 2] (σ : K →+* K)
    (hσ : ∀ a, (σ a)^2 = a) (δ : K) (hδ : δ ≠ 0) (f : K → K)
    (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b c => σ c+δ*a*b+f a) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hD,_⟩ :=
    parameters_char_two (K := K) hq
  let M := moment u v r t (fun a b c => σ c+δ*a*b+f a)
  let τ := -M/(δ*Erdos713C8FiniteQuadratic.D u v r t)
  apply contains_of_octagon
  apply shift_octagon τ (Q := fun a b c =>
    σ (c+2*τ*b+τ^2*a)+δ*a*(b+τ*a)+f a)
  · intro a b c; rfl
  · apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
    rw [root_third_shift σ hσ δ f u v r t τ hB]
    change M+δ*(-M/(δ*Erdos713C8FiniteQuadratic.D u v r t))*
      Erdos713C8FiniteQuadratic.D u v r t = 0
    field_simp
    ring

#print axioms noncube_linearized_surjective
#print axioms square_third_noncube
#print axioms root_third_mixed
#print axioms octagon_of_moment
#print axioms shift_octagon
#print axioms contains_of_octagon
end Erdos713C8ThirdPotential
