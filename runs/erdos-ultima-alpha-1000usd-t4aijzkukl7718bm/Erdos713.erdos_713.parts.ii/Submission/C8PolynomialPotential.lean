import FormalConjecturesUtil
import Submission.FinitePolynomialCollision

/-! A diagnostic for univariate polynomial potentials in a four-coordinate
incidence construction. This file does not settle the extremal-exponent conjecture. -/
open SimpleGraph Polynomial
namespace Erdos713C8Polynomial

abbrev Vertex (F : Type*) := F × (Fin 3 → F)
def Inc {F : Type*} [Field F] (P : F → F) (p l : Vertex F) : Prop :=
  p.2 0+l.2 0 = l.1*p.1 ∧ p.2 1+l.2 1 = l.2 0*p.1 ∧ p.2 2+l.2 2 = P l.1*p.1

def graph {F : Type*} [Field F] (P : F → F) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj v w := match v,w with
    | .inl p,.inr l => Inc P p l
    | .inr l,.inl p => Inc P p l
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

set_option maxHeartbeats 1000000 in
lemma contains_of_octagon {F : Type*} [Field F] (P : F → F)
    (p l : Fin 4 → Vertex F) (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, Inc P (p i) (l i)) (hB : ∀ i, Inc P (p (i+1)) (l i)) :
    cycleGraph 8 ⊑ graph P := by
  let f : Fin 8 → Vertex F ⊕ Vertex F :=
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

set_option maxHeartbeats 1000000 in
lemma contains_of_moments {F : Type*} [Field F] (P : F → F) (u v r t : F)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0)
    (hM : (P u-P 0-(P 1-P 0)*u)*t = (P v-P 0-(P 1-P 0)*v)*r) :
    cycleGraph 8 ⊑ graph P := by
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
  let p : Fin 4 → Vertex F :=
    ![(0,![0,0,0]), (s,![0,0,P 0*s]),
      (s+t,![u*t,u*s*t,P 0*s+P u*t]), (r,![v*r,0,P v*r])]
  let l : Fin 4 → Vertex F :=
    ![(0,![0,0,0]), (u,![u*s,u*s^2,(P u-P 0)*s]),
      (1,![(1-v)*r,(1-v)*r*(s+t)-u*s*t,P 1*(s+t)-(P 0*s+P u*t)]), (v,![0,0,0])]
  apply contains_of_octagon P p l
  · intro i j hij
    have hx := congrArg (fun w : Vertex F => w.1) hij
    have hy := congrArg (fun w : Vertex F => w.2 0) hij
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
    have hx := congrArg (fun w : Vertex F => w.1) hij
    fin_cases i <;> fin_cases j <;> dsimp [l] at hx <;> simp_all
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals solve | ring | linear_combination hB | linear_combination -hB | linear_combination hM | linear_combination -hM

lemma contains_factored {F : Type*} [Field F] [Fintype F] (A B : F) (R : F[X])
    (hR : R ≠ 0) (hq : (2+2*R.natDegree)^2 < Fintype.card F - 1) :
    cycleGraph 8 ⊑ graph (fun a => A+B*a+a*(a-1)*R.eval a) := by
  let K : F[X] := X*(1-X)*R^2
  have hlin : (1-(X : F[X])) ≠ 0 := by
    intro he
    have hh := congrArg (Polynomial.eval 0) he
    simp at hh
  have hK : K ≠ 0 := mul_ne_zero (mul_ne_zero X_ne_zero hlin) (pow_ne_zero _ hR)
  have hdeg : K.natDegree ≤ 2+2*R.natDegree := by
    have hlin' : (1-(X : F[X])).natDegree ≤ 1 := by compute_degree
    have h1 := Polynomial.natDegree_mul_le (p := X*(1-X)) (q := R^2)
    have h2 := Polynomial.natDegree_mul_le (p := (X : F[X])) (q := 1-X)
    simp only [Polynomial.natDegree_X,Polynomial.natDegree_pow] at h1 h2
    dsimp [K]
    omega
  obtain ⟨u,v,huv,hKu,he⟩ := FinitePolynomialCollision.exists_nonzero_collision K hK
    ((Nat.pow_le_pow_left hdeg 2).trans_lt hq) (a := 0) (b := 1) zero_ne_one
    (by simp [K]) (by simp [K])
  have hKv : K.eval v ≠ 0 := he ▸ hKu
  have hu : u ≠ 0 := by intro hh; apply hKu; simp [K,hh]
  have hv : v ≠ 0 := by intro hh; apply hKv; simp [K,hh]
  have hu1 : u ≠ 1 := by intro hh; apply hKu; simp [K,hh]
  have hv1 : v ≠ 1 := by intro hh; apply hKv; simp [K,hh]
  have hRu : R.eval u ≠ 0 := by intro hh; apply hKu; simp [K,hh]
  have hRv : R.eval v ≠ 0 := by intro hh; apply hKv; simp [K,hh]
  apply contains_of_moments (fun a => A+B*a+a*(a-1)*R.eval a) u v
    (u*(u-1)*R.eval u) (v*(v-1)*R.eval v) hu hv hu1 hv1 huv
    (mul_ne_zero (mul_ne_zero hu (sub_ne_zero.mpr hu1)) hRu)
    (mul_ne_zero (mul_ne_zero hv (sub_ne_zero.mpr hv1)) hRv)
  · dsimp [K] at he
    simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_sub,Polynomial.eval_one] at he
    linear_combination u*(1-u)*v*(1-v)*he
  · ring

lemma contains_affine {F : Type*} [Field F] [Fintype F] (A B : F)
    (hq : 3 < Fintype.card F) : cycleGraph 8 ⊑ graph (fun a => A+B*a) := by
  classical
  have hS : ({0,1,1/2} : Finset F).card ≤ 3 := by
    simpa using List.toFinset_card_le ([0,1,1/2] : List F)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1,1/2} : Finset F)) (t := Finset.univ)
    (by simpa only [Finset.card_univ] using hS.trans_lt hq)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu
  have hv : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.2.1)
  have hv1 : 1-u ≠ 1 := by intro he; apply hu.1; linear_combination -he
  have huv : u ≠ 1-u := by
    intro he
    have ht : (2:F)*u = 1 := by linear_combination he
    have htwo : (2:F) ≠ 0 := by
      intro htwo
      rw [htwo,zero_mul] at ht
      exact zero_ne_one ht
    apply hu.2.2
    apply (eq_div_iff htwo).mpr
    linear_combination ht
  apply contains_of_moments (fun a => A+B*a) u (1-u) 1 1 hu.1 hv hu.2.1 hv1 huv
    one_ne_zero one_ne_zero <;> ring

lemma contains_polynomial {F : Type*} [Field F] [Fintype F] (p : F[X])
    (hq : (2*(p.natDegree+2))^2 < Fintype.card F - 1) :
    cycleGraph 8 ⊑ graph p.eval := by
  let Q : F[X] := p-C (p.eval 0)-C (p.eval 1-p.eval 0)*X
  have hQ0 : Q.eval 0 = 0 := by simp [Q]
  have hQ1 : Q.eval 1 = 0 := by simp [Q]
  by_cases hQ : Q = 0
  · have he : p.eval = fun a => p.eval 0+(p.eval 1-p.eval 0)*a := by
      funext a
      have hh : Q.eval a = 0 := by rw [hQ]; simp
      dsimp [Q] at hh
      simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at hh
      linear_combination hh
    rw [he]
    apply contains_affine
    have hh := Nat.pow_le_pow_left (show 4 ≤ 2*(p.natDegree+2) by omega) 2
    norm_num only [Nat.reducePow] at hh
    omega
  have hd0 : X-C (0:F) ∣ Q := Polynomial.dvd_iff_isRoot.mpr hQ0
  simp only [map_zero,sub_zero] at hd0
  obtain ⟨S,hS⟩ := hd0
  have hS1 : S.eval 1 = 0 := by simpa [hS] using hQ1
  obtain ⟨R,hR⟩ := Polynomial.dvd_iff_isRoot.mpr hS1
  have hQR : Q = X*(X-1)*R := by
    rw [hS,hR]
    simp only [map_one]
    ring
  have hRne : R ≠ 0 := by intro hh; apply hQ; simp [hQR,hh]
  have hRdeg : R.natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd ⟨X*(X-1),by rw [hQR]; ring⟩ hQ
  have hQdeg : Q.natDegree ≤ p.natDegree+1 := by
    have h1 := Polynomial.natDegree_sub_le (p := p) (q := C (p.eval 0))
    have h2 := Polynomial.natDegree_sub_le (p := p-C (p.eval 0))
      (q := C (p.eval 1-p.eval 0)*X)
    have h3 : (C (p.eval 1-p.eval 0)*X).natDegree ≤ 1 := by compute_degree
    simp only [Polynomial.natDegree_C] at h1
    dsimp [Q]
    omega
  have he : p.eval = fun a => p.eval 0+(p.eval 1-p.eval 0)*a+a*(a-1)*R.eval a := by
    funext a
    have hh := congrArg (Polynomial.eval a) hQR
    dsimp [Q] at hh
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_one] at hh
    linear_combination hh
  rw [he]
  apply contains_factored _ _ R hRne
  have hh : 2+2*R.natDegree ≤ 2*(p.natDegree+2) := by omega
  exact (Nat.pow_le_pow_left hh 2).trans_lt hq

#print axioms contains_of_moments
#print axioms contains_factored
#print axioms contains_polynomial
end Erdos713C8Polynomial
