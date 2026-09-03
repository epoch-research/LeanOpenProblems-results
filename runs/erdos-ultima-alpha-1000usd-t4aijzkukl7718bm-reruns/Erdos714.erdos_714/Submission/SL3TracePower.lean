import FormalConjecturesUtil

/-!
A uniform dependent-constraint obstruction for a proposed SL3 trace-power
construction. This is not a proof or disproof of Erdős Problem 714.
-/

open Matrix Polynomial SimpleGraph
namespace Erdos714SL3TracePower
variable {F : Type*} [CommRing F] [CharP F 2]
abbrev M := Matrix (Fin 3) (Fin 3) F

def row (a t : F) : M (F := F) := !![t,t^2,1;1,t,0;0,1,a]
def col (a s z w u : F) : M (F := F) := !![s,a*z,u;0,s,w;w,a^2*z+u,z]

omit [CharP F 2] in
lemma row_det (a t : F) : (row a t).det = 1 := by
  simp [row,Matrix.det_fin_three]
  ring

lemma row_trace (a t : F) : (row a t).trace = a := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  simp [row,Matrix.trace,Fin.sum_univ_three]
  linear_combination t*h2

lemma col_det (a s z w u : F) :
    (col a s z w u).det = z*(s^2+a^2*s*w+a*w^2) := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  simp [col,Matrix.det_fin_three]
  linear_combination -(a^2*s*w*z+s*u*w)*h2

lemma col_trace (a s z w u : F) : (col a s z w u).trace = z := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  simp [col,Matrix.trace,Fin.sum_univ_three]
  linear_combination s*h2

lemma trace_pair (a s z w t u : F) :
    (row a t * col a s z w u).trace = 0 := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  simp [row,col,Matrix.trace,Fin.sum_univ_three]
  linear_combination (s*t+w+a*z)*h2

lemma trace_square_pair (a s z w t u : F) :
    (row a t ^ 2 * col a s z w u).trace = 0 := by
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  simp [row,col,Matrix.trace,Fin.sum_univ_three,pow_two]
  linear_combination (2*s*t^2+a*z*t+a^2*z+t*w+a*w+u)*h2

omit [CharP F 2] in
lemma row_injective (a : F) : Function.Injective (row a) := by
  intro t u h
  exact congrArg (fun A : M => A 0 0) h

omit [CharP F 2] in
lemma col_injective (a s z w : F) : Function.Injective (col a s z w) := by
  intro t u h
  exact congrArg (fun A : M => A 0 2) h

lemma row_charpoly (a t : F) :
    (row a t).charpoly = X^3+C a*X^2+1 := by
  have h2 : (2:F[X])=0 := CharP.cast_eq_zero F[X] 2
  simp [Matrix.charpoly,Matrix.det_fin_three,row,map_pow]
  linear_combination (-C a*X^2-X^2*C t+X*C a*C t-1)*h2

lemma col_charpoly (a s z w u : F) :
    (col a s z w u).charpoly =
      X^3+C z*X^2+C (s^2+a^2*z*w)*X+C (z*(s^2+a^2*s*w+a*w^2)) := by
  have h2 : (2:F[X])=0 := CharP.cast_eq_zero F[X] 2
  simp [Matrix.charpoly,Matrix.det_fin_three,col,map_add,map_mul,map_pow]
  linear_combination (X*C s*C z-X*C z*C w*(C a)^2-X*C w*C u-
    X^2*C s-X^2*C z+C s*C w*C u-(C s)^2*C z-C z*(C w)^2*C a)*h2

/-- Both parts use precisely the proposed elliptic, nonzero-trace SL3 vertices. -/
def Vertex (F : Type*) [CommRing F] :=
  {A : Matrix (Fin 3) (Fin 3) F // A.det=1 ∧ A.trace≠0 ∧ Irreducible A.charpoly}

def graph : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := match x,y with
    | .inl A,.inr H => (A.val*H.val).trace=0 ∧ (A.val^2*H.val).trace=0
    | .inr H,.inl A => (A.val*H.val).trace=0 ∧ (A.val^2*H.val).trace=0
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- The parameter conditions certify an entire grid, not only generic fibers. -/
def parameterCopy (a s z w : F) (ha : a≠0) (hz : z≠0)
    (hd : z*(s^2+a^2*s*w+a*w^2)=1)
    (hR : Irreducible (X^3+C a*X^2+1 : F[X]))
    (hH : Irreducible (X^3+C z*X^2+C (s^2+a^2*z*w)*X+1 : F[X]))
    {r : ℕ} (e : Fin r ↪ F) :
    (completeBipartiteGraph (Fin r) (Fin r)).Copy (graph (F := F)) := by
  let L : Fin r ↪ Vertex F :=
    ⟨fun i => ⟨row a (e i),row_det a (e i),by simpa [row_trace] using ha,
      by simpa [row_charpoly] using hR⟩,
     fun i j h => e.injective (row_injective a (congrArg Subtype.val h))⟩
  let R : Fin r ↪ Vertex F :=
    ⟨fun i => ⟨col a s z w (e i),by simpa [col_det] using hd,
      by simpa [col_trace] using hz,by simpa [col_charpoly,hd] using hH⟩,
     fun i j h => e.injective (col_injective a s z w (congrArg Subtype.val h))⟩
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  have he (i j : Fin r) : (graph (F := F)).Adj (.inl (L i)) (.inr (R j)) :=
    ⟨trace_pair a s z w (e i) (e j),trace_square_pair a s z w (e i) (e j)⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr j => exact he i j
  | inr i =>
    cases y with
    | inl j => exact (he j i).symm
    | inr j => simp at h

/-- A primitive cube root specializes both characteristic polynomials to the same cubic. -/
def cubeRootCopy (a : F) (ha : a^2+a+1=0)
    (hp : Irreducible (X^3+C a*X^2+1 : F[X]))
    [Nontrivial F] {r : ℕ} (e : Fin r ↪ F) :
    (completeBipartiteGraph (Fin r) (Fin r)).Copy (graph (F := F)) := by
  have ha0 : a≠0 := by intro h; simp [h] at ha
  have hd : a*(a^2+a^2*a*(a+1)+a*(a+1)^2)=1 := by
    linear_combination (a^3+a^2+a-1)*ha
  have hc : a^2+a^2*a*(a+1)=0 := by linear_combination a^2*ha
  exact parameterCopy a a a (a+1) ha0 ha0 hd hp (by simpa [hc] using hp) e

section FourElementField
variable {K : Type*} [Field K] [CharP K 2] [Fintype K]

omit [Fintype K] in
lemma fourParameters (a : K) (ha0 : a≠0) (ha1 : a≠1) :
    Function.Injective (![0,1,a,a+1] : Fin 4 → K) := by
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have ha' : a+1≠0 := by
    intro h
    apply ha1
    linear_combination h-h2
  clear h2
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The parameter hypotheses hold in every four-element field. -/
theorem four_element_not_free (hcard : Fintype.card K=4) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := K)) := by
  classical
  have hex : ∃ a : K, a≠0 ∧ a≠1 := by
    by_contra! h
    have hs : (Finset.univ : Finset K) ⊆ {0,1} := by
      intro a _
      by_cases ha : a=0
      · simp [ha]
      · simp [h a ha]
    have hc := Finset.card_le_card hs
    simp [hcard] at hc
  obtain ⟨a,ha0,ha1⟩ := hex
  have h2 : (2:K)=0 := CharP.cast_eq_zero K 2
  have hpow : a^4=a := by simpa [hcard] using FiniteField.pow_card a
  have he : a^2+a+1=0 := by
    have hm : a*(a-1)*(a^2+a+1)=0 := by linear_combination hpow
    exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero ha0 (sub_ne_zero.mpr ha1))
  let e : Fin 4 ↪ K := ⟨![0,1,a,a+1],fourParameters a ha0 ha1⟩
  have hes : Function.Surjective e :=
    ((Fintype.bijective_iff_injective_and_card e).mpr
      ⟨e.injective,by simp [hcard]⟩).2
  have hp : Irreducible (X^3+C a*X^2+1 : K[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (X^3+C a*X^2+1 : K[X]).natDegree=3 := by compute_degree!
      simp [hdeg]
    · intro x hx
      obtain ⟨i,rfl⟩ := hes x
      change (X^3+C a*X^2+1 : K[X]).eval (e i)=0 at hx
      fin_cases i
      · simp [e] at hx
      · simp [e] at hx
        apply ha0
        linear_combination hx-h2
      · simp [e] at hx
        have h01 : (1:K)=0 := by linear_combination hx-a^3*h2
        exact one_ne_zero h01
      · simp [e] at hx
        apply pow_ne_zero 2 ha0
        linear_combination hx-(a^3+2*a^2+2*a+1)*h2
  exact fun hf => hf ⟨cubeRootCopy a he hp e⟩

end FourElementField

end Erdos714SL3TracePower
#print axioms Erdos714SL3TracePower.parameterCopy
#print axioms Erdos714SL3TracePower.cubeRootCopy


#print axioms Erdos714SL3TracePower.four_element_not_free
