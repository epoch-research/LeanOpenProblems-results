import FormalConjecturesUtil

/-!
Chevalley--Warning obstructs full translation graphs of low-codimension
quadratic fibers. This does not settle Erdős Problem 714.
-/

noncomputable section
open Finset MvPolynomial SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714QuadraticTranslation

variable {K σ ι : Type*} [Field K] [Fintype K] [Fintype σ] [Fintype ι]

/-- A zero common solution is not the only one below the Warning degree threshold. -/
lemma nonzero_common_solution (f : ι → MvPolynomial σ K)
    (hdeg : (∑ i, (f i).totalDegree) < Fintype.card σ)
    (hz : ∀ i, eval (0 : σ → K) (f i)=0) :
    ∃ v : σ → K, v≠0 ∧ ∀ i, eval v (f i)=0 := by
  classical
  by_contra h
  have heq (v : σ → K) (hv : ∀ i, eval v (f i)=0) : v=0 := by
    by_contra hn
    exact h ⟨v,hn,hv⟩
  have hc : Fintype.card {v : σ → K // ∀ i, eval v (f i)=0}=1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨0,hz⟩,?_⟩
    intro v
    exact Subtype.ext (heq v.val v.property)
  have hd := char_dvd_card_solutions_of_fintype_sum_lt (ringChar K) hdeg
  rw [hc] at hd
  exact CharP.ringChar_ne_one (Nat.dvd_one.mp hd)

/-- An arbitrary coordinate quadratic polynomial, without a symmetry assumption. -/
def value (A : σ → σ → K) (b : σ → K) (c : K) (x : σ → K) : K :=
  (∑ i, ∑ j, A i j*x i*x j) + (∑ i, b i*x i) + c

def quadraticPoly (A : σ → σ → K) : MvPolynomial σ K :=
  ∑ i, ∑ j, C (A i j)*X i*X j

def directionalPoly (A : σ → σ → K) (b z : σ → K) : MvPolynomial σ K :=
  (∑ i, ∑ j, C (A i j)*(C (z i)*X j+X i*C (z j))) + ∑ i, C (b i)*X i

omit [Fintype K] [Fintype σ] in
lemma sum_degree_le {τ : Type*} (s : Finset τ) (p : τ → MvPolynomial σ K) (d : ℕ)
    (hp : ∀ i ∈ s, (p i).totalDegree≤d) : (∑ i ∈ s, p i).totalDegree≤d :=
  (MvPolynomial.totalDegree_finset_sum s p).trans (Finset.sup_le hp)

omit [Fintype K] in
lemma quadratic_degree (A : σ → σ → K) : (quadraticPoly A).totalDegree≤2 := by
  apply sum_degree_le
  intro i _
  apply sum_degree_le
  intro j _
  have h₁ := totalDegree_mul (C (A i j) : MvPolynomial σ K) (X i)
  have h₂ := totalDegree_mul (C (A i j)*X i : MvPolynomial σ K) (X j)
  simp only [totalDegree_C,totalDegree_X,zero_add] at h₁ h₂
  omega

omit [Fintype K] in
lemma directional_degree (A : σ → σ → K) (b z : σ → K) :
    (directionalPoly A b z).totalDegree≤1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply sum_degree_le
    intro i _
    apply sum_degree_le
    intro j _
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C,zero_add]
    apply (totalDegree_add _ _).trans
    apply max_le
    · simpa using totalDegree_mul (C (z i) : MvPolynomial σ K) (X j)
    · simpa using totalDegree_mul (X i : MvPolynomial σ K) (C (z j))
  · apply sum_degree_le
    intro i _
    simpa using totalDegree_mul (C (b i) : MvPolynomial σ K) (X i)

omit [Fintype K] in
lemma eval_quadratic (A : σ → σ → K) (v : σ → K) :
    eval v (quadraticPoly A) = ∑ i, ∑ j, A i j*v i*v j := by
  simp [quadraticPoly]

omit [Fintype K] in
lemma eval_directional (A : σ → σ → K) (b z v : σ → K) :
    eval v (directionalPoly A b z) =
      (∑ i, ∑ j, A i j*(z i*v j+v i*z j)) + ∑ i, b i*v i := by
  simp [directionalPoly]

omit [Fintype K] in
/-- Exact coefficient identity along every affine line, in every characteristic. -/
lemma value_on_line (A : σ → σ → K) (b z v : σ → K) (c t : K) :
    value A b c (z+t • v) = value A b c z +
      t*eval v (directionalPoly A b z) + t^2*eval v (quadraticPoly A) := by
  rw [eval_directional,eval_quadratic]
  simp only [value,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hq : (∑ i, ∑ j, A i j*(z i+t*v i)*(z j+t*v j)) =
      (∑ i, ∑ j, A i j*z i*z j) +
      t*(∑ i, ∑ j, A i j*(z i*v j+v i*z j)) +
      t^2*(∑ i, ∑ j, A i j*v i*v j) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hl : (∑ i, b i*(z i+t*v i)) = (∑ i, b i*z i)+t*∑ i, b i*v i := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hq,hl]
  ring

/-- Every point of every nonempty quadratic fiber lies on a full affine line. -/
theorem fiber_line (A : ι → σ → σ → K) (b : ι → σ → K) (c : ι → K)
    (hdim : 3*Fintype.card ι < Fintype.card σ) (z : σ → K) :
    ∃ v : σ → K, v≠0 ∧ ∀ (t : K) (i : ι), value (A i) (b i) (c i) (z+t • v)=value (A i) (b i) (c i) z := by
  classical
  let f : ι ⊕ ι → MvPolynomial σ K := Sum.elim (fun i => quadraticPoly (A i))
    (fun i => directionalPoly (A i) (b i) z)
  have hdeg : (∑ j, (f j).totalDegree)<Fintype.card σ := by
    apply lt_of_le_of_lt _ hdim
    simp only [Fintype.sum_sum_type,f,Sum.elim_inl,Sum.elim_inr]
    calc
      _ ≤ (∑ _i : ι, 2)+(∑ _i : ι, 1) := by
        apply Nat.add_le_add
        · exact Finset.sum_le_sum (fun i _ => quadratic_degree (A i))
        · exact Finset.sum_le_sum (fun i _ => directional_degree (A i) (b i) z)
      _ = _ := by simp; omega
  obtain ⟨v,hv,hzero⟩ := nonzero_common_solution f hdeg (by
    intro i
    cases i <;> simp [f,quadraticPoly,directionalPoly])
  refine ⟨v,hv,?_⟩
  intro t i
  rw [value_on_line]
  have hq := hzero (Sum.inl i)
  have hl := hzero (Sum.inr i)
  change eval v (quadraticPoly (A i))=0 at hq
  change eval v (directionalPoly (A i) (b i) z)=0 at hl
  simp [hq,hl]

/-- The proposed full translation graph, with arbitrary quadratic coefficients
and arbitrary target values on the two identical vertex parts. -/
def graph (A : ι → σ → σ → K) (b : ι → σ → K) (c d : ι → K) :
    SimpleGraph ((σ → K) ⊕ (σ → K)) where
  Adj x y := match x,y with
    | .inl u,.inr v => ∀ i, value (A i) (b i) (c i) (u+v)=d i
    | .inr v,.inl u => ∀ i, value (A i) (b i) (c i) (u+v)=d i
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

omit [Fintype K] [Fintype σ] in
lemma line_injective {v : σ → K} (hv : v≠0) :
    Function.Injective (fun t : K => t • v) := by
  have hex : ∃ i, v i≠0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i,hi⟩ := hex
  intro s t h
  have he := congrFun h i
  exact mul_right_cancel₀ hi he

/-- Every nonempty fiber produces a complete bipartite graph as large as the field. -/
def fiberCopy (A : ι → σ → σ → K) (b : ι → σ → K) (c d : ι → K)
    (hdim : 3*Fintype.card ι < Fintype.card σ) (z : σ → K)
    (hz : ∀ i, value (A i) (b i) (c i) z=d i)
    {r : ℕ} (e : Fin r ↪ K) :
    (completeBipartiteGraph (Fin r) (Fin r)).Copy (graph A b c d) := by
  let v := Classical.choose (fiber_line A b c hdim z)
  have hv : v≠0 := (Classical.choose_spec (fiber_line A b c hdim z)).1
  have hline := (Classical.choose_spec (fiber_line A b c hdim z)).2
  let L : Fin r ↪ (σ → K) := ⟨fun i => e i • v,
    fun _ _ h => e.injective (line_injective hv h)⟩
  let R : Fin r ↪ (σ → K) := ⟨fun i => z+e i • v,
    fun _ _ h => e.injective (line_injective hv (add_left_cancel h))⟩
  have he (i j : Fin r) : (graph A b c d).Adj (.inl (L i)) (.inr (R j)) := by
    intro k
    change value (A k) (b k) (c k) (e i • v+(z+e j • v))=d k
    have heq : e i • v+(z+e j • v)=z+(e i+e j) • v := by
      simp [add_smul,add_left_comm]
    rw [heq,hline,hz]
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
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

/-- Below this dimension threshold a full quadratic translation graph can
be biclique-free only by having no edges at all. -/
theorem free_implies_empty (A : ι → σ → σ → K) (b : ι → σ → K) (c d : ι → K)
    (hdim : 3*Fintype.card ι < Fintype.card σ) {r : ℕ} (e : Fin r ↪ K)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph A b c d)) :
    graph A b c d = ⊥ := by
  apply le_antisymm _ bot_le
  intro x y h
  cases x with
  | inl u =>
    cases y with
    | inl v => exact False.elim h
    | inr v => exact False.elim (hf ⟨fiberCopy A b c d hdim (u+v) h e⟩)
  | inr v =>
    cases y with
    | inl u => exact False.elim (hf ⟨fiberCopy A b c d hdim (u+v) h e⟩)
    | inr u => exact False.elim h

/-- In the intended eight-variable/two-equation fourth-case scale, even one
edge forces a K44 whenever the field has at least four elements. -/
theorem two_quadratic_not_free (A : Fin 2 → Fin 8 → Fin 8 → K)
    (b : Fin 2 → Fin 8 → K) (c d : Fin 2 → K)
    (hcard : 4≤Fintype.card K)
    (hz : ∃ z : Fin 8 → K, ∀ i, value (A i) (b i) (c i) z=d i) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph A b c d) := by
  obtain ⟨z,hz⟩ := hz
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := K)
    (by simpa using hcard)
  exact fun hf => hf ⟨fiberCopy A b c d (by simp) z hz e⟩

end Erdos714QuadraticTranslation
#print axioms Erdos714QuadraticTranslation.nonzero_common_solution
#print axioms Erdos714QuadraticTranslation.value_on_line
#print axioms Erdos714QuadraticTranslation.fiber_line
#print axioms Erdos714QuadraticTranslation.fiberCopy
#print axioms Erdos714QuadraticTranslation.two_quadratic_not_free


#print axioms Erdos714QuadraticTranslation.free_implies_empty
