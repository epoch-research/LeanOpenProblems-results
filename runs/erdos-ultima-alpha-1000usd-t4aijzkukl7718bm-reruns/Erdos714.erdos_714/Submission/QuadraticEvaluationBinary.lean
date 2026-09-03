import Submission.QuadraticEvaluationGluing

/-!
The characteristic-two version of quadratic-evaluation gluing also contains
K44. The norm is the actual norm in a supplied quadratic power basis. Four
columns use two tags and two conjugate evaluations. This is an auxiliary
construction obstruction, not a solution of Erdős714.
-/
noncomputable section
open Classical Finset Polynomial SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714QuadraticEvaluationBinary
open Erdos714QuadraticEvaluation (Coeff Vertex extensionEval normGraph)
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharP F 2] [CharP E 2]

omit [CharP E 2] in
lemma norm_pair (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) (a b : F) :
    Algebra.norm F (algebraMap F E a+algebraMap F E b*θ)=a^2+a*b+δ*b^2 := by
  let M : Matrix (Fin 2) (Fin 2) F := !![a,δ*b;b,a+b]
  have hcol (j : Fin 2) :
      ∑ i, M i j • B i=(algebraMap F E a+algebraMap F E b*θ)*B j := by
    simp only [Fin.sum_univ_two,hB,Algebra.smul_def]
    fin_cases j
    · simp [M]
    · dsimp [M]
      simp only [pow_zero,pow_one,map_mul,map_add,mul_one]
      linear_combination -(algebraMap F E b)*hθ
  have hm : Algebra.leftMulMatrix B (algebraMap F E a+algebraMap F E b*θ)=M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul,← hcol j]
    fin_cases i <;> simp
  rw [Algebra.norm_eq_matrix_det B,hm,Matrix.det_fin_two]
  dsimp [M]
  ring_nf
  reduce_mod_char!
  ring

omit [CharP F 2] [CharP E 2] in
lemma pair_ne_zero (θ : E) (B : Module.Basis (Fin 2) F E)
    (hB : ∀ i, B i=θ^(i : ℕ)) (a b : F) (hb : b ≠ 0) :
    algebraMap F E a+algebraMap F E b*θ ≠ 0 := by
  have he : algebraMap F E a+algebraMap F E b*θ=a • B 0+b • B 1 := by
    simp [hB,Algebra.smul_def]
  intro hz
  have h := congrArg (fun x => B.repr x 1) hz
  rw [he] at h
  exact hb (by simpa using h)

omit [CharP F 2] in
lemma parameter_ne_zero (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) : δ ≠ 0 := by
  intro hd
  have hp : θ*(θ+1)=0 := by
    rw [hd,map_zero,add_zero] at hθ
    linear_combination (norm := (ring_nf;reduce_mod_char!)) hθ
  have h0 := pair_ne_zero θ B hB 0 1 one_ne_zero
  have h1 := pair_ne_zero θ B hB 1 1 one_ne_zero
  rcases mul_eq_zero.mp hp with h | h
  · exact h0 (by simpa using h)
  · exact h1 (by simpa [add_comm] using h)

def value (δ k w : F) : F := (w+1+δ)^2+(w+1+δ)*k+δ*k^2

def row (δ k w : F) : Vertex F :=
  (0,(value δ k w+w)/δ,(value δ k w+w)/δ,value δ k w)

def bit (b : Bool) : F := if b then 1 else 0
omit [CharP F 2] in
lemma bit_injective : Function.Injective (bit (F := F)) := by
  intro i j h
  cases i <;> cases j <;> simp_all [bit]

lemma bit_square_add (b : Bool) : (bit b : F)^2+bit b=0 := by
  cases b <;> simp [bit,CharTwo.add_self_eq_zero]

def leading (δ k : F) (b : Bool) : F := if b then 1+k/δ else 1

def column (δ k : F) (j : Bool × Bool) : Vertex F :=
  (bit j.1,leading δ k j.2,k+leading δ k j.2,1)

lemma leading_ne_zero (δ k : F) (hδ : δ ≠ 0) (hkδ : k ≠ δ) (b : Bool) :
    leading δ k b ≠ 0 := by
  cases b
  · simp [leading]
  · intro h
    have he : δ+k=0 := by
      have h' : 1+k/δ=0 := h
      field_simp at h'
      simpa using h'
    apply hkδ
    linear_combination (norm := (ring_nf;reduce_mod_char!)) he

omit [CharP F 2] in
lemma column_injective (δ k : F) (hδ : δ ≠ 0) (hk : k ≠ 0) :
    Function.Injective (column δ k) := by
  have hlead : Function.Injective (leading δ k) := by
    intro i j h
    cases i <;> cases j <;> try rfl
    all_goals exfalso; apply div_ne_zero hk hδ
    · change 1=1+k/δ at h
      linear_combination -h
    · change 1+k/δ=1 at h
      linear_combination h
  rintro ⟨i,j⟩ ⟨l,m⟩ h
  have hi := bit_injective (congrArg Prod.fst h)
  have hj := hlead (congrArg (fun x : Vertex F => x.2.1) h)
  exact Prod.ext hi hj

lemma row_recover (δ k w : F) (hδ : δ ≠ 0) :
    (row δ k w).2.1*δ+(row δ k w).2.2.2=w := by
  dsimp [row]
  rw [div_mul_cancel₀ _ hδ]
  ring_nf
  reduce_mod_char!

lemma row_injective (δ k : F) (hδ : δ ≠ 0) : Function.Injective (row δ k) := by
  intro w z h
  have he := congrArg (fun x : Vertex F => x.2.1*δ+x.2.2.2) h
  simpa only [row_recover δ k w hδ,row_recover δ k z hδ] using he

lemma row_eval (δ k w : F) (b : Bool) : Erdos714QuadraticEvaluation.eval (row δ k w).2 (bit b)=value δ k w := by
  dsimp [Erdos714QuadraticEvaluation.eval,row]
  linear_combination ((value δ k w+w)/δ)*bit_square_add (F := F) b

lemma row_extensionEval (δ k w : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (hδ : δ ≠ 0) (b : Bool) :
    extensionEval θ (row δ k w).2 (bit b)=algebraMap F E w := by
  have ht := congrArg (algebraMap F E) (bit_square_add (F := F) b)
  have ha := congrArg (algebraMap F E) (row_recover δ k w hδ)
  dsimp [row] at ha
  simp only [map_add,map_mul,map_zero,map_pow] at ht ha
  dsimp [extensionEval,row]
  linear_combination (norm := (ring_nf;reduce_mod_char!))
    algebraMap F E ((value δ k w+w)/δ)*hθ+
    algebraMap F E ((value δ k w+w)/δ)*ht+ha

omit [CharP F 2] in
lemma column_extensionEval (δ k : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (hδ : δ ≠ 0) (j : Bool × Bool) :
    extensionEval θ (column δ k j).2 0=
      algebraMap F E (1+δ+bit j.2*k)+algebraMap F E k*θ := by
  have ha : leading δ k j.2*δ=δ+bit j.2*k := by
    cases j.2 <;> simp [leading,bit,add_mul,div_mul_cancel₀ _ hδ]
  have ha' := congrArg (algebraMap F E) ha
  dsimp [extensionEval,column]
  simp only [map_zero,zero_add,map_add,map_one,map_mul]
  simp only [map_add,map_mul] at ha'
  linear_combination (norm := (ring_nf;reduce_mod_char!))
    algebraMap F E (leading δ k j.2)*hθ+ha'

omit [CharP E 2] in
lemma shifted_norm (δ k w : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) (b : Bool) :
    Algebra.norm F (algebraMap F E w+
      (algebraMap F E (1+δ+bit b*k)+algebraMap F E k*θ))=value δ k w := by
  rw [show algebraMap F E w+(algebraMap F E (1+δ+bit b*k)+algebraMap F E k*θ)=
      algebraMap F E (w+1+δ+bit b*k)+algebraMap F E k*θ by simp only [map_add]; ring]
  rw [norm_pair δ θ hθ B hB]
  dsimp [value]
  cases b
  · dsimp [bit]; ring
  · dsimp [bit]; ring_nf; reduce_mod_char!

omit [CharP E 2] in
lemma value_ne_zero (δ k w : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) (hk : k ≠ 0) :
    value δ k w ≠ 0 := by
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  unfold value
  rw [← norm_pair δ θ hθ B hB]
  exact Algebra.norm_ne_zero_iff.mpr (pair_ne_zero θ B hB _ k hk)

lemma good_card [Fintype F] (δ k : F) :
    Fintype.card F ≤ (univ.filter (fun w => value δ k w+w ≠ 0)).card+2 := by
  let P : F[X] := X^2+C (k+1)*X+C ((1+δ)^2+(1+δ)*k+δ*k^2)
  have hd : P.natDegree=2 := by dsimp [P]; compute_degree!
  have hP : P ≠ 0 := by intro h; rw [h,natDegree_zero] at hd; omega
  have hev (w : F) : P.eval w=value δ k w+w := by
    simp only [P,eval_add,eval_pow,eval_X,eval_mul,eval_C,value]
    ring_nf
    reduce_mod_char!
  have hb : (univ.filter (fun w => value δ k w+w=0)).card ≤ 2 := by
    have h := Polynomial.card_le_degree_of_subset_roots (p := P)
      (Z := univ.filter (fun w => value δ k w+w=0)) (fun w hw =>
        (Polynomial.mem_roots hP).mpr (by change P.eval w=0; rw [hev]; exact (mem_filter.mp hw).2))
    exact h.trans hd.le
  have h := card_filter_add_card_filter_not (s := (univ : Finset F))
    (p := fun w => value δ k w+w=0)
  simp only [card_univ] at h
  simp only [ne_eq] at *
  omega

/-- The same actual host as in the odd-characteristic file fails in
characteristic two, including the exact-degree and nonzero-weight guards. -/
theorem not_free [Fintype F] (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (hq : 6 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (normGraph (F := F) θ) := by
  have hδ := parameter_ne_zero δ θ hθ B hB
  obtain ⟨k,_,hk⟩ := exists_mem_notMem_of_card_lt_card
    (s := ({0,δ} : Finset F)) (t := univ)
    ((show ({0,δ} : Finset F).card ≤ 2 from card_le_two).trans_lt (by simp; omega))
  have hk0 : k ≠ 0 := by simpa using (not_or.mp (by simpa using hk : ¬(k=0 ∨ k=δ))).1
  have hkδ : k ≠ δ := by simpa using (not_or.mp (by simpa using hk : ¬(k=0 ∨ k=δ))).2
  let S := univ.filter (fun w : F => value δ k w+w ≠ 0)
  have hS : 4 ≤ S.card := by
    have h := good_card δ k
    change 4 ≤ (univ.filter (fun w => value δ k w+w ≠ 0)).card
    simp only [ne_eq] at *
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4) (β := S) (by simpa only [Fintype.card_fin,Fintype.card_coe] using hS)
  let L : Fin 4 ↪ Vertex F := e.trans ⟨fun w => row δ k w.val,by
    intro w z h; exact Subtype.ext (row_injective δ k hδ h)⟩
  let eqv : Fin 4 ≃ Bool × Bool :=
    (finCongr (by simp : 4=Fintype.card (Bool × Bool))).trans (Fintype.equivFin _).symm
  let R := eqv.toEmbedding.trans ⟨column δ k,column_injective δ k hδ hk0⟩
  have hedge (i j : Fin 4) : (normGraph (F := F) θ).Adj (.inl (L i)) (.inr (R j)) := by
    let w := (e i).val
    let b := eqv j
    have hv := value_ne_zero δ k w θ hθ B hB hk0
    refine ⟨div_ne_zero (mem_filter.mp (e i).property).2 hδ,
      leading_ne_zero δ k hδ hkδ b.2,?_,?_,?_⟩
    · exact (row_eval δ k w b.1).trans_ne hv
    · simp [R,column,L,row,Erdos714QuadraticEvaluation.eval]
    · change Algebra.norm F (extensionEval θ (row δ k w).2 (bit b.1)+
        extensionEval θ (column δ k b).2 0)=Erdos714QuadraticEvaluation.eval (row δ k w).2 (bit b.1)*
        Erdos714QuadraticEvaluation.eval (column δ k b).2 0
      rw [row_extensionEval δ k w θ hθ hδ,column_extensionEval δ k θ hθ hδ,
        shifted_norm δ k w θ hθ B hB,row_eval]
      simp [Erdos714QuadraticEvaluation.eval,column]
  intro hf
  apply hf
  refine ⟨⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact hedge i j
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact hedge j i

#print axioms norm_pair
#print axioms parameter_ne_zero
#print axioms row_extensionEval
#print axioms column_extensionEval
#print axioms shifted_norm
#print axioms value_ne_zero
#print axioms good_card
#print axioms not_free
end Erdos714QuadraticEvaluationBinary
