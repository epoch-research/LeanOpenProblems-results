import Submission.QuadraticEvaluationBinary

/-!
In characteristic two the quadratic-evaluation norm graph still contains K44
when all three coefficients of every vertex polynomial are nonzero and its
leading and linear coefficients are different. This is a construction
obstruction, not a solution of Erdős714 or an arbitrary-thinning theorem.
-/
noncomputable section
open Classical Finset Polynomial SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714QuadraticEvaluationFiltered
open Erdos714QuadraticEvaluation (Coeff Vertex extensionEval normGraph)
open Erdos714QuadraticEvaluationBinary (bit bit_injective bit_square_add norm_pair pair_ne_zero parameter_ne_zero)
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharP F 2] [CharP E 2]

def valid (p : Coeff F) : Prop :=
  p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.1+p.2.1 ≠ 0

def validVertex : Vertex F ⊕ Vertex F → Prop := Sum.elim (fun x => valid x.2) (fun x => valid x.2)

def graph (θ : E) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := (normGraph θ).Adj x y ∧ validVertex x ∧ validVertex y
  symm := by intro x y h; exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by intro x h; exact (normGraph θ).loopless x h.1

def Q (δ l x : F) : F := x^2+x*l+δ*l^2

def weight (δ l z b w : F) : F := Q δ l (w+z)/b

def row (δ l z b w : F) : Vertex F :=
  (0,(weight δ l z b w+w)/δ,(weight δ l z b w+w)/δ+1,weight δ l z b w)

def pointReal (l z h : F) (j : Bool × Bool) : F := z+bit j.1*(h+1)+bit j.2*l

def column (δ k z b h : F) (j : Bool × Bool) : Vertex F :=
  (bit j.1,(pointReal (k+1) z h j+b)/δ,k+(pointReal (k+1) z h j+b)/δ,b)

lemma Q_shift (δ l x h : F) (i j : Bool) :
    Q δ l (x+bit i*h+bit j*l)=Q δ l x+bit i*(h^2+h*l) := by
  cases i <;> cases j <;> dsimp [Q,bit] <;> ring_nf <;> reduce_mod_char!

lemma row_recover (δ l z b w : F) (hδ : δ ≠ 0) :
    (row δ l z b w).2.1*δ+(row δ l z b w).2.2.2=w := by
  dsimp [row]
  rw [div_mul_cancel₀ _ hδ]
  ring_nf
  reduce_mod_char!

lemma row_injective (δ l z b : F) (hδ : δ ≠ 0) : Function.Injective (row δ l z b) := by
  intro w u h
  have he := congrArg (fun x : Vertex F => x.2.1*δ+x.2.2.2) h
  simpa only [row_recover δ l z b w hδ,row_recover δ l z b u hδ] using he

lemma row_eval (δ l z b w : F) (i : Bool) :
    Erdos714QuadraticEvaluation.eval (row δ l z b w).2 (bit i)=weight δ l z b w+bit i := by
  dsimp [Erdos714QuadraticEvaluation.eval,row]
  linear_combination ((weight δ l z b w+w)/δ)*bit_square_add (F := F) i

lemma row_extensionEval (δ l z b w : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (hδ : δ ≠ 0) (i : Bool) :
    extensionEval θ (row δ l z b w).2 (bit i)=algebraMap F E (w+bit i)+θ := by
  have ht := congrArg (algebraMap F E) (bit_square_add (F := F) i)
  have ha := congrArg (algebraMap F E) (row_recover δ l z b w hδ)
  dsimp [row] at ha
  simp only [map_add,map_mul,map_zero,map_pow] at ht ha
  dsimp [extensionEval,row]
  simp only [map_add,map_one]
  linear_combination (norm := (ring_nf;reduce_mod_char!))
    algebraMap F E ((weight δ l z b w+w)/δ)*hθ+
    algebraMap F E ((weight δ l z b w+w)/δ)*ht+ha

lemma column_extensionEval (δ k z b h : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (hδ : δ ≠ 0) (j : Bool × Bool) :
    extensionEval θ (column δ k z b h j).2 0=
      algebraMap F E (pointReal (k+1) z h j)+algebraMap F E k*θ := by
  have ha : (pointReal (k+1) z h j+b)/δ*δ+b=pointReal (k+1) z h j := by
    rw [div_mul_cancel₀ _ hδ]
    ring_nf
    reduce_mod_char!
  have ha' := congrArg (algebraMap F E) ha
  simp only [map_add,map_mul] at ha'
  dsimp [extensionEval,column]
  simp only [map_add,map_zero,zero_add]
  linear_combination (norm := (ring_nf;reduce_mod_char!))
    algebraMap F E ((pointReal (k+1) z h j+b)/δ)*hθ+ha'

lemma norm_equation (δ k z b h w : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (hδ : δ ≠ 0) (hb : b ≠ 0) (hbh : b=h^2+h*(k+1)) (j : Bool × Bool) :
    Algebra.norm F (extensionEval θ (row δ (k+1) z b w).2 (bit j.1)+
      extensionEval θ (column δ k z b h j).2 0)=
        (weight δ (k+1) z b w+bit j.1)*b := by
  rw [row_extensionEval δ (k+1) z b w θ hθ hδ,column_extensionEval δ k z b h θ hθ hδ]
  have he : (algebraMap F E (w+bit j.1)+θ)+
      (algebraMap F E (pointReal (k+1) z h j)+algebraMap F E k*θ)=
      algebraMap F E (w+z+bit j.1*h+bit j.2*(k+1))+algebraMap F E (k+1)*θ := by
    simp only [pointReal,map_add,map_mul,map_one]
    ring_nf
    reduce_mod_char!
  rw [he,norm_pair δ θ hθ B hB]
  change Q δ (k+1) (w+z+bit j.1*h+bit j.2*(k+1))=_
  rw [Q_shift,← hbh]
  dsimp [weight]
  rw [add_mul,div_mul_cancel₀ _ hb]

omit [CharP E 2] in
lemma row_weight_ne_zero (δ k z b h w : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (hb : b ≠ 0) (hbh : b=h^2+h*(k+1)) (hk1 : k+1 ≠ 0) (i : Bool) :
    weight δ (k+1) z b w+bit i ≠ 0 := by
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  have hn : Q δ (k+1) (w+z+bit i*h) ≠ 0 := by
    change (w+z+bit i*h)^2+(w+z+bit i*h)*(k+1)+δ*(k+1)^2 ≠ 0
    rw [← norm_pair δ θ hθ B hB]
    exact Algebra.norm_ne_zero_iff.mpr (pair_ne_zero θ B hB _ (k+1) hk1)
  have he : Q δ (k+1) (w+z+bit i*h)=(weight δ (k+1) z b w+bit i)*b := by
    have hq := Q_shift δ (k+1) (w+z) h i false
    simp only [show (bit false : F)=0 from rfl,zero_mul,add_zero] at hq
    rw [hq,← hbh]
    dsimp [weight]
    rw [add_mul,div_mul_cancel₀ _ hb]
  intro hz
  exact hn (by rw [he,hz,zero_mul])

/-- At most four row parameters violate the two coefficient exclusions. -/
lemma good_card [Fintype F] (δ l z b : F) (hb : b ≠ 0) :
    Fintype.card F ≤
      (univ.filter (fun w => weight δ l z b w+w ≠ 0 ∧ weight δ l z b w+w+δ ≠ 0)).card+4 := by
  let P (i : Bool) : F[X] := X^2+C (l+b)*X+C (z^2+z*l+δ*l^2+b*bit i*δ)
  have hd (i) : (P i).natDegree=2 := by dsimp [P]; compute_degree!
  have hn (i) : P i ≠ 0 := by intro h; have hh := hd i; rw [h,natDegree_zero] at hh; omega
  have hev (i : Bool) (w : F) :
      (P i).eval w=b*(weight δ l z b w+w+bit i*δ) := by
    simp only [P,eval_add,eval_pow,eval_X,eval_mul,eval_C,weight,Q]
    field_simp
    ring_nf
    reduce_mod_char!
  let Bad (i : Bool) := univ.filter (fun w => weight δ l z b w+w+bit i*δ=0)
  have hc (i : Bool) : (Bad i).card ≤ 2 := by
    have hh := Polynomial.card_le_degree_of_subset_roots (p := P i) (Z := Bad i)
      (fun w hw => (Polynomial.mem_roots (hn i)).mpr (by
        change (P i).eval w=0
        rw [hev,(mem_filter.mp hw).2,mul_zero]))
    exact hh.trans (hd i).le
  have hu : (Bad false ∪ Bad true).card ≤ 4 := (card_union_le _ _).trans (by have := hc false; have := hc true; omega)
  let S := univ.filter (fun w => weight δ l z b w+w ≠ 0 ∧ weight δ l z b w+w+δ ≠ 0)
  have he : (Bad false ∪ Bad true) ∪ S=univ := by
    ext w
    simp only [Bad,S,mem_union,mem_filter,mem_univ,true_and,bit,Bool.false_eq_true,
      if_false,if_true,zero_mul,add_zero,one_mul]
    tauto
  have ht := card_union_le (Bad false ∪ Bad true) S
  rw [he,card_univ] at ht
  change Fintype.card F ≤ S.card+4
  omega

/-- Choose a center so all eight required column-coefficient tests are nonzero. -/
lemma center_exists [Fintype F] (δ k b h : F) (hq : 8 < Fintype.card F) :
    ∃ z : F, ∀ j : Bool × Bool,
      pointReal (k+1) z h j+b ≠ 0 ∧ pointReal (k+1) z h j+b+δ*k ≠ 0 := by
  let f (i : Bool × Bool × Bool) := bit i.1*(h+1)+bit i.2.1*(k+1)+b+bit i.2.2*(δ*k)
  let S := (univ : Finset (Bool × Bool × Bool)).image f
  have hs : S.card ≤ 8 := card_image_le.trans (by decide)
  obtain ⟨z,_,hz⟩ := exists_mem_notMem_of_card_lt_card (hs.trans_lt (by simpa using hq))
  refine ⟨z,fun j => ⟨?_,?_⟩⟩
  · intro he
    apply hz
    apply mem_image.mpr
    refine ⟨(j.1,j.2,false),mem_univ _,?_⟩
    dsimp [f,pointReal,bit] at he ⊢
    linear_combination (norm := (ring_nf;reduce_mod_char!)) he
  · intro he
    apply hz
    apply mem_image.mpr
    refine ⟨(j.1,j.2,true),mem_univ _,?_⟩
    dsimp [f,pointReal,bit] at he ⊢
    linear_combination (norm := (ring_nf;reduce_mod_char!)) he

lemma column_valid (δ k z b h : F) (hδ : δ ≠ 0) (hk : k ≠ 0) (hb : b ≠ 0)
    (hz : ∀ j : Bool × Bool, pointReal (k+1) z h j+b ≠ 0 ∧
      pointReal (k+1) z h j+b+δ*k ≠ 0) (j : Bool × Bool) : valid (column δ k z b h j).2 := by
  refine ⟨div_ne_zero (hz j).1 hδ,?_,hb,?_⟩
  · intro he
    apply (hz j).2
    change k+(pointReal (k+1) z h j+b)/δ=0 at he
    field_simp at he
    linear_combination he
  · change (pointReal (k+1) z h j+b)/δ+(k+(pointReal (k+1) z h j+b)/δ) ≠ 0
    have he : (pointReal (k+1) z h j+b)/δ+(k+(pointReal (k+1) z h j+b)/δ)=k := by
      ring_nf
      reduce_mod_char!
    rwa [he]

lemma row_valid (δ l z b w : F) (hδ : δ ≠ 0)
    (hw : weight δ l z b w+w ≠ 0 ∧ weight δ l z b w+w+δ ≠ 0)
    (hv : weight δ l z b w ≠ 0) : valid (row δ l z b w).2 := by
  refine ⟨div_ne_zero hw.1 hδ,?_,hv,?_⟩
  · intro he
    apply hw.2
    change (weight δ l z b w+w)/δ+1=0 at he
    field_simp at he
    linear_combination he
  · change (weight δ l z b w+w)/δ+((weight δ l z b w+w)/δ+1) ≠ 0
    have he : (weight δ l z b w+w)/δ+((weight δ l z b w+w)/δ+1)=(1:F) := by
      ring_nf
      reduce_mod_char!
    rw [he]
    exact one_ne_zero

omit [CharP F 2] in
lemma column_injective (δ k z b h : F) (hδ : δ ≠ 0) (hk1 : k+1 ≠ 0) :
    Function.Injective (column δ k z b h) := by
  rintro ⟨i,j⟩ ⟨u,v⟩ he
  have hi : i=u := bit_injective (congrArg Prod.fst he)
  subst u
  have ha : (pointReal (k+1) z h (i,j)+b)/δ=(pointReal (k+1) z h (i,v)+b)/δ :=
    congrArg (fun x : Vertex F => x.2.1) he
  have hp := add_right_cancel ((div_left_inj' hδ).mp ha)
  have hj : j=v := by
    apply bit_injective (F := F)
    apply mul_right_cancel₀ hk1
    change pointReal (k+1) z h (i,j)=pointReal (k+1) z h (i,v) at hp
    dsimp [pointReal] at hp
    linear_combination hp
  subst v
  rfl

/-- The filtered graph fails uniformly in every sufficiently large binary
field, with genuine quadratic field-norm semantics. -/
theorem not_free [Fintype F] (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (hq : 8 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) θ) := by
  have hδ := parameter_ne_zero δ θ hθ B hB
  obtain ⟨k,_,hk⟩ := exists_mem_notMem_of_card_lt_card
    (s := ({0,1} : Finset F)) (t := univ)
    ((show ({0,1} : Finset F).card ≤ 2 from card_le_two).trans_lt (by simp; omega))
  have hk' : k ≠ 0 ∧ k ≠ 1 := by simpa using hk
  have hk1 : k+1 ≠ 0 := by intro he; apply hk'.2; linear_combination (norm := (ring_nf;reduce_mod_char!)) he
  obtain ⟨h,_,hh⟩ := exists_mem_notMem_of_card_lt_card
    (s := ({0,k+1} : Finset F)) (t := univ)
    ((show ({0,k+1} : Finset F).card ≤ 2 from card_le_two).trans_lt (by simp; omega))
  have hh' : h ≠ 0 ∧ h ≠ k+1 := by simpa using hh
  let b := h^2+h*(k+1)
  have hb : b ≠ 0 := by
    have he : b=h*(h+(k+1)) := by dsimp [b]; ring
    rw [he]
    apply mul_ne_zero hh'.1
    intro hz
    apply hh'.2
    linear_combination (norm := (ring_nf;reduce_mod_char!)) hz
  obtain ⟨z,hz⟩ := center_exists δ k b h hq
  let S := univ.filter (fun w => weight δ (k+1) z b w+w ≠ 0 ∧ weight δ (k+1) z b w+w+δ ≠ 0)
  have hS : 4 ≤ S.card := by
    have hc := good_card δ (k+1) z b hb
    change 4 ≤ (univ.filter (fun w => weight δ (k+1) z b w+w ≠ 0 ∧ weight δ (k+1) z b w+w+δ ≠ 0)).card
    simp only [ne_eq] at *
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := S)
    (by simpa only [Fintype.card_fin,Fintype.card_coe] using hS)
  let L : Fin 4 ↪ Vertex F := e.trans ⟨fun w => row δ (k+1) z b w.val,by
    intro w u he; exact Subtype.ext (row_injective δ (k+1) z b hδ he)⟩
  let eqv : Fin 4 ≃ Bool × Bool :=
    (finCongr (by simp : 4=Fintype.card (Bool × Bool))).trans (Fintype.equivFin _).symm
  let R := eqv.toEmbedding.trans ⟨column δ k z b h,column_injective δ k z b h hδ hk1⟩
  have hedge (i j : Fin 4) : (graph (F := F) θ).Adj (.inl (L i)) (.inr (R j)) := by
    let w := (e i).val
    let d := eqv j
    have hw := (mem_filter.mp (e i).property).2
    have hv (t) := row_weight_ne_zero δ k z b h w θ hθ B hB hb rfl hk1 t
    have hl : valid (L i).2 := row_valid δ (k+1) z b w hδ hw (by simpa [bit] using hv false)
    have hr : valid (R j).2 := column_valid δ k z b h hδ hk'.1 hb hz d
    refine ⟨⟨hl.1,hr.1,?_,?_,?_⟩,hl,hr⟩
    · exact (row_eval δ (k+1) z b w d.1).trans_ne (hv d.1)
    · simpa [R,L,column,row,Erdos714QuadraticEvaluation.eval] using hb
    · change Algebra.norm F (extensionEval θ (row δ (k+1) z b w).2 (bit d.1)+
        extensionEval θ (column δ k z b h d).2 0)=
          Erdos714QuadraticEvaluation.eval (row δ (k+1) z b w).2 (bit d.1)*
          Erdos714QuadraticEvaluation.eval (column δ k z b h d).2 0
      rw [norm_equation δ k z b h w θ hθ B hB hδ hb rfl,row_eval]
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
    | inl j => exact (hedge j i).symm

#print axioms Q_shift
#print axioms norm_equation
#print axioms row_weight_ne_zero
#print axioms good_card
#print axioms center_exists
#print axioms row_valid
#print axioms column_valid
#print axioms not_free
end Erdos714QuadraticEvaluationFiltered
