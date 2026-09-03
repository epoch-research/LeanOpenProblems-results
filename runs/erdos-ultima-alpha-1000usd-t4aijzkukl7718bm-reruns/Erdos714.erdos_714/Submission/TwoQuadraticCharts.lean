import Submission.QuadraticEvaluationBinary

/-!
Two binary quadratic-norm charts can already force K44. The theorem below
states all linear compatibility hypotheses explicitly; it does not assert
that arbitrary endpoint-dependent permutations have those properties, and
it does not settle Erdős 714.
-/
noncomputable section
open Classical Polynomial SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714TwoQuadraticCharts
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharP F 2] [CharP E 2]

abbrev kappa (x : F) := x*(x+1)

omit [Field E] [Algebra F E] [CharP F 2] [CharP E 2] in
lemma parameter [Fintype F] (hq : 6 < Fintype.card F) (b₀ b₁ Δ₀ Δ₁ : F)
    (h₀ : Δ₀ ≠ 0) (h₁ : Δ₁ ≠ 0) :
    ∃ x : F, kappa x ≠ 0 ∧ Δ₀+b₀*kappa x ≠ 0 ∧ Δ₁+b₁*kappa x ≠ 0 := by
  let P (b Δ : F) : F[X] := C Δ+C b*(X*(X+1))
  have hn (b Δ : F) (h : Δ ≠ 0) : P b Δ ≠ 0 := by
    intro he
    have hh := congrArg (Polynomial.eval 0) he
    exact h (by simpa [P] using hh)
  let Q := X*(X+1)*P b₀ Δ₀*P b₁ Δ₁
  have hQ : Q ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero X_ne_zero (by exact (monic_X_add_C 1).ne_zero)) (hn _ _ h₀)
    · exact hn _ _ h₁
  have hdeg : Q.natDegree ≤ 6 := by dsimp [Q,P]; compute_degree!
  obtain ⟨x,hx⟩ := Q.exists_eval_ne_zero_of_natDegree_lt_card hQ (by
    rw [Cardinal.mk_fintype]
    exact_mod_cast (lt_of_le_of_lt hdeg hq))
  have hx' : x*(x+1)*(Δ₀+b₀*(x*(x+1)))*(Δ₁+b₁*(x*(x+1))) ≠ 0 := by
    simpa [Q,P] using hx
  exact ⟨x,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').1).2,(mul_ne_zero_iff.mp hx').2⟩

def offset (x γ : F) : Fin 4 → F := ![0,1,x+γ,x+γ+1]
def step : Fin 4 → F := ![0,0,1,1]
def bit (e : Bool) : F := if e then 1 else 0

omit [Field E] [Algebra F E] [CharP E 2] in
lemma offset_square (x γ : F) (hγ : γ^2=γ) (i : Fin 4) :
    offset x γ i^2+offset x γ i=step (F := F) i*kappa x := by
  fin_cases i <;> simp [offset,step] <;>
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hγ
  all_goals simpa only [hγ] using CharTwo.add_self_eq_zero γ

omit [CharP E 2] in
lemma norm_identity (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (η : E) (β d a b Δ μ σ : F) (hd : d=1+b*β) (ha : a*β=δ*d^2)
    (hμ : μ^2+μ=σ*(β*Δ)) (e : Bool) :
    Algebra.norm F (η*(algebraMap F E (μ+bit e*d)+algebraMap F E d*θ))=
      (a+b*μ+σ*Δ)*(Algebra.norm F η*β) := by
  rw [map_mul,Erdos714QuadraticEvaluationBinary.norm_pair δ θ hθ B hB]
  have hscalar : (μ+bit e*d)^2+(μ+bit e*d)*d+δ*d^2=(a+b*μ+σ*Δ)*β := by
    cases e <;> simp only [bit,Bool.false_eq_true,↓reduceIte,zero_mul,add_zero,one_mul]
    all_goals rw [←ha,hd]
    all_goals linear_combination (norm := (ring_nf <;> reduce_mod_char!)) hμ
  rw [hscalar]
  ring

omit [CharP F 2] [CharP E 2] in
lemma norm_point_ne_zero (θ : E) (B : Module.Basis (Fin 2) F E)
    (hB : ∀ i, B i=θ^(i : ℕ)) (η : E) (hη : η ≠ 0) (d μ : F) (hd : d ≠ 0) (e : Bool) :
    Algebra.norm F (η*(algebraMap F E (μ+bit e*d)+algebraMap F E d*θ)) ≠ 0 := by
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  apply Algebra.norm_ne_zero_iff.mpr
  exact mul_ne_zero hη (Erdos714QuadraticEvaluationBinary.pair_ne_zero θ B hB _ _ hd)

section Linear
variable {V : Type*} [AddCommGroup V] [Module F V]

def rows (p u w : V) (x : F) : Fin 4 → V :=
  ![p,p+u,p+x • u+w,p+(x+1) • u+w]

def graph (z : Bool → V →ₗ[F] E) (a : Bool → V →ₗ[F] F) :
    SimpleGraph (V ⊕ (Bool × E × Fˣ)) where
  Adj v w := match v,w with
    | .inl v,.inr w => Algebra.norm F (z w.1 v+w.2.1)=a w.1 v*(w.2.2 : F) ∧ a w.1 v ≠ 0
    | .inr w,.inl v => Algebra.norm F (z w.1 v+w.2.1)=a w.1 v*(w.2.2 : F) ∧ a w.1 v ≠ 0
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

omit [CharP F 2] [CharP E 2] in
lemma rows_injective (p u w : V) (x : F) (z : V →ₗ[F] E) (a : V →ₗ[F] F)
    (hu : z u ≠ 0) (hw : z w=0) (ha : a w ≠ 0) : Function.Injective (rows p u w x) := by
  let f : F × F → V := fun v => v.1 • u+v.2 • w
  have hf : Function.Injective f := by
    intro v v' he
    have hz := congrArg z he
    change z (v.1 • u+v.2 • w)=z (v'.1 • u+v'.2 • w) at hz
    simp only [map_add,map_smul,hw,Algebra.smul_def,mul_zero,add_zero] at hz
    have h1 : v.1=v'.1 := (algebraMap F E).injective (mul_right_cancel₀ hu hz)
    have hh := congrArg a he
    change a (v.1 • u+v.2 • w)=a (v'.1 • u+v'.2 • w) at hh
    simp only [map_add,map_smul,smul_eq_mul,h1] at hh
    exact Prod.ext h1 (mul_right_cancel₀ ha (add_left_cancel hh))
  let c : Fin 4 → F × F := fun i => (offset x 0 i,step i)
  have hc : Function.Injective c := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp [c,offset,step] at he ⊢
  have hr (i : Fin 4) : rows p u w x i=p+f (c i) := by
    fin_cases i <;> simp [rows,f,c,offset,step,add_assoc]
  intro i j he
  exact hc (hf (add_left_cancel ((hr i).symm.trans (he.trans (hr j)))))


omit [CharP F 2] [CharP E 2] in
lemma point_rows (p u w : V) (x γ : F) (z : V →ₗ[F] E) (η : E)
    (hu : z u=η) (hw : z w=algebraMap F E γ*η) (i : Fin 4) :
    z (rows p u w x i)=z p+η*algebraMap F E (offset x γ i) := by
  fin_cases i <;> simp [rows,offset,map_add,map_smul,hu,hw,Algebra.smul_def] <;> ring

lemma weight_rows (p u w : V) (x γ : F) (a : V →ₗ[F] F) (Δ : F)
    (hΔ : Δ=a w+γ*a u) (i : Fin 4) :
    a (rows p u w x i)=a p+a u*offset x γ i+step (F := F) i*Δ := by
  fin_cases i <;> simp [rows,offset,step,map_add,map_smul,hΔ,smul_eq_mul] <;>
    ring_nf <;> reduce_mod_char!

omit [CharP E 2] in
/-- Two local charts with the displayed common plane of directions and
jointly surjective weights cannot be glued freely. Both distinct and common
point-kernel directions are allowed, through the parameter ε. -/
theorem not_free [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (z : Bool → V →ₗ[F] E) (a : Bool → V →ₗ[F] F) (u w : V) (ε : Bool)
    (hη : ∀ j, z j u ≠ 0) (hw₀ : z false w=0) (hw₁ : z true w=algebraMap F E (bit ε)*z true u)
    (hΔ₀ : a false w ≠ 0) (hΔ₁ : a true w+bit ε*a true u ≠ 0)
    (hsurj : ∀ v₀ v₁ : F, ∃ p : V, a false p=v₀ ∧ a true p=v₁) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph z a) := by
  let γ (j : Bool) : F := if j then bit ε else 0
  let Δ (j : Bool) : F := a j w+γ j*a j u
  have hΔ (j : Bool) : Δ j ≠ 0 := by cases j <;> simpa only [Δ,γ,Bool.false_eq_true,↓reduceIte,zero_mul,add_zero] using (by assumption)
  obtain ⟨x,hκ,hx₀,hx₁⟩ := parameter hq (a false u) (a true u) (Δ false) (Δ true) (hΔ _) (hΔ _)
  let β (j : Bool) : F := kappa x/Δ j
  let d (j : Bool) : F := 1+a j u*β j
  let A (j : Bool) : F := δ*(d j)^2/β j
  let b (j : Bool) : F := Algebra.norm F (z j u)*β j
  have hβ (j : Bool) : β j ≠ 0 := div_ne_zero hκ (hΔ j)
  have hd (j : Bool) : d j ≠ 0 := by
    have hn : Δ j+a j u*kappa x ≠ 0 := by cases j <;> assumption
    have he : d j=(Δ j+a j u*kappa x)/Δ j := by dsimp [d,β]; field_simp [hΔ j]
    rw [he]
    exact div_ne_zero hn (hΔ j)
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  have hb (j : Bool) : b j ≠ 0 := mul_ne_zero (Algebra.norm_ne_zero_iff.mpr (hη j)) (hβ j)
  obtain ⟨p,hp₀,hp₁⟩ := hsurj (A false) (A true)
  have hp (j : Bool) : a j p=A j := by cases j <;> assumption
  let col (j e : Bool) : E := z j u*(algebraMap F E (bit e*d j)+algebraMap F E (d j)*θ)-z j p
  have hpoint (i : Fin 4) (j e : Bool) : z j (rows p u w x i)+col j e=
      z j u*(algebraMap F E (offset x (γ j) i+bit e*d j)+algebraMap F E (d j)*θ) := by
    have hw : z j w=algebraMap F E (γ j)*z j u := by cases j <;> simp [γ,bit,hw₀,hw₁]
    rw [point_rows p u w x (γ j) (z j) (z j u) rfl hw]
    dsimp [col]
    simp only [map_add]
    ring
  have hedge (i : Fin 4) (j e : Bool) :
      Algebra.norm F (z j (rows p u w x i)+col j e)=a j (rows p u w x i)*b j := by
    rw [hpoint,weight_rows p u w x (γ j) (a j) (Δ j) rfl,hp]
    apply norm_identity δ θ hθ B hB (z j u) (β j) (d j) (A j) (a j u) (Δ j)
      (offset x (γ j) i) (step i) rfl
    · dsimp [A]; field_simp [hβ j]
    · rw [show β j*Δ j=kappa x by dsimp [β]; field_simp [hΔ j]]
      exact offset_square x (γ j) (by cases j <;> cases ε <;> simp [γ,bit]) i
  have hweight (i : Fin 4) : ∀ j, a j (rows p u w x i) ≠ 0 := by
    intro j
    have hn := norm_point_ne_zero θ B hB (z j u) (hη j) (d j) (offset x (γ j) i) (hd j) false
    rw [← hpoint i j false,hedge] at hn
    exact (mul_ne_zero_iff.mp hn).1
  have hcol (j : Bool) : Function.Injective (col j) := by
    intro e f he
    have hh : algebraMap F E (bit e*d j)=algebraMap F E (bit f*d j) := by
      dsimp [col] at he
      exact add_right_cancel (mul_left_cancel₀ (hη j) (sub_left_injective he))
    have hbits : bit (F := F) e=bit f := mul_right_cancel₀ (hd j) ((algebraMap F E).injective hh)
    cases e <;> cases f <;> simp_all [bit]
  let l : Fin 4 ↪ V := ⟨rows p u w x,rows_injective p u w x (z false) (a false) (hη false) hw₀ hΔ₀⟩
  let r₀ : Bool × Bool ↪ Bool × E × Fˣ := ⟨fun v => (v.1,col v.1 v.2,Units.mk0 (b v.1) (hb v.1)),by
    rintro ⟨j,e⟩ ⟨k,f⟩ he
    have hj : j=k := congrArg Prod.fst he
    subst k
    have hh : col j e=col j f := congrArg (fun v : Bool × E × Fˣ => v.2.1) he
    exact Prod.ext rfl (hcol j hh)⟩
  let eqv : Fin 4 ≃ Bool × Bool := (Fintype.equivFinOfCardEq (by simp : Fintype.card (Bool × Bool)=4)).symm
  let r : Fin 4 ↪ Bool × E × Fˣ := eqv.toEmbedding.trans r₀
  have he (i j : Fin 4) : (graph z a).Adj (.inl (l i)) (.inr (r j)) := by
    exact ⟨hedge i (eqv j).1 (eqv j).2,hweight i (eqv j).1⟩
  intro hf
  apply hf
  refine ⟨⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩⟩
  intro v w hvw
  cases v with
  | inl i => cases w with
    | inl j => simp at hvw
    | inr j => exact he i j
  | inr i => cases w with
    | inr j => simp at hvw
    | inl j => exact he j i

end Linear
#print axioms parameter
#print axioms norm_identity
#print axioms rows_injective
#print axioms not_free
end Erdos714TwoQuadraticCharts
