import Submission.TwoQuadraticCharts

/-!
A uniform application of the two-chart obstruction to evaluation maps whose
quadratic-extension basis coefficient varies with the column tag. All
polynomial coefficients are allowed; no exact-degree or coefficient guard
is silently imposed. This does not settle Erdős 714.
-/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714VaryingQuadraticEvaluation
open Erdos714QuadraticEvaluation (Coeff)
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharP F 2] [CharP E 2]

def point (ζ : E) : Coeff F →ₗ[F] E where
  toFun p := algebraMap F E p.1*ζ^2+algebraMap F E p.2.1*ζ+algebraMap F E p.2.2
  map_add' := by intro p q; simp [map_add]; ring
  map_smul' := by intro c p; simp [Algebra.smul_def]; ring

def weight (t : F) : Coeff F →ₗ[F] F where
  toFun p := p.1*t^2+p.2.1*t+p.2.2
  map_add' := by intro p q; simp; ring
  map_smul' := by intro c p; simp; ring

def place (θ : E) (α β : F) : E := algebraMap F E α+algebraMap F E β*θ

def quadratic (δ α β : F) : Coeff F := (1,β,α^2+α*β+δ*β^2)

omit [CharP F 2] in
lemma root (δ α β : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ) :
    point (place θ α β) (quadratic δ α β)=0 := by
  simp only [point,place,quadratic,LinearMap.coe_mk,AddHom.coe_mk,map_one,map_add,map_mul,map_pow,one_mul]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) (algebraMap F E β)^2*hθ

omit [CharP F 2] in
lemma sum_points (δ α₀ β₀ α₁ β₁ α β : F) (θ : E) :
    point (place θ α β) (quadratic δ α₀ β₀+quadratic δ α₁ β₁)=
      algebraMap F E ((β₀+β₁)*α+(α₀^2+α₀*β₀+δ*β₀^2)+(α₁^2+α₁*β₁+δ*β₁^2))+
      algebraMap F E ((β₀+β₁)*β)*θ := by
  simp [point,place,quadratic,map_add,map_mul,map_pow]
  ring_nf
  reduce_mod_char!

omit [CharP E 2] in
lemma weight_norm (δ α β t : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) :
    weight t (quadratic δ α β)=Algebra.norm F (place θ (t+α) β) := by
  rw [place,Erdos714QuadraticEvaluationBinary.norm_pair δ θ hθ B hB]
  simp only [weight,quadratic,LinearMap.coe_mk,AddHom.coe_mk]
  ring_nf
  reduce_mod_char!

omit [CharP E 2] in
lemma weight_quad_ne_zero (δ α β t : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) (hβ : β ≠ 0) :
    weight t (quadratic δ α β) ≠ 0 := by
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  rw [weight_norm δ α β t θ hθ B hB]
  apply Algebra.norm_ne_zero_iff.mpr
  exact Erdos714QuadraticEvaluationBinary.pair_ne_zero θ B hB _ _ hβ

omit [CharP F 2] [CharP E 2] in
lemma weight_surjective (t₀ t₁ : F) (ht : t₀ ≠ t₁) (v₀ v₁ : F) :
    ∃ p : Coeff F, weight t₀ p=v₀ ∧ weight t₁ p=v₁ := by
  let c := (v₁-v₀)/(t₁-t₀)
  refine ⟨(0,c,v₀-c*t₀),?_,?_⟩
  · simp [weight]
  · have hn : t₁-t₀ ≠ 0 := sub_ne_zero.mpr ht.symm
    simp only [weight,LinearMap.coe_mk,AddHom.coe_mk,zero_mul,zero_add]
    dsimp [c]
    field_simp
    ring

/-- Distinct quadratic minimal polynomials give the distinct-kernel
case of the two-chart obstruction. -/
theorem not_free [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (t α β : Bool → F) (ht : t false ≠ t true)
    (hβ : ∀ j, β j ≠ 0)
    (hK : quadratic δ (α false) (β false) ≠ quadratic δ (α true) (β true)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714TwoQuadraticCharts.graph (fun j => point (place θ (α j) (β j))) (fun j => weight (t j))) := by
  let k (j : Bool) : Coeff F := quadratic δ (α j) (β j)
  let u : Coeff F := k false+k true
  let w : Coeff F := k false
  have hu (j : Bool) : point (place θ (α j) (β j)) u ≠ 0 := by
    rw [show u=quadratic δ (α false) (β false)+quadratic δ (α true) (β true) from rfl,sum_points]
    by_cases hb : β false+β true=0
    · have hbeq : β false=β true := by
        linear_combination (norm := (ring_nf; reduce_mod_char!)) hb
      have hn : (α false^2+α false*β false+δ*β false^2)+
          (α true^2+α true*β true+δ*β true^2) ≠ 0 := by
        intro he
        apply hK
        refine Prod.ext rfl (Prod.ext hbeq ?_)
        dsimp [quadratic]
        linear_combination (norm := (ring_nf; reduce_mod_char!)) he
      simp only [hb,zero_mul,zero_add,map_zero,add_zero]
      exact fun he => hn ((algebraMap F E).injective (he.trans (map_zero _).symm))
    · exact Erdos714QuadraticEvaluationBinary.pair_ne_zero θ B hB _ _ (mul_ne_zero hb (hβ j))
  apply Erdos714TwoQuadraticCharts.not_free hq δ θ hθ B hB
    (fun j => point (place θ (α j) (β j))) (fun j => weight (t j)) u w true hu
  · exact root δ (α false) (β false) θ hθ
  · simp only [Erdos714TwoQuadraticCharts.bit,↓reduceIte,map_one,one_mul]
    change point (place θ (α true) (β true)) (k false)=
      point (place θ (α true) (β true)) (k false+k true)
    rw [map_add,show point (place θ (α true) (β true)) (k true)=0 from root δ _ _ θ hθ,add_zero]
  · exact weight_quad_ne_zero δ (α false) (β false) (t false) θ hθ B hB (hβ false)
  · simp only [Erdos714TwoQuadraticCharts.bit,↓reduceIte,one_mul]
    change weight (t true) (k false)+weight (t true) (k false+k true) ≠ 0
    rw [map_add,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
    exact weight_quad_ne_zero δ (α true) (β true) (t true) θ hθ B hB (hβ true)
  · exact weight_surjective (t false) (t true) ht


/-- No distinctness assumption on the two extension points is required.
If their minimal polynomials agree, a constant polynomial and their common
minimal polynomial give the common-kernel case instead. -/
theorem all_charts_not_free [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (t α β : Bool → F) (ht : t false ≠ t true) (hβ : ∀ j, β j ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714TwoQuadraticCharts.graph (fun j => point (place θ (α j) (β j))) (fun j => weight (t j))) := by
  by_cases hK : quadratic δ (α false) (β false)=quadratic δ (α true) (β true)
  · let u : Coeff F := (0,0,1)
    let w : Coeff F := quadratic δ (α false) (β false)
    apply Erdos714TwoQuadraticCharts.not_free hq δ θ hθ B hB
      (fun j => point (place θ (α j) (β j))) (fun j => weight (t j)) u w false
    · intro j; simp [point,u]
    · exact root δ _ _ θ hθ
    · simp only [Erdos714TwoQuadraticCharts.bit,Bool.false_eq_true,↓reduceIte,map_zero,zero_mul]
      change point (place θ (α true) (β true)) (quadratic δ (α false) (β false))=0
      rw [hK]
      exact root δ _ _ θ hθ
    · exact weight_quad_ne_zero δ _ _ _ θ hθ B hB (hβ false)
    · simp only [Erdos714TwoQuadraticCharts.bit,Bool.false_eq_true,↓reduceIte,zero_mul,add_zero]
      change weight (t true) (quadratic δ (α false) (β false)) ≠ 0
      rw [hK]
      exact weight_quad_ne_zero δ _ _ _ θ hθ B hB (hβ true)
    · exact weight_surjective (t false) (t true) ht
  · exact not_free hq δ θ hθ B hB t α β ht hβ hK

/-- A quadratic polynomial can prescribe independently its value at a base
point and its value at a genuinely quadratic extension point. -/
lemma evaluation_surjective (δ α β t : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) (hβ : β ≠ 0)
    (y : E) (v : F) :
    ∃ p : Coeff F, point (place θ α β) p=y ∧ weight t p=v := by
  let c : F := B.repr y 1/β
  let l : Coeff F := (0,c,B.repr y 0-c*α)
  have hl : point (place θ α β) l=y := by
    have hy := B.sum_repr y
    simp only [Fin.sum_univ_two,hB,Algebra.smul_def] at hy
    rw [←hy]
    dsimp [point,place,l,c]
    simp only [map_zero,zero_mul,zero_add,map_sub,map_div₀,map_mul]
    field_simp [hβ]
    ring
  let K := quadratic δ α β
  have hK : point (place θ α β) K=0 := root δ α β θ hθ
  have hKt : weight t K ≠ 0 := weight_quad_ne_zero δ α β t θ hθ B hB hβ
  refine ⟨l+((v-weight t l)/weight t K) • K,?_,?_⟩
  · rw [map_add,map_smul,hK,smul_zero,add_zero,hl]
  · rw [map_add,map_smul,smul_eq_mul]
    field_simp
    ring

abbrev Vertex (F : Type*) := F × Coeff F

/-- Both tags and both edge weights are nonzero. Polynomial coefficients
are unrestricted; in particular the definition does not require exact degree two. -/
def gluingGraph (θ : E) (α β : F → F) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj v w := match v,w with
    | .inl v,.inr w => v.1 ≠ 0 ∧ w.1 ≠ 0 ∧ weight w.1 v.2 ≠ 0 ∧ weight v.1 w.2 ≠ 0 ∧
        Algebra.norm F (point (place θ (α w.1) (β w.1)) v.2+point (place θ (α v.1) (β v.1)) w.2)=
          weight w.1 v.2*weight v.1 w.2
    | .inr w,.inl v => v.1 ≠ 0 ∧ w.1 ≠ 0 ∧ weight w.1 v.2 ≠ 0 ∧ weight v.1 w.2 ≠ 0 ∧
        Algebra.norm F (point (place θ (α w.1) (β w.1)) v.2+point (place θ (α v.1) (β v.1)) w.2)=
          weight w.1 v.2*weight v.1 w.2
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

/-- Transfer to the actual two-sided evaluation host, not merely a coordinate
surrogate. Recovery checks both evaluations and injectivity of all columns. -/
theorem gluing_not_free [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (α β : F → F) (s : F) (hs : s ≠ 0) (hβs : β s ≠ 0)
    (t : Bool → F) (ht : t false ≠ t true) (ht0 : ∀ j, t j ≠ 0)
    (hβ : ∀ j, β (t j) ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (gluingGraph θ α β) := by
  let z (j : Bool) : Coeff F →ₗ[F] E := point (place θ (α (t j)) (β (t j)))
  let a (j : Bool) : Coeff F →ₗ[F] F := weight (t j)
  have hnf := all_charts_not_free hq δ θ hθ B hB t (α ∘ t) (β ∘ t) ht hβ
  choose g hg hw using evaluation_surjective δ (α s) (β s) s θ hθ B hB hβs
  have hti : Function.Injective t := by
    intro i j he
    cases i <;> cases j <;> simp_all
  let l : Coeff F ↪ Vertex F := ⟨fun p => (s,p),fun _ _ he => congrArg Prod.snd he⟩
  let r : Bool × E × Fˣ ↪ Vertex F := ⟨fun q => (t q.1,g q.2.1 q.2.2),by
    rintro ⟨j,y,b⟩ ⟨k,y',b'⟩ he
    have hj := hti (congrArg Prod.fst he)
    change j=k at hj
    subst k
    have hp : g y (b : F)=g y' (b' : F) := congrArg Prod.snd he
    have hy : y=y' := by rw [← hg y (b : F),hp,hg]
    have hb : b=b' := Units.ext (by rw [← hw y (b : F),hp,hw])
    exact Prod.ext rfl (Prod.ext hy hb)⟩
  have he (p : Coeff F) (q : Bool × E × Fˣ)
      (h : (Erdos714TwoQuadraticCharts.graph z a).Adj (.inl p) (.inr q)) :
      (gluingGraph θ α β).Adj (.inl (l p)) (.inr (r q)) := by
    refine ⟨hs,ht0 q.1,h.2,?_,?_⟩
    · change weight s (g q.2.1 (q.2.2 : F)) ≠ 0
      rw [hw]
      exact Units.ne_zero _
    · change Algebra.norm F (z q.1 p+point (place θ (α s) (β s)) (g q.2.1 (q.2.2 : F)))=
        a q.1 p*weight s (g q.2.1 (q.2.2 : F))
      rw [hg,hw]
      exact h.1
  have cp : (Erdos714TwoQuadraticCharts.graph z a).Copy (gluingGraph θ α β) := by
    refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
    intro v w hvw
    cases v with
    | inl p => cases w with
      | inl p' => exact False.elim hvw
      | inr q => exact he p q hvw
    | inr q => cases w with
      | inr q' => exact False.elim hvw
      | inl p => exact he p q hvw
  intro hf
  apply hnf
  rintro ⟨c⟩
  exact hf ⟨cp.comp c⟩

/-- In particular, scaling the extension evaluation point with its tag
(t maps to t*theta) cannot repair the full gluing construction. All tags in
the graph's edges are already required to be nonzero. -/
theorem scaled_not_free [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (gluingGraph (F := F) θ (fun _ => 0) id) := by
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset F).card < Finset.univ.card from
      lt_of_le_of_lt Finset.card_le_two (by simpa using (show 2 < Fintype.card F by omega)))
  have hc0 : c ≠ 0 := by intro h; apply hc; simp [h]
  have hc1 : c ≠ 1 := by intro h; apply hc; simp [h]
  let t : Bool → F := fun j => if j then c else 1
  apply gluing_not_free hq δ θ hθ B hB (fun _ => 0) id 1 one_ne_zero one_ne_zero t
  · exact hc1.symm
  · intro j; cases j <;> simp [t,hc0]
  · intro j; cases j <;> simp [t,hc0]

#print axioms root
#print axioms sum_points
#print axioms weight_norm
#print axioms weight_surjective
#print axioms evaluation_surjective
#print axioms not_free
#print axioms all_charts_not_free
#print axioms gluing_not_free
#print axioms scaled_not_free
end Erdos714VaryingQuadraticEvaluation
