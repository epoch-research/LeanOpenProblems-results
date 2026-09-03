import Submission.TwoQuadraticCharts

/-!
Two arbitrary linear quadratic-norm charts in characteristic two cannot be
combined freely in the full-point/full-weight host. This is a construction
obstruction, not a theorem about arbitrary nonlinear relabelings or thinnings.
-/
noncomputable section
open Classical Polynomial SimpleGraph
set_option maxHeartbeats 5000000
namespace Erdos714LinearQuadraticCharts
open Erdos714TwoQuadraticCharts
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {V : Type*} [AddCommGroup V] [Module F V]

def pointMap (Φ : V ≃ₗ[F] E × F) : V →ₗ[F] E :=
  (LinearMap.fst F E F).comp Φ.toLinearMap

def weightMap (Φ : V ≃ₗ[F] E × F) : V →ₗ[F] F :=
  (LinearMap.snd F E F).comp Φ.toLinearMap

def kernelVector (Φ : V ≃ₗ[F] E × F) : V := Φ.symm (0,1)
def pointVector (Φ : V ≃ₗ[F] E × F) : V := Φ.symm (1,0)

@[simp] lemma point_kernel (Φ : V ≃ₗ[F] E × F) : pointMap Φ (kernelVector Φ)=0 := by
  simp [pointMap,kernelVector]
@[simp] lemma weight_kernel (Φ : V ≃ₗ[F] E × F) : weightMap Φ (kernelVector Φ)=1 := by
  simp [weightMap,kernelVector]
@[simp] lemma point_point (Φ : V ≃ₗ[F] E × F) : pointMap Φ (pointVector Φ)=1 := by
  simp [pointMap,pointVector]
@[simp] lemma weight_point (Φ : V ≃ₗ[F] E × F) : weightMap Φ (pointVector Φ)=0 := by
  simp [weightMap,pointVector]

lemma coordinates_ext (Φ : V ≃ₗ[F] E × F) {v w : V}
    (hz : pointMap Φ v=pointMap Φ w) (ha : weightMap Φ v=weightMap Φ w) : v=w :=
  Φ.injective (Prod.ext hz ha)

lemma kernel_line (Φ : V ≃ₗ[F] E × F) (v : V) (hv : pointMap Φ v=0) :
    v=weightMap Φ v • kernelVector Φ := by
  apply coordinates_ext Φ
  · simp [hv]
  · simp

/-- If two point maps have the same kernel direction, it has nonzero
weight in both charts, and every point direction for one is a point
direction for the other. -/
lemma common_kernel (Φ Ψ : V ≃ₗ[F] E × F)
    (h : pointMap Φ (kernelVector Ψ)=0) :
    pointMap Ψ (kernelVector Φ)=0 ∧ weightMap Ψ (kernelVector Φ) ≠ 0 ∧
      ∀ v, pointMap Φ v ≠ 0 → pointMap Ψ v ≠ 0 := by
  have he := kernel_line Φ (kernelVector Ψ) h
  have ha : weightMap Φ (kernelVector Ψ)*weightMap Ψ (kernelVector Φ)=1 := by
    have hh := congrArg (weightMap Ψ) he
    simpa only [weight_kernel,map_smul,smul_eq_mul] using hh.symm
  have hs : weightMap Φ (kernelVector Ψ) ≠ 0 := by intro hh; simp [hh] at ha
  have ht : weightMap Ψ (kernelVector Φ) ≠ 0 := by intro hh; simp [hh] at ha
  have hz : pointMap Ψ (kernelVector Φ)=0 := by
    have hh := congrArg (pointMap Ψ) he
    simp only [point_kernel,map_smul] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_left hs
  refine ⟨hz,ht,?_⟩
  intro v hv hv'
  apply hv
  rw [kernel_line Ψ v hv',map_smul,h,smul_zero]

/-- Two nonzero weight maps either jointly prescribe arbitrary weights,
or are nonzero scalar multiples. The proof gives the actual linear
interpolation vector in the independent case. -/
lemma weight_dichotomy (Φ Ψ : V ≃ₗ[F] E × F) :
    (∀ s t : F, ∃ p : V, weightMap Φ p=s ∧ weightMap Ψ p=t) ∨
      ∃ c : F, c ≠ 0 ∧ ∀ v, weightMap Ψ v=c*weightMap Φ v := by
  let c := weightMap Ψ (kernelVector Φ)
  by_cases hd : ∀ v, weightMap Ψ v=c*weightMap Φ v
  · right
    refine ⟨c,?_,hd⟩
    intro hc
    have hh := hd (kernelVector Ψ)
    simp [hc] at hh
  · push_neg at hd
    obtain ⟨v,hv⟩ := hd
    let d := weightMap Ψ v-c*weightMap Φ v
    have hd : d ≠ 0 := sub_ne_zero.mpr hv
    let u := v-weightMap Φ v • kernelVector Φ
    have hu₀ : weightMap Φ u=0 := by simp [u]
    have hu₁ : weightMap Ψ u=d := by simp [u,d,c,mul_comm]
    left
    intro s t
    refine ⟨s • kernelVector Φ + ((t-c*s)/d) • u, ?_, ?_⟩
    · simp [hu₀]
    · simp only [map_add,map_smul,smul_eq_mul,hu₁]
      change s*c+(t-c*s)/d*d=t
      field_simp
      ring

/-- A shared zero-slope direction lets the two required row weights be
chosen on one line, without joint surjectivity of the weight maps. -/
theorem zero_slope_not_free [CharP F 2] [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (z : Bool → V →ₗ[F] E) (a : Bool → V →ₗ[F] F) (u w : V) (ε : Bool)
    (hη : ∀ j, z j u ≠ 0) (hw₀ : z false w=0) (hw₁ : z true w=algebraMap F E (bit ε)*z true u)
    (hΔ₀ : a false w ≠ 0) (hΔ₁ : a true w+bit ε*a true u ≠ 0)
    (hzero : ∀ j, a j u=0) :
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
  let p : V := (δ/kappa x) • w
  have hp (j : Bool) : a j p=A j := by
    simp only [p,map_smul,smul_eq_mul]
    dsimp [A,d,β,Δ]
    rw [hzero j]
    simp only [zero_mul,add_zero,mul_zero,one_pow,mul_one]
    field_simp
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


/-- Arbitrary linear coordinate isomorphisms are excluded: no compatibility
condition on their kernels or weight maps is left as a hypothesis. -/
theorem all_linear_charts_not_free [CharP F 2] [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ))
    (Φ : Bool → V ≃ₗ[F] E × F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun j => pointMap (Φ j)) (fun j => weightMap (Φ j))) := by
  let z := fun j => pointMap (Φ j)
  let a := fun j => weightMap (Φ j)
  let k := fun j => kernelVector (Φ j)
  have hkz (j : Bool) : z j (k j)=0 := point_kernel _
  have hka (j : Bool) : a j (k j)=1 := weight_kernel _
  rcases weight_dichotomy (Φ false) (Φ true) with hsurj | ⟨c,hc,hdep⟩
  · by_cases hker : z false (k true)=0
    · obtain ⟨hz,ha,hu⟩ := common_kernel (Φ false) (Φ true) hker
      let u := pointVector (Φ false)
      apply Erdos714TwoQuadraticCharts.not_free hq δ θ hθ B hB z a u (k false) false
      · intro j
        cases j
        · exact (show z false u=1 from point_point _).trans_ne one_ne_zero
        · exact hu u ((show z false u=1 from point_point _).trans_ne one_ne_zero)
      · exact hkz _
      · simpa only [bit,Bool.false_eq_true,↓reduceIte,map_zero,zero_mul] using hz
      · rw [hka]; exact one_ne_zero
      · simpa only [bit,Bool.false_eq_true,↓reduceIte,zero_mul,add_zero] using ha
      · exact hsurj
    · have hz : z true (k false) ≠ 0 := by
        intro h
        exact hker (common_kernel (Φ true) (Φ false) h).1
      let u := k false+k true
      apply Erdos714TwoQuadraticCharts.not_free hq δ θ hθ B hB z a u (k false) true
      · intro j
        cases j
        · simpa only [u,map_add,hkz,zero_add] using hker
        · simpa only [u,map_add,hkz,add_zero] using hz
      · exact hkz _
      · simp only [bit,↓reduceIte,map_one,one_mul,u,map_add,hkz,add_zero]
      · rw [hka]; exact one_ne_zero
      · simp only [bit,↓reduceIte,one_mul,u,map_add,hka,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
        exact one_ne_zero
      · exact hsurj
  · have hd (v : V) : a true v=c*a false v := hdep v
    by_cases hker : z false (k true)=0
    · obtain ⟨hz,ha,hu⟩ := common_kernel (Φ false) (Φ true) hker
      let u := pointVector (Φ false)
      apply zero_slope_not_free hq δ θ hθ B hB z a u (k false) false
      · intro j
        cases j
        · exact (show z false u=1 from point_point _).trans_ne one_ne_zero
        · exact hu u ((show z false u=1 from point_point _).trans_ne one_ne_zero)
      · exact hkz _
      · simpa only [bit,Bool.false_eq_true,↓reduceIte,map_zero,zero_mul] using hz
      · rw [hka]; exact one_ne_zero
      · simpa only [bit,Bool.false_eq_true,↓reduceIte,zero_mul,add_zero] using ha
      · intro j
        cases j
        · exact weight_point _
        · rw [hd,show a false u=0 from weight_point _,mul_zero]
    · have hz : z true (k false) ≠ 0 := by
        intro h
        exact hker (common_kernel (Φ true) (Φ false) h).1
      let u := k false+c • k true
      have hu₀ : a false u=0 := by
        have hh := hd (k true)
        rw [hka] at hh
        simp only [u,map_add,map_smul,smul_eq_mul,hka,←hh,CharTwo.add_self_eq_zero]
      have hu₁ : a true u=0 := by rw [hd,hu₀,mul_zero]
      apply zero_slope_not_free hq δ θ hθ B hB z a u (k false) true
      · intro j
        cases j
        · simpa only [u,map_add,map_smul,hkz,zero_add] using (smul_ne_zero hc hker)
        · simpa only [u,map_add,map_smul,hkz,smul_zero,add_zero] using hz
      · exact hkz _
      · simp only [bit,↓reduceIte,map_one,one_mul,u,map_add,map_smul,hkz,smul_zero,add_zero]
      · rw [hka]; exact one_ne_zero
      · simp only [bit,↓reduceIte,one_mul,hu₁,add_zero,hd,hka,mul_one]
        exact hc
      · intro j
        cases j
        · exact hu₀
        · exact hu₁

variable {I J : Type*}

/-- Both coordinate changes may depend on both endpoint tags. Zero
transformed weights are excluded explicitly in each local block. -/
def gluingGraph (L R : I → J → V ≃ₗ[F] E × F) :
    SimpleGraph ((I × V) ⊕ (J × V)) where
  Adj x y := match x,y with
    | .inl x,.inr y =>
      Algebra.norm F (pointMap (L x.1 y.1) x.2+pointMap (R x.1 y.1) y.2)=
        weightMap (L x.1 y.1) x.2*weightMap (R x.1 y.1) y.2 ∧
      weightMap (L x.1 y.1) x.2 ≠ 0 ∧ weightMap (R x.1 y.1) y.2 ≠ 0
    | .inr y,.inl x =>
      Algebra.norm F (pointMap (L x.1 y.1) x.2+pointMap (R x.1 y.1) y.2)=
        weightMap (L x.1 y.1) x.2*weightMap (R x.1 y.1) y.2 ∧
      weightMap (L x.1 y.1) x.2 ≠ 0 ∧ weightMap (R x.1 y.1) y.2 ≠ 0
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

/-- Recover the two full column charts using the actual inverse linear
isomorphisms. The copy verifies all transformed nonzero-weight guards. -/
def chartCopy (L R : I → J → V ≃ₗ[F] E × F) (i : I) (j : Bool ↪ J) :
    (graph (fun b => pointMap (L i (j b))) (fun b => weightMap (L i (j b)))).Copy
      (gluingGraph L R) := by
  let l : V ↪ I × V := ⟨fun v => (i,v),fun _ _ he => congrArg Prod.snd he⟩
  let r : Bool × E × Fˣ ↪ J × V := ⟨fun v =>
    (j v.1,(R i (j v.1)).symm (v.2.1,(v.2.2 : F))), by
    rintro ⟨b,y,t⟩ ⟨b',y',t'⟩ he
    have hb : b=b' := j.injective (congrArg Prod.fst he)
    subst b'
    have hv := congrArg Prod.snd he
    have hp := (R i (j b)).symm.injective hv
    have hy : y=y' := congrArg Prod.fst hp
    have ht : t=t' := Units.ext (congrArg Prod.snd hp)
    exact Prod.ext rfl (Prod.ext hy ht)⟩
  have hz (b : Bool) (y : E) (t : F) :
      pointMap (R i (j b)) ((R i (j b)).symm (y,t))=y := by simp [pointMap]
  have ha (b : Bool) (y : E) (t : F) :
      weightMap (R i (j b)) ((R i (j b)).symm (y,t))=t := by simp [weightMap]
  have hed (v : V) (w : Bool × E × Fˣ)
      (h : (graph (fun b => pointMap (L i (j b)))
        (fun b => weightMap (L i (j b)))).Adj (.inl v) (.inr w)) :
      (gluingGraph L R).Adj (.inl (l v)) (.inr (r w)) := by
    change Algebra.norm F (pointMap (L i (j w.1)) v+
      pointMap (R i (j w.1)) ((R i (j w.1)).symm (w.2.1,(w.2.2 : F))))=
      weightMap (L i (j w.1)) v*
      weightMap (R i (j w.1)) ((R i (j w.1)).symm (w.2.1,(w.2.2 : F))) ∧
      weightMap (L i (j w.1)) v ≠ 0 ∧
      weightMap (R i (j w.1)) ((R i (j w.1)).symm (w.2.1,(w.2.2 : F))) ≠ 0
    rw [hz,ha]
    exact ⟨h.1,h.2,Units.ne_zero _⟩
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro x y hxy
  cases x with
  | inl v => cases y with
    | inl v' => exact False.elim hxy
    | inr w => exact hed v w hxy
  | inr w => cases y with
    | inr w' => exact False.elim hxy
    | inl v => exact hed v w hxy

/-- A full endpoint-dependent linear gluing already has a K44 as soon as
there is one row tag and two distinct column tags. No shared coordinate
change or shared point-kernel direction is assumed. -/
theorem gluing_not_free [CharP F 2] [Fintype F] (hq : 6 < Fintype.card F)
    (δ : F) (θ : E) (hθ : θ^2=θ+algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ k, B k=θ^(k : ℕ))
    (L R : I → J → V ≃ₗ[F] E × F) (i : I) (j : Bool ↪ J) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (gluingGraph L R) := by
  have hn := all_linear_charts_not_free hq δ θ hθ B hB (fun b => L i (j b))
  intro hf
  apply hn
  rintro ⟨c⟩
  exact hf ⟨(chartCopy L R i j).comp c⟩

#print axioms chartCopy
#print axioms gluing_not_free
#print axioms kernel_line
#print axioms common_kernel
#print axioms weight_dichotomy
#print axioms all_linear_charts_not_free
#print axioms zero_slope_not_free
end Erdos714LinearQuadraticCharts
