import Submission.BinaryConicPoints

/-!
Quadratic evaluation mixes the local norm point with its scalar weight. This
file proves a repeated-tag obstruction, including nonzero leading coefficients
and nonzero edge weights. It does not resolve Erdős714 and does not bound
arbitrary edge thinnings or arbitrary permutations of local vertices.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714QuadraticEvaluation
variable {F : Type*} [Field F]

/-- A vertical slice of a nonsingular diagonal conic has at most two points. -/
lemma vertical_card [Fintype F] (a b u : F) (hb : b ≠ 0) :
    (univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1 ∧ p.1=u)).card ≤ 2 := by
  let S := univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1 ∧ p.1=u)
  by_cases he : S.Nonempty
  · obtain ⟨p,hp⟩ := he
    have hp' := (mem_filter.mp hp).2
    have hs : S ⊆ {(u,p.2),(u,-p.2)} := by
      intro z hz
      have hz' := (mem_filter.mp hz).2
      have hsq : z.2^2=p.2^2 := by
        apply mul_left_cancel₀ hb
        have hz0 : a*u^2+b*z.2^2=1 := by simpa only [hz'.2] using hz'.1
        have hp0 : a*u^2+b*p.2^2=1 := by simpa only [hp'.2] using hp'.1
        linear_combination hz0-hp0
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · have he : z=(u,p.2) := Prod.ext hz'.2 h
        simp [he]
      · have he : z=(u,-p.2) := Prod.ext hz'.2 h
        simp [he]
    exact (card_le_card hs).trans (card_le_two)
  · simp [S,not_nonempty_iff_eq_empty.mp he]

/-- Swapping coordinates gives the same horizontal-slice bound. -/
lemma horizontal_card [Fintype F] (a b v : F) (ha : a ≠ 0) :
    (univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1 ∧ p.2=v)).card ≤ 2 := by
  have h := vertical_card b a v ha
  have he : (univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1 ∧ p.2=v)).card =
      (univ.filter (fun p : F × F => b*p.1^2+a*p.2^2=1 ∧ p.1=v)).card := by
    apply card_nbij Prod.swap
    · intro p hp
      simpa [add_comm] using hp
    · exact fun _ _ _ _ h => Prod.swap_injective h
    · intro p hp
      exact ⟨p.swap,by simpa [add_comm] using hp,rfl⟩
  exact he.trans_le h

/-- The four exclusions needed for the signed rectangle remove at most eight
points from a conic that has at least q-2 points. -/
theorem parameters [Fintype F] (h2 : (2 : F) ≠ 0) (δ : F)
    (hδ : δ ≠ 0) (hδ4 : δ ≠ 4) (hq : 10 < Fintype.card F) :
    ∃ u c : F, u ≠ 0 ∧ c ≠ 0 ∧ u ≠ δ ∧ u ≠ -δ ∧
      16*u^2+(4-δ)*c^2=64*δ := by
  have h4 : (4 : F) ≠ 0 := by convert mul_ne_zero h2 h2 using 1; ring
  have h16 : (16 : F) ≠ 0 := by convert mul_ne_zero h4 h4 using 1; ring
  have h64 : (64 : F) ≠ 0 := by convert mul_ne_zero h16 h4 using 1; ring
  let a : F := 1/(4*δ)
  let b : F := (4-δ)/(64*δ)
  have ha : a ≠ 0 := div_ne_zero one_ne_zero (mul_ne_zero h4 hδ)
  have hb : b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hδ4.symm) (mul_ne_zero h64 hδ)
  let C := univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1)
  let V (u : F) := univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1 ∧ p.1=u)
  let W := univ.filter (fun p : F × F => a*p.1^2+b*p.2^2=1 ∧ p.2=0)
  let B := V 0 ∪ V δ ∪ V (-δ) ∪ W
  have hc : Fintype.card F ≤ C.card+2 := by
    have h := Erdos714BinaryConic.quadratic_level_card h2 a 0 b ha (by
      simp only [zero_pow (by decide : 2 ≠ 0),zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h4 ha) hb))
    simpa [C,Fintype.card_subtype] using h
  have hB : B.card ≤ 8 := by
    have h0 := vertical_card a b 0 hb
    have h1 := vertical_card a b δ hb
    have h2' := vertical_card a b (-δ) hb
    have h3 := horizontal_card a b 0 ha
    have hu1 := card_union_le (V 0) (V δ)
    have hu2 := card_union_le (V 0 ∪ V δ) (V (-δ))
    have hu3 := card_union_le (V 0 ∪ V δ ∪ V (-δ)) W
    dsimp [B,V,W] at *
    omega
  obtain ⟨p,hp,hbad⟩ := exists_mem_notMem_of_card_lt_card (show B.card < C.card by omega)
  have hp' := (mem_filter.mp hp).2
  have hex : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ δ ∧ p.1 ≠ -δ := by
    have h : p.1 ≠ 0 ∧ p.1 ≠ δ ∧ p.1 ≠ -δ ∧ p.2 ≠ 0 := by
      simpa [B,V,W,hp'] using hbad
    tauto
  refine ⟨p.1,p.2,hex.1,hex.2.1,hex.2.2.1,hex.2.2.2,?_⟩
  dsimp [a,b] at hp'
  field_simp at hp'
  apply mul_left_cancel₀ h4
  linear_combination hp'

abbrev Coeff (F : Type*) := F × F × F
abbrev Vertex (F : Type*) := F × Coeff F

def eval (p : Coeff F) (t : F) : F := p.1*t^2+p.2.1*t+p.2.2

def realPart (δ : F) (p : Coeff F) (t : F) : F := p.1*(t^2+δ)+p.2.1*t+p.2.2

def imagPart (p : Coeff F) (t : F) : F := 2*p.1*t+p.2.1

/-- Exact-degree-two vertices, and the two evaluated weights are nonzero. -/
def relation (δ : F) (x y : Vertex F) : Prop :=
  x.2.1 ≠ 0 ∧ y.2.1 ≠ 0 ∧ eval x.2 y.1 ≠ 0 ∧ eval y.2 x.1 ≠ 0 ∧
    (realPart δ x.2 y.1+realPart δ y.2 x.1)^2-
      δ*(imagPart x.2 y.1+imagPart y.2 x.1)^2=eval x.2 y.1*eval y.2 x.1

def graph (δ : F) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := match x,y with
    | .inl x,.inr y | .inr y,.inl x => relation δ x y
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

def sign (i : Bool) : F := if i then 1 else -1
lemma sign_sq (i : Bool) : (sign i : F)^2=1 := by cases i <;> simp [sign]
lemma sign_ne_zero (i : Bool) : (sign i : F) ≠ 0 := by cases i <;> simp [sign]
lemma sign_injective (h2 : (2 : F) ≠ 0) : Function.Injective (sign (F := F)) := by
  intro i j h
  cases i <;> cases j <;> try rfl
  all_goals exfalso; apply h2; dsimp [sign] at h
  · linear_combination -h
  · linear_combination h

def row (δ u : F) (i : Bool × Bool) : Vertex F :=
  (0,sign i.2,0,sign i.1*u-sign i.2*(δ+1))
def column (δ c : F) (j : Bool × Bool) : Vertex F :=
  (sign j.1,-(sign j.2*c)/(2*δ),(sign j.2*c)/(4*sign j.1),sign j.2*c)

lemma row_injective (h2 : (2 : F) ≠ 0) (δ u : F) (hu : u ≠ 0) :
    Function.Injective (row δ u) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  have h1 : sign j=sign l := congrArg (fun x : Vertex F => x.2.1) h
  have hj : j=l := sign_injective h2 h1
  subst l
  have h2' : sign i*u-sign j*(δ+1)=sign k*u-sign j*(δ+1) :=
    congrArg (fun x : Vertex F => x.2.2.2) h
  have hi := sign_injective h2 (mul_right_cancel₀ hu (sub_left_injective h2'))
  subst k
  rfl

lemma column_injective (h2 : (2 : F) ≠ 0) (δ c : F) (hc : c ≠ 0) :
    Function.Injective (column δ c) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  have h1 : sign i=sign k := congrArg Prod.fst h
  have h2' : sign j*c=sign l*c := congrArg (fun x : Vertex F => x.2.2.2) h
  have hi := sign_injective h2 h1
  have hj := sign_injective h2 (mul_right_cancel₀ hc h2')
  subst k; subst l
  rfl

lemma signed_edge (h2 : (2 : F) ≠ 0) (δ u c : F) (hδ : δ ≠ 0) (hc : c ≠ 0)
    (huD : u ≠ δ) (humD : u ≠ -δ)
    (hconic : 16*u^2+(4-δ)*c^2=64*δ) (i j : Bool × Bool) :
    relation δ (row δ u i) (column δ c j) := by
  have h4 : (4 : F) ≠ 0 := by convert mul_ne_zero h2 h2 using 1; ring
  have ht := sign_ne_zero (F := F) j.1
  have he := sign_ne_zero (F := F) j.2
  have hc' : sign j.2*c ≠ 0 := mul_ne_zero he hc
  have hweight : eval (row δ u i).2 (column δ c j).1=sign i.1*u-sign i.2*δ := by
    dsimp [row,column,eval]
    rw [sign_sq]
    ring
  have hw0 : sign i.1*u-sign i.2*δ ≠ 0 := by
    rcases i with ⟨i,k⟩
    cases i <;> cases k <;> dsimp [sign]
    all_goals intro h
    · exact huD (by linear_combination -h)
    · exact humD (by linear_combination -h)
    · exact humD (by linear_combination h)
    · exact huD (by linear_combination h)
  refine ⟨sign_ne_zero _,div_ne_zero (neg_ne_zero.mpr hc') (mul_ne_zero h2 hδ),
    by rwa [hweight],by simpa [row,column,eval] using hc',?_⟩
  dsimp [row,column,realPart,imagPart,eval]
  rw [sign_sq]
  have hs1 := sign_sq (F := F) i.1
  have hs2 := sign_sq (F := F) i.2
  have ht2 := sign_sq (F := F) j.1
  have he2 := sign_sq (F := F) j.2
  field_simp
  linear_combination
    4*δ^2*(sign j.1)^2*hconic +
    64*δ^2*u^2*(sign j.1)^2*hs1 -
    256*δ^3*(sign j.1)^4*hs2 +
    4*δ^2*c^2*(4*(sign j.1)^2-δ)*he2 +
    4*δ^3*(c^2-64*(sign j.1)^2)*ht2

/-- Four rows have the same tag, and the columns use the two tags ±1. -/
def parameterCopy (h2 : (2 : F) ≠ 0) (δ u c : F) (hδ : δ ≠ 0)
    (hu : u ≠ 0) (hc : c ≠ 0) (huD : u ≠ δ) (humD : u ≠ -δ)
    (hconic : 16*u^2+(4-δ)*c^2=64*δ) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph δ) := by
  let e : Fin 4 ≃ Bool × Bool :=
    (finCongr (by simp : 4=Fintype.card (Bool × Bool))).trans (Fintype.equivFin _).symm
  let L := e.toEmbedding.trans ⟨row δ u,row_injective h2 δ u hu⟩
  let R := e.toEmbedding.trans ⟨column δ c,column_injective h2 δ c hc⟩
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact signed_edge h2 δ u c hδ hc huD humD hconic _ _
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact signed_edge h2 δ u c hδ hc huD humD hconic _ _

theorem not_free [Fintype F] (h2 : (2 : F) ≠ 0) (δ : F)
    (hδ : δ ≠ 0) (hδ4 : δ ≠ 4) (hq : 10 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph δ) := by
  obtain ⟨u,c,hu,hc,huD,humD,hconic⟩ := parameters h2 δ hδ hδ4 hq
  exact fun hf => hf ⟨parameterCopy h2 δ u c hδ hu hc huD humD hconic⟩


section ActualNorm
variable {E : Type*} [Field E] [Algebra F E]

/-- The actual multiplication matrix in the basis 1,θ. -/
lemma norm_pair (δ : F) (θ : E) (hθ : θ^2=algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) (a b : F) :
    Algebra.norm F (algebraMap F E a+algebraMap F E b*θ)=a^2-δ*b^2 := by
  let M : Matrix (Fin 2) (Fin 2) F := !![a,δ*b;b,a]
  have hcol (j : Fin 2) :
      ∑ i, M i j • B i=(algebraMap F E a+algebraMap F E b*θ)*B j := by
    simp only [Fin.sum_univ_two,hB,Algebra.smul_def]
    fin_cases j
    · simp [M]
    · dsimp [M]
      simp only [pow_zero,pow_one,map_mul,mul_one]
      linear_combination -(algebraMap F E b)*hθ
  have hm : Algebra.leftMulMatrix B (algebraMap F E a+algebraMap F E b*θ)=M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul,← hcol j]
    fin_cases i <;> simp
  rw [Algebra.norm_eq_matrix_det B,hm,Matrix.det_fin_two]
  dsimp [M]
  ring

/-- Original evaluation at t+θ, before coordinates or norm expansion. -/
def extensionEval (θ : E) (p : Coeff F) (t : F) : E :=
  algebraMap F E p.1*(algebraMap F E t+θ)^2+
    algebraMap F E p.2.1*(algebraMap F E t+θ)+algebraMap F E p.2.2

lemma extensionEval_eq (δ : F) (θ : E) (hθ : θ^2=algebraMap F E δ)
    (p : Coeff F) (t : F) : extensionEval θ p t=
      algebraMap F E (realPart δ p t)+algebraMap F E (imagPart p t)*θ := by
  dsimp [extensionEval,realPart,imagPart]
  simp only [map_add,map_mul,map_pow,map_ofNat]
  linear_combination (algebraMap F E p.1)*hθ

/-- The host is defined with the field norm, not with an assumed norm polynomial. -/
def normGraph (θ : E) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := match x,y with
    | .inl x,.inr y | .inr y,.inl x =>
      x.2.1 ≠ 0 ∧ y.2.1 ≠ 0 ∧ eval x.2 y.1 ≠ 0 ∧ eval y.2 x.1 ≠ 0 ∧
      Algebra.norm F (extensionEval θ x.2 y.1+extensionEval θ y.2 x.1)=
        eval x.2 y.1*eval y.2 x.1
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

lemma normGraph_eq (δ : F) (θ : E) (hθ : θ^2=algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) :
    normGraph θ=graph δ := by
  have hn (x y : Vertex F) :
      Algebra.norm F (extensionEval θ x.2 y.1+extensionEval θ y.2 x.1)=
        (realPart δ x.2 y.1+realPart δ y.2 x.1)^2-
          δ*(imagPart x.2 y.1+imagPart y.2 x.1)^2 := by
    rw [extensionEval_eq δ θ hθ,extensionEval_eq δ θ hθ]
    have he : algebraMap F E (realPart δ x.2 y.1)+algebraMap F E (imagPart x.2 y.1)*θ+
        (algebraMap F E (realPart δ y.2 x.1)+algebraMap F E (imagPart y.2 x.1)*θ)=
        algebraMap F E (realPart δ x.2 y.1+realPart δ y.2 x.1)+
          algebraMap F E (imagPart x.2 y.1+imagPart y.2 x.1)*θ := by
      simp only [map_add]; ring
    rw [he,norm_pair δ θ hθ B hB]
  ext x y
  cases x <;> cases y <;> simp only [normGraph,graph,relation,hn]

/-- Uniform failure of the actual norm host, with all displayed exclusions. -/
theorem normGraph_not_free [Fintype F] (h2 : (2 : F) ≠ 0) (δ : F)
    (hδ : ¬IsSquare δ) (hq : 10 < Fintype.card F)
    (θ : E) (hθ : θ^2=algebraMap F E δ)
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (normGraph (F := F) θ) := by
  rw [normGraph_eq δ θ hθ B hB]
  apply not_free h2 δ
  · intro h; apply hδ; rw [h]; exact IsSquare.zero
  · intro h; apply hδ; rw [h]; exact ⟨2,by ring⟩
  · exact hq
end ActualNorm

#print axioms parameters
#print axioms signed_edge
#print axioms parameterCopy
#print axioms not_free
#print axioms norm_pair
#print axioms extensionEval_eq
#print axioms normGraph_eq
#print axioms normGraph_not_free
end Erdos714QuadraticEvaluation
