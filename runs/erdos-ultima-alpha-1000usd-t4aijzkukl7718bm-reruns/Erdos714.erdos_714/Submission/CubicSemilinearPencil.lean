import FormalConjecturesUtil

/-!
A cubic Frobenius, weight-dependent pencil gives genuine local permutations,
but a scalar-ray synchronization produces K(4,q-1) in the full nonzero-tag
host. This is a construction obstruction, not a resolution of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714CubicSemilinearPencil
variable {F : Type*} [Field F] [CharP F 3]

lemma two_ne_zero : (2:F) ≠ 0 := by
  intro h
  have h3 := CharP.cast_eq_zero F 3
  have hh : (1:F)=0 := by linear_combination h3-h
  exact one_ne_zero hh

/-- Nontrivial points on this conic supply four distinct nonzero row scalars. -/
theorem conic_parameters [Fintype F] (hns : ¬IsSquare (-1:F))
    (hq : 3 < Fintype.card F) :
    ∃ c k : F, c ≠ 0 ∧ k ≠ 0 ∧ c^2 ≠ 1 ∧ c^2+k^2=-1 := by
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1,-1}:Finset F)) (t := univ)
    ((Finset.card_le_three).trans_lt (by simpa using hq))
  have ht0 : t ≠ 0 := by simpa using fun h => ht (by simp [h])
  have ht1 : t ≠ 1 := by intro h; exact ht (by simp [h])
  have htm : t ≠ -1 := by intro h; exact ht (by simp [h])
  have hd : 1+t^2 ≠ 0 := by
    intro h
    apply hns
    exact ⟨t,by linear_combination -h⟩
  let c := (t^2+t-1)/(1+t^2)
  let k := (1+t-t^2)/(1+t^2)
  have he : c^2+k^2=-1 := by
    dsimp [c,k]
    field_simp
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!
  have hc : c ≠ 0 := by
    intro h
    apply hns
    refine ⟨k,?_⟩
    rw [h,zero_pow (by decide),zero_add] at he
    simpa only [pow_two] using he.symm
  have hk : k ≠ 0 := by
    intro h
    apply hns
    refine ⟨c,?_⟩
    rw [h,zero_pow (by decide),add_zero] at he
    simpa only [pow_two] using he.symm
  have hc1 : c ≠ 1 := by
    intro h
    have hh := (div_eq_iff hd).mp h
    have h3 := CharP.cast_eq_zero F 3
    apply htm
    linear_combination hh+h3
  have hcm : c ≠ -1 := by
    intro h
    have hh := (div_eq_iff hd).mp h
    have h3 := CharP.cast_eq_zero F 3
    have hp : t*(t-1)=0 := by linear_combination -hh+t^2*h3
    rcases mul_eq_zero.mp hp with h | h
    · exact ht0 h
    · exact ht1 (sub_eq_zero.mp h)
  exact ⟨c,k,hc,hk,fun h => (sq_eq_one_iff.mp h).elim hc1 hcm,he⟩

variable [Fact (¬IsSquare (-1:F))]
abbrev Ext (F : Type*) [Field F] := QuadraticAlgebra F (-1) 0

instance rootless : Fact (∀ x : F, x^2 ≠ -1+(0:F)*x) := ⟨by
  intro x h
  apply (Fact.out : ¬IsSquare (-1:F))
  exact ⟨x,by simpa only [zero_mul,add_zero,pow_two] using h.symm⟩⟩

instance extChar : CharP (Ext F) 3 :=
  charP_of_injective_algebraMap (algebraMap F (Ext F)).injective 3

instance extFintype [Fintype F] : Fintype (Ext F) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd (-1:F) 0).symm

def delta : Ext F := ⟨1,1⟩
abbrev scalar : F →+* Ext F := algebraMap F (Ext F)
abbrev N : Ext F →* F := QuadraticAlgebra.norm

def pencil (u : F) (x : Ext F) : Ext F := x+delta*scalar u*x^3

omit [Fact (¬IsSquare (-1:F))] in
lemma norm_delta : N (delta : Ext F)=-1 := by
  have h3 := CharP.cast_eq_zero F 3
  change (1:F)*1+0*1*1-(-1)*1*1=-1
  linear_combination h3

omit [CharP F 3] in
lemma pencil_zero (u : F) : pencil u (0:Ext F)=0 := by simp [pencil]

/-- The cubic term is additive over the prime field, and its coefficient
has a nonsquare norm whenever the scalar parameter is nonzero. -/
theorem pencil_injective (u : F) : Function.Injective (pencil u : Ext F → Ext F) := by
  intro x y h
  have h3 := sub_pow_char x y
  have he : (x-y)*(1+delta*scalar u*(x-y)^2)=0 := by
    dsimp only [pencil] at h
    linear_combination h+delta*scalar u*h3
  rcases mul_eq_zero.mp he with he | he
  · exact sub_eq_zero.mp he
  · have hh : delta*scalar u*(x-y)^2=(-1:Ext F) := by linear_combination he
    have hn := congrArg N hh
    simp only [map_mul,map_pow,norm_delta,QuadraticAlgebra.norm_algebraMap,
      QuadraticAlgebra.norm_neg,QuadraticAlgebra.norm_one] at hn
    apply False.elim
    apply (Fact.out : ¬IsSquare (-1:F))
    refine ⟨u*N (x-y),?_⟩
    linear_combination hn

variable [Fintype F]

def pencilEquiv (u : F) : Ext F ≃ Ext F :=
  Equiv.ofBijective (pencil u) ⟨pencil_injective u,Finite.surjective_of_injective (pencil_injective u)⟩

def ray (t : F) : Ext F := 1+delta*scalar t

omit [Fintype F] in
lemma ray_nonzero (t : F) : ray t ≠ (0:Ext F) := by
  have he : ray t=pencil t (1:Ext F) := by simp [ray,pencil]
  rw [he,← pencil_zero t]
  exact (pencil_injective t).ne one_ne_zero

omit [Fintype F] in
lemma ray_norm_nonzero (t : F) : N (ray t : Ext F) ≠ 0 :=
  mt QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (ray_nonzero t)

omit [CharP F 3] [Fintype F] in
/-- The weight v^(-2) exactly cancels the excess degree of the cubic. -/
lemma aligned_ray (t : F) (v : Fˣ) :
    pencil (t*((v⁻¹)^2:Fˣ)) (scalar (v:F))=scalar (v:F)*ray t := by
  dsimp only [pencil,ray]
  simp only [map_mul,map_pow,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,
    map_inv₀]
  have hv : scalar (v:F) ≠ 0 := (map_ne_zero scalar).mpr v.ne_zero
  field_simp

abbrev Vertex (F : Type*) [Field F] := Fˣ × Ext F × Fˣ

def relation (x y : Vertex F) : Prop :=
  N (pencil ((y.1:F)*(x.2.2:F)) x.2.1+pencil ((x.1:F)*(y.2.2:F)) y.2.1)=
    (x.2.2:F)*(y.2.2:F)

def graph : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := match x,y with
    | .inl x,.inr y => relation x y
    | .inr y,.inl x => relation x y
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

omit [CharP F 3] [Fintype F] in
lemma norm_scalar_imaginary (v k : F) :
    N (scalar v+(⟨0,k⟩:Ext F))=v^2+k^2 := by
  simp [N,QuadraticAlgebra.norm_def,scalar]
  ring

omit [CharP F 3] [Fintype F] in
lemma scalar_norm_identity (c k : F) (hc : c^2+k^2=-1) (v : Fˣ)
    (hv : (v:F)^2=1 ∨ (v:F)^2=c^2) :
    N (scalar (v:F)+(⟨0,k⟩:Ext F))=(v⁻¹:Fˣ)^2*(-c^2) := by
  rw [norm_scalar_imaginary]
  simp only [Units.val_inv_eq_inv_val]
  apply (mul_right_cancel₀ (pow_ne_zero 2 v.ne_zero))
  rw [mul_assoc,show (-c^2)*(v:F)^2=(v:F)^2*(-c^2) by ring,
    ←mul_assoc,inv_pow,inv_mul_cancel₀ (pow_ne_zero 2 v.ne_zero),one_mul]
  rcases hv with hv | hv <;> rw [hv]
  · linear_combination hc
  · linear_combination c^2*hc

def rowScalars (c : Fˣ) : Fin 4 → Fˣ := ![1,-1,c,-c]

omit [Fact (¬IsSquare (-1:F))] [Fintype F] in
lemma rowScalars_injective (c : Fˣ) (hc : (c:F)^2 ≠ 1) :
    Function.Injective (rowScalars c) := by
  have hpm : (1:F) ≠ -1 := by
    intro h
    exact two_ne_zero (by linear_combination h)
  have hcn : (c:F) ≠ -(c:F) := by
    intro h
    have hh : (2:F)*(c:F)=0 := by linear_combination h
    exact mul_ne_zero two_ne_zero c.ne_zero hh
  have hc1 : (c:F) ≠ 1 := by intro h; apply hc; simp [h]
  have hcm : (c:F) ≠ -1 := by intro h; apply hc; simp [h]
  intro i j h
  have hh := congrArg (fun a : Fˣ => (a:F)) h
  fin_cases i <;> fin_cases j <;>
    simp [rowScalars,hpm,Ne.symm hpm,hcn,Ne.symm hcn,hc1,Ne.symm hc1,hcm,Ne.symm hcm] at hh ⊢
  all_goals
    apply hcm
    first | linear_combination hh | linear_combination -hh

def rows (c : Fˣ) (i : Fin 4) : Vertex F :=
  (1,scalar (rowScalars c i:F),(rowScalars c i)⁻¹^2)

def columnWeight (c : Fˣ) (t : Fˣ) : Fˣ :=
  Units.mk0 (-(c:F)^2*N (ray (t:F)))
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 c.ne_zero)) (ray_norm_nonzero (t:F)))

def columns (c : Fˣ) (k : F) (t : Fˣ) : Vertex F :=
  (t,(pencilEquiv (columnWeight c t:F)).symm (ray (t:F)*(⟨0,k⟩:Ext F)),columnWeight c t)

lemma original_edge (c : Fˣ) (k : F) (hc : (c:F)^2+k^2=-1)
    (i : Fin 4) (t : Fˣ) : relation (rows c i) (columns c k t) := by
  let v := rowScalars c i
  have hv : (v:F)^2=1 ∨ (v:F)^2=(c:F)^2 := by
    fin_cases i <;> simp [v,rowScalars]
  change N (pencil ((t:F)*((v⁻¹)^2:Fˣ)) (scalar (v:F))+
    pencil (1*(columnWeight c t:F))
      ((pencilEquiv (columnWeight c t:F)).symm (ray (t:F)*(⟨0,k⟩:Ext F))))=
      ((v⁻¹)^2:Fˣ)*(columnWeight c t:F)
  rw [one_mul,aligned_ray]
  have hp := (pencilEquiv (columnWeight c t:F)).apply_symm_apply (ray (t:F)*(⟨0,k⟩:Ext F))
  change pencil _ _=_ at hp
  rw [hp,show scalar (v:F)*ray (t:F)+ray (t:F)*(⟨0,k⟩:Ext F)=
      ray (t:F)*(scalar (v:F)+(⟨0,k⟩:Ext F)) by ring,map_mul,scalar_norm_identity _ _ hc v hv]
  change N (ray (t:F))*(((v⁻¹)^2:Fˣ)*(-(c:F)^2))=
    ((v⁻¹)^2:Fˣ)*(-(c:F)^2*N (ray (t:F)))
  ring

/-- There is one distinct common column for every nonzero tag. -/
def rayCopy (c : Fˣ) (k : F) (hc1 : (c:F)^2 ≠ 1) (hc : (c:F)^2+k^2=-1) :
    Copy (completeBipartiteGraph (Fin 4) Fˣ) (graph (F := F)) := by
  let l : Fin 4 ↪ Vertex F := ⟨rows c,by
    intro i j h
    apply rowScalars_injective c hc1
    apply Units.ext
    apply scalar.injective
    exact congrArg (fun v : Vertex F => v.2.1) h⟩
  let r : Fˣ ↪ Vertex F := ⟨columns c k,by
    intro t u h
    exact congrArg Prod.fst h⟩
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr t => exact original_edge c k hc i t
  | inr t =>
    cases y with
    | inr u => simp at h
    | inl i => exact original_edge c k hc i t

theorem not_free (hq : 5 ≤ Fintype.card F) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  obtain ⟨c,k,hc,hk,hc1,he⟩ := conic_parameters (Fact.out : ¬IsSquare (-1:F)) (by omega)
  let cu : Fˣ := Units.mk0 c hc
  obtain ⟨tags⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := Fˣ)
    (by simpa only [Fintype.card_fin,Fintype.card_units] using show 4 ≤ Fintype.card F-1 by omega)
  let small : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph (Fin 4) Fˣ) :=
    ⟨⟨(Function.Embedding.refl (Fin 4)).sumMap tags,by
      intro x y h; cases x <;> cases y <;> simp_all⟩,
      ((Function.Embedding.refl (Fin 4)).sumMap tags).injective⟩
  intro hf
  exact hf ⟨(rayCopy cu k hc1 he).comp small⟩

omit [CharP F 3] [Fintype F] in
/-- The coordinate norm used by the host is the actual algebra norm. -/
lemma norm_actual (x : Ext F) : Algebra.norm F x=N x := by
  let B := QuadraticAlgebra.basis (-1:F) 0
  let M : Matrix (Fin 2) (Fin 2) F := !![x.re,-x.im;x.im,x.re]
  have hB (i : Fin 2) : B i=(![(1:Ext F),⟨0,1⟩] i) := by
    apply B.repr.injective
    rw [B.repr_self]
    fin_cases i <;> ext j <;> fin_cases j <;> simp [B,QuadraticAlgebra.basis_repr_apply] <;> rfl
  have hm : Algebra.leftMulMatrix B x=M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul,hB]
    change ![(x*(![(1:Ext F),⟨0,1⟩] j)).re,(x*(![(1:Ext F),⟨0,1⟩] j)).im] i=M i j
    fin_cases i <;> fin_cases j <;> simp [M]
  rw [Algebra.norm_eq_matrix_det B,hm,Matrix.det_fin_two]
  change x.re*x.re-(-x.im)*x.im=x.re*x.re+0*x.re*x.im-(-1)*x.im*x.im
  ring

omit [CharP F 3] [Fintype F] in
lemma rows_point_nonzero (c : Fˣ) (i : Fin 4) : (rows c i).2.1 ≠ 0 := by
  change scalar (rowScalars c i:F) ≠ 0
  exact (map_ne_zero scalar).mpr (rowScalars c i).ne_zero

lemma columns_point_nonzero (c : Fˣ) (k : F) (hk : k ≠ 0) (t : Fˣ) :
    (columns c k t).2.1 ≠ 0 := by
  intro h
  have hh := congrArg (pencilEquiv (columnWeight c t:F)) h
  change (pencilEquiv (columnWeight c t:F))
    ((pencilEquiv (columnWeight c t:F)).symm (ray (t:F)*(⟨0,k⟩:Ext F)))=
      pencil (columnWeight c t:F) 0 at hh
  rw [Equiv.apply_symm_apply,pencil_zero] at hh
  have hk' : (⟨0,k⟩:Ext F) ≠ 0 := by
    intro he
    exact hk (congrArg QuadraticAlgebra.im he)
  exact mul_ne_zero (ray_nonzero (t:F)) hk' hh

abbrev NonzeroVertex (F : Type*) [Field F] := {v : Vertex F // v.2.1 ≠ 0}

def nonzeroGraph : SimpleGraph (NonzeroVertex F ⊕ NonzeroVertex F) :=
  graph.comap (Sum.map Subtype.val Subtype.val)

/-- Even deleting every zero-point vertex leaves the entire K(4,q-1). -/
def nonzeroRayCopy (c : Fˣ) (k : F) (hk : k ≠ 0)
    (hc1 : (c:F)^2 ≠ 1) (hc : (c:F)^2+k^2=-1) :
    Copy (completeBipartiteGraph (Fin 4) Fˣ) (nonzeroGraph (F := F)) := by
  let l : Fin 4 ↪ NonzeroVertex F := ⟨fun i => ⟨rows c i,rows_point_nonzero c i⟩,by
    intro i j h
    apply rowScalars_injective c hc1
    apply Units.ext
    apply scalar.injective
    exact congrArg (fun v : NonzeroVertex F => v.val.2.1) h⟩
  let r : Fˣ ↪ NonzeroVertex F := ⟨fun t => ⟨columns c k t,columns_point_nonzero c k hk t⟩,by
    intro t u h
    exact congrArg (fun v : NonzeroVertex F => v.val.1) h⟩
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr t => exact original_edge c k hc i t
  | inr t =>
    cases y with
    | inr u => simp at h
    | inl i => exact original_edge c k hc i t

theorem nonzero_not_free (hq : 5 ≤ Fintype.card F) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (nonzeroGraph (F := F)) := by
  obtain ⟨c,k,hc,hk,hc1,he⟩ := conic_parameters (Fact.out : ¬IsSquare (-1:F)) (by omega)
  let cu : Fˣ := Units.mk0 c hc
  obtain ⟨tags⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := Fˣ)
    (by simpa only [Fintype.card_fin,Fintype.card_units] using show 4 ≤ Fintype.card F-1 by omega)
  let small : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph (Fin 4) Fˣ) :=
    ⟨⟨(Function.Embedding.refl (Fin 4)).sumMap tags,by
      intro x y h; cases x <;> cases y <;> simp_all⟩,
      ((Function.Embedding.refl (Fin 4)).sumMap tags).injective⟩
  intro hf
  exact hf ⟨(nonzeroRayCopy cu k hk hc1 he).comp small⟩

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
instance oddGalois_nonsquare (k : ℕ) : Fact (¬IsSquare (-1:GaloisField 3 (2*k+3))) := ⟨by
  letI : Fintype (GaloisField 3 (2*k+3)) := Fintype.ofFinite _
  rw [FiniteField.isSquare_neg_one_iff,Fintype.card_eq_nat_card,
    GaloisField.card 3 (2*k+3) (by omega),pow_add,pow_mul]
  norm_num [Nat.mul_mod,Nat.pow_mod]⟩

theorem oddGalois_nonzero_not_free (k : ℕ) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (nonzeroGraph (F := GaloisField 3 (2*k+3))) := by
  letI : Fintype (GaloisField 3 (2*k+3)) := Fintype.ofFinite _
  apply nonzero_not_free
  rw [Fintype.card_eq_nat_card,GaloisField.card 3 (2*k+3) (by omega)]
  have h : (3:ℕ)^3 ≤ 3^(2*k+3) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

#print axioms conic_parameters
#print axioms pencil_injective
#print axioms pencilEquiv
#print axioms aligned_ray
#print axioms scalar_norm_identity
#print axioms original_edge
#print axioms rayCopy
#print axioms norm_actual
#print axioms nonzeroRayCopy
#print axioms nonzero_not_free
#print axioms oddGalois_nonzero_not_free
#print axioms not_free
end Erdos714CubicSemilinearPencil
