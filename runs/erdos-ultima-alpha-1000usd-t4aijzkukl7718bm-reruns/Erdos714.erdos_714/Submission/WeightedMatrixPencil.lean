import FormalConjecturesUtil

/-!
A weight-dependent matrix pencil gives actual local permutations of a
quadratic norm seed, but it need not preserve global K44-freeness. The
certificate here uses nonzero tags and transfers through field embeddings.
This is a construction obstruction, not a resolution of Erdős 714.
-/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714WeightedMatrixPencil

variable {F K : Type*} [Field F] [Field K]

abbrev Point (F : Type*) := F × F
abbrev Vertex (F : Type*) [Field F] := F × Point F × Fˣ

def quad (D : F) (x : Point F) : F := x.1^2-D*x.2^2

def pencil (E u : F) (x : Point F) : Point F :=
  (x.1+E*u*x.2,x.2+u*x.1)

lemma determinant_ne_zero (E : F) (hE : ¬IsSquare E) (u : F) :
    1-E*u^2 ≠ 0 := by
  intro h
  have he : E*u^2=1 := (sub_eq_zero.mp h).symm
  have hu : u ≠ 0 := by intro hu; simp [hu] at he
  apply hE
  refine ⟨u⁻¹,?_⟩
  apply mul_right_cancel₀ (pow_ne_zero 2 hu)
  calc
    E*u^2=1 := he
    _ = (u⁻¹*u⁻¹)*u^2 := by field_simp

def pencilInverse (E u : F) (x : Point F) : Point F :=
  ((x.1-E*u*x.2)/(1-E*u^2),(x.2-u*x.1)/(1-E*u^2))

lemma inverse_pencil (E u : F) (h : 1-E*u^2 ≠ 0) (x : Point F) :
    pencilInverse E u (pencil E u x)=x := by
  apply Prod.ext
  · dsimp only [pencilInverse,pencil]
    apply (div_eq_iff h).mpr
    ring
  · dsimp only [pencilInverse,pencil]
    apply (div_eq_iff h).mpr
    ring

lemma pencil_inverse (E u : F) (h : 1-E*u^2 ≠ 0) (x : Point F) :
    pencil E u (pencilInverse E u x)=x := by
  apply Prod.ext
  · dsimp only [pencilInverse,pencil]
    rw [←mul_div_assoc,←add_div]
    apply (div_eq_iff h).mpr
    ring
  · dsimp only [pencilInverse,pencil]
    rw [←mul_div_assoc,←add_div]
    apply (div_eq_iff h).mpr
    ring

/-- Every pencil map is an actual permutation, not just a surjection. -/
def pencilEquiv (E : F) (hE : ¬IsSquare E) (u : F) : Point F ≃ Point F where
  toFun := pencil E u
  invFun := pencilInverse E u
  left_inv := inverse_pencil E u (determinant_ne_zero E hE u)
  right_inv := pencil_inverse E u (determinant_ne_zero E hE u)

/-- The scalar weight is retained by each tag-dependent local permutation. -/
def seedEquiv (E : F) (hE : ¬IsSquare E) (t : F) :
    (Point F × Fˣ) ≃ (Point F × Fˣ) where
  toFun x := (pencil E (t*(x.2:F)) x.1,x.2)
  invFun x := (pencilInverse E (t*(x.2:F)) x.1,x.2)
  left_inv x := Prod.ext (inverse_pencil E _ (determinant_ne_zero E hE _) x.1) rfl
  right_inv x := Prod.ext (pencil_inverse E _ (determinant_ne_zero E hE _) x.1) rfl

def relation (D E : F) (x y : Vertex F) : Prop :=
  quad D (pencil E (y.1*(x.2.2:F)) x.2.1 +
    pencil E (x.1*(y.2.2:F)) y.2.1) = (x.2.2:F)*(y.2.2:F)

def graph (D E : F) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := match x,y with
    | .inl x,.inr y => relation D E x y
    | .inr y,.inl x => relation D E x y
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

lemma quad_zero_iff (D : F) (hD : ¬IsSquare D) (x : Point F) :
    quad D x=0 ↔ x=0 := by
  constructor
  · intro h
    by_cases hx : x.2=0
    · have h₁ : x.1^2=0 := by simpa [quad,hx] using h
      exact Prod.ext (sq_eq_zero_iff.mp h₁) hx
    · apply False.elim
      apply hD
      refine ⟨x.1/x.2,?_⟩
      dsimp [quad] at h
      rw [←pow_two,div_pow,eq_div_iff (pow_ne_zero 2 hx)]
      linear_combination -h
  · rintro rfl
    simp [quad]

lemma relation_symm (D E : F) (x y : Vertex F) :
    relation D E x y ↔ relation D E y x := by
  unfold relation
  rw [add_comm,mul_comm (x.2.2:F)]

/-- A neighbor is parameterized by its tag and a nonzero original point sum. -/
def relationNeighborEquiv (D E : F) (hD : ¬IsSquare D) (hE : ¬IsSquare E)
    (x : Vertex F) : {y : Vertex F // relation D E x y} ≃
      F × {z : Point F // z ≠ 0} where
  toFun y := (y.val.1,⟨pencil E (y.val.1*(x.2.2:F)) x.2.1+
      pencil E (x.1*(y.val.2.2:F)) y.val.2.1,by
    intro hz
    have hh := y.property
    unfold relation at hh
    rw [hz] at hh
    have hzero : quad D (0:Point F)=0 := by simp [quad]
    rw [hzero] at hh
    exact mul_ne_zero x.2.2.ne_zero y.val.2.2.ne_zero hh.symm⟩)
  invFun z :=
    let b : Fˣ := Units.mk0 (quad D z.2.val/(x.2.2:F))
      (div_ne_zero (mt (quad_zero_iff D hD _).mp z.2.property) x.2.2.ne_zero)
    ⟨(z.1,pencilInverse E (x.1*(b:F))
        (z.2.val-pencil E (z.1*(x.2.2:F)) x.2.1),b),by
      change quad D (pencil E (z.1*(x.2.2:F)) x.2.1+
        pencil E (x.1*(b:F)) (pencilInverse E (x.1*(b:F)) _))=(x.2.2:F)*(b:F)
      rw [pencil_inverse E _ (determinant_ne_zero E hE _),add_sub_cancel]
      change quad D z.2.val=(x.2.2:F)*(quad D z.2.val/(x.2.2:F))
      exact (mul_div_cancel₀ _ x.2.2.ne_zero).symm⟩
  left_inv y := by
    apply Subtype.ext
    have hb : quad D (pencil E (y.val.1*(x.2.2:F)) x.2.1+
        pencil E (x.1*(y.val.2.2:F)) y.val.2.1)/(x.2.2:F)=(y.val.2.2:F) := by
      rw [y.property]
      exact mul_div_cancel_left₀ _ x.2.2.ne_zero
    apply Prod.ext
    · rfl
    apply Prod.ext
    · change pencilInverse E (x.1*(_/(x.2.2:F)))
        (_+pencil E (x.1*(y.val.2.2:F)) y.val.2.1-_) = y.val.2.1
      rw [hb,add_sub_cancel_left,inverse_pencil E _ (determinant_ne_zero E hE _)]
    · exact Units.ext hb
  right_inv z := by
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change pencil E (z.1*(x.2.2:F)) x.2.1+
      pencil E _ (pencilInverse E _ (z.2.val-pencil E (z.1*(x.2.2:F)) x.2.1))=z.2.val
    rw [pencil_inverse E _ (determinant_ne_zero E hE _),add_sub_cancel]

/-- Restricting both tag sets to nonzero elements is a genuine induced subgraph. -/
abbrev NonzeroVertex (F : Type*) [Field F] := {x : Vertex F // x.1 ≠ 0}

def nonzeroGraph (D E : F) : SimpleGraph (NonzeroVertex F ⊕ NonzeroVertex F) :=
  (graph D E).comap (Sum.map Subtype.val Subtype.val)

lemma vertex_count [Fintype F] :
    Fintype.card (Vertex F ⊕ Vertex F)=2*Fintype.card F^3*(Fintype.card F-1) := by
  simp only [Vertex,Point,Fintype.card_sum,Fintype.card_prod,Fintype.card_units]
  ring

lemma relation_neighbor_count [Fintype F] (D E : F) (hD : ¬IsSquare D)
    (hE : ¬IsSquare E) (x : Vertex F) :
    Fintype.card {y : Vertex F // relation D E x y}=
      Fintype.card F*(Fintype.card F^2-1) := by
  rw [Fintype.card_congr (relationNeighborEquiv D E hD hE x),Fintype.card_prod,
    Fintype.card_subtype_compl]
  simp only [Fintype.card_unique,Point,Fintype.card_prod,pow_two]

def leftNeighborEquiv (D E : F) (x : Vertex F) :
    (graph D E).neighborSet (.inl x) ≃ {y : Vertex F // relation D E x y} where
  toFun y := match y with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr y,h⟩ => ⟨y,h⟩
  invFun y := ⟨.inr y.val,y.property⟩
  left_inv := by
    rintro ⟨y,h⟩
    cases y with
    | inl y => exact False.elim h
    | inr y => rfl
  right_inv y := rfl

def rightNeighborEquiv (D E : F) (x : Vertex F) :
    (graph D E).neighborSet (.inr x) ≃ {y : Vertex F // relation D E x y} where
  toFun y := match y with
    | ⟨.inr _,h⟩ => False.elim h
    | ⟨.inl y,h⟩ => ⟨y,(relation_symm D E y x).mp h⟩
  invFun y := ⟨.inl y.val,(relation_symm D E x y.val).mp y.property⟩
  left_inv := by
    rintro ⟨y,h⟩
    cases y with
    | inr y => exact False.elim h
    | inl y => rfl
  right_inv y := rfl

theorem degree [Fintype F] (D E : F) (hD : ¬IsSquare D) (hE : ¬IsSquare E)
    (v : Vertex F ⊕ Vertex F) :
    (graph D E).degree v=Fintype.card F*(Fintype.card F^2-1) := by
  rw [←card_neighborSet_eq_degree]
  cases v with
  | inl x =>
    rw [Fintype.card_congr (leftNeighborEquiv D E x)]
    exact relation_neighbor_count D E hD hE x
  | inr x =>
    rw [Fintype.card_congr (rightNeighborEquiv D E x)]
    exact relation_neighbor_count D E hD hE x

/-- Exact critical-scale edge count for the full host, before imposing freeness. -/
theorem edge_count [Fintype F] (D E : F) (hD : ¬IsSquare D) (hE : ¬IsSquare E) :
    (graph D E).edgeFinset.card=Fintype.card F^4*(Fintype.card F-1)^2*
      (Fintype.card F+1) := by
  have h := (graph D E).sum_degrees_eq_twice_card_edges
  simp only [degree D E hD hE,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,vertex_count] at h
  have hq : Fintype.card F^2-1=(Fintype.card F-1)*(Fintype.card F+1) := by
    have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
    have hq2 : 1 ≤ Fintype.card F^2 := one_le_pow₀ hq1
    have h₁ := Nat.sub_add_cancel hq1
    have h₂ := Nat.sub_add_cancel hq2
    nlinarith
  rw [hq] at h
  nlinarith only [h]

def pointMap (f : F →+* K) (x : Point F) : Point K := (f x.1,f x.2)

def vertexMap (f : F →+* K) (x : Vertex F) : Vertex K :=
  (f x.1,pointMap f x.2.1,Units.map f x.2.2)

lemma pointMap_injective (f : F →+* K) : Function.Injective (pointMap f) := by
  intro x y h
  exact Prod.ext (f.injective (congrArg Prod.fst h))
    (f.injective (congrArg Prod.snd h))

lemma vertexMap_injective (f : F →+* K) : Function.Injective (vertexMap f) := by
  intro x y h
  apply Prod.ext
  · exact f.injective (congrArg Prod.fst h)
  apply Prod.ext
  · exact pointMap_injective f (congrArg (fun z : Vertex K => z.2.1) h)
  · apply Units.ext
    exact f.injective (congrArg (fun z : Vertex K => (z.2.2:K)) h)

lemma relation_map (f : F →+* K) (D E : F) (x y : Vertex F)
    (h : relation D E x y) : relation (f D) (f E) (vertexMap f x) (vertexMap f y) := by
  have hh := congrArg f h
  simpa only [relation,quad,pencil,vertexMap,pointMap,Prod.fst_add,Prod.snd_add,
    Units.coe_map,map_add,map_sub,map_mul,map_pow] using hh

/-- A copy in the original host transfers with the actual scalar weights. -/
def embeddingCopy (f : F →+* K) (D E : F) : Copy (graph D E) (graph (f D) (f E)) := by
  let e : Vertex F ↪ Vertex K := ⟨vertexMap f,vertexMap_injective f⟩
  refine ⟨⟨e.sumMap e,?_⟩,(e.sumMap e).injective⟩
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact False.elim h
    | inr y => exact relation_map f D E x y h
  | inr x =>
    cases y with
    | inr y => exact False.elim h
    | inl y => exact relation_map f D E y x h

section Certificate
abbrev Base := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def six : Baseˣ := Units.mk0 6 (by decide)
def two : Baseˣ := Units.mk0 2 (by decide)

def rows : Fin 4 → Vertex Base :=
  ![(1,(1,0),1),(1,(6,0),1),(1,(0,1),1),(1,(0,1),six)]
def columns : Fin 4 → Vertex Base :=
  ![(3,(0,5),six),(4,(5,3),six),(2,(3,3),two),(5,(5,6),two)]

lemma rows_injective : Function.Injective rows := by decide
lemma columns_injective : Function.Injective columns := by decide
lemma rows_nonzero_tag (i : Fin 4) : (rows i).1 ≠ 0 := by fin_cases i <;> decide
lemma columns_nonzero_tag (i : Fin 4) : (columns i).1 ≠ 0 := by fin_cases i <;> decide
lemma nonsquare_parameters : ¬IsSquare (3 : Base) ∧ ¬IsSquare (5 : Base) := by decide
lemma certificate_edges (i j : Fin 4) : relation 3 5 (rows i) (columns j) := by
  fin_cases i <;> fin_cases j <;> unfold relation <;> decide

/-- The four rows and four columns are vertices of the ORIGINAL pencil host. -/
def baseCopy : Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (3:Base) 5) := by
  let l : Fin 4 ↪ Vertex Base := ⟨rows,rows_injective⟩
  let r : Fin 4 ↪ Vertex Base := ⟨columns,columns_injective⟩
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr j => exact certificate_edges i j
  | inr j =>
    cases y with
    | inr i => simp at h
    | inl i => exact certificate_edges i j

variable (F : Type*) [Field F] [CharP F 7]

/-- Incidence transfer does not assume that 3 and 5 stay nonsquare. -/
def characteristicSevenCopy :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (3:F) 5) := by
  let f : Base →+* F := ZMod.castHom (dvd_refl 7) F
  have hf3 : f 3=3 := map_natCast f 3
  have hf5 : f 5=5 := map_natCast f 5
  simpa only [hf3,hf5] using (embeddingCopy f 3 5).comp baseCopy

theorem characteristicSeven_not_free :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (3:F) 5) := by
  intro h
  exact h ⟨characteristicSevenCopy F⟩

/-- The forbidden copy still has nonzero tags after transfer. -/
def characteristicSevenNonzeroCopy :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (nonzeroGraph (3:F) 5) := by
  let f : Base →+* F := ZMod.castHom (dvd_refl 7) F
  have hn (x : Vertex Base) (hx : x.1 ≠ 0) : (vertexMap f x).1 ≠ 0 := by
    change f x.1 ≠ 0
    exact (map_ne_zero f).mpr hx
  let l : Fin 4 ↪ NonzeroVertex F := ⟨fun i =>
    ⟨vertexMap f (rows i),hn _ (rows_nonzero_tag i)⟩,by
    intro i j hij
    exact rows_injective (vertexMap_injective f (congrArg Subtype.val hij))⟩
  let r : Fin 4 ↪ NonzeroVertex F := ⟨fun j =>
    ⟨vertexMap f (columns j),hn _ (columns_nonzero_tag j)⟩,by
    intro i j hij
    exact columns_injective (vertexMap_injective f (congrArg Subtype.val hij))⟩
  have he (i j : Fin 4) : relation (3:F) 5 (l i).val (r j).val := by
    have hh := relation_map f 3 5 (rows i) (columns j) (certificate_edges i j)
    simpa only [map_ofNat] using hh
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inr i => simp at h
    | inl i => exact he i j

theorem characteristicSeven_nonzero_not_free :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (nonzeroGraph (3:F) 5) := by
  intro h
  exact h ⟨characteristicSevenNonzeroCopy F⟩

end Certificate

section OddExtension
variable [Algebra F K]

/-- Odd-degree extensions preserve nonsquareness, via the actual field norm. -/
lemma nonsquare_odd_extension (a : F) (ha : ¬IsSquare a) (k : ℕ)
    (hd : Module.finrank F K=2*k+1) : ¬IsSquare (algebraMap F K a) := by
  rintro ⟨z,hz⟩
  have ha0 : a ≠ 0 := by intro h; apply ha; rw [h]; exact ⟨0,by simp⟩
  have hh := congrArg (Algebra.norm F) hz
  rw [Algebra.norm_algebraMap,map_mul,hd] at hh
  apply ha
  refine ⟨Algebra.norm F z/a^k,?_⟩
  rw [←pow_two,div_pow,eq_div_iff (pow_ne_zero 2 (pow_ne_zero k ha0))]
  calc
    a*(a^k)^2=a^(2*k+1) := by ring
    _ = Algebra.norm F z*Algebra.norm F z := hh
    _ = _ := by ring

end OddExtension

lemma oddGalois_nonsquare_parameters (k : ℕ) :
    ¬IsSquare (3:GaloisField 7 (2*k+1)) ∧ ¬IsSquare (5:GaloisField 7 (2*k+1)) := by
  have hd := GaloisField.finrank 7 (show 2*k+1 ≠ 0 by omega)
  have h₃ := nonsquare_odd_extension (K := GaloisField 7 (2*k+1))
    (3:Base) nonsquare_parameters.1 k hd
  have h₅ := nonsquare_odd_extension (K := GaloisField 7 (2*k+1))
    (5:Base) nonsquare_parameters.2 k hd
  simpa only [map_ofNat] using And.intro h₃ h₅

/-- An unbounded family with legitimate anisotropic seed and invertible pencil
still contains the forbidden copy, even after deleting every zero-tag vertex. -/
theorem oddGalois_nonzero_not_free (k : ℕ) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (nonzeroGraph (3:GaloisField 7 (2*k+1)) 5) :=
  characteristicSeven_nonzero_not_free _

#print axioms determinant_ne_zero
#print axioms pencilEquiv
#print axioms seedEquiv
#print axioms relationNeighborEquiv
#print axioms relation_neighbor_count
#print axioms vertex_count
#print axioms degree
#print axioms edge_count
#print axioms embeddingCopy
#print axioms certificate_edges
#print axioms characteristicSevenCopy
#print axioms characteristicSevenNonzeroCopy
#print axioms characteristicSeven_nonzero_not_free
#print axioms nonsquare_odd_extension
#print axioms oddGalois_nonsquare_parameters
#print axioms oddGalois_nonzero_not_free
#print axioms characteristicSeven_not_free
end Erdos714WeightedMatrixPencil
