import Submission.BinaryQuarticFiber
import Submission.SidonFiberGluing

/-!
A binary semilinear weight-dependent pencil has a synchronized four-row norm
fiber. The full host fails even with nonzero tags, points, and weights. This
is an obstruction to the proposed construction, not a solution of Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
open scoped CharTwo
set_option maxHeartbeats 4000000
namespace Erdos714BinarySemilinearPencil
variable {F E : Type*} [Field F] [Field E] [CharP F 2] [CharP E 2]
  [Algebra F E]

abbrev scalar : F →+* E := algebraMap F E

def pencil (σ : E →+* E) (δ : E) (u : F) (x : E) : E :=
  x+δ*scalar u*σ x

omit [CharP F 2] [CharP E 2] in
lemma pencil_zero (σ : E →+* E) (δ : E) (u : F) : pencil σ δ u 0=0 := by
  simp [pencil]

omit [CharP F 2] in
lemma pencil_injective (σ : E →+* E) (δ : E)
    (hσ : ∀ x, σ (σ x)=x^4) (hbase : ∀ a : F, σ (scalar a)=scalar (a^2))
    (hδ : ∀ z : E, z^3 ≠ δ*σ δ) (u : F) : Function.Injective (pencil σ δ u) := by
  by_cases hu : u=0
  · subst u
    intro x y h
    simpa [pencil,scalar] using h
  have hu' : scalar (E := E) u ≠ 0 := (map_ne_zero scalar).mpr hu
  apply Erdos714SidonGluing.form_injective
  intro x hx
  apply Erdos714SidonGluing.form_ne_zero σ hσ _ _ hx
  intro z hz
  apply hδ (z/scalar u)
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 3 hu')).mpr
  rw [map_mul,hbase,map_pow] at hz
  linear_combination hz

variable [Fintype F] [Fintype E]

def pencilEquiv (σ : E →+* E) (δ : E)
    (hp : ∀ u : F, Function.Bijective (pencil σ δ u)) (u : F) : E ≃ E :=
  Equiv.ofBijective (pencil σ δ u) (hp u)

omit [CharP F 2] [CharP E 2] [Fintype F] [Fintype E] in
/-- The weight cancels the squared scalar, making the tag term independent of the row. -/
lemma synchronized (σ : E →+* E) (δ : E)
    (hbase : ∀ a : F, σ (scalar a)=scalar (a^2)) (t : F) (v : Fˣ) :
    pencil σ δ (t*((v⁻¹)^2:Fˣ)) (scalar (v:F))=scalar (v:F)+δ*scalar t := by
  dsimp only [pencil]
  rw [hbase]
  simp only [map_mul,map_pow,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,map_inv₀]
  have hv : scalar (E := E) (v:F) ≠ 0 := (map_ne_zero scalar).mpr v.ne_zero
  field_simp

omit [CharP F 2] [CharP E 2] [Fintype E] in
lemma choose_tags (Z δ : E) (hZ : Z ≠ 0) (hq : 6≤Fintype.card F) :
    ∃ t : Fin 4 ↪ F, (∀ i, t i ≠ 0) ∧ ∀ i, Z+δ*scalar (t i) ≠ 0 := by
  let B := univ.filter (fun t : F => Z+δ*scalar t=0)
  have hB : B.card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro t u ht hu
    have ht' := (mem_filter.mp ht).2
    have hu' := (mem_filter.mp hu).2
    by_cases hd : δ=0
    · simp [hd,hZ] at ht'
    · exact scalar.injective (mul_left_cancel₀ hd (add_left_cancel (ht'.trans hu'.symm)))
  let Bad := insert (0:F) B
  have hBad : Bad.card ≤ 2 := (card_insert_le _ _).trans (by omega)
  let Good := univ \ Bad
  have hc : 4≤Good.card := by
    rw [card_sdiff_of_subset (subset_univ Bad),card_univ]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := ↥Good)
    (by simpa using hc)
  let t : Fin 4 ↪ F := ⟨fun i => e i,by intro i j h; exact e.injective (Subtype.ext h)⟩
  have ht (i : Fin 4) : t i ∉ Bad := (mem_sdiff.mp (e i).property).2
  refine ⟨t,?_,?_⟩
  · intro i hi
    exact ht i (by simp [Bad,hi])
  · intro i hi
    apply ht i
    exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,hi⟩)

abbrev Vertex (F E : Type*) [Field F] [Field E] := Fˣ × Eˣ × Fˣ

def relation (σ : E →+* E) (δ : E) (x y : Vertex F E) : Prop :=
  Algebra.norm F (pencil σ δ ((y.1:F)*(x.2.2:F)) (x.2.1:E)+
    pencil σ δ ((x.1:F)*(y.2.2:F)) (y.2.1:E))=(x.2.2:F)*(y.2.2:F)

def graph (σ : E →+* E) (δ : E) : SimpleGraph (Vertex F E ⊕ Vertex F E) where
  Adj x y := match x,y with
    | .inl x,.inr y => relation σ δ x y
    | .inr y,.inl x => relation σ δ x y
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

/-- The copy uses four actual nonzero point coordinates and weights, and
four nonzero tags with nonzero recovered column points. -/
theorem exists_copy (σ : E →+* E) (δ : E)
    (hbase : ∀ a : F, σ (scalar a)=scalar (a^2))
    (hp : ∀ u : F, Function.Bijective (pencil σ δ u))
    (m : ℕ) (hcard : Fintype.card F=2^m) (hE : Fintype.card E=Fintype.card F^2)
    (hq : 6≤Fintype.card F) :
    Nonempty (Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) σ δ)) := by
  obtain ⟨Z,hZ,b,hb,v,hv,he⟩ := Erdos714BinaryQuarticFiber.norm_four_fiber m hcard hE (by omega)
  obtain ⟨t,ht,htZ⟩ := choose_tags Z δ hZ hq
  let bu := Units.mk0 b hb
  let vs (i : Fin 4) : Fˣ := Units.mk0 (v i) (hv i)
  let row (i : Fin 4) : Vertex F E :=
    (1,Units.mk0 (scalar (v i)) ((map_ne_zero scalar).mpr (hv i)),(vs i)⁻¹^2)
  let point (j : Fin 4) : E := (pencilEquiv σ δ hp b).symm (Z+δ*scalar (t j))
  have hpoint (j : Fin 4) : point j ≠ 0 := by
    intro h
    apply htZ j
    have hh := (pencilEquiv σ δ hp b).apply_symm_apply (Z+δ*scalar (t j))
    change pencil σ δ b (point j)=Z+δ*scalar (t j) at hh
    rw [h,pencil_zero] at hh
    exact hh.symm
  let col (j : Fin 4) : Vertex F E :=
    (Units.mk0 (t j) (ht j),Units.mk0 (point j) (hpoint j),bu)
  let l : Fin 4 ↪ Vertex F E := ⟨row,by
    intro i j h
    apply v.injective
    apply (scalar (F := F) (E := E)).injective
    exact congrArg (fun r : Vertex F E => (r.2.1:E)) h⟩
  let r : Fin 4 ↪ Vertex F E := ⟨col,by
    intro i j h
    apply t.injective
    exact congrArg (fun r : Vertex F E => (r.1:F)) h⟩
  have hed (i j : Fin 4) : relation σ δ (l i) (r j) := by
    change Algebra.norm F (pencil σ δ ((t j)*((vs i)⁻¹^2:Fˣ)) (scalar (v i))+
      pencil σ δ (1*b) (point j))=((vs i)⁻¹^2:Fˣ)*b
    rw [one_mul]
    have hs := synchronized σ δ hbase (t j) (vs i)
    change pencil σ δ ((t j)*((vs i)⁻¹^2:Fˣ)) (scalar (v i))=scalar (v i)+δ*scalar (t j) at hs
    rw [hs]
    have hc := (pencilEquiv σ δ hp b).apply_symm_apply (Z+δ*scalar (t j))
    change pencil σ δ b (point j)=Z+δ*scalar (t j) at hc
    rw [hc,show scalar (v i)+δ*scalar (t j)+(Z+δ*scalar (t j))=scalar (v i)+Z by
      simp [add_left_comm,add_comm]]
    simp only [Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,vs,Units.val_mk0]
    apply mul_left_cancel₀ (pow_ne_zero 2 (hv i))
    rw [he i]
    field_simp [hv i]
  refine ⟨⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact hed i j
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact hed j i

/-- The local-permutation hypothesis follows from actual field equations. -/
theorem not_free (σ : E →+* E) (δ : E)
    (hσ : ∀ x, σ (σ x)=x^4) (hbase : ∀ a : F, σ (scalar a)=scalar (a^2))
    (hδ : ∀ z : E, z^3 ≠ δ*σ δ)
    (m : ℕ) (hcard : Fintype.card F=2^m) (hE : Fintype.card E=Fintype.card F^2)
    (hq : 6≤Fintype.card F) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) σ δ) := by
  intro hf
  apply hf
  apply exists_copy σ δ hbase _ m hcard hE hq
  intro u
  have hi := pencil_injective σ δ hσ hbase hδ u
  exact ⟨hi,Finite.surjective_of_injective hi⟩


/-- The intended odd-degree binary fields fail for EVERY noncube parameter. -/
theorem binary_odd_not_free (k : ℕ) (hk : 1≤k)
    (hF : Fintype.card F=2^(2*k+1)) (hE : Fintype.card E=(2^(2*k+1))^2)
    (δ : E) (hδ : ∀ z : E, z^3≠δ) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := F) (iterateFrobenius E 2 (2*k+2)) δ) := by
  let σ := iterateFrobenius E 2 (2*k+2)
  have hp (x : E) : σ x=x^(2*(2^(2*k+1))) := by
    simp only [σ,iterateFrobenius_def]
    congr 1
    rw [show 2*k+2=(2*k+1)+1 by omega,pow_succ]
    ring
  have hq3 : (2^(2*k+1))%3=2 := by
    rw [pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  apply not_free σ δ (Erdos714SidonGluing.sigma_square_of_power σ _ hE hp) _
    (Erdos714SidonGluing.noncube_product σ _ hq3 hp δ hδ) (2*k+1) hF _ _
  · intro a
    rw [hp,←map_pow,show 2*(2^(2*k+1))=(2^(2*k+1))*2 by ring,
      pow_mul,←hF,FiniteField.pow_card]
  · simpa only [hF] using hE
  · rw [hF]
    have h := Nat.pow_le_pow_right (n := 2) (by decide : 0<2) (show 3≤2*k+1 by omega)
    norm_num at h
    omega

omit [CharP F 2] [CharP E 2] [Fintype F] in
lemma exists_noncube (hcard : Fintype.card E%3=1) :
    ∃ δ : E, ∀ z : E, z^3 ≠ δ := by
  have hdvd : 3 ∣ Fintype.card Eˣ := by rw [Fintype.card_units]; omega
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := Eˣ) 3 hdvd
  have hr : IsPrimitiveRoot (u:E) 3 := by
    apply IsPrimitiveRoot.coe_units_iff.mpr
    simpa only [hu] using IsPrimitiveRoot.orderOf u
  by_contra! hs
  have hi : Function.Injective (fun z : E => z^3) := Finite.injective_iff_surjective.mpr hs
  exact hr.ne_one (by decide) (hi (by simpa using hr.pow_eq_one))

section ConcreteFamily
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev Base (k : ℕ) := GaloisField 2 (2*k+3)
abbrev Ext (k : ℕ) := FiniteField.Extension (Base k) 2 2
local instance (k : ℕ) : Fintype (Base k) := Fintype.ofFinite _
local instance (k : ℕ) : Fintype (Ext k) := Fintype.ofFinite _
local instance (k : ℕ) : CharP (Ext k) 2 :=
  charP_of_injective_algebraMap (algebraMap (Base k) (Ext k)).injective 2

def familyGraph (k : ℕ) (δ : Ext k) : SimpleGraph
    (Vertex (Base k) (Ext k) ⊕ Vertex (Base k) (Ext k)) :=
  graph (iterateFrobenius (Ext k) 2 (2*k+4)) δ

lemma family_base_card (k : ℕ) : Fintype.card (Base k)=2^(2*k+3) := by
  rw [Fintype.card_eq_nat_card,GaloisField.card 2 _ (by omega)]

lemma family_ext_card (k : ℕ) : Fintype.card (Ext k)=(2^(2*k+3))^2 := by
  rw [Module.card_eq_pow_finrank (K := Base k),FiniteField.finrank_extension,
    family_base_card]

theorem family_not_free (k : ℕ) (δ : Ext k) (hδ : ∀ z : Ext k, z^3≠δ) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (familyGraph k δ) := by
  have h := binary_odd_not_free (k+1) (by omega)
    (show Fintype.card (Base k)=2^(2*(k+1)+1) by
      convert family_base_card k using 1)
    (show Fintype.card (Ext k)=(2^(2*(k+1)+1))^2 by
      convert family_ext_card k using 1) δ hδ
  convert h using 1

/-- Noncube parameters actually exist in every member of the family. -/
theorem family_has_parameter (k : ℕ) :
    ∃ δ : Ext k, (∀ z : Ext k, z^3≠δ) ∧
      ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (familyGraph k δ) := by
  obtain ⟨δ,hδ⟩ := exists_noncube (E := Ext k) (show Fintype.card (Ext k)%3=1 from by
    rw [family_ext_card,pow_add,pow_mul]
    norm_num [Nat.pow_mod,Nat.mul_mod])
  exact ⟨δ,hδ,family_not_free k δ hδ⟩
end ConcreteFamily

#print axioms pencil_injective
#print axioms synchronized
#print axioms choose_tags
#print axioms exists_copy
#print axioms not_free
#print axioms binary_odd_not_free
#print axioms exists_noncube
#print axioms family_not_free
#print axioms family_has_parameter
end Erdos714BinarySemilinearPencil
