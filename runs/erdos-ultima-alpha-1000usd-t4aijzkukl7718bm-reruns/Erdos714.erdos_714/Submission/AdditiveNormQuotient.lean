import FormalConjecturesUtil

/-!
An obstruction to the additive quotient of the quadratic norm construction.
This file does not prove or disprove the balanced Zarankiewicz conjecture.
-/

noncomputable section
open SimpleGraph Classical

namespace Erdos714AdditiveNormQuotient

variable {F : Type*} [Field F]

abbrev Point (K : Subfield F) := (F ⧸ K.toAddSubgroup) × F
abbrev Vertex (K : Subfield F) := Point K × Fˣ

def relation (K : Subfield F) (ν : F) (x y : Vertex K) : Prop :=
  ∃ t : F, QuotientAddGroup.mk' K.toAddSubgroup t = x.1.1 + y.1.1 ∧
    t^2 - ν*(x.1.2 + y.1.2)^2 = (x.2 : F)*(y.2 : F)

def graph (K : Subfield F) (ν : F) : SimpleGraph (Vertex K ⊕ Vertex K) where
  Adj x y := match x,y with
    | .inl u, .inr v => relation K ν u v
    | .inr v, .inl u => relation K ν u v
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

def rowCoordinate (D h : F) : F := (D-h^2)/(2*h)

lemma row_equation (D h : F) (h₂ : (2 : F) ≠ 0) (hh : h ≠ 0) :
    2*h*rowCoordinate D h + h^2 = D := by
  dsimp [rowCoordinate]
  field_simp
  ring

lemma rowCoordinate_injective (K : Subfield F) {D : F} (hD : D ∉ K)
    (h₂ : (2 : F) ≠ 0) :
    Function.Injective (fun h : Kˣ =>
      QuotientAddGroup.mk' K.toAddSubgroup (rowCoordinate D (h : K))) := by
  intro h k he
  by_contra hne
  have hh : ((h : K) : F) ≠ 0 := by exact_mod_cast h.ne_zero
  have hk : ((k : K) : F) ≠ 0 := by exact_mod_cast k.ne_zero
  have hhk : ((h : K) : F) ≠ ((k : K) : F) := by
    intro heq
    apply hne
    apply Units.ext
    exact Subtype.ext heq
  have hd : rowCoordinate D (h : K) - rowCoordinate D (k : K) ∈ K :=
    QuotientAddGroup.eq_iff_sub_mem.mp he
  have hcoeff : ((k : K) : F) - ((h : K) : F) ≠ 0 := sub_ne_zero.mpr hhk.symm
  have hformula : D =
      (2*(h : K)*(k : K)*(rowCoordinate D (h : K)-rowCoordinate D (k : K)) -
        (h : K)*(k : K)*((k : K)-(h : K))) / ((k : K)-(h : K)) := by
    dsimp [rowCoordinate]
    field_simp
    ring
  apply hD
  rw [hformula]
  exact K.div_mem
    (K.sub_mem (K.mul_mem (K.mul_mem (K.mul_mem (by norm_num) (h : K).property)
      (k : K).property) hd)
      (K.mul_mem (K.mul_mem (h : K).property (k : K).property)
        (K.sub_mem (k : K).property (h : K).property)))
    (K.sub_mem (k : K).property (h : K).property)

lemma weight_ne_zero {ν : F} (hν : ¬ IsSquare ν) (u : F) : u^2 - ν ≠ 0 := by
  intro h
  apply hν
  exact ⟨u, by linear_combination -h⟩

def row (K : Subfield F) (ν D : F) (hν : ¬ IsSquare ν) (h : Kˣ) : Vertex K :=
  ((QuotientAddGroup.mk' K.toAddSubgroup (rowCoordinate D (h : K)),0),
    Units.mk0 _ (weight_ne_zero hν (rowCoordinate D (h : K))))

def column (K : Subfield F) (y : F) : Vertex K := ((0,y),1)

lemma row_injective (K : Subfield F) (ν D : F) (hν : ¬ IsSquare ν)
    (hD : D ∉ K) (h₂ : (2 : F) ≠ 0) : Function.Injective (row K ν D hν) := by
  intro h k he
  exact rowCoordinate_injective K hD h₂ (congrArg (fun x : Vertex K => x.1.1) he)

lemma column_injective (K : Subfield F) : Function.Injective (column K) := by
  intro h k he
  exact congrArg (fun x : Vertex K => x.1.2) he

lemma edge_one (K : Subfield F) (ν D : F) (hν : ¬ IsSquare ν) (h : Kˣ)
    (y : F) (hy : y^2 = 1) : relation K ν (row K ν D hν h) (column K y) := by
  refine ⟨rowCoordinate D (h : K), by simp [row,column], ?_⟩
  simp [row, column, hy]

lemma edge_lambda (K : Subfield F) (ν ℓ : F) (hν : ¬ IsSquare ν)
    (h₂ : (2 : F) ≠ 0) (h : Kˣ) (y : F) (hy : y^2 = ℓ^2) :
    relation K ν (row K ν (ν*(ℓ^2-1)) hν h) (column K y) := by
  let u : F := rowCoordinate (ν*(ℓ^2-1)) (h : K)
  have hh : ((h : K) : F) ≠ 0 := by exact_mod_cast h.ne_zero
  have he := row_equation (F := F) (ν*(ℓ^2-1)) (h : K) h₂ hh
  refine ⟨u + (h : K), ?_, ?_⟩
  · change QuotientAddGroup.mk' K.toAddSubgroup (u + (h : K)) =
      QuotientAddGroup.mk' K.toAddSubgroup u + 0
    rw [add_zero]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simp
  · change (u + (h : K))^2 - ν*(0+y)^2 = (u^2-ν)*1
    rw [zero_add,hy]
    change 2*(h : K)*u + (h : K)^2 = ν*(ℓ^2-1) at he
    linear_combination he

lemma four_columns_injective (K : Subfield F) {ν ℓ : F}
    (hD : ν*(ℓ^2-1) ∉ K) (hℓ : ℓ ≠ 0) (h₂ : (2 : F) ≠ 0) :
    Function.Injective (fun j : Fin 4 => (![1,-1,ℓ,-ℓ] : Fin 4 → F) j) := by
  have h1 : ℓ ≠ 1 := by intro h; apply hD; simp [h]
  have hn1 : ℓ ≠ -1 := by intro h; apply hD; simp [h]
  have h1n1 : (1 : F) ≠ -1 := by intro h; apply h₂; linear_combination h
  have hlnl : ℓ ≠ -ℓ := by
    intro h
    apply mul_ne_zero h₂ hℓ
    linear_combination h
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [neg_eq_iff_eq_neg, eq_comm]

/-- The odd-characteristic quotient host contains a biclique with all nonzero
subfield parameters on the left and four explicit columns on the right. -/
def copy (K : Subfield F) (ν ℓ : F) (hν : ¬ IsSquare ν)
    (hD : ν*(ℓ^2-1) ∉ K) (hℓ : ℓ ≠ 0) (h₂ : (2 : F) ≠ 0)
    {r : ℕ} (e : Fin r ↪ Kˣ) :
    Copy (completeBipartiteGraph (Fin r) (Fin 4)) (graph K ν) := by
  let L : Fin r ↪ Vertex K :=
    ⟨fun i => row K ν (ν*(ℓ^2-1)) hν (e i),
      (row_injective K ν _ hν hD h₂).comp e.injective⟩
  let R : Fin 4 ↪ Vertex K :=
    ⟨fun j => column K ((![1,-1,ℓ,-ℓ] : Fin 4 → F) j),
      (column_injective K).comp (four_columns_injective K hD hℓ h₂)⟩
  have he (i : Fin r) (j : Fin 4) : relation K ν (L i) (R j) := by
    change relation K ν (row K ν (ν*(ℓ^2-1)) hν (e i))
      (column K ((![1,-1,ℓ,-ℓ] : Fin 4 → F) j))
    fin_cases j
    · exact edge_one K ν _ hν (e i) 1 (by simp)
    · exact edge_one K ν _ hν (e i) (-1) (by simp)
    · exact edge_lambda K ν ℓ hν h₂ (e i) ℓ rfl
    · exact edge_lambda K ν ℓ hν h₂ (e i) (-ℓ) (by simp)
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl k => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inr k => simp at h
    | inl i => exact he i j


/-- Each bad parameter is in a quadratic fiber over the subfield. -/
theorem bad_parameters_card [Fintype F] (K : Subfield F) [Fintype K]
    {ν : F} (hν : ν ≠ 0) :
    (Finset.univ.filter (fun ℓ : F => ν*(ℓ^2-1) ∈ K)).card ≤ 2*Fintype.card K := by
  let S := Finset.univ.filter (fun ℓ : F => ν*(ℓ^2-1) ∈ K)
  let T := Finset.univ.image (fun a : K => (a : F))
  have hT : T.card = Fintype.card K := by
    exact (Finset.card_image_of_injective _ Subtype.val_injective).trans Finset.card_univ
  rw [← hT]
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun ℓ : F => ν*(ℓ^2-1)) (s := S) (t := T) ?_ 2 ?_
  · intro ℓ hℓ
    exact Finset.mem_image.mpr ⟨⟨_, (Finset.mem_filter.mp hℓ).2⟩, Finset.mem_univ _, rfl⟩
  · intro b _
    let U := S.filter (fun ℓ : F => ν*(ℓ^2-1) = b)
    by_cases hu : U.Nonempty
    · obtain ⟨x,hx⟩ := hu
      apply (Finset.card_le_card (show U ⊆ {x,-x} from ?_)).trans Finset.card_le_two
      intro y hy
      have he : ν*(y^2-1) = ν*(x^2-1) :=
        (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hx).2.symm
      have hs : y^2 = x^2 := sub_left_inj.mp (mul_left_cancel₀ hν he)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        sq_eq_sq_iff_eq_or_eq_neg.mp hs
    · change U.card ≤ 2
      simp only [Finset.not_nonempty_iff_eq_empty.mp hu, Finset.card_empty, Nat.zero_le]

/-- A nonzero good parameter exists whenever the ambient field is more than
 twice as large as the subfield, with room to exclude zero. -/
theorem exists_parameter [Fintype F] (K : Subfield F) [Fintype K]
    {ν : F} (hν : ν ≠ 0) (hcard : 2*Fintype.card K + 1 < Fintype.card F) :
    ∃ ℓ : F, ℓ ≠ 0 ∧ ν*(ℓ^2-1) ∉ K := by
  let S := Finset.univ.filter (fun ℓ : F => ν*(ℓ^2-1) ∈ K)
  have hb : S.card ≤ 2*Fintype.card K := bad_parameters_card K hν
  have hs : (insert 0 S).card < (Finset.univ : Finset F).card := by
    have hi := Finset.card_insert_le 0 S
    simp only [Finset.card_univ]
    omega
  obtain ⟨ℓ,_,hℓ⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  refine ⟨ℓ, ?_⟩
  simpa only [Finset.mem_insert, S, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] using hℓ

/-- In particular the proposed cubic-field/subfield quotient is not free. -/
theorem not_free [Fintype F] (K : Subfield F) [Fintype K]
    {ν : F} (hν : ¬ IsSquare ν) (h₂ : (2 : F) ≠ 0)
    (hK : 5 ≤ Fintype.card K) (hcard : 2*Fintype.card K + 1 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph K ν) := by
  have hn : ν ≠ 0 := by intro h; exact hν (by simp [h])
  obtain ⟨ℓ,hℓ,hD⟩ := exists_parameter K hn hcard
  have hc : Fintype.card (Fin 4) ≤ Fintype.card Kˣ := by
    rw [Fintype.card_fin, Fintype.card_units]
    omega
  let e : Fin 4 ↪ Kˣ := (Fin.castLEEmb (by simpa using hc)).trans (Fintype.equivFin Kˣ).symm.toEmbedding
  intro hf
  exact hf ⟨copy K ν ℓ hν hD hℓ h₂ e⟩

/-- The uniform obstruction at the intended seventh-quarter exponent scale. -/
theorem cubic_not_free [Fintype F] (K : Subfield F) [Fintype K]
    {ν : F} (hν : ¬ IsSquare ν) (h₂ : (2 : F) ≠ 0)
    (hK : 5 ≤ Fintype.card K) (hcard : Fintype.card F = Fintype.card K ^ 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph K ν) := by
  apply not_free K hν h₂ hK
  rw [hcard]
  nlinarith [sq_nonneg (Fintype.card K - 2 : ℤ)]

end Erdos714AdditiveNormQuotient


#print axioms Erdos714AdditiveNormQuotient.rowCoordinate_injective
#print axioms Erdos714AdditiveNormQuotient.copy
#print axioms Erdos714AdditiveNormQuotient.bad_parameters_card
#print axioms Erdos714AdditiveNormQuotient.exists_parameter
#print axioms Erdos714AdditiveNormQuotient.cubic_not_free
