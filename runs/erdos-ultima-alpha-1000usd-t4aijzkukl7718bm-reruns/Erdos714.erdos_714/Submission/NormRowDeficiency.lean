import Submission.EqualRowCubicNorm
import Submission.OddCubicNormGrid

/-!
A co-large weight row cannot repair the cubic norm construction in odd
characteristic. Rescaling moves a checked norm rectangle off a prescribed
small exceptional set. This is not a disproof of Erdős 714.
-/

noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714NormRowDeficiency
variable {F : Type*} [Field F] [Fintype F]

/-- A single nonzero scaling avoids a small exceptional set at every one of
finitely many nonzero values. Repeated values are allowed. -/
theorem avoid_scaled_values {I : Type*} [Fintype I] (v : I → F)
    (hv : ∀ i, v i ≠ 0) (B : Finset F)
    (hsize : Fintype.card I*B.card+1 < Fintype.card F) :
    ∃ c : F, c ≠ 0 ∧ ∀ i, c*v i ∉ B := by
  let T (i : I) := B.image (fun z => z/v i)
  let S := insert 0 (univ.biUnion T)
  have hS : S.card ≤ Fintype.card I*B.card+1 := by
    calc
      _ ≤ (univ.biUnion T).card+1 := card_insert_le _ _
      _ ≤ (∑ i : I, (T i).card)+1 := Nat.add_le_add_right card_biUnion_le _
      _ ≤ (∑ _i : I, B.card)+1 := Nat.add_le_add_right
        (sum_le_sum (fun i _ => card_image_le)) _
      _ = _ := by simp
  obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card
    (show S.card < (univ : Finset F).card by simpa using hS.trans_lt hsize)
  refine ⟨c,fun h => hc (by simp [S,h]),?_⟩
  intro i hi
  apply hc
  apply mem_insert_of_mem
  apply mem_biUnion.mpr
  refine ⟨i,mem_univ _,mem_image.mpr ⟨c*v i,hi,?_⟩⟩
  exact mul_div_cancel_right₀ c (hv i)

variable {E A D : Type*} [Field E] [Algebra F E] [Fintype E]

/-- An actual finite norm rectangle transfers to an arbitrary weight law
whose selected row omits only a sufficiently small exceptional set. -/
theorem copy_of_small_missing (l r : Fin 4 ↪ E) (v : Fin 4 → F)
    (hv : ∀ j, v j ≠ 0) (hedge : ∀ i j, Algebra.norm F (l i+r j)=v j)
    (W : A → D → F) (a : A) (B : Finset F)
    (hsize : 4*B.card+1 < Fintype.card F)
    (hrow : ∀ w : F, w ≠ 0 → w ∉ B → ∃ b : D, W a b=w) :
    Nonempty ((completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714EqualRowCubicNorm.graph (E := E) W)) := by
  obtain ⟨c,hc,havoid⟩ := avoid_scaled_values v hv B (by simpa using hsize)
  obtain ⟨z,hz⟩ := FiniteField.norm_surjective F E c
  have hz0 : z ≠ 0 := by
    intro h
    have he : c=0 := by simpa [h] using hz.symm
    exact hc he
  choose b hb using fun j : Fin 4 => hrow (c*v j) (mul_ne_zero hc (hv j)) (havoid j)
  let L : Fin 4 ↪ E × A := ⟨fun i => (z*l i,a),by
    intro i j h
    exact l.injective (mul_left_cancel₀ hz0 (congrArg Prod.fst h))⟩
  let R : Fin 4 ↪ E × D := ⟨fun j => (z*r j,b j),by
    intro i j h
    exact r.injective (mul_left_cancel₀ hz0 (congrArg Prod.fst h))⟩
  have he (i j : Fin 4) : (Erdos714EqualRowCubicNorm.graph (E := E) W).Adj
      (.inl (L i)) (.inr (R j)) := by
    change Algebra.norm F (z*l i+z*r j)=W a (b j) ∧ W a (b j) ≠ 0
    rw [←mul_add,map_mul,hz,hedge,hb]
    exact ⟨rfl,mul_ne_zero hc (hv j)⟩
  refine ⟨⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j => exact he i j
  | inr i =>
    cases y with
    | inl j => exact he j i
    | inr j => simp at hxy

/-- Combine the already verified ternary and nonternary odd-field grids.
The last four norms depend only on the column, not on the row. -/
theorem odd_equal_row_template (hq : 9 < Fintype.card F)
    (hdim : Module.finrank F E=3) (h2 : (2 : F) ≠ 0) :
    ∃ l r : Fin 4 ↪ E, ∃ v : Fin 4 → F,
      (∀ j, v j ≠ 0) ∧ ∀ i j, Algebra.norm F (l i+r j)=v j := by
  by_cases h3 : (3 : F)=0
  · letI : CharP F 3 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 3)).mpr h3
    obtain ⟨l,r,hn,he⟩ := Erdos714EqualRowCubicNorm.exists_equal_row_rectangle hq hdim
    exact ⟨l,r,fun j => Algebra.norm F (r j),hn,he⟩
  · obtain ⟨d,hd,b,l,r,hl,he⟩ := Erdos714OddCubicNormGrid.exists_planar_grid hdim h2 h3
    refine ⟨r,l,![d,d,-d,-d],?_,?_⟩
    · intro j
      fin_cases j <;> simpa using (show d ≠ 0 from hd)
    · intro i j
      simpa only [add_comm] using he j i

/-- A nonlinear and field-dependent weight law is allowed. Only one row
needs to miss at most the explicitly bounded exceptional set. -/
theorem odd_not_free_of_small_missing (hq : 9 < Fintype.card F)
    (hdim : Module.finrank F E=3) (h2 : (2 : F) ≠ 0)
    (W : A → D → F) (a : A) (B : Finset F)
    (hsize : 4*B.card+1 < Fintype.card F)
    (hrow : ∀ w : F, w ≠ 0 → w ∉ B → ∃ b : D, W a b=w) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714EqualRowCubicNorm.graph (E := E) W) := by
  obtain ⟨l,r,v,hv,he⟩ := odd_equal_row_template hq hdim h2
  exact fun hf => hf (copy_of_small_missing l r v hv he W a B hsize hrow)

/-- The shifted multiplicative law uses units on BOTH sides, and even deletes
zero-norm edges. Thus zero scalar labels are not the source of the obstruction. -/
def offsetGraph (δ : F) : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ)) :=
  Erdos714EqualRowCubicNorm.graph (fun a b : Fˣ => (a : F)*(b : F)+δ)

omit [Fintype F] [Fintype E] in
@[simp] lemma offset_adj (δ : F) (x y : E) (a b : Fˣ) :
    (offsetGraph (E := E) δ).Adj (.inl (x,a)) (.inr (y,b)) ↔
      Algebra.norm F (x+y)=(a : F)*(b : F)+δ ∧ (a : F)*(b : F)+δ ≠ 0 := Iff.rfl

/-- Adding any constant to the product of the scalar weights cannot repair
ordinary cubic norm incidence in any odd characteristic once q>9. -/
theorem offset_not_free (hq : 9 < Fintype.card F)
    (hdim : Module.finrank F E=3) (h2 : (2 : F) ≠ 0) (δ : F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (offsetGraph (E := E) δ) := by
  apply odd_not_free_of_small_missing hq hdim h2
    (fun a b : Fˣ => (a : F)*(b : F)+δ) 1 {δ} (by simp; omega)
  intro w hw hwδ
  have hn : w-δ ≠ 0 := sub_ne_zero.mpr (by simpa using hwδ)
  refine ⟨Units.mk0 (w-δ) hn,?_⟩
  simp

#print axioms avoid_scaled_values
#print axioms copy_of_small_missing
#print axioms odd_equal_row_template
#print axioms odd_not_free_of_small_missing
#print axioms offset_adj
#print axioms offset_not_free
end Erdos714NormRowDeficiency
