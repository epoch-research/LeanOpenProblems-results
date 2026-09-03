import Submission.CubicQuarticPlane
import Submission.CubicTraceNormPlane
import Submission.RationalNormDifference

/-!
The actual fourth-power norm graph over a nine-element base field contains K46,
even though its connection set has no affine F3-plane. This is an obstruction
to one proposed construction, not a disproof of Erdős 714.
-/
noncomputable section
open Polynomial SimpleGraph Classical
set_option maxHeartbeats 3000000
namespace Erdos714CubicQuarticNine
variable {F E : Type*} [Field F] [CharP F 3] [Field E] [Algebra F E]

def p : F[X] := X^3-X^2-X-1
omit [CharP F 3] in
lemma p_degree : (p (F := F)).natDegree = 3 := by unfold p; compute_degree!

lemma p_irreducible [Fintype F] (hq : Fintype.card F = 9) :
    Irreducible (p (F := F)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [p_degree]
  · intro x hx
    have hp : x^3-x^2-x-1 = 0 := by simpa [p,Polynomial.IsRoot] using hx
    have h9 : x^9-x = 0 := sub_eq_zero.mpr (hq ▸ FiniteField.pow_card x)
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    have hx2 : x^2 = 0 := by
      linear_combination (x^6+x^5-x^4+x^3+x^2+x)*hp-h9+(x^7+x^3+x^2)*h3
    have hx0 := eq_zero_of_pow_eq_zero hx2
    simp [hx0] at hp

lemma two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h1 : (1 : F) = 0 := by linear_combination h3-h
  exact one_ne_zero h1

lemma sqrt_neg_one_distinct (w : F) (hw : w^2 = -1) :
    w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 ∧ (1 : F) ≠ -1 := by
  have hpm : (1 : F) ≠ -1 := by
    intro h
    exact two_ne_zero (by linear_combination h)
  refine ⟨?_,?_,?_,hpm⟩
  · intro h; simp [h] at hw
  · intro h; exact hpm (by simpa [h] using hw)
  · intro h; exact hpm (by simpa [h] using hw)

def rowPoint (w : F) : Fin 4 → F := ![0,1,-1,w-1]
def rowWeight : Fin 4 → F := ![1,0,0,-1]
def colWeight (w : F) : Bool → F := fun b => if b then w else -w

lemma row_injective (w : F) (hw : w^2 = -1) : Function.Injective (rowPoint w) := by
  obtain ⟨hw0,hw1,hwm,hpm⟩ := sqrt_neg_one_distinct w hw
  have hz0 : w-1 ≠ 0 := sub_ne_zero.mpr hw1
  have hz1 : w-1 ≠ 1 := by
    intro h
    apply hwm
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    linear_combination h+h3
  have hzm : w-1 ≠ -1 := by
    intro h
    apply hw0
    linear_combination h
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [rowPoint,Ne.symm hz0,Ne.symm hz1,Ne.symm hzm,Ne.symm hpm]

lemma col_weight_injective (w : F) (hw : w^2 = -1) : Function.Injective (colWeight w) := by
  have hw0 := (sqrt_neg_one_distinct w hw).1
  have hpm : w ≠ -w := by
    intro h
    have hh : 2*w = 0 := by linear_combination h
    exact (mul_ne_zero two_ne_zero hw0) hh
  intro i j hij
  cases i <;> cases j <;> simp_all [colWeight,Ne.symm hpm]

lemma fourth_sum (a w : F) (ha : a^3 = a) (hw : w^2 = -1) :
    (a+w)^4 = a^2+1 := by
  have hw3 : w^3 = -w := by linear_combination w*hw
  rw [show (4 : ℕ) = 3+1 from rfl,pow_succ,add_pow_char,ha,hw3]
  linear_combination -hw

lemma profile (w : F) (hw : w^2 = -1) (i : Fin 4) (b : Bool) :
    (p (F := F)).eval (rowPoint w i) = (rowWeight i+colWeight w b)^4 := by
  have hs : (colWeight w b)^2 = -1 := by
    cases b <;> simpa [colWeight] using hw
  have ha : (rowWeight (F := F) i)^3 = rowWeight (F := F) i := by
    fin_cases i <;> norm_num [rowWeight]
  rw [fourth_sum _ _ ha hs]
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  fin_cases i
  · norm_num [p,rowPoint,rowWeight]
    linear_combination -h3
  · norm_num [p,rowPoint,rowWeight]
    linear_combination -h3
  · norm_num [p,rowPoint,rowWeight]
    linear_combination -h3
  · norm_num [p,rowPoint,rowWeight]
    linear_combination (w-4)*hw+w*h3

lemma weight_sum_nonzero (w : F) (hw : w^2 = -1) (i : Fin 4) (b : Bool) :
    rowWeight i+colWeight w b ≠ 0 := by
  have hs : (colWeight w b)^2 = -1 := by
    cases b <;> simpa [colWeight] using hw
  have ha : (rowWeight (F := F) i)^3 = rowWeight (F := F) i := by
    fin_cases i <;> norm_num [rowWeight]
  intro hz
  have hf := fourth_sum (rowWeight i) (colWeight w b) ha hs
  rw [hz,zero_pow (by decide : 4 ≠ 0)] at hf
  fin_cases i <;> norm_num [rowWeight] at hf
  all_goals exact two_ne_zero hf.symm

/-- We even delete all zero-weight-sum edges from the candidate. -/
def relation (x y : E × F) : Prop :=
  x.2+y.2 ≠ 0 ∧ Algebra.norm F (x.1+y.1) = (x.2+y.2)^4

def graph : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj x y := match x,y with
    | .inl x,.inr y => relation x y
    | .inr y,.inl x => relation x y
    | _,_ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x; cases x <;> simp

/-- Both groups of three conjugate columns are retained, with distinct weights. -/
def powerBasis_copy (w : F) (hw : w^2 = -1)
    (pb : PowerBasis F E) (hmin : minpoly F pb.gen = p)
    (sigma : Fin 3 → E ≃ₐ[F] E) (hsigma : Function.Injective sigma) :
    (completeBipartiteGraph (Fin 4) (Bool × Fin 3)).Copy (graph (F := F) (E := E)) := by
  letI : FiniteDimensional F E := pb.finite
  have hinj : Function.Injective (fun j => sigma j pb.gen) := by
    intro i j hij
    apply hsigma
    ext z
    exact DFunLike.congr_fun (pb.algHom_ext (f := (sigma i).toAlgHom)
      (g := (sigma j).toAlgHom) hij) z
  have hn (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x-sigma j pb.gen) = (p (F := F)).eval x := by
    rw [show algebraMap F E x-sigma j pb.gen = sigma j (algebraMap F E x-pb.gen) by simp]
    rw [Algebra.norm_eq_of_algEquiv,Erdos714QuarticDiagonal.norm_scalar_sub_gen,hmin]
  let L : Fin 4 → E × F := fun i => (algebraMap F E (rowPoint w i),rowWeight i)
  let R : Bool × Fin 3 → E × F := fun j => (-sigma j.2 pb.gen,colWeight w j.1)
  have hL : Function.Injective L := by
    intro i j h
    exact row_injective w hw ((algebraMap F E).injective (congrArg Prod.fst h))
  have hR : Function.Injective R := by
    intro i j h
    have hfirst := hinj (neg_injective (congrArg Prod.fst h))
    have hsecond := col_weight_injective w hw (congrArg Prod.snd h)
    exact Prod.ext hsecond hfirst
  have hedge (i : Fin 4) (j : Bool × Fin 3) : relation (L i) (R j) := by
    refine ⟨weight_sum_nonzero w hw i j.1,?_⟩
    change Algebra.norm F (algebraMap F E (rowPoint w i)+ -sigma j.2 pb.gen) = _
    rw [← sub_eq_add_neg,hn,profile w hw]
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact hedge i j
  | inr i => cases y with
    | inl j => exact hedge j i
    | inr j => simp at hxy

omit [CharP F 3] in
lemma p_eq_pencil : p (F := F) = Erdos714CubicTraceNormPlane.pencil 1 (-1) 1 := by
  simp [p,Erdos714CubicTraceNormPlane.pencil,sub_eq_add_neg]

lemma exists_powerBasis [Fintype F] [Fintype E]
    (hq : Fintype.card F = 9) (hdim : Module.finrank F E = 3) :
    ∃ pb : PowerBasis F E, pb.dim = 3 ∧ minpoly F pb.gen = p := by
  have hp : Irreducible (Erdos714CubicTraceNormPlane.pencil (1 : F) (-1) 1) := by
    rw [← p_eq_pencil]
    exact p_irreducible hq
  obtain ⟨pb,hpb,hmin⟩ := Erdos714CubicTraceNormPlane.exists_powerBasis hdim 1 (-1) 1 hp
  exact ⟨pb,hpb,hmin.trans p_eq_pencil.symm⟩

/-- Every cubic extension of every nine-element field has this actual K46. -/
theorem not_free_six [Fintype F] [Fintype E]
    (hq : Fintype.card F = 9) (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 6)).Free (graph (F := F) (E := E)) := by
  have hs : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by omega)
  obtain ⟨w,hw⟩ := hs
  have hw' : w^2 = -1 := by simpa only [pow_two] using hw.symm
  obtain ⟨pb,hpb,hmin⟩ := exists_powerBasis hq hdim
  letI : FiniteDimensional F E := pb.finite
  letI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hcard : Fintype.card (E ≃ₐ[F] E) = 3 := by
    rw [← Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank,hdim]
  let sigma : Fin 3 ≃ (E ≃ₐ[F] E) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let e : Fin 6 ≃ Bool × Fin 3 := Fintype.equivOfCardEq (by simp)
  intro hfree
  exact hfree ⟨(powerBasis_copy w hw' pb hmin sigma sigma.injective).comp
    (Erdos714RationalNormDifference.bicliqueCopy (Function.Embedding.refl _) e.toEmbedding)⟩

theorem not_free_four [Fintype F] [Fintype E]
    (hq : Fintype.card F = 9) (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  intro hfree
  apply not_free_six hq hdim
  rintro ⟨f⟩
  exact hfree ⟨f.comp (Erdos714RationalNormDifference.bicliqueCopy
    (Function.Embedding.refl _) (Fin.castLEEmb (by decide : 4 ≤ 6)))⟩

open Erdos714CubicQuarticPlane (sample)

/-- A verified separation between a local plane diagnostic and actual biclique freeness. -/
theorem plane_free_but_not_biclique_free [Fintype F] [Fintype E]
    (hq : Fintype.card F = 9) (hdim : Module.finrank F E = 3) :
    (∀ (x u v : E) (a b c : F),
      (∀ i j : Fin 3, Algebra.norm F (x+sample i*u+sample j*v) =
        (a+sample (E := F) i*b+sample (E := F) j*c)^4) →
      ¬ Function.Injective (fun p : Fin 3 × Fin 3 =>
        (x+sample p.1*u+sample p.2*v,
         a+sample (E := F) p.1*b+sample (E := F) p.2*c))) ∧
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  letI : CharP E 3 := CharP.of_ringHom_of_ne_zero (algebraMap F E) 3 (by decide)
  exact ⟨fun x u v a b c h =>
    Erdos714CubicQuarticPlane.no_injective_actual_norm_grid hdim x u v a b c h,
    not_free_four hq hdim⟩

#print axioms p_irreducible
#print axioms powerBasis_copy
#print axioms not_free_six
#print axioms not_free_four
#print axioms plane_free_but_not_biclique_free

end Erdos714CubicQuarticNine
