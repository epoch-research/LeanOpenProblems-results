import Submission.RationalNormDifference

/-!
A square-point counterexample to the rational norm-difference candidate over F11.
This does not settle the balanced Zarankiewicz conjecture.
-/
noncomputable section
open Polynomial SimpleGraph Classical
set_option maxHeartbeats 4000000
namespace Erdos714RationalNormSquare
open Erdos714RationalNormDifference (relation norm_neg norm_scalar_add_gen bicliqueCopy)
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev F := ZMod 11

def p : F[X] := X^3+3*X+2
lemma p_monic : p.Monic := by unfold p; monicity <;> norm_num
lemma p_degree : p.natDegree = 3 := by unfold p; compute_degree!
lemma p_irreducible : Irreducible p := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [p_degree]
  · intro x
    change p.eval x ≠ 0
    fin_cases x <;> norm_num [p] <;> decide

variable {E : Type*} [Field E] [Algebra F E]

def squareRelation (x y : E × F) : Prop := relation x y ∧ IsSquare x.1 ∧ IsSquare y.1

def graph : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj x y := match x,y with
    | .inl x,.inr y => squareRelation x y
    | .inr y,.inl x => squareRelation x y
    | _,_ => False
  symm := by intro x y h; cases x <;> cases y <;> exact h
  loopless := by intro x; cases x <;> simp

lemma eleven_zero : (11 : E) = 0 := by
  calc
    (11 : E) = algebraMap F E (11 : F) := (map_ofNat _ 11).symm
    _ = 0 := by rw [show (11 : F) = 0 by decide, map_zero]

lemma root_square (z : E) (hz : z^3+3*z+2 = 0) : IsSquare z := by
  refine ⟨6+2*z-z^2, ?_⟩
  have h11 := eleven_zero (E := E)
  linear_combination -(z-4)*hz-(-z^2+3*z+4)*h11

lemma affine_root_square (z : E) (hz : z^3+3*z+2 = 0) : IsSquare (5+7*z) := by
  refine ⟨-3*z+5*z^2, ?_⟩
  have h11 := eleven_zero (E := E)
  linear_combination -(25*z-30)*hz-(-6*z^2+3*z+5)*h11

def rowPoint : Fin 4 → F := ![1,3,4,5]
def rowWeight : Fin 4 → F := ![8,2,1,9]
def subValue : Bool → Fin 4 → F := fun b => if b then ![1,10,10,4] else ![6,5,1,10]
def addValue : Bool → Fin 4 → F := fun b => if b then ![5,1,2,2] else ![2,1,8,6]

lemma row_injective : Function.Injective rowPoint := by decide
lemma row_nonzero (i : Fin 4) : rowPoint i ≠ 0 := by fin_cases i <;> decide
lemma weight_nonzero (i : Fin 4) : rowWeight i ≠ 0 := by fin_cases i <;> decide
lemma row_square (i : Fin 4) : IsSquare (rowPoint i) := by
  fin_cases i
  · exact ⟨1,by decide⟩
  · exact ⟨5,by decide⟩
  · exact ⟨2,by decide⟩
  · exact ⟨4,by decide⟩
lemma sub_nonzero (b : Bool) (i : Fin 4) : subValue b i ≠ 0 := by cases b <;> fin_cases i <;> decide
lemma add_nonzero (b : Bool) (i : Fin 4) : addValue b i ≠ 0 := by cases b <;> fin_cases i <;> decide
lemma profile_equation (b : Bool) (i : Fin 4) :
    addValue b i = (rowWeight i - if b then 3 else 4)*subValue b i := by
  cases b <;> fin_cases i <;> decide

def powerBasis_copy (pb : PowerBasis F E) (hdim : pb.dim = 3) (hmin : minpoly F pb.gen = p)
    (sigma : Fin 3 → E ≃ₐ[F] E) (hsigma : Function.Injective sigma) :
    (completeBipartiteGraph (Fin 4) (Bool × Fin 3)).Copy (graph (E := E)) := by
  letI : FiniteDimensional F E := pb.finite
  have hdimE : Module.finrank F E = 3 := pb.finrank.trans hdim
  have hroot : pb.gen^3+3*pb.gen+2 = 0 := by
    have h := minpoly.aeval F pb.gen
    rw [hmin] at h
    simpa only [p,map_add,map_mul,map_pow,aeval_X,map_ofNat,map_zero] using h
  have hroot' (j : Fin 3) : (sigma j pb.gen)^3+3*sigma j pb.gen+2 = 0 := by
    have h := congrArg (sigma j) hroot
    simpa only [map_add,map_mul,map_pow,map_ofNat,map_zero] using h
  have hinj : Function.Injective (fun j => sigma j pb.gen) := by
    intro i j hij
    apply hsigma
    ext z
    exact DFunLike.congr_fun (pb.algHom_ext (f := (sigma i).toAlgHom)
      (g := (sigma j).toAlgHom) hij) z
  have hnsub (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x-sigma j pb.gen) = p.eval x := by
    rw [show algebraMap F E x-sigma j pb.gen = sigma j (algebraMap F E x-pb.gen) by simp]
    rw [Algebra.norm_eq_of_algEquiv,Erdos714QuarticDiagonal.norm_scalar_sub_gen,hmin]
  have hnadd (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x+sigma j pb.gen) = -p.eval (-x) := by
    rw [show algebraMap F E x+sigma j pb.gen = sigma j (algebraMap F E x+pb.gen) by simp]
    rw [Algebra.norm_eq_of_algEquiv,norm_scalar_add_gen pb hdim,hmin]
  have h7 : (7 : E) ≠ 0 := by
    have h := (_root_.map_ne_zero (algebraMap F E)).mpr (show (7 : F) ≠ 0 by decide)
    rwa [map_ofNat] at h
  have hnaffsub (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x-(5+7*sigma j pb.gen)) =
        (7 : F)^3*p.eval ((x-5)/7) := by
    have hh : algebraMap F E x-(5+7*sigma j pb.gen) =
        algebraMap F E 7 * (algebraMap F E ((x-5)/7)-sigma j pb.gen) := by
      simp only [map_div₀,map_sub,map_ofNat]
      field_simp
      ring
    rw [hh,map_mul,Algebra.norm_algebraMap,hdimE,hnsub]
  have hnaffadd (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x+(5+7*sigma j pb.gen)) =
        (7 : F)^3*(-p.eval (-((x+5)/7))) := by
    have hh : algebraMap F E x+(5+7*sigma j pb.gen) =
        algebraMap F E 7 * (algebraMap F E ((x+5)/7)+sigma j pb.gen) := by
      simp only [map_div₀,map_add,map_ofNat]
      field_simp
      ring
    rw [hh,map_mul,Algebra.norm_algebraMap,hdimE,hnadd]
  let L : Fin 4 → E × F := fun i => (algebraMap F E (rowPoint i),rowWeight i)
  let R : Bool × Fin 3 → E × F := fun j =>
    (if j.1 then 5+7*sigma j.2 pb.gen else sigma j.2 pb.gen,if j.1 then 3 else 4)
  have hL : Function.Injective L := by
    intro i j h
    exact row_injective ((algebraMap F E).injective (congrArg Prod.fst h))
  have hR : Function.Injective R := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have he := congrArg Prod.fst h
    have hw := congrArg Prod.snd h
    cases a <;> cases b
    · exact Prod.ext rfl (hinj he)
    · exact False.elim ((show (4 : F) ≠ 3 by decide) hw)
    · exact False.elim ((show (3 : F) ≠ 4 by decide) hw)
    · have hij := hinj (mul_left_cancel₀ h7 (add_left_cancel he))
      exact Prod.ext rfl hij
  have hRnorm (j : Bool × Fin 3) : Algebra.norm F (R j).1 = 9 := by
    have hsub0 := hnsub 0 j.2
    have haff0 := hnaffsub 0 j.2
    simp only [map_zero,zero_sub,norm_neg hdimE] at hsub0 haff0
    rcases j with ⟨b,j⟩
    cases b <;> dsimp [R]
    · apply neg_injective
      exact hsub0.trans (by norm_num [p]; decide)
    · apply neg_injective
      exact haff0.trans (by norm_num [p]; decide)
  have hSub (i : Fin 4) (j : Bool × Fin 3) :
      Algebra.norm F ((L i).1-(R j).1) = subValue j.1 i := by
    rcases j with ⟨b,j⟩
    cases b <;> dsimp [L,R]
    · rw [hnsub]; fin_cases i <;> norm_num [p,rowPoint,subValue] <;> decide
    · rw [hnaffsub]; fin_cases i <;> norm_num [p,rowPoint,subValue] <;> decide
  have hAdd (i : Fin 4) (j : Bool × Fin 3) :
      Algebra.norm F ((L i).1+(R j).1) = addValue j.1 i := by
    rcases j with ⟨b,j⟩
    cases b <;> dsimp [L,R]
    · rw [hnadd]; fin_cases i <;> norm_num [p,rowPoint,addValue] <;> decide
    · rw [hnaffadd]; fin_cases i <;> norm_num [p,rowPoint,addValue] <;> decide
  have he (i : Fin 4) (j : Bool × Fin 3) : squareRelation (L i) (R j) := by
    refine ⟨?_,?_,?_⟩
    · rw [Erdos714RationalNormDifference.relation_iff]
      refine ⟨(_root_.map_ne_zero (algebraMap F E)).mpr (row_nonzero i),?_,weight_nonzero i,?_,?_,?_,?_⟩
      · apply (Algebra.norm_ne_zero_iff (R := F)).mp
        rw [hRnorm]; decide
      · rcases j with ⟨b,j⟩
        cases b <;> dsimp [R] <;> decide
      · apply (Algebra.norm_ne_zero_iff (R := F)).mp
        rw [hSub]; exact sub_nonzero _ _
      · apply (Algebra.norm_ne_zero_iff (R := F)).mp
        rw [hAdd]; exact add_nonzero _ _
      · rw [hAdd,hSub]; exact profile_equation _ _
    · obtain ⟨r,hr⟩ := row_square i
      exact ⟨algebraMap F E r,by change algebraMap F E (rowPoint i) = _; rw [hr,map_mul]⟩
    · rcases j with ⟨b,j⟩
      cases b
      · exact root_square _ (hroot' j)
      · exact affine_root_square _ (hroot' j)
  refine ⟨⟨Sum.map L R,?_⟩, Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro v w hvw
  cases v with
  | inl i => cases w with
    | inl j => simp at hvw
    | inr j => exact he i j
  | inr i => cases w with
    | inl j => exact he j i
    | inr j => simp at hvw


lemma exists_powerBasis [Fintype E] (hdim : Module.finrank F E = 3) :
    ∃ pb : PowerBasis F E, pb.dim = 3 ∧ minpoly F pb.gen = p := by
  letI : Fact (Irreducible p) := ⟨p_irreducible⟩
  let pb := AdjoinRoot.powerBasis p_irreducible.ne_zero
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv (Fin pb.dim → F) pb.basis.equivFun.symm.toEquiv
  have hdimP : Module.finrank F (AdjoinRoot p) = 3 := pb.finrank.trans p_degree
  let P : F[X] := X^(Fintype.card F^3)-X
  letI : IsSplittingField F E P := by
    have h := FiniteField.isSplittingField_sub E F
    rw [Module.card_eq_pow_finrank (K := F) (V := E),hdim] at h
    exact h
  letI : IsSplittingField F (AdjoinRoot p) P := by
    have h := FiniteField.isSplittingField_sub (AdjoinRoot p) F
    rw [Module.card_eq_pow_finrank (K := F) (V := AdjoinRoot p),hdimP] at h
    exact h
  let e : AdjoinRoot p ≃ₐ[F] E :=
    (IsSplittingField.algEquiv (AdjoinRoot p) P).trans (IsSplittingField.algEquiv E P).symm
  refine ⟨pb.map e, ?_, ?_⟩
  · rw [PowerBasis.map_dim]; exact p_degree
  · rw [PowerBasis.map_gen,minpoly.algEquiv_eq]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic p_monic

/-- All cubic models over F11 have the square-point K46 obstruction. -/
theorem not_free_six [Fintype E] (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 6)).Free (graph (E := E)) := by
  obtain ⟨pb,hpb,hmin⟩ := exists_powerBasis hdim
  letI : FiniteDimensional F E := pb.finite
  letI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hcard : Fintype.card (E ≃ₐ[F] E) = 3 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, pb.finrank, hpb]
  let sigma : Fin 3 ≃ (E ≃ₐ[F] E) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let e : Fin 6 ≃ Bool × Fin 3 := Fintype.equivOfCardEq (by simp)
  intro hfree
  exact hfree ⟨(powerBasis_copy pb hpb hmin sigma sigma.injective).comp
    (bicliqueCopy (Function.Embedding.refl _) e.toEmbedding)⟩

theorem not_free_four [Fintype E] (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E)) := by
  intro hfree
  apply not_free_six hdim
  rintro ⟨f⟩
  exact hfree ⟨f.comp (bicliqueCopy (Function.Embedding.refl _) (Fin.castLEEmb (by decide : 4 ≤ 6)))⟩

/-- An explicit field and an actual square-point counterexample. -/
theorem quotient_not_free :
    letI : Fact (Irreducible p) := ⟨p_irreducible⟩
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := AdjoinRoot p)) := by
  letI : Fact (Irreducible p) := ⟨p_irreducible⟩
  let pb := AdjoinRoot.powerBasis p_irreducible.ne_zero
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv (Fin pb.dim → F) pb.basis.equivFun.symm.toEquiv
  exact not_free_four (pb.finrank.trans p_degree)

#print axioms not_free_six
#print axioms not_free_four
#print axioms quotient_not_free

#print axioms powerBasis_copy
end Erdos714RationalNormSquare
