import Submission.QuarticDiagonalNorm

/-!
An obstruction to the additive-weight rational cubic norm lift.
This is NOT a disproof of Erdős Problem 714.
-/
noncomputable section
open Polynomial SimpleGraph Classical
set_option maxHeartbeats 3000000
namespace Erdos714RationalNormDifference
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def pencil (u t : F) : F[X] := X^3-C t*X^2-C (u^2)*X+C t

lemma degree_pencil (u t : F) : (pencil u t).natDegree = 3 := by
  unfold pencil
  compute_degree!

lemma monic_pencil (u t : F) : (pencil u t).Monic := by
  unfold pencil
  monicity <;> norm_num

lemma eval_pencil (u t z : F) : (pencil u t).eval z = z^3-t*z^2-u^2*z+t := by
  simp [pencil]

/-- The collision at 1 and -1 supplies a missing value. -/
theorem exists_irreducible_pencil [Finite F] (h2 : (2 : F) ≠ 0)
    (u : F) (hu : u^2 ≠ 1) :
    ∃ t : F, t ≠ 0 ∧ Irreducible (pencil u t) := by
  let R : F → F := fun z => (z^3-u^2*z)/(z^2-1)
  have hneg : (1 : F) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hnot : ¬ Function.Injective R := by
    intro h
    apply hneg
    apply h
    simp [R]
  have hns : ¬ Function.Surjective R := fun h => hnot (Finite.injective_iff_surjective.mpr h)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨t,ht⟩ := hns
  have ht0 : t ≠ 0 := by intro h; exact ht 0 (by simp [R,h])
  refine ⟨t,ht0,irreducible_of_degree_le_three_of_not_isRoot ?_ ?_⟩
  · simp [degree_pencil]
  · intro z hz
    change (pencil u t).eval z = 0 at hz
    rw [eval_pencil] at hz
    by_cases hd : z^2 = 1
    · rcases sq_eq_one_iff.mp hd with rfl | rfl
      · apply hu
        linear_combination -hz
      · apply hu
        linear_combination hz
    · apply ht z
      apply (div_eq_iff (sub_ne_zero.mpr hd)).mpr
      linear_combination hz

/-- The original rational incidence, with no zero coordinates, weights,
zero numerators, or zero denominators. -/
def relation (p q : E × F) : Prop :=
  p.1 ≠ 0 ∧ q.1 ≠ 0 ∧ p.2 ≠ 0 ∧ q.2 ≠ 0 ∧
  p.1-q.1 ≠ 0 ∧ p.1+q.1 ≠ 0 ∧
  p.2-q.2 = Algebra.norm F ((p.1+q.1)/(p.1-q.1))

def graph : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj p q := match p,q with
    | Sum.inl p, Sum.inr q => relation p q
    | Sum.inr q, Sum.inl p => relation p q
    | _,_ => False
  symm := by intro p q h; cases p <;> cases q <;> exact h
  loopless := by intro p; cases p <;> simp

lemma relation_iff [FiniteDimensional F E] (p q : E × F) :
    relation p q ↔ p.1 ≠ 0 ∧ q.1 ≠ 0 ∧ p.2 ≠ 0 ∧ q.2 ≠ 0 ∧
      p.1-q.1 ≠ 0 ∧ p.1+q.1 ≠ 0 ∧
      Algebra.norm F (p.1+q.1) = (p.2-q.2)*Algebra.norm F (p.1-q.1) := by
  unfold relation
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun hd => and_congr_right fun _ => ?_
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [← div_eq_mul_inv, eq_div_iff (Algebra.norm_ne_zero_iff.mpr hd), eq_comm]

lemma norm_neg [FiniteDimensional F E] (hdim : Module.finrank F E = 3) (z : E) :
    Algebra.norm F (-z) = -Algebra.norm F z := by
  rw [show -z = algebraMap F E (-1)*z by simp, map_mul, Algebra.norm_algebraMap, hdim]
  ring

lemma norm_scalar_add_gen (pb : PowerBasis F E) (hdim : pb.dim = 3) (x : F) :
    Algebra.norm F (algebraMap F E x + pb.gen) = -(minpoly F pb.gen).eval (-x) := by
  letI : FiniteDimensional F E := pb.finite
  rw [show algebraMap F E x + pb.gen = -(algebraMap F E (-x)-pb.gen) by simp [add_comm]]
  rw [norm_neg (pb.finrank.trans hdim), Erdos714QuarticDiagonal.norm_scalar_sub_gen]


def rowPoint (u : F) : Fin 4 → F := ![1,-1,u,-u]
def rowWeight (u : F) : Fin 4 → F := ![u+1,u+1,u-1,u-1]

lemma rowPoint_injective (h2 : (2 : F) ≠ 0) (u : F) (hu0 : u ≠ 0) (hu : u^2 ≠ 1) :
    Function.Injective (rowPoint u) := by
  have hu1 := (sq_ne_one_iff.mp hu).1
  have hum := (sq_ne_one_iff.mp hu).2
  have hneg : (1 : F) ≠ -1 := by intro h; apply h2; linear_combination h
  have hun : u ≠ -u := by
    intro h
    have hz : (2 : F)*u = 0 := by linear_combination h
    exact (mul_ne_zero h2 hu0) hz
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [rowPoint, Ne.symm hu1, Ne.symm hum, Ne.symm hun,
      neg_eq_iff_eq_neg]

lemma rowPoint_ne_zero (u : F) (hu0 : u ≠ 0) (i : Fin 4) : rowPoint u i ≠ 0 := by
  fin_cases i <;> simp [rowPoint,hu0]

lemma rowWeight_ne_zero (u : F) (hu : u^2 ≠ 1) (i : Fin 4) : rowWeight u i ≠ 0 := by
  have hu1 := (sq_ne_one_iff.mp hu).1
  have hum := (sq_ne_one_iff.mp hu).2
  fin_cases i <;> simp [rowWeight, sub_ne_zero, add_eq_zero_iff_eq_neg,hu1,hum]

lemma eval_row_ne_zero (u t : F) (hu : u^2 ≠ 1) (ht : t ≠ 0) (i : Fin 4) :
    (pencil u t).eval (rowPoint u i) ≠ 0 ∧ (pencil u t).eval (-rowPoint u i) ≠ 0 := by
  have h1 : 1-u^2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h2 : u^2-1 ≠ 0 := sub_ne_zero.mpr hu
  have h3 : t*(1-u^2) ≠ 0 := mul_ne_zero ht h1
  fin_cases i <;> dsimp [rowPoint] <;>
    constructor <;> rw [eval_pencil] <;> ring_nf at * <;> assumption


/-- The polynomial evaluations give all 24 rational incidences. -/
def powerBasis_copy (h2 : (2 : F) ≠ 0) (u t : F)
    (hu0 : u ≠ 0) (hu : u^2 ≠ 1) (ht : t ≠ 0)
    (pb : PowerBasis F E) (hdim : pb.dim = 3) (hmin : minpoly F pb.gen = pencil u t)
    (sigma : Fin 3 → E ≃ₐ[F] E) (hsigma : Function.Injective sigma) :
    (completeBipartiteGraph (Fin 4) (Bool × Fin 3)).Copy (graph (F := F) (E := E)) := by
  letI : FiniteDimensional F E := pb.finite
  have hdimE : Module.finrank F E = 3 := pb.finrank.trans hdim
  have hn (j : Fin 3) : Algebra.norm F (sigma j pb.gen) = -t := by
    rw [Algebra.norm_eq_of_algEquiv]
    have h := Erdos714QuarticDiagonal.norm_scalar_sub_gen pb 0
    rw [hmin,eval_pencil] at h
    simp only [map_zero,zero_sub,zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,zero_add,norm_neg hdimE] at h
    linear_combination -h
  have hinj : Function.Injective (fun j => sigma j pb.gen) := by
    intro i j hij
    apply hsigma
    ext z
    exact DFunLike.congr_fun (pb.algHom_ext (f := (sigma i).toAlgHom)
      (g := (sigma j).toAlgHom) hij) z
  have hopp (i j : Fin 3) : sigma i pb.gen ≠ -sigma j pb.gen := by
    intro h
    have he := congrArg (Algebra.norm F) h
    rw [norm_neg hdimE,hn,hn] at he
    have hz : (2 : F)*t = 0 := by linear_combination -he
    exact mul_ne_zero h2 ht hz
  let L : Fin 4 → E × F := fun i => (algebraMap F E (rowPoint u i),rowWeight u i)
  let R : Bool × Fin 3 → E × F := fun j =>
    (if j.1 then -sigma j.2 pb.gen else sigma j.2 pb.gen,u)
  have hL : Function.Injective L := by
    intro i j h
    exact rowPoint_injective h2 u hu0 hu ((algebraMap F E).injective (congrArg Prod.fst h))
  have hR : Function.Injective R := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have he := congrArg Prod.fst h
    cases a <;> cases b
    · exact Prod.ext rfl (hinj he)
    · exact False.elim (hopp i j he)
    · exact False.elim (hopp j i he.symm)
    · exact Prod.ext rfl (hinj (neg_injective he))
  have hevalSub (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x - sigma j pb.gen) = (pencil u t).eval x := by
    rw [show algebraMap F E x - sigma j pb.gen = sigma j (algebraMap F E x-pb.gen) by simp]
    rw [Algebra.norm_eq_of_algEquiv,Erdos714QuarticDiagonal.norm_scalar_sub_gen,hmin]
  have hevalAdd (x : F) (j : Fin 3) :
      Algebra.norm F (algebraMap F E x + sigma j pb.gen) = -(pencil u t).eval (-x) := by
    rw [show algebraMap F E x + sigma j pb.gen = sigma j (algebraMap F E x+pb.gen) by simp]
    rw [Algebra.norm_eq_of_algEquiv,norm_scalar_add_gen pb hdim,hmin]
  have hR0 (j : Bool × Fin 3) : (R j).1 ≠ 0 := by
    have hn0 : sigma j.2 pb.gen ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rw [hn]; exact neg_ne_zero.mpr ht)
    cases j with | mk a j => cases a <;> simp [R,hn0]
  have hsub (i : Fin 4) (j : Bool × Fin 3) : (L i).1-(R j).1 ≠ 0 := by
    apply (Algebra.norm_ne_zero_iff (R := F)).mp
    have hp := eval_row_ne_zero u t hu ht i
    cases j with | mk a j =>
      cases a <;> simp only [L,R,Bool.false_eq_true,↓reduceIte,sub_neg_eq_add]
      · rw [hevalSub]; exact hp.1
      · rw [hevalAdd]; exact neg_ne_zero.mpr hp.2
  have hadd (i : Fin 4) (j : Bool × Fin 3) : (L i).1+(R j).1 ≠ 0 := by
    apply (Algebra.norm_ne_zero_iff (R := F)).mp
    have hp := eval_row_ne_zero u t hu ht i
    cases j with | mk a j =>
      cases a <;> simp only [L,R,Bool.false_eq_true,↓reduceIte,← sub_eq_add_neg]
      · rw [hevalAdd]; exact neg_ne_zero.mpr hp.2
      · rw [hevalSub]; exact hp.1
  have hedge (i : Fin 4) (j : Bool × Fin 3) : relation (L i) (R j) := by
    rw [relation_iff]
    refine ⟨(_root_.map_ne_zero (algebraMap F E)).mpr (rowPoint_ne_zero u hu0 i), hR0 j,
      rowWeight_ne_zero u hu i, hu0, hsub i j, hadd i j, ?_⟩
    cases j with | mk a j =>
      cases a <;> simp only [L,R,Bool.false_eq_true,↓reduceIte,sub_neg_eq_add,← sub_eq_add_neg]
      · rw [hevalAdd,hevalSub]
        fin_cases i <;> simp [rowPoint,rowWeight,eval_pencil] <;> ring
      · rw [hevalSub,hevalAdd]
        fin_cases i <;> simp [rowPoint,rowWeight,eval_pencil] <;> ring
  refine ⟨⟨Sum.map L R, ?_⟩, Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro v w hvw
  cases v with
  | inl i => cases w with
    | inl j => simp at hvw
    | inr j => exact hedge i j
  | inr i => cases w with
    | inl j => exact hedge j i
    | inr j => simp at hvw


/-- Relabeling or restricting the two parts of a biclique. -/
def bicliqueCopy {A B C D : Type*} (f : A ↪ C) (g : B ↪ D) :
    (completeBipartiteGraph A B).Copy (completeBipartiteGraph C D) where
  toHom := ⟨Sum.map f g, by
    intro v w h
    cases v <;> cases w <;> simp_all⟩
  injective' := Sum.map_injective.mpr ⟨f.injective,g.injective⟩

def finite_powerBasis_copy [Fintype F] [Fintype E]
    (h2 : (2 : F) ≠ 0) (u t : F) (hu0 : u ≠ 0) (hu : u^2 ≠ 1) (ht : t ≠ 0)
    (pb : PowerBasis F E) (hdim : pb.dim = 3) (hmin : minpoly F pb.gen = pencil u t) :
    (completeBipartiteGraph (Fin 4) (Fin 6)).Copy (graph (F := F) (E := E)) := by
  letI : FiniteDimensional F E := pb.finite
  letI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hcard : Fintype.card (E ≃ₐ[F] E) = 3 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, pb.finrank, hdim]
  let sigma : Fin 3 ≃ (E ≃ₐ[F] E) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let e : Fin 6 ≃ Bool × Fin 3 := Fintype.equivOfCardEq (by simp)
  exact (powerBasis_copy h2 u t hu0 hu ht pb hdim hmin sigma sigma.injective).comp
    (bicliqueCopy (Function.Embedding.refl _) e.toEmbedding)

/-- The obstruction transfers to ANY finite cubic extension, not just a quotient model. -/
theorem exists_powerBasis_pencil [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (u t : F) (hp : Irreducible (pencil u t)) :
    ∃ pb : PowerBasis F E, pb.dim = 3 ∧ minpoly F pb.gen = pencil u t := by
  let p := pencil u t
  letI : Fact (Irreducible p) := ⟨hp⟩
  let pb := AdjoinRoot.powerBasis hp.ne_zero
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv (Fin pb.dim → F) pb.basis.equivFun.symm.toEquiv
  have hdimP : Module.finrank F (AdjoinRoot p) = 3 :=
    pb.finrank.trans (degree_pencil u t)
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
  · rw [PowerBasis.map_dim]; exact degree_pencil u t
  · rw [PowerBasis.map_gen,minpoly.algEquiv_eq]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic (monic_pencil u t)

lemma exists_parameter [Fintype F] (hq : 5 ≤ Fintype.card F) :
    ∃ u : F, u ≠ 0 ∧ u^2 ≠ 1 := by
  let S : Finset F := {0,1,-1}
  have hS : S.card ≤ 3 := by
    have h := Finset.card_insert_le (0 : F) {1,-1}
    have h' := Finset.card_insert_le (1 : F) {-1}
    simp only [Finset.card_singleton] at h'
    dsimp [S]
    omega
  have hlt : S.card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [S,Finset.mem_insert,Finset.mem_singleton,not_or] at hu
  exact ⟨u,hu.1,sq_ne_one_iff.mpr hu.2⟩

/-- A uniform K46 obstruction in every odd-characteristic cubic extension
with at least five base-field elements. -/
theorem not_free_six [Fintype F] [Fintype E] (h2 : (2 : F) ≠ 0)
    (hq : 5 ≤ Fintype.card F) (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 6)).Free (graph (F := F) (E := E)) := by
  obtain ⟨u,hu0,hu⟩ := exists_parameter hq
  obtain ⟨t,ht,hp⟩ := exists_irreducible_pencil h2 u hu
  obtain ⟨pb,hpb,hmin⟩ := exists_powerBasis_pencil hdim u t hp
  exact fun hfree => hfree ⟨finite_powerBasis_copy h2 u t hu0 hu ht pb hpb hmin⟩

/-- In particular, this rational norm lift is not K44-free. -/
theorem not_free_four [Fintype F] [Fintype E] (h2 : (2 : F) ≠ 0)
    (hq : 5 ≤ Fintype.card F) (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  intro hfree
  apply not_free_six h2 hq hdim
  rintro ⟨f⟩
  exact hfree ⟨f.comp (bicliqueCopy (Function.Embedding.refl _) (Fin.castLEEmb (by decide : 4 ≤ 6)))⟩

#print axioms not_free_six
#print axioms not_free_four

#print axioms powerBasis_copy

#print axioms exists_irreducible_pencil
#print axioms relation_iff
#print axioms norm_scalar_add_gen
end Erdos714RationalNormDifference
