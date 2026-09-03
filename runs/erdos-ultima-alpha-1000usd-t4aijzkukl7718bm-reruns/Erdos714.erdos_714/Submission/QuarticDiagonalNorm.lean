import FormalConjecturesUtil

/-!
A polynomial-pencil obstruction to quartic norm graphs with diagonal
weights N(x)+c. This does not settle Erdős Problem 714.
-/
noncomputable section
open Finset Polynomial SimpleGraph Classical
set_option maxHeartbeats 3000000
namespace Erdos714QuarticDiagonal
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Diagonal weight slice of the weighted quartic norm graph. -/
def graph (c : F) : SimpleGraph (Bool × E) where
  Adj u v := u.1 ≠ v.1 ∧ Algebra.norm F u.2 + c ≠ 0 ∧ Algebra.norm F v.2 + c ≠ 0 ∧
    Algebra.norm F (u.2+v.2) = (Algebra.norm F u.2+c)*(Algebra.norm F v.2+c)
  symm := by intro u v h; exact ⟨h.1.symm,h.2.2.1,h.2.1,by simpa [add_comm,mul_comm] using h.2.2.2⟩
  loopless := by intro u h; exact h.1 rfl

/-- Polynomial evaluation equals the norm of a scalar minus a primitive element. -/
theorem norm_scalar_sub_gen (pb : PowerBasis F E) (x : F) :
    Algebra.norm F (algebraMap F E x - pb.gen) = (minpoly F pb.gen).eval x := by
  rw [Algebra.norm_eq_matrix_det pb.basis, ← charpoly_leftMulMatrix pb, Matrix.eval_charpoly]
  congr 1
  rw [map_sub, AlgHom.commutes]
  rfl

/-- Four distinct conjugates of one primitive element supply four columns. -/
theorem not_free_of_powerBasis (pb : PowerBasis F E) (hdim : pb.dim = 4)
    (sigma : Fin 4 → E ≃ₐ[F] E) (hsigma : Function.Injective sigma)
    (x : Fin 4 → F) (hx : Function.Injective x) (c : F)
    (hw : ∀ i, x i ^ 4+c ≠ 0)
    (hb : (minpoly F pb.gen).eval 0+c ≠ 0)
    (hpoly : ∀ i, (minpoly F pb.gen).eval (x i) =
      (x i^4+c)*((minpoly F pb.gen).eval 0+c)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) c) := by
  letI : FiniteDimensional F E := pb.finite
  have hdimE : Module.finrank F E = 4 := pb.finrank.trans hdim
  let L : Fin 4 → Bool × E := fun i => (false, algebraMap F E (x i))
  let R : Fin 4 → Bool × E := fun j => (true, -(sigma j) pb.gen)
  have hL : Function.Injective L := by
    intro i j hij
    exact hx ((algebraMap F E).injective (congrArg Prod.snd hij))
  have hR : Function.Injective R := by
    intro i j hij
    have hgen : (sigma i) pb.gen = (sigma j) pb.gen := neg_injective (congrArg Prod.snd hij)
    apply hsigma
    ext z
    exact DFunLike.congr_fun (pb.algHom_ext (f := (sigma i).toAlgHom)
      (g := (sigma j).toAlgHom) hgen) z
  have hn (i : Fin 4) : Algebra.norm F (L i).2 = x i^4 := by
    change Algebra.norm F (algebraMap F E (x i)) = _
    rw [Algebra.norm_algebraMap, hdimE]
  have hrn (j : Fin 4) : Algebra.norm F (R j).2 = (minpoly F pb.gen).eval 0 := by
    change Algebra.norm F (-sigma j pb.gen) = _
    rw [← map_neg (sigma j), Algebra.norm_eq_of_algEquiv]
    simpa using norm_scalar_sub_gen pb 0
  have he : ∀ i j, (graph (E := E) c).Adj (L i) (R j) := by
    intro i j
    refine ⟨Bool.false_ne_true, ?_, ?_, ?_⟩
    · rw [hn]; exact hw i
    · rw [hrn]; exact hb
    · change Algebra.norm F (algebraMap F E (x i) + -sigma j pb.gen) =
        (Algebra.norm F (L i).2+c)*(Algebra.norm F (R j).2+c)
      rw [hn,hrn]
      rw [show algebraMap F E (x i) + -sigma j pb.gen =
        sigma j (algebraMap F E (x i) - pb.gen) by simp [sub_eq_add_neg]]
      rw [Algebra.norm_eq_of_algEquiv, norm_scalar_sub_gen]
      exact hpoly i
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl i => cases v with
      | inl j => simp at huv
      | inr j => exact he i j
    | inr i => cases v with
      | inl j => exact (he j i).symm
      | inr j => simp at huv
  · intro u v huv
    cases u with
    | inl i => cases v with
      | inl j => exact congrArg Sum.inl (hL huv)
      | inr j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst huv))
    | inr i => cases v with
      | inl j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst huv).symm)
      | inr j => exact congrArg Sum.inr (hR huv)

/-- In a finite quartic extension, all four automorphisms are available. -/
theorem finite_not_free_of_powerBasis [Fintype F] [Fintype E]
    (pb : PowerBasis F E) (hdim : pb.dim = 4)
    (x : Fin 4 → F) (hx : Function.Injective x) (c : F)
    (hw : ∀ i, x i^4+c ≠ 0)
    (hb : (minpoly F pb.gen).eval 0+c ≠ 0)
    (hpoly : ∀ i, (minpoly F pb.gen).eval (x i) =
      (x i^4+c)*((minpoly F pb.gen).eval 0+c)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) c) := by
  letI : FiniteDimensional F E := pb.finite
  letI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hcard : Fintype.card (E ≃ₐ[F] E) = 4 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, pb.finrank, hdim]
  let sigma : Fin 4 ≃ (E ≃ₐ[F] E) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  exact not_free_of_powerBasis pb hdim sigma sigma.injective x hx c hw hb hpoly

/-- An irreducible quartic with the prescribed evaluations supplies an
actual finite-field counterexample to the diagonal norm-slice candidate. -/
theorem irreducible_not_free [Fintype F] (p : F[X]) (hp : Irreducible p)
    (hm : p.Monic) (hdeg : p.natDegree = 4)
    (x : Fin 4 → F) (hx : Function.Injective x) (c : F)
    (hw : ∀ i, x i^4+c ≠ 0) (hb : p.eval 0+c ≠ 0)
    (hpoly : ∀ i, p.eval (x i) = (x i^4+c)*(p.eval 0+c)) :
    letI : Fact (Irreducible p) := ⟨hp⟩
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (E := AdjoinRoot p) c) := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  let pb := AdjoinRoot.powerBasis hp.ne_zero
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv (Fin pb.dim → F) pb.basis.equivFun.symm.toEquiv
  have hdim : pb.dim = 4 := hdeg
  have hmin : minpoly F pb.gen = p := AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  apply finite_not_free_of_powerBasis pb hdim x hx c hw
  · simpa [hmin] using hb
  · simpa [hmin] using hpoly

/-- The one-parameter quartic pencil obtained by prescribing four scalar rows. -/
def pencil (Q : F[X]) (c k : F) : F[X] :=
  C k*Q + C (1-k)*X^4 + C (c*(1-k))

/-- The pencil has exactly the required norm evaluations at the roots of Q. -/
theorem pencil_eval (Q : F[X]) (c k x : F)
    (hk : k*(Q.eval 0+1-c) = 1-2*c) (hx : Q.eval x = 0) :
    (pencil Q c k).eval x = (x^4+c)*((pencil Q c k).eval 0+c) := by
  simp only [pencil,eval_add,eval_mul,eval_C,eval_pow,eval_X,zero_pow (by decide : 4 ≠ 0),
    mul_zero,add_zero,hx]
  linear_combination -(x^4+c)*hk

#print axioms norm_scalar_sub_gen
#print axioms not_free_of_powerBasis
#print axioms pencil_eval
#print axioms finite_not_free_of_powerBasis
#print axioms irreducible_not_free
end Erdos714QuarticDiagonal
