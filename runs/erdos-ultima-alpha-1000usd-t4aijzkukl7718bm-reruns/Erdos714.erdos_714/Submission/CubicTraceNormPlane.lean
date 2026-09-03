import Submission.BinaryLift

/-!
Prescribed trace and norm in a finite cubic extension, and a binary norm
plane whose directions lie in any prescribed linear hyperplane.
These lemmas do not settle Erdős Problem 714.
-/
noncomputable section
open Polynomial Classical
open scoped CharTwo
set_option maxHeartbeats 4000000
namespace Erdos714CubicTraceNormPlane
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def pencil (t c n : F) : F[X] := X^3-C t*X^2+C c*X-C n

lemma degree_pencil (t c n : F) : (pencil t c n).natDegree = 3 := by
  unfold pencil
  compute_degree!

lemma monic_pencil (t c n : F) : (pencil t c n).Monic := by
  unfold pencil
  monicity <;> norm_num

/-- There are q choices of the remaining coefficient but only q-1 possible
nonzero roots. Consequently every trace and nonzero norm is realized by an
irreducible monic cubic. -/
theorem exists_irreducible [Fintype F] (t n : F) (hn : n ≠ 0) :
    ∃ c : F, Irreducible (pencil t c n) := by
  let R : Fˣ → F := fun z => (-(z:F)^3+t*(z:F)^2+n)/(z:F)
  have hns : ¬ Function.Surjective R := by
    intro hs
    have h := Fintype.card_le_of_surjective R hs
    rw [Fintype.card_units] at h
    have hp : 0 < Fintype.card F := Fintype.card_pos
    omega
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨c,hc⟩ := hns
  refine ⟨c,Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_⟩
  · simp [degree_pencil]
  · intro x hx
    have he : x^3-t*x^2+c*x-n=0 := by simpa [Polynomial.IsRoot,pencil] using hx
    have hx0 : x ≠ 0 := by intro h; subst x; simp [hn] at he
    apply hc (Units.mk0 x hx0)
    apply (div_eq_iff hx0).mpr
    change -x^3+t*x^2+n=c*x
    linear_combination -he

/-- Transfer an irreducible monic cubic to any finite cubic model. -/
theorem exists_powerBasis [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (t c n : F) (hp : Irreducible (pencil t c n)) :
    ∃ pb : PowerBasis F E, pb.dim = 3 ∧ minpoly F pb.gen = pencil t c n := by
  let p := pencil t c n
  letI : Fact (Irreducible p) := ⟨hp⟩
  let pb := AdjoinRoot.powerBasis hp.ne_zero
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv (Fin pb.dim → F) pb.basis.equivFun.symm.toEquiv
  have hdimP : Module.finrank F (AdjoinRoot p) = 3 :=
    pb.finrank.trans (degree_pencil t c n)
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
  · rw [PowerBasis.map_dim]; exact degree_pencil t c n
  · rw [PowerBasis.map_gen,minpoly.algEquiv_eq]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic (monic_pencil t c n)

/-- Both invariants are realized by a primitive element, not just a scalar. -/
theorem exists_prescribed [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (t n : F) (hn : n ≠ 0) :
    ∃ pb : PowerBasis F E, pb.dim = 3 ∧
      Algebra.trace F E pb.gen = t ∧ Algebra.norm F pb.gen = n := by
  obtain ⟨c,hc⟩ := exists_irreducible t n hn
  obtain ⟨pb,hpb,hmin⟩ := exists_powerBasis hdim t c n hc
  refine ⟨pb,hpb,?_,?_⟩
  · rw [pb.trace_gen_eq_nextCoeff_minpoly,hmin]
    rw [Polynomial.nextCoeff,degree_pencil]
    norm_num [pencil]
  · rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,hpb,hmin]
    norm_num [pencil]

/-- Two homogeneous scalar constraints on a three-dimensional field always
have a common nonzero solution. -/
lemma exists_scale [FiniteDimensional F E] (hdim : Module.finrank F E = 3)
    (l : E →ₗ[F] F) (a b : E) :
    ∃ c : E, c ≠ 0 ∧ l (c*a) = 0 ∧ l (c*b) = 0 := by
  let L : E →ₗ[F] (F × F) :=
    { toFun := fun c => (l (c*a),l (c*b))
      map_add' := by intro x y; simp [add_mul]
      map_smul' := by intro x y; simp }
  have hL : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_prod, Module.finrank_self,hdim]
    norm_num)
  obtain ⟨c,hc,hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  exact ⟨c,hc0,congrArg Prod.fst hc,congrArg Prod.snd hc⟩

/-- Any binary finite cubic field contains three distinct norm-one elements
whose sum is one. -/
theorem exists_norm_one_triple [Fintype F] [Fintype E] [CharP E 2]
    (hdim : Module.finrank F E = 3) :
    ∃ r : Fin 3 → E, Function.Injective r ∧
      (∀ i, Algebra.norm F (r i) = 1) ∧ r 0+r 1+r 2=1 := by
  obtain ⟨pb,hpb,ht,hn⟩ := exists_prescribed hdim 1 1 one_ne_zero
  letI : FiniteDimensional F E := pb.finite
  have hcard : Fintype.card (E ≃ₐ[F] E) = 3 := by
    rw [← Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank,hdim]
  let sigma : Fin 3 ≃ (E ≃ₐ[F] E) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let r : Fin 3 → E := fun i => sigma i pb.gen
  have hr : Function.Injective r := by
    intro i j hij
    apply sigma.injective
    ext z
    exact DFunLike.congr_fun (pb.algHom_ext (f := (sigma i).toAlgHom)
      (g := (sigma j).toAlgHom) hij) z
  refine ⟨r,hr,?_,?_⟩
  · intro i
    change Algebra.norm F (sigma i pb.gen) = 1
    rw [Algebra.norm_eq_of_algEquiv,hn]
  · have hs := trace_eq_sum_automorphisms (K := F) pb.gen
    rw [ht,map_one] at hs
    have he : (∑ i : Fin 3, r i) = ∑ s : E ≃ₐ[F] E, s pb.gen :=
      Fintype.sum_equiv sigma _ _ (fun _ => rfl)
    rw [← hs] at he
    simpa [Fin.sum_univ_succ,add_assoc] using he

/-- A norm-one affine binary plane can be scaled so that both of its
independent directions lie in the kernel of ANY scalar linear map. -/
theorem exists_plane_in_kernel [Fintype F] [Fintype E] [CharP E 2]
    (hdim : Module.finrank F E = 3) (l : E →ₗ[F] F) :
    ∃ p u v : E, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ l u = 0 ∧ l v = 0 ∧
      Algebra.norm F p ≠ 0 ∧ ∀ i : Fin 4,
        Algebra.norm F (p+Erdos714BinaryLift.plane u v i) = Algebra.norm F p := by
  obtain ⟨r,hr,hn,hs⟩ := exists_norm_one_triple (F := F) hdim
  let a := r 0+r 1
  let b := r 0+r 2
  have ha : a ≠ 0 := fun h => (by have := hr (CharTwo.add_eq_zero.mp h); omega)
  have hb : b ≠ 0 := fun h => (by have := hr (CharTwo.add_eq_zero.mp h); omega)
  have hab : a ≠ b := by
    intro h
    have := hr (add_left_cancel h)
    omega
  have hf (i : Fin 4) : Algebra.norm F (r 0+Erdos714BinaryLift.plane a b i) = 1 := by
    fin_cases i <;> simp [Erdos714BinaryLift.plane, a,b,hn,
      add_assoc,add_left_comm,add_comm]
    simpa [add_assoc] using congrArg (Algebra.norm F) hs
  obtain ⟨c,hc,hca,hcb⟩ := exists_scale hdim l a b
  refine ⟨c*r 0,c*a,c*b,mul_ne_zero hc ha,mul_ne_zero hc hb,
    fun h => hab (mul_left_cancel₀ hc h),hca,hcb,?_,?_⟩
  · rw [map_mul,hn,mul_one]
    exact Algebra.norm_ne_zero_iff.mpr hc
  · intro i
    have he : c*r 0+Erdos714BinaryLift.plane (c*a) (c*b) i =
        c*(r 0+Erdos714BinaryLift.plane a b i) := by
      fin_cases i <;> simp [Erdos714BinaryLift.plane] <;> ring
    rw [he,map_mul,hf,mul_one,map_mul,hn,mul_one]

#print axioms exists_irreducible
#print axioms exists_prescribed
#print axioms exists_norm_one_triple
#print axioms exists_plane_in_kernel
end Erdos714CubicTraceNormPlane
