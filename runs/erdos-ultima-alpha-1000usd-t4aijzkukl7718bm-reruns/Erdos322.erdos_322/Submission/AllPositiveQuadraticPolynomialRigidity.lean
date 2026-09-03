import Submission.PositiveQuadraticPolynomialRigidity

/-! Polynomial rigidity for positive rational quadratic sources of every
finite dimension at least three. No unrestricted counting estimate follows. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

private lemma extend_subspace_dimension {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (k : ℕ) : ∀ U : Submodule ℚ V,
      Module.finrank ℚ U≤k → k≤Module.finrank ℚ V →
      ∃ W : Submodule ℚ V, U≤W ∧ Module.finrank ℚ W=k := by
  induction k with
  | zero =>
    intro U hU _
    exact ⟨U,le_rfl,by omega⟩
  | succ k ih =>
    intro U hU hk
    by_cases he : Module.finrank ℚ U=k+1
    · exact ⟨U,le_rfl,he⟩
    · obtain ⟨W,hUW,hW⟩ := ih U (by omega) (by omega)
      obtain ⟨v,hv⟩ := W.exists_of_finrank_lt (by omega)
      have hvW : v ∉ W := by simpa using hv 1 (by norm_num)
      have hv0 : v ≠ 0 := by intro h; exact hvW (h ▸ W.zero_mem)
      let W' : Submodule ℚ V := W ⊔ Submodule.span ℚ {v}
      have hle : W≤W' := le_sup_left
      have hmem : v∈W' := (show Submodule.span ℚ {v}≤W' from le_sup_right)
        (Submodule.mem_span_singleton_self v)
      have hlt : W<W' := lt_of_le_of_ne hle (by intro h; exact hvW (h.symm ▸ hmem))
      have hlo := Submodule.finrank_lt_finrank_of_lt hlt
      have hhi := Submodule.finrank_add_le_finrank_add_finrank W (Submodule.span ℚ {v})
      rw [finrank_span_singleton hv0] at hhi
      exact ⟨W',hUW.trans hle,by dsimp [W'] at *; omega⟩

private lemma ternary_embedding_through_pair {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (hV : 3≤Module.finrank ℚ V) (x y : V) :
    ∃ L : (Fin 3 → ℚ) →ₗ[ℚ] V, Function.Injective L ∧
      ∃ u v : Fin 3 → ℚ, L u=x ∧ L v=y := by
  let U := Submodule.span ℚ (Set.range (![x,y] : Fin 2 → V))
  have hU : Module.finrank ℚ U≤3 := by
    have hh := finrank_range_le_card (R := ℚ) (![x,y] : Fin 2 → V)
    have hh' : Module.finrank ℚ U≤2 := by simpa only [Fintype.card_fin] using hh
    omega
  obtain ⟨W,hUW,hW⟩ := extend_subspace_dimension 3 U hU hV
  have hx : x∈W := hUW (Submodule.subset_span ⟨0,rfl⟩)
  have hy : y∈W := hUW (Submodule.subset_span ⟨1,rfl⟩)
  let E : (Fin 3 → ℚ) ≃ₗ[ℚ] W := LinearEquiv.ofFinrankEq _ _
    (by rw [Module.finrank_fin_fun,hW])
  let L := W.subtype.comp E.toLinearMap
  have hL : Function.Injective L := Subtype.val_injective.comp E.injective
  refine ⟨L,hL,E.symm ⟨x,hx⟩,E.symm ⟨y,hy⟩,?_,?_⟩ <;> simp [L]

private def generalSubstitution {n : ℕ} (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (i : Fin n) : MvPolynomial (Fin 3) ℚ :=
  ∑ j : Fin 3, MvPolynomial.C (L (Pi.single j 1) i)*MvPolynomial.X j

private lemma generalSubstitution_eval {n : ℕ} (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (x : Fin 3 → ℚ) (i : Fin n) : MvPolynomial.eval x (generalSubstitution L i)=L x i := by
  have hx : (∑ j : Fin 3, x j • (Pi.single j (1 : ℚ) : Fin 3 → ℚ))=x := by
    funext k
    simp [Finset.sum_apply,Pi.single_apply]
  have hh := congrArg (fun v ↦ L v i) hx
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simpa [generalSubstitution,mul_comm] using hh

private lemma general_eval_substitution {n : ℕ} (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (P : MvPolynomial (Fin n) ℚ) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x (MvPolynomial.eval₂Hom MvPolynomial.C (generalSubstitution L) P)=
      MvPolynomial.eval (L x) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℚ) x
    (MvPolynomial.eval₂Hom MvPolynomial.C (generalSubstitution L) P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℚ) x).comp MvPolynomial.C=RingHom.id ℚ := by
    ext a
    simp
  rw [hc]
  change MvPolynomial.eval (fun i ↦ MvPolynomial.eval x (generalSubstitution L i)) P=_
  simp_rw [generalSubstitution_eval]

/-- Any two points lie in a positive ternary subspace, so the ternary theorem
extends to all finite source dimensions at least three. -/
theorem positive_constant_on_rational_fibers (n : ℕ) (hn : 3≤n)
    (Q : QuadraticForm ℚ (Fin n → ℚ)) (hQ : Q.PosDef)
    (P : Fin 4 → MvPolynomial (Fin n) ℚ) (H : Polynomial ℚ)
    (h : ∀ x : Fin n → ℚ, ∑ i, (MvPolynomial.eval x (P i))^4=H.eval (Q x))
    (x y : Fin n → ℚ) (hxy : Q x=Q y) (i : Fin 4) :
    MvPolynomial.eval x (P i)=MvPolynomial.eval y (P i) := by
  obtain ⟨L,hL,u,v,hu,hv⟩ := ternary_embedding_through_pair
    (by simpa only [Module.finrank_fin_fun] using hn) x y
  let F (j : Fin 4) := MvPolynomial.eval₂Hom MvPolynomial.C (generalSubstitution L) (P j)
  have hQL : (Q.comp L).PosDef := by
    intro w hw
    apply hQ
    intro hz
    exact hw (hL (by simpa using hz))
  have hF (w : Fin 3 → ℚ) : ∑ j, (MvPolynomial.eval w (F j))^4=H.eval ((Q.comp L) w) := by
    simp only [F,general_eval_substitution,QuadraticMap.comp_apply]
    exact h (L w)
  have huv : (Q.comp L) u=(Q.comp L) v := by simpa only [QuadraticMap.comp_apply,hu,hv] using hxy
  have hh := positive_ternary_constant_on_rational_fibers (Q.comp L) hQL F H hF u v huv i
  simpa only [F,general_eval_substitution,hu,hv] using hh

/-- Denominators depending only on the quadratic value cannot restore fiber multiplicity. -/
theorem positive_rational_fiber_unique (n : ℕ) (hn : 3≤n)
    (Q : QuadraticForm ℚ (Fin n → ℚ)) (hQ : Q.PosDef)
    (P : Fin 4 → MvPolynomial (Fin n) ℚ) (H D : Polynomial ℚ)
    (h : ∀ x : Fin n → ℚ, ∑ i, (MvPolynomial.eval x (P i))^4=H.eval (Q x))
    (x y : Fin n → ℚ) (hxy : Q x=Q y) (i : Fin 4) :
    MvPolynomial.eval x (P i)/D.eval (Q x)=MvPolynomial.eval y (P i)/D.eval (Q y) := by
  rw [positive_constant_on_rational_fibers n hn Q hQ P H h x y hxy i,hxy]

end
end Erdos322Research.QuadraticQuarticFive
