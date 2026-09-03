import Submission.FixedQuadraticSphereRigidity

/-! Single-fiber polynomial rigidity for positive rational quadratic forms.
No upper bound for unrestricted quartic representation counts is claimed. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

private lemma orthogonal_basis_starting_at (Q : QuadraticForm ℚ (Fin 3 → ℚ))
    (hQ : Q.PosDef) (x : Fin 3 → ℚ) (hx : x ≠ 0) :
    ∃ b : Module.Basis (Fin 3) ℚ (Fin 3 → ℚ),
      b 0=x ∧ Q.associated.IsOrthoᵢ b := by
  let B : LinearMap.BilinForm ℚ (Fin 3 → ℚ) := Q.associated
  have hB : LinearMap.IsSymm B := ⟨QuadraticMap.associated_isSymm ℚ Q⟩
  have hxx : ¬ B.IsOrtho x x := by
    change B x x ≠ 0
    have hh : B x x=Q x := Q.associated_eq_self_apply ℚ x
    rw [hh]
    exact ne_of_gt (hQ x hx)
  let W := B.orthogonal (Submodule.span ℚ {x})
  have hdim : Module.finrank ℚ W=2 := by
    have hh := Submodule.finrank_add_eq_of_isCompl
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hxx)
    rw [finrank_span_singleton hx,Module.finrank_fin_fun] at hh
    dsimp [W]
    omega
  let B' := B.domRestrict₁₂ W W
  have hex := LinearMap.BilinForm.exists_orthogonal_basis
    (hB.domRestrict W : B'.IsSymm)
  rw [hdim] at hex
  obtain ⟨v',hv'⟩ := hex
  let b := Module.Basis.mkFinCons x v'
    (by
      rintro c y hy hc
      rw [add_eq_zero_iff_neg_eq] at hc
      rw [←hc,Submodule.neg_mem_iff] at hy
      have hh := (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hxx).disjoint
      rw [Submodule.disjoint_def] at hh
      have hh' := hh (c • x)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) hy
      exact (smul_eq_zero.mp hh').resolve_right hx)
    (by
      intro y
      refine ⟨-B x y/B x x,fun z hz ↦ ?_⟩
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [LinearMap.BilinForm.IsOrtho,map_smul,LinearMap.smul_apply,map_add,map_smul,
        smul_eq_mul,smul_eq_mul,div_mul_cancel₀ _ hxx,add_neg_cancel,mul_zero])
  refine ⟨b,?_,?_⟩
  · simp only [b,Module.Basis.coe_mkFinCons,Fin.cons_zero]
  · rw [show Q.associated=B from rfl,show (b : Fin 3 → (Fin 3 → ℚ))=_ from
        Module.Basis.coe_mkFinCons ..]
    intro j i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      intro hij <;> simp only [Function.onFun,Fin.cons_zero,Fin.cons_succ,Function.comp_apply]
    · exact (hij rfl).elim
    · rw [LinearMap.IsOrtho,←hB.eq]
      exact (v' j).property _ (Submodule.mem_span_singleton_self x)
    · exact (v' i).property _ (Submodule.mem_span_singleton_self x)
    · exact hv' (ne_of_apply_ne _ hij)

private def fixedLinearSubstitution {n : ℕ} (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (i : Fin n) : TernaryPoly :=
  ∑ j : Fin 3, MvPolynomial.C (L (Pi.single j 1) i)*MvPolynomial.X j

private lemma fixedLinearSubstitution_eval {n : ℕ}
    (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin n → ℚ)) (x : Fin 3 → ℚ) (i : Fin n) :
    MvPolynomial.eval x (fixedLinearSubstitution L i)=L x i := by
  have hx : (∑ j : Fin 3, x j • (Pi.single j (1 : ℚ) : Fin 3 → ℚ))=x := by
    funext k
    simp [Finset.sum_apply,Pi.single_apply]
  have hh := congrArg (fun v ↦ L v i) hx
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simpa [fixedLinearSubstitution,mul_comm] using hh

private lemma fixed_eval_substitution {n : ℕ}
    (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin n → ℚ)) (P : MvPolynomial (Fin n) ℚ) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x (MvPolynomial.eval₂Hom MvPolynomial.C (fixedLinearSubstitution L) P)=
      MvPolynomial.eval (L x) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℚ) x
    (MvPolynomial.eval₂Hom MvPolynomial.C (fixedLinearSubstitution L) P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℚ) x).comp MvPolynomial.C=RingHom.id ℚ := by
    ext r
    simp
  rw [hc]
  change MvPolynomial.eval (fun i ↦ MvPolynomial.eval x (fixedLinearSubstitution L i)) P=_
  simp_rw [fixedLinearSubstitution_eval]

/-- Arbitrary positive ternary forms and arbitrary fixed levels. -/
theorem fixed_positive_ternary_sphere_constant
    (Q : QuadraticForm ℚ (Fin 3 → ℚ)) (hQ : Q.PosDef)
    (P : Fin 4 → TernaryPoly) (N c : ℚ)
    (h : ∀ z : Fin 3 → ℚ, Q z=N → ∑ i, (MvPolynomial.eval z (P i))^4=c)
    (x y : Fin 3 → ℚ) (hx : Q x=N) (hy : Q y=N) (i : Fin 4) :
    MvPolynomial.eval x (P i)=MvPolynomial.eval y (P i) := by
  by_cases hx0 : x=0
  · have hN : N=0 := by simpa [hx0] using hx.symm
    have hy0 : y=0 := by
      by_contra hny
      have hp := hQ y hny
      rw [hy,hN] at hp
      exact (lt_irrefl (0 : ℚ)) hp
    simp [hx0,hy0]
  obtain ⟨b,hb0,hb⟩ := orthogonal_basis_starting_at Q hQ x hx0
  have hN : 0<N := hx ▸ hQ x hx0
  have hN0 : N ≠ 0 := ne_of_gt hN
  let L := b.equivFun.symm.toLinearMap
  let d : ℚ := Q (b 1)/N
  let e : ℚ := Q (b 2)/N
  have hd : 0<d := div_pos (hQ _ (b.ne_zero 1)) hN
  have he : 0<e := div_pos (hQ _ (b.ne_zero 2)) hN
  have hnorm (u : Fin 3 → ℚ) : Q (L u)=N*sourceNorm d e u := by
    have hh := congrArg (fun F : QuadraticForm ℚ (Fin 3 → ℚ) ↦ F u)
      (Q.basisRepr_eq_of_iIsOrtho b hb)
    simp only [QuadraticMap.basisRepr,QuadraticMap.comp_apply,QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul,←pow_two,Fin.sum_univ_three,hb0,hx] at hh
    change Q (L u)=_ at hh
    rw [hh]
    dsimp [sourceNorm,d,e]
    field_simp
  let F (j : Fin 4) := MvPolynomial.eval₂Hom MvPolynomial.C (fixedLinearSubstitution L) (P j)
  have hF (u : Fin 3 → ℚ) (hu : sourceNorm d e u=1) :
      ∑ j, (MvPolynomial.eval u (F j))^4=c := by
    simp only [F,fixed_eval_substitution]
    apply h
    rw [hnorm,hu,mul_one]
  obtain ⟨v,hv⟩ := fixed_diagonal_unit_sphere_constant d e hd he F c hF
  have hL (z : Fin 3 → ℚ) : L (b.equivFun z)=z := b.equivFun.symm_apply_apply z
  have hux : sourceNorm d e (b.equivFun x)=1 := by
    have hh := hnorm (b.equivFun x)
    rw [hL,hx] at hh
    exact (mul_left_cancel₀ hN0) (by simpa using hh.symm)
  have huy : sourceNorm d e (b.equivFun y)=1 := by
    have hh := hnorm (b.equivFun y)
    rw [hL,hy] at hh
    exact (mul_left_cancel₀ hN0) (by simpa using hh.symm)
  have hh := (hv (b.equivFun x) hux i).trans (hv (b.equivFun y) huy i).symm
  simpa only [F,fixed_eval_substitution,hL] using hh

private lemma fixed_extend_subspace_dimension {V : Type*} [AddCommGroup V] [Module ℚ V]
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

private lemma fixed_ternary_embedding_through_pair {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (hV : 3≤Module.finrank ℚ V) (x y : V) :
    ∃ L : (Fin 3 → ℚ) →ₗ[ℚ] V, Function.Injective L ∧
      ∃ u v : Fin 3 → ℚ, L u=x ∧ L v=y := by
  let U := Submodule.span ℚ (Set.range (![x,y] : Fin 2 → V))
  have hU : Module.finrank ℚ U≤3 := by
    have hh := finrank_range_le_card (R := ℚ) (![x,y] : Fin 2 → V)
    have hh' : Module.finrank ℚ U≤2 := by simpa only [Fintype.card_fin] using hh
    omega
  obtain ⟨W,hUW,hW⟩ := fixed_extend_subspace_dimension 3 U hU hV
  have hx : x∈W := hUW (Submodule.subset_span ⟨0,rfl⟩)
  have hy : y∈W := hUW (Submodule.subset_span ⟨1,rfl⟩)
  let E : (Fin 3 → ℚ) ≃ₗ[ℚ] W := LinearEquiv.ofFinrankEq _ _
    (by rw [Module.finrank_fin_fun,hW])
  let L := W.subtype.comp E.toLinearMap
  have hL : Function.Injective L := Subtype.val_injective.comp E.injective
  refine ⟨L,hL,E.symm ⟨x,hx⟩,E.symm ⟨y,hy⟩,?_,?_⟩ <;> simp [L]


/-- A polynomial map need only have constant fourth-power norm on the single
specified source fiber. Its coordinates are constant on that entire rational fiber. -/
theorem fixed_positive_sphere_constant (n : ℕ) (hn : 3≤n)
    (Q : QuadraticForm ℚ (Fin n → ℚ)) (hQ : Q.PosDef)
    (P : Fin 4 → MvPolynomial (Fin n) ℚ) (N c : ℚ)
    (h : ∀ z : Fin n → ℚ, Q z=N → ∑ i, (MvPolynomial.eval z (P i))^4=c)
    (x y : Fin n → ℚ) (hx : Q x=N) (hy : Q y=N) (i : Fin 4) :
    MvPolynomial.eval x (P i)=MvPolynomial.eval y (P i) := by
  obtain ⟨L,hL,u,v,hu,hv⟩ := fixed_ternary_embedding_through_pair
    (by simpa only [Module.finrank_fin_fun] using hn) x y
  let F (j : Fin 4) := MvPolynomial.eval₂Hom MvPolynomial.C (fixedLinearSubstitution L) (P j)
  have hQL : (Q.comp L).PosDef := by
    intro w hw
    apply hQ
    intro hz
    exact hw (hL (by simpa using hz))
  have hF (w : Fin 3 → ℚ) (hw : (Q.comp L) w=N) :
      ∑ j, (MvPolynomial.eval w (F j))^4=c := by
    simp only [F,fixed_eval_substitution]
    exact h (L w) hw
  have hqu : (Q.comp L) u=N := by simpa only [QuadraticMap.comp_apply,hu] using hx
  have hqv : (Q.comp L) v=N := by simpa only [QuadraticMap.comp_apply,hv] using hy
  have hh := fixed_positive_ternary_sphere_constant (Q.comp L) hQL F N c hF u v hqu hqv i
  simpa only [F,fixed_eval_substitution,hu,hv] using hh

end
end Erdos322Research.QuadraticQuarticFive
