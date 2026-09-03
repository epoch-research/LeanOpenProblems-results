import FormalConjecturesUtil

/-!
An obstruction to norm graphs obtained from nonlinear pencils of linear maps.
This is an auxiliary construction obstruction, not a solution of Erdős 714.
-/

open SimpleGraph

noncomputable section

namespace Erdos714NonlinearNormPencil

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A nonscalar linear map over a finite field has an affine line on which
`(1 + T x) / x` is constant. -/
theorem affine_pencil [Finite E] (T : E →ₗ[F] E)
    (hT : ¬ ∃ z : E, ∀ x : E, T x = z * x) :
    ∃ b v z : E, v ≠ 0 ∧ T v = z * v ∧ 1 + T b = z * b := by
  classical
  let g : E → E := fun x => if x = 0 then T 1 else (1 + T x) / x
  have collision : ∀ {b v z : E}, b ≠ 0 → v ≠ 0 →
      T v = z * v → 1 + T b = z * b →
      b + v ≠ 0 ∧ g (b + v) = g b := by
    intro b v z hb _ hv he
    have he' : 1 + T (b + v) = z * (b + v) := by
      rw [map_add, hv]
      linear_combination he
    have hsum : b + v ≠ 0 := by
      intro hz
      rw [hz, map_zero, mul_zero, add_zero] at he'
      exact one_ne_zero he'
    refine ⟨hsum, ?_⟩
    simp only [g, if_neg hb, if_neg hsum]
    rw [he', he, mul_div_cancel_right₀ _ hsum, mul_div_cancel_right₀ _ hb]
  have hginj : ¬ Function.Injective g := by
    intro hinj
    apply hT
    refine ⟨T 1, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    let z := T x / x
    have hxz : T x = z * x := by simp [z, hx]
    obtain ⟨b, hb⟩ := (Finite.surjective_of_injective hinj) z
    by_cases hb0 : b = 0
    · have hz : T 1 = z := by simpa [g, hb0] using hb
      rw [hz]
      exact hxz
    · have he : 1 + T b = z * b := by
        exact (div_eq_iff hb0).mp (by simpa [g, hb0] using hb)
      have hcol := (collision hb0 hx hxz he).2
      have hbx := hinj hcol
      exact False.elim (hx (add_left_cancel (show b + x = b + 0 by simpa using hbx)))
  obtain ⟨b, c, hbc, hne⟩ := Function.not_injective_iff.mp hginj
  by_cases hb : b = 0
  · have hc : c ≠ 0 := by simpa [hb] using Ne.symm hne
    refine ⟨c, 1, T 1, one_ne_zero, by simp, ?_⟩
    exact (div_eq_iff hc).mp (by simpa [g, hb, hc] using hbc.symm)
  by_cases hc : c = 0
  · refine ⟨b, 1, T 1, one_ne_zero, by simp, ?_⟩
    exact (div_eq_iff hb).mp (by simpa [g, hb, hc] using hbc)
  let z := (1 + T b) / b
  have heb : 1 + T b = z * b := by simp [z, hb]
  have hec : 1 + T c = z * c := by
    apply (div_eq_iff hc).mp
    simpa [g, hb, hc, z] using hbc.symm
  refine ⟨b, c-b, z, sub_ne_zero.mpr (Ne.symm hne), ?_, heb⟩
  rw [map_sub]
  linear_combination hec - heb

/-- Every point of the affine line is nonzero and has the same pencil value. -/
theorem affine_pencil_line (T : E →ₗ[F] E) {b v z : E}
    (hv : T v = z*v) (hb : 1 + T b = z*b) (s : F) :
    b + algebraMap F E s * v ≠ 0 ∧
      1 + T (b + algebraMap F E s * v) = z * (b + algebraMap F E s * v) := by
  have he : 1 + T (b + algebraMap F E s * v) =
      z * (b + algebraMap F E s * v) := by
    have hsm : T (algebraMap F E s * v) = algebraMap F E s * T v := by
      simpa only [Algebra.smul_def] using T.map_smul s v
    rw [map_add, hsm, hv]
    linear_combination hb
  refine ⟨?_, he⟩
  intro h
  rw [h, map_zero, mul_zero, add_zero] at he
  exact one_ne_zero he


/-- The bipartite norm graph for an arbitrary bilinear multiplication. -/
def graph (B : E →ₗ[F] E →ₗ[F] E) : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ)) where
  Adj v w := match v, w with
    | .inl x, .inr y => Algebra.norm F (1 + B x.1 y.1) = (x.2 : F) * (y.2 : F)
    | .inr y, .inl x => Algebra.norm F (1 + B x.1 y.1) = (x.2 : F) * (y.2 : F)
    | _, _ => False
  symm := by intro v w; cases v <;> cases w <;> simp_all
  loopless := by intro v; cases v <;> simp

variable [FiniteDimensional F E]

/-- A nonscalar pencil gives all but at most one scalar row against an entire
scalar line of columns. -/
theorem norm_pencil_grid [Finite E] (B : E →ₗ[F] E →ₗ[F] E)
    (a u : E) (hu : u ≠ 0) (L : E ≃ₗ[F] E)
    (hL : ∀ x, B u x = L x)
    (hT : ¬ ∃ z : E, ∀ x : E, B a (L.symm x) = z*x) :
    ∃ z : E, Nonempty (Copy
      (completeBipartiteGraph {t : F // z + algebraMap F E t ≠ 0} F) (graph B)) := by
  classical
  let T : E →ₗ[F] E := (B a).comp L.symm.toLinearMap
  obtain ⟨b,v,z,hv0,hv,hb⟩ := affine_pencil T hT
  let S := {t : F // z + algebraMap F E t ≠ 0}
  let d : F → E := fun s => b + algebraMap F E s * v
  have hd (s : F) := affine_pencil_line T hv hb s
  let row : S → E × Fˣ := fun t =>
    (a + algebraMap F E (t : F) * u,
      Units.mk0 (Algebra.norm F (z + algebraMap F E (t : F)))
        (Algebra.norm_ne_zero_iff.mpr t.property))
  let col : F → E × Fˣ := fun s =>
    (L.symm (d s), Units.mk0 (Algebra.norm F (d s))
      (Algebra.norm_ne_zero_iff.mpr (hd s).1))
  have hrow : Function.Injective row := by
    intro t s he
    have hx := congrArg Prod.fst he
    change a + algebraMap F E (t : F) * u = a + algebraMap F E (s : F) * u at hx
    exact Subtype.ext ((algebraMap F E).injective (mul_right_cancel₀ hu (add_left_cancel hx)))
  have hcol : Function.Injective col := by
    intro t s he
    have hx := L.symm.injective (congrArg Prod.fst he)
    change b + algebraMap F E t * v = b + algebraMap F E s * v at hx
    exact (algebraMap F E).injective (mul_right_cancel₀ hv0 (add_left_cancel hx))
  have hedge (t : S) (s : F) :
      Algebra.norm F (1 + B (row t).1 (col s).1) =
        ((row t).2 : F) * ((col s).2 : F) := by
    have hsm : B (algebraMap F E (t : F) * u) = (t : F) • B u := by
      simpa only [Algebra.smul_def] using B.map_smul (t : F) u
    have hline : 1 + B (row t).1 (col s).1 =
        (z + algebraMap F E (t : F)) * d s := by
      change 1 + B (a + algebraMap F E (t : F) * u) (L.symm (d s)) = _
      rw [map_add, hsm, LinearMap.add_apply, LinearMap.smul_apply,
        hL, L.apply_symm_apply, Algebra.smul_def]
      have ht : 1 + B a (L.symm (d s)) = z * d s := (hd s).2
      linear_combination ht
    rw [hline, map_mul]
    rfl
  let le : S ↪ E × Fˣ := ⟨row, hrow⟩
  let re : F ↪ E × Fˣ := ⟨col, hcol⟩
  refine ⟨z, ⟨⟨⟨le.sumMap re, ?_⟩, (le.sumMap re).injective⟩⟩⟩
  intro x y hxy
  cases x with
  | inl t =>
    cases y with
    | inl s => simp at hxy
    | inr s => exact hedge t s
  | inr s =>
    cases y with
    | inl t => exact hedge t s
    | inr t => simp at hxy


/-- In particular a nonscalar pencil prevents `K_{r,r}`-freeness once `|F|>r`. -/
theorem norm_pencil_not_free [Fintype F] [Finite E]
    (B : E →ₗ[F] E →ₗ[F] E) (a u : E) (hu : u ≠ 0)
    (L : E ≃ₗ[F] E) (hL : ∀ x, B u x = L x)
    (hT : ¬ ∃ z : E, ∀ x : E, B a (L.symm x) = z*x)
    {r : ℕ} (hq : r + 1 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph B) := by
  classical
  obtain ⟨z, ⟨grid⟩⟩ := norm_pencil_grid B a u hu L hL hT
  haveI : Subsingleton {t : F // z + algebraMap F E t = 0} := by
    exact ⟨fun t s => Subtype.ext ((algebraMap F E).injective
      (add_left_cancel (t.property.trans s.property.symm)))⟩
  have hbad : Fintype.card {t : F // z + algebraMap F E t = 0} ≤ 1 := by
    simpa using Fintype.card_le_of_injective
      (fun _ : {t : F // z + algebraMap F E t = 0} => ())
      (fun _ _ _ => Subsingleton.elim _ _)
  have hgood : r ≤ Fintype.card {t : F // z + algebraMap F E t ≠ 0} := by
    rw [Fintype.card_subtype_compl]
    omega
  obtain ⟨le⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := {t : F // z + algebraMap F E t ≠ 0}) (by simpa using hgood)
  obtain ⟨re⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := F) (by simp only [Fintype.card_fin]; omega)
  let emb : Copy (completeBipartiteGraph (Fin r) (Fin r))
      (completeBipartiteGraph {t : F // z + algebraMap F E t ≠ 0} F) :=
    ⟨⟨le.sumMap re, by intro x y hxy; cases x <;> cases y <;> simp_all⟩,
      (le.sumMap re).injective⟩
  intro hfree
  exact hfree ⟨grid.comp emb⟩

/-- Every free bilinear norm graph with an invertible row has the ordinary
field-multiplication form after a linear change of column coordinates. -/
theorem scalar_form_of_free [Fintype F] [Finite E]
    (B : E →ₗ[F] E →ₗ[F] E) (u : E) (hu : u ≠ 0)
    (L : E ≃ₗ[F] E) (hL : ∀ x, B u x = L x)
    {r : ℕ} (hq : r + 1 ≤ Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph B)) :
    ∀ a x, B a x = B a (L.symm 1) * L x := by
  intro a x
  have hscalar : ∃ z : E, ∀ y : E, B a (L.symm y) = z*y := by
    by_contra hn
    exact norm_pencil_not_free B a u hu L hL hn hq hfree
  obtain ⟨z,hz⟩ := hscalar
  have hone : B a (L.symm 1) = z := by simpa using hz 1
  rw [hone]
  simpa using hz (L x)


/-- An Albert-type twisted bilinear product. -/
def twisted (σ τ : E ≃ₐ[F] E) (c : E) : E →ₗ[F] E →ₗ[F] E where
  toFun a :=
    { toFun := fun b => a*b - c*σ a*τ b
      map_add' := by intro x y; simp only [map_add]; ring
      map_smul' := by
        intro t x
        simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes, RingHom.id_apply]
        ring }
  map_add' := by
    intro x y
    ext b
    change (x+y)*b-c*σ (x+y)*τ b = (x*b-c*σ x*τ b)+(y*b-c*σ y*τ b)
    rw [map_add]
    ring
  map_smul' := by
    intro t x
    ext b
    change (t • x)*b-c*σ (t • x)*τ b = t • (x*b-c*σ x*τ b)
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]
    ring

/-- The row at one is invertible whenever the twisting coefficient has norm
other than one. -/
theorem twisted_one_injective (σ τ : E ≃ₐ[F] E) (c : E)
    (hc : Algebra.norm F c ≠ 1) : Function.Injective (twisted σ τ c 1) := by
  have hker : ∀ x, twisted σ τ c 1 x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have he : x = c * τ x := by simpa [twisted] using sub_eq_zero.mp hx
    have hn := congrArg (Algebra.norm F) he
    rw [map_mul, Algebra.norm_eq_of_algEquiv] at hn
    apply hc
    exact mul_right_cancel₀ (Algebra.norm_ne_zero_iff.mpr hx0)
      (by simpa using hn.symm : Algebra.norm F c * Algebra.norm F x = 1 * Algebra.norm F x)
  intro x y hxy
  exact sub_eq_zero.mp (hker (x-y) (by rw [map_sub, hxy, sub_self]))

omit [FiniteDimensional F E] in
/-- With both automorphisms nontrivial, some row is not a scalar multiple of
the row at one. -/
theorem twisted_nonscalar (σ τ : E ≃ₐ[F] E) (hσ : σ ≠ 1) (hτ : τ ≠ 1)
    (c : E) (hc : c ≠ 0) :
    ∃ a : E, ¬ ∃ z : E, ∀ x, twisted σ τ c a x = z * twisted σ τ c 1 x := by
  have hex : ∃ a : E, σ a ≠ a := by
    by_contra! h
    apply hσ
    ext a
    exact h a
  obtain ⟨a,ha⟩ := hex
  refine ⟨a, ?_⟩
  rintro ⟨z,hz⟩
  have hone : a - c*σ a = z*(1-c) := by simpa [twisted] using hz 1
  let k := c*(σ a-z)
  have hk : k ≠ 0 := by
    intro hk0
    have hs : σ a = z := sub_eq_zero.mp ((mul_eq_zero.mp hk0).resolve_left hc)
    apply ha
    linear_combination -hone + (1-c)*hs
  apply hτ
  ext x
  have he : a*x - c*σ a*τ x = z*(x-c*τ x) := by simpa [twisted] using hz x
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show k*(τ x-x) = 0 by
    dsimp only [k]
    linear_combination -he + x*hone)).resolve_left hk

/-- Nontrivially twisted bilinear norm graphs are never free at the critical
parameters; this holds in every characteristic and extension degree. -/
theorem twisted_not_free [Fintype F] [Finite E]
    (σ τ : E ≃ₐ[F] E) (hσ : σ ≠ 1) (hτ : τ ≠ 1)
    (c : E) (hc0 : c ≠ 0) (hc : Algebra.norm F c ≠ 1)
    {r : ℕ} (hq : r + 1 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph (twisted σ τ c)) := by
  let B := twisted σ τ c
  have hi := twisted_one_injective σ τ c hc
  let L : E ≃ₗ[F] E := LinearEquiv.ofBijective (B 1) ⟨hi, Finite.surjective_of_injective hi⟩
  obtain ⟨a,ha⟩ := twisted_nonscalar σ τ hσ hτ c hc0
  apply norm_pencil_not_free B a 1 one_ne_zero L (fun _ => rfl) _ hq
  rintro ⟨z,hz⟩
  apply ha
  refine ⟨z, fun x => ?_⟩
  simpa only [L.symm_apply_apply] using hz (L x)

end Erdos714NonlinearNormPencil

#print axioms Erdos714NonlinearNormPencil.affine_pencil
#print axioms Erdos714NonlinearNormPencil.affine_pencil_line
#print axioms Erdos714NonlinearNormPencil.norm_pencil_grid
#print axioms Erdos714NonlinearNormPencil.norm_pencil_not_free
#print axioms Erdos714NonlinearNormPencil.scalar_form_of_free
#print axioms Erdos714NonlinearNormPencil.twisted_one_injective
#print axioms Erdos714NonlinearNormPencil.twisted_nonscalar
#print axioms Erdos714NonlinearNormPencil.twisted_not_free
