import FormalConjecturesUtil

/-!
A conjugate-grid obstruction to multiplicatively weighted norms on the trace-zero
subspace of a cyclic quartic extension. This does not settle Erdős Problem 714.
-/

open SimpleGraph

noncomputable section

namespace Erdos714QuarticNormProduct

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

abbrev Point (F E : Type*) [Field F] [Field E] [Algebra F E] :=
  LinearMap.ker (Algebra.trace F E)

/-- Two copies of the trace-zero space, with nonzero multiplicative weights. -/
def graph : SimpleGraph ((Point F E × Fˣ) ⊕ (Point F E × Fˣ)) where
  Adj v w := match v, w with
    | .inl x, .inr y => Algebra.norm F ((x.1 : E) + (y.1 : E)) = (x.2 : F) * (y.2 : F)
    | .inr y, .inl x => Algebra.norm F ((x.1 : E) + (y.1 : E)) = (x.2 : F) * (y.2 : F)
    | _, _ => False
  symm := by intro v w; cases v <;> cases w <;> simp_all
  loopless := by intro v; cases v <;> simp

/-- An element negated by an algebra automorphism has zero trace in odd characteristic. -/
lemma trace_zero_of_skew (h2 : (2 : F) ≠ 0) (σ : E ≃ₐ[F] E) {x : E}
    (hx : σ x = -x) : Algebra.trace F E x = 0 := by
  have ht := Algebra.trace_eq_of_algEquiv σ x
  rw [hx, map_neg] at ht
  apply (mul_eq_zero.mp (show (2 : F) * Algebra.trace F E x = 0 by linear_combination -ht)).resolve_left h2

/-- Four successive conjugates, written using the relative trace-zero identity. -/
def orbit (σ : E ≃ₐ[F] E) (v : E) : Fin 4 → E := ![v, σ v, -v, -σ v]

lemma orbit_pow (σ : E ≃ₐ[F] E) (v : E) (hv : (σ ^ 2) v = -v) (j : Fin 4) :
    orbit σ v j = (σ ^ (j : ℕ)) v := by
  have h3 : (σ ^ 3) v = -σ v := by
    rw [show 3 = 1 + 2 by rfl, pow_add, pow_one, AlgEquiv.mul_apply, hv, map_neg]
  fin_cases j <;> simp [orbit, hv, h3]

lemma orbit_skew (σ : E ≃ₐ[F] E) (v : E) (hv : (σ ^ 2) v = -v) (j : Fin 4) :
    (σ ^ 2) (orbit σ v j) = -orbit σ v j := by
  rw [orbit_pow σ v hv]
  have hc : σ ^ 2 * σ ^ (j : ℕ) = σ ^ (j : ℕ) * σ ^ 2 := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  rw [← AlgEquiv.mul_apply, hc, AlgEquiv.mul_apply, hv, map_neg]

lemma orbit_injective (h2 : (2 : E) ≠ 0) (σ : E ≃ₐ[F] E) (v : E)
    (hv0 : v ≠ 0) (hv : (σ ^ 2) v = -v) : Function.Injective (orbit σ v) := by
  have hn : v ≠ -v := by
    intro h
    exact (mul_ne_zero h2 hv0) (by linear_combination h : (2 : E) * v = 0)
  have hn' : σ v ≠ -σ v := by simpa only [← map_neg, σ.injective.ne_iff] using hn
  have h1 : v ≠ σ v := by
    intro h
    apply hn
    calc
      v = σ (σ v) := h.trans (congrArg σ h)
      _ = -v := hv
  have h3 : v ≠ -σ v := by
    intro h
    have hh := congrArg σ h
    rw [map_neg] at hh
    change σ v = -(σ ^ 2) v at hh
    rw [hv, neg_neg] at hh
    exact h1 hh.symm
  have h3' : σ v ≠ -v := by
    intro h
    exact h3 (by rw [h, neg_neg])
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [orbit, hn, hn', h1, h3, h3', Ne.symm hn, Ne.symm hn', Ne.symm h1,
      Ne.symm h3, Ne.symm h3'] at hij ⊢

variable [FiniteDimensional F E]

/-- The trace-zero weighted norm graph contains a whole scalar line against four conjugates. -/
def conjugateGrid (h2 : (2 : F) ≠ 0) (σ : E ≃ₐ[F] E) (u v : E)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : σ u = -u) (hv : (σ ^ 2) v = -v) :
    Copy (completeBipartiteGraph F (Fin 4)) (graph (F := F) (E := E)) := by
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  have hu2 : (σ ^ 2) u = u := by
    simp [pow_two, AlgEquiv.mul_apply, hu]
  have htu (t : F) : Algebra.trace F E (algebraMap F E t * u) = 0 := by
    apply trace_zero_of_skew h2 σ
    rw [map_mul, σ.commutes, hu]
    ring
  have huv (j : Fin 4) : Algebra.trace F E (u * orbit σ v j) = 0 := by
    apply trace_zero_of_skew h2 (σ ^ 2)
    rw [map_mul, hu2, orbit_skew σ v hv]
    ring
  have htv (t : F) : algebraMap F E t + v ≠ 0 := by
    intro h
    have he : v = -algebraMap F E t := eq_neg_of_add_eq_zero_right h
    have hfix : (σ ^ 2) v = v := by rw [he, map_neg, AlgEquiv.commutes]
    have hn : v = -v := hfix.symm.trans hv
    exact mul_ne_zero h2E hv0 (by linear_combination hn : (2 : E) * v = 0)
  let weight (t : F) : Fˣ := Units.mk0 (Algebra.norm F u * Algebra.norm F (algebraMap F E t + v))
    (mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hu0) (Algebra.norm_ne_zero_iff.mpr (htv t)))
  let L (t : F) : Point F E × Fˣ := (⟨algebraMap F E t * u, htu t⟩, weight t)
  let R (j : Fin 4) : Point F E × Fˣ := (⟨u * orbit σ v j, huv j⟩, 1)
  have hL : Function.Injective L := by
    intro t s h
    exact (algebraMap F E).injective (mul_right_cancel₀ hu0
      (congrArg (fun w : Point F E × Fˣ => (w.1 : E)) h))
  have hR : Function.Injective R := by
    intro i j h
    exact orbit_injective h2E σ v hv0 hv (mul_left_cancel₀ hu0
      (congrArg (fun w : Point F E × Fˣ => (w.1 : E)) h))
  have hE (t : F) (j : Fin 4) : graph.Adj (.inl (L t)) (.inr (R j)) := by
    change Algebra.norm F (algebraMap F E t * u + u * orbit σ v j) =
      (Algebra.norm F u * Algebra.norm F (algebraMap F E t + v)) * 1
    rw [show algebraMap F E t * u + u * orbit σ v j =
      u * (algebraMap F E t + orbit σ v j) by ring, map_mul, mul_one]
    congr 1
    rw [orbit_pow σ v hv]
    have he : algebraMap F E t + (σ ^ (j : ℕ)) v =
        (σ ^ (j : ℕ)) (algebraMap F E t + v) := by rw [map_add, AlgEquiv.commutes]
    rw [he, Algebra.norm_eq_of_algEquiv]
  let le : F ↪ Point F E × Fˣ := ⟨L, hL⟩
  let re : Fin 4 ↪ Point F E × Fˣ := ⟨R, hR⟩
  refine ⟨⟨le.sumMap re, ?_⟩, (le.sumMap re).injective⟩
  intro a b hab
  cases a with
  | inl t =>
    cases b with
    | inl s => simp at hab
    | inr j => exact hE t j
  | inr j =>
    cases b with
    | inl t => exact hE t j
    | inr i => simp at hab

/-- A normal basis supplies the two skew elements in every cyclic quartic Galois extension. -/
theorem skew_parameters [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : orderOf σ = 4) :
    ∃ u v : E, u ≠ 0 ∧ v ≠ 0 ∧ σ u = -u ∧ (σ ^ 2) v = -v := by
  classical
  let b := IsGalois.normalBasis F E
  have hact (e f : E ≃ₐ[F] E) : e (b f) = b (e * f) := by
    dsimp only [b]
    rw [IsGalois.normalBasis_apply f, ← AlgEquiv.mul_apply,
      ← IsGalois.normalBasis_apply (e * f)]
  have h4 : σ ^ 4 = 1 := by simpa only [hσ] using pow_orderOf_eq_one σ
  have h1 : σ ≠ 1 := by
    simpa only [pow_one] using pow_ne_one_of_lt_orderOf
      (x := σ) (n := 1) (by decide) (by omega)
  have h2 : σ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by decide) (by omega)
  have h3 : σ ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by decide) (by omega)
  let u := b 1 - b σ + b (σ ^ 2) - b (σ ^ 3)
  let v := b 1 - b (σ ^ 2)
  have hu0 : u ≠ 0 := by
    intro h
    have hc := congrArg (fun x : E => b.repr x 1) h
    simp [u, h1, h2, h3] at hc
  have hv0 : v ≠ 0 := by
    intro h
    have hc := congrArg (fun x : E => b.repr x 1) h
    simp [v, h2] at hc
  refine ⟨u, v, hu0, hv0, ?_, ?_⟩
  · dsimp only [u]
    simp only [map_sub, map_add, hact, mul_one]
    rw [← pow_two, ← pow_succ', ← pow_succ', h4]
    ring
  · dsimp only [v]
    simp only [map_sub, hact, mul_one, ← pow_add, show 2 + 2 = 4 by rfl, h4]
    ring

/-- In a cyclic quartic extension of odd characteristic the proposed graph has a K_|F|,4. -/
def cyclicQuarticGrid [IsGalois F E] (h2 : (2 : F) ≠ 0)
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ = 4) :
    Copy (completeBipartiteGraph F (Fin 4)) (graph (F := F) (E := E)) := by
  apply Classical.choice
  obtain ⟨u, v, hu0, hv0, hu, hv⟩ := skew_parameters σ hσ
  exact ⟨conjugateGrid h2 σ u v hu0 hv0 hu hv⟩

/-- Over every odd finite base field, every quartic extension has the conjugate grid. -/
def finiteQuarticGrid [Fintype F] [Finite E] (h2 : (2 : F) ≠ 0)
    (hdegree : Module.finrank F E = 4) :
    Copy (completeBipartiteGraph F (Fin 4)) (graph (F := F) (E := E)) :=
  cyclicQuarticGrid h2 (FiniteField.frobeniusAlgEquivOfAlgebraic F E)
    ((FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E).trans hdegree)

/-- The odd-characteristic quartic trace-zero norm construction is not K44-free. -/
theorem finiteQuartic_not_free [Fintype F] [Finite E] (h2 : (2 : F) ≠ 0)
    (hdegree : Module.finrank F E = 4) (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  let e : Fin 4 ↪ F := (Fin.castLEEmb hq).trans (Fintype.equivFin F).symm.toEmbedding
  let f := e.sumMap (Function.Embedding.refl (Fin 4))
  have c : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph F (Fin 4)) := by
    refine ⟨⟨f, ?_⟩, f.injective⟩
    intro x y h
    cases x <;> cases y <;> simp_all [f]
  intro hfree
  exact hfree ⟨(finiteQuarticGrid h2 hdegree).comp c⟩

#print axioms trace_zero_of_skew
#print axioms conjugateGrid
#print axioms skew_parameters
#print axioms cyclicQuarticGrid
#print axioms finiteQuarticGrid
#print axioms finiteQuartic_not_free

end Erdos714QuarticNormProduct
