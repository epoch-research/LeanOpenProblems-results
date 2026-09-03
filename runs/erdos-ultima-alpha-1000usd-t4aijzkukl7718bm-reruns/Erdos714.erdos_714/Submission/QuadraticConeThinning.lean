import Submission.QuadraticProfileThinning

/-!
Weighted quadratic slices inherit the existing arbitrary edge-thinning bound.
An application covers the displayed characteristic-three degree-five chart.
This is an obstruction to these incidence models, not a proof or disproof of
Erdős 714. No global classification of threefolds is used or asserted.
-/

noncomputable section
open SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714QuadraticCone

variable {F C X : Type*} [Field F]

/-- Reciprocal-symbol incidence, including isolated vertices with scale zero. -/
def weightedGraph (f : C → X × F → F) : SimpleGraph (C ⊕ ((X × F) × F)) where
  Adj v w := match v, w with
    | .inl c, .inr p => p.2 * f c p.1 = 1
    | .inr p, .inl c => p.2 * f c p.1 = 1
    | _, _ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

lemma inv_weight_imp {s v : F} (h : s⁻¹*v = 1) : v = s := by
  have hs : s ≠ 0 := by intro hs; simp [hs] at h
  exact ((inv_mul_eq_one₀ hs).mp h).symm

variable [Fintype F] [Fintype C] [Fintype X]

/-- Inverting the scale turns every edge of a weighted quadratic host into a
quadratic-code edge. No nonzero-scale hypothesis is omitted: scale zero has
no edges in the weighted host. -/
theorem weighted_quadratic_thinning (f : C → X × F → F)
    (P₀ P₁ P₂ : X → C → F)
    (hf : ∀ c x t, f c (x,t) = P₀ x c + P₁ x c*t + P₂ x c*t^2)
    (H : SimpleGraph (C ⊕ ((X × F) × F))) (hH : H ≤ weightedGraph f)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hX : Fintype.card X ≤ Fintype.card F^2)
    (hC : Fintype.card C ≤ Fintype.card F^4) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  let e := Equiv.sumCongr (Equiv.refl C)
    (Equiv.prodCongr (Equiv.refl (X × F)) (Equiv.inv F))
  let H' := H.comap e
  have hfree' : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H' :=
    Erdos714GraphAveraging.free_comap _ H e.toEmbedding hfree
  have hsub : H' ≤ Erdos714Coding.graph f := by
    intro u v huv
    have h := hH huv
    cases u with
    | inl c =>
      cases v with
      | inl d => exact False.elim h
      | inr p =>
        change p.2⁻¹*f c p.1 = 1 at h
        change p ∈ Erdos714Coding.symbols f c
        exact (Erdos714Coding.mem_symbols f c p.1 p.2).mpr (inv_weight_imp h)
    | inr p =>
      cases v with
      | inr q => exact False.elim h
      | inl c =>
        change p.2⁻¹*f c p.1 = 1 at h
        change p ∈ Erdos714Coding.symbols f c
        exact (Erdos714Coding.mem_symbols f c p.1 p.2).mpr (inv_weight_imp h)
  have hb := Erdos714QuadraticProfileThinning.fourth_power_bound
    f P₀ P₁ P₂ hf H' hsub hfree' hX hC
  let iso : H' ≃g H := ⟨e, Iff.rfl⟩
  rw [iso.card_edgeFinset_eq] at hb
  exact hb

abbrev Point (F : Type*) := Fin 7 → F

/-- The explicit open chart used in the characteristic-three candidate. -/
def chart (a b c : F) : Point F :=
  ![1,a,b,c,b^2-a*c,a^2*c-a*b^2-b*c,c^2+b^3-a*b*c]

def constant (a b : F) : Point F := ![1,a,b,0,b^2,-a*b^2,b^3]
def linear (a b : F) : Point F := ![0,0,0,1,-a,a^2-b,-a*b]
def quadratic : Point F := ![0,0,0,0,0,0,1]

omit [Fintype F] in
lemma chart_expansion (a b c : F) :
    chart a b c = constant a b + c • linear a b + c^2 • quadratic := by
  ext i
  fin_cases i <;> simp [chart, constant, linear, quadratic] <;> ring

/-- The five reduced quadrics; their vanishing on the chart is verified below
directly, rather than inferred from a geometric label. -/
def quadrics (v : Point F) : Fin 5 → F :=
  ![-v 2^2+v 1*v 3+v 0*v 4,
    v 2*v 3+v 1*v 4+v 0*v 5,
    v 3^2+v 2*v 4-v 0*v 6,
    v 3*v 4+v 2*v 5+v 1*v 6,
    -v 4^2+v 3*v 5+v 2*v 6]

omit [Fintype F] in
lemma chart_quadrics_zero (a b c : F) (i : Fin 5) :
    quadrics (chart a b c) i = 0 := by
  fin_cases i <;> simp [quadrics, chart] <;> ring

/-- Nonzero scalar multiples of the chart have an injective parametrization. -/
def conePoint (p : (((F × F) × F) × Fˣ)) : Point F :=
  (p.2 : F) • chart p.1.1.1 p.1.1.2 p.1.2

omit [Fintype F] in
lemma conePoint_injective : Function.Injective (conePoint (F := F)) := by
  rintro ⟨⟨⟨a,b⟩,c⟩,s⟩ ⟨⟨⟨d,e⟩,f⟩,t⟩ h
  have hs : (s : F) = (t : F) := by
    simpa [conePoint, chart] using congrFun h 0
  have hst : s = t := Units.ext hs
  subst t
  have ha : a = d := by
    apply mul_left_cancel₀ (Units.ne_zero s)
    simpa [conePoint, chart] using congrFun h 1
  have hb : b = e := by
    apply mul_left_cancel₀ (Units.ne_zero s)
    simpa [conePoint, chart] using congrFun h 2
  have hc : c = f := by
    apply mul_left_cancel₀ (Units.ne_zero s)
    simpa [conePoint, chart] using congrFun h 3
  subst d
  subst e
  subst f
  rfl

/-- Arbitrary linear column functionals, not only an invariant bilinear form. -/
def coneCode (L : C → Point F →ₗ[F] F) (v : C) (p : (F × F) × F) : F :=
  L v (chart p.1.1 p.1.2 p.2)

omit [Fintype F] [Fintype C] in
lemma coneCode_quadratic (L : C → Point F →ₗ[F] F) (v : C) (ab : F × F) (t : F) :
    coneCode L v (ab,t) = L v (constant ab.1 ab.2) +
      L v (linear ab.1 ab.2)*t + L v quadratic*t^2 := by
  simp only [coneCode, chart_expansion, map_add, map_smul, smul_eq_mul]
  ring

omit [Fintype F] [Fintype C] in
lemma scaled_chart_equation (L : C → Point F →ₗ[F] F)
    (v : C) (ab : F × F) (t s : F) :
    L v (s • chart ab.1 ab.2 t) = 1 ↔ s*coneCode L v (ab,t) = 1 := by
  rw [map_smul, smul_eq_mul]
  rfl

/-- Every free edge subgraph of this cone-chart host loses a power of the
field order. Arbitrary row vertex restrictions are included by deleting all
edges incident with the omitted rows. -/
theorem cone_thinning (L : C → Point F →ₗ[F] F)
    (H : SimpleGraph (C ⊕ (((F × F) × F) × F)))
    (hH : H ≤ weightedGraph (coneCode L))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hC : Fintype.card C ≤ Fintype.card F^4) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  apply weighted_quadratic_thinning (coneCode L)
    (fun ab v => L v (constant ab.1 ab.2))
    (fun ab v => L v (linear ab.1 ab.2)) (fun _ v => L v quadratic)
    (coneCode_quadratic L) H hH hfree _ hC
  simp [pow_two]

/-- In particular a fixed critical-density constant forces bounded field order. -/
theorem cone_size_budget (L : C → Point F →ₗ[F] F)
    (H : SimpleGraph (C ⊕ (((F × F) × F) × F)))
    (hH : H ≤ weightedGraph (coneCode L))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hC : Fintype.card C ≤ Fintype.card F^4)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := cone_thinning L H hH hfree hC
  have h : Fintype.card F^27*Fintype.card F ≤
      Fintype.card F^27*(165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

end Erdos714QuadraticCone

#print axioms Erdos714QuadraticCone.weighted_quadratic_thinning
#print axioms Erdos714QuadraticCone.chart_quadrics_zero
#print axioms Erdos714QuadraticCone.scaled_chart_equation
#print axioms Erdos714QuadraticCone.cone_thinning
#print axioms Erdos714QuadraticCone.cone_size_budget

#print axioms Erdos714QuadraticCone.conePoint_injective
