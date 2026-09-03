import Submission.SkewPowerGrid

/-! Uniform finite-field skew parameters for degree-twelve power graphs. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714SkewPowerGrid
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A normal basis supplies the required degree-four and degree-six skew
orbits without making any choice of a polynomial defining the field. -/
theorem skew_parameters [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ=12) :
    ∃ x y : E, x ≠ 0 ∧ y ≠ 0 ∧ (σ^2) x = -x ∧ (σ^3) y = -y ∧ (σ^2) y ≠ y := by
  let b := IsGalois.normalBasis F E
  have hact (e f : E ≃ₐ[F] E) : e (b f)=b (e*f) := by
    dsimp only [b]
    rw [IsGalois.normalBasis_apply f,←AlgEquiv.mul_apply,←IsGalois.normalBasis_apply (e*f)]
  have h12 : σ^12=1 := by simpa only [hσ] using pow_orderOf_eq_one σ
  have hn (n : ℕ) (h0 : 0<n) (h1 : n<12) : σ^n ≠ 1 :=
    pow_ne_one_of_lt_orderOf h0.ne' (hσ ▸ h1)
  let x := b 1+b (σ^4)+b (σ^8)-b (σ^2)-b (σ^6)-b (σ^10)
  let y := b 1+b (σ^6)-b (σ^3)-b (σ^9)
  have hx0 : x ≠ 0 := by
    intro h
    have hc := congrArg (fun z : E => b.repr z 1) h
    simp [x,hn 2 (by decide) (by decide),hn 4 (by decide) (by decide),
      hn 6 (by decide) (by decide),hn 8 (by decide) (by decide),
      hn 10 (by decide) (by decide)] at hc
  have hy0 : y ≠ 0 := by
    intro h
    have hc := congrArg (fun z : E => b.repr z 1) h
    simp [y,hn 3 (by decide) (by decide),hn 6 (by decide) (by decide),
      hn 9 (by decide) (by decide)] at hc
  have hx : (σ^2) x = -x := by
    dsimp [x]
    simp only [map_sub,map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    rw [h12]
    ring
  have hy : (σ^3) y = -y := by
    dsimp [y]
    simp only [map_sub,map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    rw [h12]
    ring
  refine ⟨x,y,hx0,hy0,hx,hy,?_⟩
  have hy2 : (σ^2) y = b (σ^2)+b (σ^8)-b (σ^5)-b (σ^11) := by
    dsimp [y]
    simp only [map_sub,map_add,hact,mul_one,←pow_add]
  intro h
  rw [hy2] at h
  have hc := congrArg (fun z : E => b.repr z 1) h
  simp [y,hn 2 (by decide) (by decide),hn 3 (by decide) (by decide),
    hn 5 (by decide) (by decide),hn 6 (by decide) (by decide),
    hn 8 (by decide) (by decide),hn 9 (by decide) (by decide),
    hn 11 (by decide) (by decide)] at hc

variable [Fintype F] [Fintype E]

/-- A general exponent-divisibility criterion for a degree-twelve extension. -/
theorem finite_not_free (hq : Odd (Fintype.card F)) (h₂ : (2 : E) ≠ 0)
    (hdegree : Module.finrank F E=12) (d : ℕ)
    (hd : Fintype.card E-1 ∣ d*modulus (Fintype.card F)) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph (Erdos714WeightedPower.powerMap E d)) := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hσ : orderOf σ=12 :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E).trans hdegree
  obtain ⟨x,y,hx0,hy0,hx,hy,hy2⟩ := skew_parameters σ hσ
  have hf (z : E) : σ.toRingEquiv z=z^(Fintype.card F) := rfl
  apply not_free_of_skew σ.toRingEquiv (Fintype.card F) d hq hf h₂ x y hx0 hy0 hx hy hy2
  have hz : x+y ≠ 0 := by
    simpa using sum_ne_zero σ.toRingEquiv x y h₂ hx0 hx hy 0 0
  let u : Eˣ := Units.mk0 (x+y) hz
  have hu : u^(Fintype.card E-1)=1 := by
    simpa only [Fintype.card_units] using pow_card_eq_one (x := u)
  obtain ⟨m,hm⟩ := hd
  have hpow : u^(d*modulus (Fintype.card F))=1 := by rw [hm,pow_mul,hu,one_pow]
  have he := congrArg (fun v : Eˣ => (v : E)) hpow
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,Units.val_mk0,pow_mul] using he

end Erdos714SkewPowerGrid
#print axioms Erdos714SkewPowerGrid.skew_parameters
#print axioms Erdos714SkewPowerGrid.finite_not_free
