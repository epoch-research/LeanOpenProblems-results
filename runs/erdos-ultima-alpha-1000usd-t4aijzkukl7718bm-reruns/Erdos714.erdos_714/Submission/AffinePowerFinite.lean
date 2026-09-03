import Submission.AffinePowerGrid

/-! Normal-basis affine parameters and a uniform exclusion of the full
unrefined degree-twelve power host in every characteristic. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714AffinePowerGrid
open Erdos714SkewPowerGrid
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [CharP E 2]

theorem affine_parameters [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ=12) :
    ∃ x y : E, (σ^2) x=x+1 ∧ (σ^3) y=y+1 ∧ (σ^2) y ≠ y := by
  let b := IsGalois.normalBasis F E
  have h₂ : (2 : E)=0 := CharP.cast_eq_zero E 2
  have hact (e f : E ≃ₐ[F] E) : e (b f)=b (e*f) := by
    dsimp only [b]
    rw [IsGalois.normalBasis_apply f,←AlgEquiv.mul_apply,←IsGalois.normalBasis_apply (e*f)]
  have h12 : σ^12=1 := by simpa only [hσ] using pow_orderOf_eq_one σ
  have hn (n : ℕ) (h0 : 0<n) (h1 : n<12) : σ^n ≠ 1 :=
    pow_ne_one_of_lt_orderOf h0.ne' (hσ ▸ h1)
  have hn1 : σ ≠ 1 := by simpa using hn 1 (by decide) (by decide)
  let T := b 1+b (σ^1)+b (σ^2)+b (σ^3)+b (σ^4)+b (σ^5)+b (σ^6)+b (σ^7)+b (σ^8)+b (σ^9)+b (σ^10)+b (σ^11)
  let X := b 1+b (σ^1)+b (σ^4)+b (σ^5)+b (σ^8)+b (σ^9)
  let Y := b 1+b (σ^1)+b (σ^2)+b (σ^6)+b (σ^7)+b (σ^8)
  have hT0 : T ≠ 0 := by
    intro h
    have hc := congrArg (fun z : E => b.repr z 1) h
    simp [T,hn1,hn 2 (by decide) (by decide),hn 3 (by decide) (by decide),hn 4 (by decide) (by decide),hn 5 (by decide) (by decide),hn 6 (by decide) (by decide),hn 7 (by decide) (by decide),hn 8 (by decide) (by decide),hn 9 (by decide) (by decide),hn 10 (by decide) (by decide),hn 11 (by decide) (by decide)] at hc
  have hTσ : σ T=T := by
    change (σ^1) T=T
    dsimp [T]
    simp only [map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    rw [h12]
    ring
  have hTσn (n : ℕ) : (σ^n) T=T := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,AlgEquiv.mul_apply,hTσ,ih]
  have hX : (σ^2) X+X=T := by
    dsimp [X,T]
    simp only [map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    ring
  have hY : (σ^3) Y+Y=T := by
    dsimp [Y,hn1,T]
    simp only [map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    ring
  refine ⟨X/T,Y/T,?_,?_,?_⟩
  · rw [map_div₀,hTσn]
    field_simp [hT0]
    linear_combination hX-X*h₂
  · rw [map_div₀,hTσn]
    field_simp [hT0]
    linear_combination hY-Y*h₂
  · intro h
    rw [map_div₀,hTσn] at h
    have he : (σ^2) Y=Y := (div_left_inj' hT0).mp h
    have hY2 : (σ^2) Y=b (σ^2)+b (σ^3)+b (σ^4)+b (σ^8)+b (σ^9)+b (σ^10) := by
      dsimp [Y]
      simp only [map_add,hact,mul_one,←pow_add]
    rw [hY2] at he
    have hc := congrArg (fun z : E => b.repr z 1) he
    simp [Y,hn1,hn 2 (by decide) (by decide),hn 3 (by decide) (by decide),hn 4 (by decide) (by decide),hn 6 (by decide) (by decide),hn 7 (by decide) (by decide),hn 8 (by decide) (by decide),hn 9 (by decide) (by decide),hn 10 (by decide) (by decide)] at hc

variable [Fintype F] [Fintype E]

def finiteAffineCopy (hdegree : Module.finrank F E=12) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 6))
      (Erdos714WeightedPower.graph
        (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)))) := by
  apply Classical.choice
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hσ : orderOf σ=12 :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E).trans hdegree
  obtain ⟨x,y,hx,hy,hy2⟩ := affine_parameters σ hσ
  have hf (z : E) : σ.toRingEquiv z=z^(Fintype.card F) := rfl
  apply Nonempty.intro
  apply affineCopy σ.toRingEquiv (Fintype.card F) (torusExponent (Fintype.card F))
    Fintype.card_pos hf x y hx hy hy2
  rw [←pow_mul,←exponent_factorization _ Fintype.card_pos]
  have hcard : Fintype.card E=Fintype.card F^12 := by
    rw [Module.card_eq_pow_finrank (K := F),hdegree]
  rw [←hcard]
  apply FiniteField.pow_card_sub_one_eq_one
  simpa using sum_ne_zero σ.toRingEquiv x y hx hy 0 0

theorem twelfth_binary_not_free (hdegree : Module.finrank F E=12) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph
        (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)))) := by
  let e := (Function.Embedding.refl (Fin 4)).sumMap (Fin.castLEEmb (by decide : 4 ≤ 6))
  let c : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph (Fin 4) (Fin 6)) :=
    ⟨⟨e,by intro a b h; cases a <;> cases b <;> simp_all [e]⟩,e.injective⟩
  intro hf
  exact hf ⟨(finiteAffineCopy hdegree).comp c⟩

omit [CharP E 2] in
/-- The original degree-twelve quotient fails over EVERY finite base field,
including q=2. No arbitrary edge-thinning assertion is made. -/
theorem twelfth_not_free_all (hdegree : Module.finrank F E=12) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph
        (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)))) := by
  by_cases hchar : ringChar E=2
  · letI : CharP E 2 := ringChar.of_eq hchar
    exact twelfth_binary_not_free hdegree
  · have ho : Odd (Fintype.card E) :=
      Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hchar)
    rw [Module.card_eq_pow_finrank (K := F),hdegree] at ho
    exact Erdos714SkewPowerGrid.twelfth_not_free ((Nat.odd_pow_iff (by decide : 12 ≠ 0)).mp ho) hdegree

end Erdos714AffinePowerGrid
#print axioms Erdos714AffinePowerGrid.affine_parameters
#print axioms Erdos714AffinePowerGrid.finiteAffineCopy
#print axioms Erdos714AffinePowerGrid.twelfth_not_free_all
