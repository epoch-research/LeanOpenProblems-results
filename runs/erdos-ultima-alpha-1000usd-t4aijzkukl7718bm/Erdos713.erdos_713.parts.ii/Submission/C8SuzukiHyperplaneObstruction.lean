import FormalConjecturesUtil
import Submission.SuzukiTraceSlices
import Submission.C8MixedSuzukiCosets
import Submission.C8SuzukiNormalization

/-! A uniform mixed octagon obstruction for restricted Suzuki-type centers
opposite shifted noncentral hyperplanes. This does not settle Erdos 713. -/
open SimpleGraph
namespace Erdos713C8SuzukiHyperplaneObstruction
open Erdos713C8MixedSuzukiMatrices Erdos713C8SuzukiNormalization
open Erdos713SuzukiTraceBasics Erdos713SuzukiTraceSlices
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
set_option maxHeartbeats 2000000

/-- The full center is unnecessary if it contains this one parameter. -/
theorem contains_normalized_at (σ : F →+* F) (hσ : ∀ a, σ (σ a)=a^2)
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (x y : G) (hx : x ∈ H) (hy : y ∈ K) (t : F)
    (hX : ρ x=X (1/((1+t+σ t)*σ (1+t+σ t)))
      (σ (1/((1+t+σ t)*σ (1+t+σ t)))))
    (hY : ρ y=Y t (1+t+σ t)) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  let k := 1+t+σ t
  let ℓ := t^2+t+k
  let u := 1/(k*ℓ)
  let v := u/k
  have hℓσ : σ k=ℓ := by
    dsimp [k,ℓ]
    simp only [map_add,map_one,hσ]
    ring_nf
    reduce_mod_char!
  obtain ⟨hk,hℓ,hσu⟩ := twisted_scalars σ hσ t
  have hu : u ≠ 0 := one_div_ne_zero (mul_ne_zero hk hℓ)
  have hv : v ≠ 0 := div_ne_zero hu hk
  have hvσ : σ u=v := hσu
  have hX' : ρ x=X u v := by
    change ρ x=X (1/(k*σ k)) (σ (1/(k*σ k))) at hX
    rw [hℓσ] at hX
    change ρ x=X u (σ u) at hX
    simpa only [hvσ] using hX
  have hrel := scalar_relations t k hk
  exact Erdos713C8MixedSuzukiCosets.contains_from_matrices ρ hρ H K hH hK
    x y hx hy t k u v hX' hY hk hu hv hrel.1 hrel.2

/-- Both central and noncentral parameters may be restricted to the
indicated hyperplanes. The upper shift may be zero or one. -/
theorem contains_normalized [Fintype F] (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F=2^(2*r-1))
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (β δ a : F) (hβ : β ≠ 0) (hδ0 : δ ≠ 0) (hδ : tr (2*r-1) δ=0) (ha : a=0 ∨ a=1)
    (hCenter : ∀ z : F, tr (2*r-1) (β*z)=0 → ∃ x ∈ H, ρ x=X z (z^(2^r)))
    (hUpper : ∀ t : F, tr (2*r-1) (δ*t)=a → ∃ y ∈ K, ρ y=Y t (1+t+t^(2^r))) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  obtain ⟨t,ht,hu⟩ := shifted_hyperplane_intersection r hr hcard β δ a hβ hδ0 hδ ha
  let u := 1/((1+t+t^(2^r))*(1+t+t^(2^r))^(2^r))
  have hu' : tr (2*r-1) (β*u)=0 := by
    simpa only [u,one_div,div_eq_mul_inv,one_mul] using hu
  obtain ⟨x,hx,hX⟩ := hCenter u hu'
  obtain ⟨y,hy,hY⟩ := hUpper t ht
  let σ := iterateFrobenius F 2 r
  have hσ : ∀ z : F, σ (σ z)=z^2 := fun z => sigma_twice r (by omega) hcard z
  exact contains_normalized_at σ hσ ρ hρ H K hH hK x y hx hy t hX hY

/-- Arbitrary relative scaling is allowed. The closure condition for the
upper hyperplane is precisely that it contain the square parameter `c*c^sigma`. -/
theorem contains_scaled [Fintype F] (r : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card F=2^(2*r-1))
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (β δ a c : F) (hβ : β ≠ 0) (hδ0 : δ ≠ 0) (hc : c ≠ 0)
    (hδ : tr (2*r-1) (δ*(c*c^(2^r)))=0) (ha : a=0 ∨ a=1)
    (hCenter : ∀ z : F, tr (2*r-1) (β*z)=0 → ∃ x ∈ H, ρ x=X z (z^(2^r)))
    (hUpper : ∀ d : F, tr (2*r-1) (δ*d)=a →
      ∃ y ∈ K, ρ y=upper (iterateFrobenius F 2 r) c d) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  let σ := iterateFrobenius F 2 r
  have hσ : ∀ z : F, σ (σ z)=z^2 := fun z => sigma_twice r (by omega) hcard z
  let w := weights σ c
  have hw : ∀ i, w i ≠ 0 := weights_ne_zero σ c hc
  let ρ' : G →* Mat F := (conjugate w hw).comp ρ
  have hρ' : Function.Injective ρ' := (conjugate_injective w hw).comp hρ
  have hH' : ∀ g ∈ H, ρ' g 0 3=0 := by
    intro g hg
    change conjugate w hw (ρ g) 0 3=0
    rw [conjugate_apply,hH g hg]
    simp
  have hK' : ∀ g ∈ K, ρ' g 3 0=0 := by
    intro g hg
    change conjugate w hw (ρ g) 3 0=0
    rw [conjugate_apply,hK g hg]
    simp
  let s := c*σ c
  have hs : s ≠ 0 := mul_ne_zero hc ((map_ne_zero σ).mpr hc)
  apply contains_normalized r hr hcard ρ' hρ' H K hH' hK' (β/s) (δ*s) a
    (div_ne_zero hβ hs) (mul_ne_zero hδ0 hs) hδ ha
  · intro z hz
    have hz' : tr (2*r-1) (β*(z/s))=0 := by
      have he : β*(z/s)=(β/s)*z := by ring
      rw [he]
      exact hz
    obtain ⟨x,hx,hX⟩ := hCenter (z/s) hz'
    refine ⟨x,hx,?_⟩
    change conjugate w hw (ρ x)=_
    rw [hX]
    change conjugate (weights σ c) (weights_ne_zero σ c hc)
      (X (z/s) (σ (z/s)))=X z (σ z)
    rw [normalize_center σ hσ c (z/s) hc]
    have he : z/s*c*σ c=z := by
      rw [mul_assoc]
      change z/s*s=z
      exact div_mul_cancel₀ z hs
    rw [he]
  · intro t ht
    have ht' : tr (2*r-1) (δ*(t*s))=a := by
      have he : δ*(t*s)=(δ*s)*t := by ring
      rw [he]
      exact ht
    obtain ⟨y,hy,hY⟩ := hUpper (t*s) ht'
    refine ⟨y,hy,?_⟩
    change conjugate w hw (ρ y)=_
    rw [hY,normalize_upper σ hσ c (t*s) hc]
    have he : t*s/(c*σ c)=t := by change t*s/s=t; exact mul_div_cancel_right₀ t hs
    rw [he]
    rfl

end Erdos713C8SuzukiHyperplaneObstruction
