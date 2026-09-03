import FormalConjecturesUtil
import Submission.C8CosetOctagon
import Submission.C8MixedSuzukiMatrices

/-! An injective octagon obstruction for a full central matrix subgroup
opposite a normalized noncentral unipotent element. -/
open SimpleGraph
namespace Erdos713C8MixedSuzukiCosets
open Erdos713C8MixedSuzukiMatrices
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
set_option maxHeartbeats 2000000

/-- Only two zero-corner constraints on the subgroups are required. -/
theorem contains_from_matrices (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (x y : G) (hx : x ∈ H) (hy : y ∈ K) (t k u v : F)
    (hX : ρ x=X u v) (hY : ρ y=Y t k)
    (hk : k ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : k*v+u=0) (h2 : (t^2+t+k)*u^2+v=0) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  apply Erdos713C8CosetOctagon.contains H K x y hx hy
  · apply hρ
    simpa only [map_pow,map_mul,map_one,hX,hY] using order_four t k u v h1 h2
  · intro hh
    apply hk
    have he := hH (x*y) hh
    simpa only [map_mul,hX,hY,product_corner] using he
  · intro hh
    have he := hH ((x*y)^2) hh
    rw [map_pow,map_mul,hX,hY,square_corner t k u v h1] at he
    exact one_ne_zero he
  · intro hh
    apply hv
    have he := hK (y*x) hh
    simpa only [map_mul,hX,hY,reverse_corner] using he
  · intro hh
    have he := hK ((y*x)^2) hh
    rw [map_pow,map_mul,hX,hY,reverse_square_corner t k u v h1] at he
    exact pow_ne_zero 2 hu he

/-- The field endomorphism squares to Frobenius. The lower subgroup
contains its entire central parameter family, while the upper subgroup
contains one noncentral element whose first coordinate is one. -/
theorem contains_normalized (σ : F →+* F) (hσ : ∀ a, σ (σ a)=a^2)
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (hCenter : ∀ a : F, ∃ x ∈ H, ρ x=X a (σ a))
    (y : G) (hy : y ∈ K) (t : F) (hY : ρ y=Y t (1+t+σ t)) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  let k := 1+t+σ t
  let ℓ := t^2+t+k
  let u := 1/(k*ℓ)
  let v := u/k
  obtain ⟨hk,hℓ,hσu⟩ := twisted_scalars σ hσ t
  have hu : u ≠ 0 := one_div_ne_zero (mul_ne_zero hk hℓ)
  have hv : v ≠ 0 := div_ne_zero hu hk
  obtain ⟨x,hx,hX⟩ := hCenter u
  have hvσ : σ u=v := hσu
  have hX' : ρ x=X u v := by rw [hX,hvσ]
  have hrel := scalar_relations t k hk
  exact contains_from_matrices ρ hρ H K hH hK x y hx hy t k u v hX' hY
    hk hu hv hrel.1 hrel.2

end Erdos713C8MixedSuzukiCosets
