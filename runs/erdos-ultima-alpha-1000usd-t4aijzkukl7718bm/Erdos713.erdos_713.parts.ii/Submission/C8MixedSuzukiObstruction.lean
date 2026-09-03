import FormalConjecturesUtil
import Submission.C8MixedSuzukiCosets
import Submission.C8SuzukiNormalization

/-! Full central versus noncentral opposite Suzuki-type subgroups cannot
yield C8-free coset graphs. No Suzuki group-order theorem is required or
asserted, and the case of two noncentral subgroups is not covered. -/
open SimpleGraph
namespace Erdos713C8MixedSuzukiObstruction
open Erdos713C8MixedSuzukiMatrices Erdos713C8SuzukiNormalization
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
set_option maxHeartbeats 2000000

/-- The lower subgroup contains every twisted central matrix. The upper
subgroup contains any one root element with nonzero first coordinate.
Only the two indicated vanishing corners are required of the subgroups.
The ambient faithful matrix group and the field need not be finite. -/
theorem contains (σ : F →+* F) (hσ : ∀ a, σ (σ a)=a^2)
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (hCenter : ∀ a : F, ∃ x ∈ H, ρ x=X a (σ a))
    (y : G) (hy : y ∈ K) (c d : F) (hc : c ≠ 0) (hY : ρ y=upper σ c d) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  let w := weights σ c
  have hw : ∀ i, w i ≠ 0 := weights_ne_zero σ c hc
  let τ := conjugate w hw
  let ρ' : G →* Mat F := τ.comp ρ
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
  have hCenter' : ∀ a : F, ∃ x ∈ H, ρ' x=X a (σ a) := by
    intro a
    let b := a/(c*σ c)
    obtain ⟨x,hx,hX⟩ := hCenter b
    refine ⟨x,hx,?_⟩
    change conjugate w hw (ρ x)=X a (σ a)
    rw [hX]
    have hb : b*c*σ c=a := by
      have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
      dsimp [b]
      field_simp
    simpa only [hb] using normalize_center σ hσ c b hc
  have hY' : ρ' y=Y (d/(c*σ c)) (1+d/(c*σ c)+σ (d/(c*σ c))) := by
    change conjugate w hw (ρ y)=_
    rw [hY]
    exact normalize_upper σ hσ c d hc
  exact Erdos713C8MixedSuzukiCosets.contains_normalized σ hσ ρ' hρ' H K
    hH' hK' hCenter' y hy (d/(c*σ c)) hY'

/-- A smaller prime-field core already obstructs the canonical
noncentral hyperplane family. This does not require the full center. -/
theorem contains_prime_field_pair (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G) (hH : ∀ g ∈ H, ρ g 0 3=0) (hK : ∀ g ∈ K, ρ g 3 0=0)
    (x y : G) (hx : x ∈ H) (hy : y ∈ K)
    (hX : ρ x=X 1 1) (hY : ρ y=Y 0 1) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  apply Erdos713C8MixedSuzukiCosets.contains_from_matrices ρ hρ H K hH hK
    x y hx hy 0 1 1 1 hX hY one_ne_zero one_ne_zero one_ne_zero
  · simpa using (CharTwo.add_self_eq_zero (1 : F))
  · simpa using (CharTwo.add_self_eq_zero (1 : F))


end Erdos713C8MixedSuzukiObstruction
