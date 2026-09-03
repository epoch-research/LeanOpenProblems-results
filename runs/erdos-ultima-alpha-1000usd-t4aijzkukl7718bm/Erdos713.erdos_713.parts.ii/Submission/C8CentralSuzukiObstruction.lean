import FormalConjecturesUtil
import Submission.C8CentralSuzukiMatrices
import Submission.C8CentralSuzukiParameters
import Submission.C8CentralSuzukiCosets

/-! A uniform opposite-center obstruction outside the eight-element
exceptional field. This does not settle the extremal rationality conjecture. -/
open SimpleGraph
namespace Erdos713C8CentralSuzukiObstruction
open Erdos713C8MixedSuzukiMatrices Erdos713C8CentralSuzukiMatrices
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
set_option maxHeartbeats 2000000

/-- Both subgroups contain their complete twisted central parameter
families. Four vanishing-entry conditions suffice for the conclusion. -/
theorem contains (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G)
    (hH03 : ∀ x ∈ H, ρ x 0 3=0) (hH10 : ∀ x ∈ H, ρ x 1 0=0)
    (hK30 : ∀ x ∈ K, ρ x 3 0=0) (hK21 : ∀ x ∈ K, ρ x 2 1=0)
    (hZ : ∀ a : F, ∃ x ∈ H, ρ x=Z σ a)
    (hO : ∀ a : F, ∃ x ∈ K, ρ x=O σ a)
    (c : F) (hc8 : c^8 ≠ c) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  classical
  choose z hzH hz using hZ
  choose o hoK ho using hO
  obtain ⟨hc,hJ,hA,hd,he,hf,hg,hh⟩ :=
    Erdos713C8CentralSuzukiParameters.nonzero σ hσ c hc8
  apply Erdos713C8CentralSuzukiCosets.contains_word σ ρ hρ H K hH03 hH10 hK30 hK21
    z o hz ho hzH hoK 1 c (d σ c) (e σ c) (f σ c) (g σ c) (h σ c)
    one_ne_zero hc hd he hf hg hh
  apply hρ
  simpa only [map_mul,hz,ho] using word_identity σ hσ c hc hJ hA

/-- In particular all finite twisted fields of order greater than eight
are covered; there is no subgroup-size or ambient-group-order premise. -/
theorem contains_finite [Fintype F] (hq : 8 < Fintype.card F)
    (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G)
    (hH03 : ∀ x ∈ H, ρ x 0 3=0) (hH10 : ∀ x ∈ H, ρ x 1 0=0)
    (hK30 : ∀ x ∈ K, ρ x 3 0=0) (hK21 : ∀ x ∈ K, ρ x 2 1=0)
    (hZ : ∀ a : F, ∃ x ∈ H, ρ x=Z σ a)
    (hO : ∀ a : F, ∃ x ∈ K, ρ x=O σ a) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  obtain ⟨c,hc⟩ := Erdos713C8SuzukiScalarExclusions.exists_parameter hq
  exact contains σ hσ ρ hρ H K hH03 hH10 hK30 hK21 hZ hO c hc

end Erdos713C8CentralSuzukiObstruction
