import Submission.PacketMatchingMassExplore

/-! Exact splitting of finite packet representations into designated and
unintended ordered pairs. -/
namespace Erdos66PacketDecomposition
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66PacketMatching
  Erdos66OriginRepair
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] [∀ i, DecidableEq (α i)]

lemma packet_count_split (n : ι → ℤ) (x : ∀ i, α i → ℤ) (ω : ∀ i, α i)
    (hinj : Function.Injective (point n (chosen x ω))) (z : ℤ) :
    pairCount (packet n (chosen x ω)) (packet n (chosen x ω)) z =
      2*(Finset.univ.filter (fun i ↦ n i = z)).card+(offPairs n x z ω).card := by
  rw [← pairLabels_card n (chosen x ω) hinj z]
  have hh := Finset.card_filter_add_card_filter_not (s := pairLabels n (chosen x ω) z)
    (p := fun p ↦ Designated p.1 p.2)
  rw [designated_card] at hh
  have he : (pairLabels n (chosen x ω) z).filter (fun p ↦ ¬ Designated p.1 p.2) =
      offPairs n x z ω := by
    ext p
    simp only [pairLabels,offPairs,sumEvents,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [he] at hh
  exact hh.symm

end Erdos66PacketDecomposition
