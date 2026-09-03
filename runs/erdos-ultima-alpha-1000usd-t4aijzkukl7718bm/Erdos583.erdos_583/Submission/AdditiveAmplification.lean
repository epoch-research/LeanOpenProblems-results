import Submission.StarCopyIntegrated

/-! A uniform additive constant would already imply the exact conjecture.
The required uniform bound is not asserted here. -/
namespace Erdos583AdditiveAmplificationDevelopment
open SimpleGraph Erdos583Work Erdos583Work.StarCopyAmplification
open scoped Classical
universe uAdditive
set_option maxHeartbeats 1200000

/-- An odd-order bound with slack c+1 implies the odd-order bound with slack c.
Four-copy projection absorbs the extra unit by integer rounding. -/
lemma reduce_odd_uniform_slack (c : ℕ)
    (hbound : ∀ {W : Type uAdditive} [Fintype W] (G : SimpleGraph W),
      Odd (Fintype.card W) → G.Connected →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
        D.card ≤ ⌈(Fintype.card W : ℚ)/2⌉₊+(c+1))
    {V : Type uAdditive} [Fintype V] (G : SimpleGraph V)
    (ho : Odd (Fintype.card V)) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊+c := by
  let u : V := Classical.choice hG.nonempty
  obtain ⟨D,hD,hDc⟩ := hbound (fourHub G u) (fourHub_odd (V := V)) (fourHub_connected G u hG)
  obtain ⟨E,hE,hEc⟩ := fourHub_project G u hD
  rw [BridgeGlue.ceil_half,fourHub_card] at hDc
  rw [BridgeGlue.ceil_half]
  obtain ⟨q,hq⟩ := ho
  exact ⟨E,hE,by omega⟩

lemma odd_bound_of_uniform_slack (c : ℕ)
    (hbound : ∀ {W : Type uAdditive} [Fintype W] (G : SimpleGraph W),
      Odd (Fintype.card W) → G.Connected →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
        D.card ≤ ⌈(Fintype.card W : ℚ)/2⌉₊+c)
    {V : Type uAdditive} [Fintype V] (G : SimpleGraph V)
    (ho : Odd (Fintype.card V)) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  induction c with
  | zero => simpa using hbound G ho hG
  | succ c ih => exact ih (fun J hJodd hJ ↦ reduce_odd_uniform_slack c hbound J hJodd hJ)

/-- It suffices to have ANY fixed additive constant, even only on odd orders.
This conditional equivalence does not supply that constant or its bound. -/
lemma gallai_of_uniform_odd_additive_bound (c : ℕ)
    (hbound : ∀ {W : Type uAdditive} [Fintype W] (G : SimpleGraph W),
      Odd (Fintype.card W) → G.Connected →
      ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
        D.card ≤ ⌈(Fintype.card W : ℚ)/2⌉₊+c)
    {V : Type uAdditive} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  exact gallai_of_odd_order (fun J ho hJ ↦ odd_bound_of_uniform_slack c hbound J ho hJ) G hG

end Erdos583AdditiveAmplificationDevelopment
