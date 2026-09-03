import Submission.CubicTwinsExisting

/-! Cubic true twins with an odd root are reducible under residual connectivity. -/
namespace Erdos583CubicTwinsReductionDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open Erdos583CubicTwinsExistingDevelopment Erdos583CubicTwinsFreshDevelopment
open Erdos583ResidualOddAttachmentDevelopment Erdos583CubicTriangleOddAttachmentDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cubic_twins_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a : Fin n}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hya : G.Adj y a) (har : a ≠ r)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=a)
    (hrodd : Odd (Nat.card (G.neighborSet r)))
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (hra : (puncture G ({x,y} : Set (Fin n))).Reachable r a) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  by_cases hraG : G.Adj r a
  · exact cubic_twins_existing_reduction hsmall hrx hry hxy hxa hya hraG hNx hNy hK
  by_cases hae : Even (Nat.card (G.neighborSet a))
  · exact cubic_twins_fresh_even_reduction hsmall hrx hry hxy hxa hya har hNx hNy hraG hae hK hra
  have hao := Nat.not_even_iff_odd.mp hae
  have haK : (puncture G ({x,y} : Set (Fin n))).neighborSet a=G.neighborSet a \ {x,y} := by
    ext z
    simp [puncture_adj,hxa.ne.symm,hya.ne.symm]
  have haKo := odd_after_two_neighbors hxa.symm hya.symm hxy.ne haK hao
  apply gallai_private_pair_proxy hsmall G (puncture G ({x,y} : Set (Fin n))) hxy.ne hK
  · rintro ⟨z,hz⟩; exact hz.2.1 (Or.inl rfl)
  · rintro ⟨z,hz⟩; exact hz.2.1 (Or.inr rfl)
  · intro D hD
    exact cubic_triangle_residual_odd_lift hrx hry hxy hxa hya har hya.ne.symm har hxa.ne.symm
      hNx hNy hrodd haKo D hD

end Erdos583CubicTwinsReductionDevelopment
