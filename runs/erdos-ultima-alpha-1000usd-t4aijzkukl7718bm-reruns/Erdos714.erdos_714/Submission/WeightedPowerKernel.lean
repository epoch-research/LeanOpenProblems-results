import Submission.WeightedPowerSymmetry

/-! A growing subfield in the multiplicative kernel excludes critical-density
edge thinnings of weighted power hosts. This is not a solution of Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000

namespace Erdos714WeightedPower
variable {E W K : Type*} [Field E] [CommGroup W] [Field K]

/-- Disjoint subfield point sets give a genuine biclique with constant weights. -/
def kernelCopy (ν : Eˣ →* W) (ι : K →+* E)
    (hker : ∀ u : Kˣ, ν (Units.map ι.toMonoidHom u)=1) {r s : ℕ} (f : Fin r ⊕ Fin s ↪ K) :
    Copy (completeBipartiteGraph (Fin r) (Fin s)) (graph ν) := by
  let L (i : Fin r) : E × W := (ι (f (.inl i)),1)
  let R (j : Fin s) : E × W := (-ι (f (.inr j)),1)
  have hL : Function.Injective L := by
    intro i j h
    exact Sum.inl.inj (f.injective (ι.injective (congrArg Prod.fst h)))
  have hR : Function.Injective R := by
    intro i j h
    exact Sum.inr.inj (f.injective (ι.injective (neg_injective (congrArg Prod.fst h))))
  have he (i : Fin r) (j : Fin s) : relation ν (L i) (R j) := by
    have hne : f (.inl i)-f (.inr j) ≠ 0 := by
      intro h
      exact Sum.inl_ne_inr (f.injective (sub_eq_zero.mp h))
    refine ⟨Units.map ι.toMonoidHom (Units.mk0 (f (.inl i)-f (.inr j)) hne),?_,?_⟩
    · change ι (f (.inl i)-f (.inr j))=ι (f (.inl i)) + -ι (f (.inr j))
      simp [sub_eq_add_neg]
    · change ν (Units.map ι.toMonoidHom _) = 1*1
      simp only [hker,mul_one]
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => simp at hij
    | inr j => exact he i j
  | inr i =>
    cases j with
    | inl j => exact he j i
    | inr j => simp at hij

variable [Fintype K]

def subfieldCopy (ν : Eˣ →* W) (ι : K →+* E)
    (hker : ∀ u : Kˣ, ν (Units.map ι.toMonoidHom u)=1) (t : ℕ) (ht : 2*t ≤ Fintype.card K) :
    Copy (completeBipartiteGraph (Fin t) (Fin t)) (graph ν) := by
  apply Classical.choice
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin t ⊕ Fin t) (β := K) (by simpa only [Fintype.card_sum,Fintype.card_fin,two_mul] using ht)
  exact ⟨kernelCopy ν ι hker f⟩

variable [Fintype E] [Fintype W]

/-- The biclique is averaged over actual affine automorphisms of the host. -/
theorem kernel_thinning (ν : Eˣ →* W) (ι : K →+* E)
    (hker : ∀ u : Kˣ, ν (Units.map ι.toMonoidHom u)=1) (t : ℕ) (ht : 0<t)
    (hcard : 2*t ≤ Fintype.card K) (H : SimpleGraph ((E × W) ⊕ (E × W)))
    (hH : H ≤ graph ν) (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    t*H.edgeFinset.card^4 ≤ 10368*(graph ν).edgeFinset.card^4 := by
  have h := Erdos714GraphAveraging.biclique_bound H (graph ν) 4 t
    (subfieldCopy ν ι hker t hcard) hH hfree (edge_transitive ν)
  have hp := Nat.pow_le_pow_left h 4
  rw [mul_pow,mul_pow] at hp
  have hb := hp.trans (Nat.mul_le_mul_right ((graph ν).edgeFinset.card^4)
    (Erdos714BicliquePartition.extremal_fourth t))
  apply Nat.le_of_mul_le_mul_left (c := t^7) _ (pow_pos ht _)
  convert hb using 1 <;> ring

/-- No fixed retained fraction is possible when the kernel subfield grows. -/
theorem kernel_budget (ν : Eˣ →* W) (ι : K →+* E)
    (hker : ∀ u : Kˣ, ν (Units.map ι.toMonoidHom u)=1) (t C : ℕ) (ht : 0<t)
    (hcard : 2*t ≤ Fintype.card K) (H : SimpleGraph ((E × W) ⊕ (E × W)))
    (hH : H ≤ graph ν) (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hpos : 0<H.edgeFinset.card) (hdense : (graph ν).edgeFinset.card ≤ C*H.edgeFinset.card) :
    t ≤ 10368*C^4 := by
  have hb := kernel_thinning ν ι hker t ht hcard H hH hfree
  apply Nat.le_of_mul_le_mul_right (c := H.edgeFinset.card^4) _ (pow_pos hpos _)
  calc
    t*H.edgeFinset.card^4 ≤ 10368*(graph ν).edgeFinset.card^4 := hb
    _ ≤ 10368*(C*H.edgeFinset.card)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdense 4)
    _ = _ := by ring

end Erdos714WeightedPower
#print axioms Erdos714WeightedPower.kernelCopy
#print axioms Erdos714WeightedPower.kernel_thinning
#print axioms Erdos714WeightedPower.kernel_budget
