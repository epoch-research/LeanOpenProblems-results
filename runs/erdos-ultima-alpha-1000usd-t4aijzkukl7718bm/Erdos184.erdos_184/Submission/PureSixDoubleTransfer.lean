import Submission.PureSixDoublePatterns

/-! Transferring the six-color Boolean classification to natural-valued pair counts.
The five-subset count bound is an explicit hypothesis, not a graph conclusion. -/
namespace Erdos184Work.PureSixDoublePatterns
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
def fivePairCoords : Fin 10 → Fin 5 × Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def omitColor : Fin 6 → Fin 5 → Fin 6 := ![![1,2,3,4,5],![0,2,3,4,5],![0,1,3,4,5],![0,1,2,4,5],![0,1,2,3,5],![0,1,2,3,4]]
def pullPair : Fin 6 → Fin 15 → Fin 10 := ![![0,0,0,0,0,0,1,2,3,4,5,6,7,8,9],![0,0,1,2,3,0,0,0,0,4,5,6,7,8,9],![0,0,1,2,3,0,4,5,6,0,0,0,7,8,9],![0,1,0,2,3,4,0,5,6,0,7,8,0,0,9],![0,1,2,0,3,4,5,0,6,7,0,8,0,9,0],![0,1,2,3,0,4,5,6,0,7,8,0,9,0,0]]

lemma omitColor_injective : ∀ v : Fin 6, Function.Injective (omitColor v) := by decide +kernel
lemma pull_coords : ∀ (v : Fin 6) (q : Fin 15),
    (pairCoords q).1 ≠ v → (pairCoords q).2 ≠ v →
    (omitColor v (fivePairCoords (pullPair v q)).1,
      omitColor v (fivePairCoords (pullPair v q)).2) = pairCoords q := by decide +kernel
lemma pull_injective : ∀ (v : Fin 6) (q r : Fin 15),
    (pairCoords q).1 ≠ v → (pairCoords q).2 ≠ v →
    (pairCoords r).1 ≠ v → (pairCoords r).2 ≠ v →
    pullPair v q = pullPair v r → q = r := by decide +kernel

def FiveBound (a : Fin 6 → Fin 6 → ℕ) : Prop := ∀ v : Fin 6,
  (Finset.univ.filter (fun q : Fin 10 =>
    a (omitColor v (fivePairCoords q).1) (omitColor v (fivePairCoords q).2) = 2)).card ≤ 2

def doubled (a : Fin 6 → Fin 6 → ℕ) (q : Fin 15) : Bool :=
  decide (a (pairCoords q).1 (pairCoords q).2 = 2)

lemma admissible_of_five_bound (a : Fin 6 → Fin 6 → ℕ) (ha : FiveBound a) :
    Admissible (doubled a) := by
  intro v
  have hc :
      (Finset.univ.filter (fun q : Fin 15 => doubled a q = true ∧
        (pairCoords q).1 ≠ v ∧ (pairCoords q).2 ≠ v)).card ≤
      (Finset.univ.filter (fun q : Fin 10 =>
        a (omitColor v (fivePairCoords q).1) (omitColor v (fivePairCoords q).2) = 2)).card := by
    apply Finset.card_le_card_of_injOn (pullPair v)
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have hh : a (pairCoords q).1 (pairCoords q).2 = 2 := of_decide_eq_true hq.1
      have he := pull_coords v q hq.2.1 hq.2.2
      simpa only [← he] using hh
    · intro q hq r hr hqr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact pull_injective v q r hq.2.1 hq.2.2 hr.2.1 hr.2.2 hqr
  exact hc.trans (ha v)

lemma between_doubled (a : Fin 6 → Fin 6 → ℕ)
    (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ i j, i ≠ j → 0 < a i j)
    (hbound : ∀ i j, i ≠ j → a i j ≤ 2)
    (i j : Fin 6) (hij : i ≠ j) : between (doubled a) i j = a i j := by
  unfold between
  rw [if_neg hij]
  have hp := pairCoords_pairIndex i j hij
  have hb : doubled a (pairIndex i j) = decide (a i j = 2) := by
    rcases hp with hp | hp <;> simp only [doubled,hp]
    rw [hsym j i]
  rw [hb]
  by_cases h : a i j = 2
  · simp [h]
  · have he : a i j = 1 := by have := hpos i j hij; have := hbound i j hij; omega
    simp [he]

lemma classified_nat (a : Fin 6 → Fin 6 → ℕ)
    (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ i j, i ≠ j → 0 < a i j)
    (hbound : ∀ i j, i ≠ j → a i j ≤ 2)
    (hfive : FiveBound a) :
    ∃ k : Fin 5, ∃ p : Equiv.Perm (Fin 6), ∀ i j, i ≠ j →
      a (p i) (p j) = between (representative k) i j := by
  obtain ⟨k,p,hp⟩ := classified (doubled a) (admissible_of_five_bound a hfive)
  refine ⟨k,p,?_⟩
  intro i j hij
  rw [← between_doubled a hsym hpos hbound _ _ (p.injective.ne hij)]
  exact hp i j

#print axioms admissible_of_five_bound
#print axioms classified_nat
end Erdos184Work.PureSixDoublePatterns
