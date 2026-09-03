import Submission.Flags

/-!
# A checked finite test for proposed prefix obstructions

This length-ten example is not an unbounded family and does not settle the
liminf question. It prevents a particular strengthening of the prefix-tail
exclusion from being used in a proof.
-/

namespace Work

/-- Checking the sum map on the finite family of subsets certifies the condition. -/
theorem ntupleCondition_of_sum_injOn_powersetCard {S : Finset ℕ} {n : ℕ}
    (h : Set.InjOn (fun I : Finset ℕ => ∑ i ∈ I, i)
      (↑(S.powersetCard n) : Set (Finset ℕ))) : NtupleCondition (↑S : Set ℕ) n := by
  intro I J hIJ
  rcases hIJ with ⟨hI, hJ, hcI, hcJ, hsum⟩
  apply h ?_ ?_ hsum
  · exact Finset.mem_powersetCard.mpr ⟨hI, hcI⟩
  · exact Finset.mem_powersetCard.mpr ⟨hJ, hcJ⟩

/-- A fixed, explicitly ordered, cubic-bounded restricted-B3 flag. -/
def testFlag : Fin 10 → ℕ := ![1, 4, 6, 7, 8, 27, 81, 243, 729, 869]

theorem testFlag_strictMono : StrictMono testFlag := by decide

theorem testFlag_cubic_bound : ∀ i, testFlag i ≤ 1 * (i.val + 1)^3 := by decide

theorem testFlag_triples : NtupleCondition (Set.range testFlag) 3 := by
  have hRange : Set.range testFlag =
      (↑((Finset.univ : Finset (Fin 10)).image testFlag) : Set ℕ) := by
    ext a
    simp
  rw [hRange]
  apply ntupleCondition_of_sum_injOn_powersetCard
  decide

theorem finiteCubicFlag_one_ten : FiniteCubicFlag 1 10 :=
  ⟨testFlag, testFlag_strictMono, testFlag_cubic_bound, testFlag_triples⟩

/-- A difference of disjoint prefix pair sums is also a difference of disjoint tail pair sums.
This is permitted: it is an equality of four-element sums, not of triple sums. -/
theorem testFlag_prefix_tail_pair_difference :
    testFlag 5 + testFlag 4 - (testFlag 2 + testFlag 3) = 22 ∧
    testFlag 7 + testFlag 8 - (testFlag 6 + testFlag 9) = 22 := by decide

/-- Four distinct completions of the same oriented five-element core. -/
theorem testFlag_four_trade_completions :
    (243 + 729 + 6 + 7 : ℕ) = 27 + 81 + 869 + 8 ∧
    (243 + 729 + 4 + 8 : ℕ) = 27 + 81 + 869 + 7 ∧
    (243 + 729 + 4 + 7 : ℕ) = 27 + 81 + 869 + 6 ∧
    (243 + 729 + 1 + 8 : ℕ) = 27 + 81 + 869 + 4 := by decide

end Work

#print axioms Work.finiteCubicFlag_one_ten
#print axioms Work.testFlag_prefix_tail_pair_difference
#print axioms Work.testFlag_four_trade_completions
