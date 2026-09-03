import Submission.NFAAntichainCertificates

/-! A direct rank criterion for a finite intersection between an NFA language
and the canonical ternary 0/1 words. No invariant witness is supplied. -/
namespace Erdos406NFARank
open Erdos406MSDCertificate

variable {σ : Type*} [Fintype σ]

noncomputable def setRank (K : Set σ) (rank : σ → ℕ) (S : Set σ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun q => q ∈ S ∧ q ∈ K)).sup rank

lemma le_setRank (K : Set σ) (rank : σ → ℕ) (S : Set σ) (q : σ)
    (hqS : q ∈ S) (hqK : q ∈ K) : rank q ≤ setRank K rank S := by
  classical
  exact Finset.le_sup (by simp [hqS, hqK])

lemma setRank_step_lt (M : NFA ℕ σ) (G K : Set σ) (rank : σ → ℕ)
    (hback : ∀ q d r, d < 2 → r ∈ M.step q d → r ∈ K → q ∈ K)
    (hdecrease : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ M.step q d →
      rank r < rank q)
    (S : Set σ) (d : ℕ) (hd : d < 2) (hS : S ⊆ G)
    (hK : ∃ r ∈ M.stepSet S d, r ∈ K) :
    setRank K rank (M.stepSet S d) < setRank K rank S := by
  classical
  have hpos : 0 < setRank K rank S := by
    obtain ⟨r, hr, hrK⟩ := hK
    obtain ⟨q, hqS, hqr⟩ := NFA.mem_stepSet.mp hr
    have hlt := hdecrease q d r hd (hS hqS) hrK hqr
    exact (Nat.zero_le _).trans_lt (hlt.trans_le
      (le_setRank K rank S q hqS (hback q d r hd hqr hrK)))
  unfold setRank
  apply (Finset.sup_lt_iff hpos).mpr
  intro r hr
  obtain ⟨_, hrS, hrK⟩ := Finset.mem_filter.mp hr
  obtain ⟨q, hqS, hqr⟩ := NFA.mem_stepSet.mp hrS
  exact (hdecrease q d r hd (hS hqS) hrK hqr).trans_le
    (le_setRank K rank S q hqS (hback q d r hd hqr hrK))

/-- NFA productive-state ranks lift to the powerset DFA by taking a finite
maximum. This avoids exporting exponentially many DFA states. -/
theorem finite_of_rank (C : Erdos406NFAAntichain.Core σ)
    (G K : Set σ) (rank : σ → ℕ)
    (hstart : C.M.stepSet C.M.start 1 ⊆ G)
    (hforward : ∀ q ∈ G, ∀ d, d < 2 → C.M.step q d ⊆ G)
    (haccept : C.M.accept ⊆ K)
    (hback : ∀ q d r, d < 2 → r ∈ C.M.step q d → r ∈ K → q ∈ K)
    (hdecrease : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ C.M.step q d →
      rank r < rank q) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply finite_language_criterion C.toDFAcore (fun S => S ⊆ G)
    (fun S => ∃ q ∈ S, q ∈ K) (setRank K rank)
  · exact hstart
  · intro S d hd hS r hr
    obtain ⟨q, hqS, hqr⟩ := NFA.mem_stepSet.mp hr
    exact hforward q (hS hqS) d hd hqr
  · intro S hacc
    obtain ⟨q, hqS, hqa⟩ := hacc
    exact ⟨q, hqS, haccept hqa⟩
  · intro S d hd hK
    obtain ⟨r, hrS, hrK⟩ := hK
    obtain ⟨q, hqS, hqr⟩ := NFA.mem_stepSet.mp hrS
    exact ⟨q, hqS, hback q d r hd hqr hrK⟩
  · intro S d hd hS hK
    exact setRank_step_lt C.M G K rank hback hdecrease S d hd hS hK

#print axioms setRank_step_lt
#print axioms finite_of_rank
end Erdos406NFARank
