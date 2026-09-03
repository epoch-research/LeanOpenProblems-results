import Submission.NFAFiniteLanguageCertificates

/-! The finite-good NFA search template rejects every canonical good word
of length at least its number of states. This is only a template bound;
no multiplication-closed automaton is supplied. -/

namespace Erdos406NFAOrderedLength
open Erdos406MSDCertificate Erdos406NFARank

/-- Lift a productive-state rank bound to the length of an accepted number. -/
theorem good_length_le_rank {σ : Type*} [Fintype σ]
    (M : NFA ℕ σ) (G K : Set σ) (rank : σ → ℕ)
    (hstart : M.stepSet M.start 1 ⊆ G)
    (hforward : ∀ q ∈ G, ∀ d, d < 2 → M.step q d ⊆ G)
    (haccept : M.accept ⊆ K)
    (hback : ∀ q d r, d < 2 → r ∈ M.step q d → r ∈ K → q ∈ K)
    (hdecrease : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ M.step q d →
      rank r < rank q)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1])
    (ha : evalNat M.toDFA n ∈ M.toDFA.accept) :
    (Nat.digits 3 n).length ≤ setRank K rank (M.stepSet M.start 1) + 1 := by
  apply good_length_bound M.toDFA (fun S => S ⊆ G)
    (fun S => ∃ q ∈ S, q ∈ K) (setRank K rank) hstart ?_ ?_ ?_ ?_ hn hd ha
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
    exact setRank_step_lt M G K rank hback hdecrease S d hd hS hK

/-- A bound on productive state indices gives a length bound independent
of the total number of nonproductive states. -/
theorem good_length_lt_bound {N H : ℕ} (hH : 2 ≤ H)
    (M : NFA ℕ (Fin N)) (G K : Set (Fin N))
    (hstart : M.stepSet M.start 1 ⊆ G)
    (hforward : ∀ q ∈ G, ∀ d, d < 2 → M.step q d ⊆ G)
    (haccept : M.accept ⊆ K)
    (hback : ∀ q d r, d < 2 → r ∈ M.step q d → r ∈ K → q ∈ K)
    (hzero : ∀ q ∈ G, 0 < q.val)
    (horder : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ M.step q d →
      r.val < q.val)
    (hbound : ∀ q ∈ G, q ∈ K → q.val < H)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1])
    (ha : evalNat M.toDFA n ∈ M.toDFA.accept) :
    (Nat.digits 3 n).length < H := by
  have hr : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ M.step q d →
      r.val - 1 < q.val - 1 := by
    intro q d r hd hq hr hqr
    have hp := hzero r (hforward q hq d hd hqr)
    have hh := horder q d r hd hq hr hqr
    omega
  have hl := good_length_le_rank M G K (fun q => q.val - 1)
    hstart hforward haccept hback hr hn hd ha
  have hb : setRank K (fun q : Fin N => q.val - 1) (M.stepSet M.start 1) ≤ H - 2 := by
    classical
    unfold setRank
    apply Finset.sup_le
    intro q hq
    obtain ⟨_, hqS, hqK⟩ := Finset.mem_filter.mp hq
    have hh := hbound q (hstart hqS) hqK
    omega
  omega

/-- State zero is excluded from the binary-reachable states. Productive
binary edges strictly decrease the state index. Therefore the good-word
length is strictly smaller than `N`, not just bounded by `N`. -/
theorem good_length_lt_states {N : ℕ} (hN : 2 ≤ N)
    (M : NFA ℕ (Fin N)) (G K : Set (Fin N))
    (hstart : M.stepSet M.start 1 ⊆ G)
    (hforward : ∀ q ∈ G, ∀ d, d < 2 → M.step q d ⊆ G)
    (haccept : M.accept ⊆ K)
    (hback : ∀ q d r, d < 2 → r ∈ M.step q d → r ∈ K → q ∈ K)
    (hzero : ∀ q ∈ G, 0 < q.val)
    (horder : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ M.step q d →
      r.val < q.val)
    {n : ℕ} (hn : 0 < n) (hd : Nat.digits 3 n ⊆ [0, 1])
    (ha : evalNat M.toDFA n ∈ M.toDFA.accept) :
    (Nat.digits 3 n).length < N := by
  have hr : ∀ q d r, d < 2 → q ∈ G → r ∈ K → r ∈ M.step q d →
      r.val - 1 < q.val - 1 := by
    intro q d r hd hq hr hqr
    have hp := hzero r (hforward q hq d hd hqr)
    have hh := horder q d r hd hq hr hqr
    omega
  have hl := good_length_le_rank M G K (fun q => q.val - 1)
    hstart hforward haccept hback hr hn hd ha
  have hb : setRank K (fun q : Fin N => q.val - 1) (M.stepSet M.start 1) ≤ N - 2 := by
    classical
    unfold setRank
    apply Finset.sup_le
    intro q _
    have hq := q.isLt
    omega
  omega

#print axioms good_length_lt_bound
#print axioms good_length_lt_states
end Erdos406NFAOrderedLength
