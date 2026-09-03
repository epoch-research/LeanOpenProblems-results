import Submission.ZeroSumObstruction

/-! Sufficient zero-sum-free certificates from finite reachability supersets.
The sets need not be exact; closure and exclusion of the next negative suffice.
No universal frequency selection is asserted. -/

namespace Erdos7ReachabilityZeroSum
open scoped BigOperators

set_option maxHeartbeats 2000000

theorem prefix_sum_reachable {G : Type*} [AddCommMonoid G] {L : ℕ}
    (k : Fin L → G) (R : ℕ → G → Prop) (h0 : R 0 0)
    (hstay : ∀ i : Fin L, ∀ x, R i.val x → R (i.val+1) x)
    (hmove : ∀ i : Fin L, ∀ x, R i.val x → R (i.val+1) (x+k i)) :
    ∀ j, j ≤ L → ∀ s : Finset (Fin L), (∀ i ∈ s, i.val < j) → R j (∑ i ∈ s, k i) := by
  classical
  intro j
  induction j with
  | zero =>
    intro hj s hs
    have he : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := hs i hi
      omega
    simpa [he] using h0
  | succ j ih =>
    intro hj s hs
    let i : Fin L := ⟨j,by omega⟩
    have hjL : j ≤ L := by omega
    by_cases hi : i ∈ s
    · have hsmall : ∀ t ∈ s.erase i, t.val < j := by
        intro t ht
        obtain ⟨hti,hts⟩ := Finset.mem_erase.mp ht
        have htj := hs t hts
        have hne : t.val ≠ j := by
          intro he
          exact hti (Fin.ext he)
        omega
      have hr := hmove i _ (ih hjL (s.erase i) hsmall)
      change R (j+1) ((∑ t ∈ s.erase i, k t)+k i) at hr
      rwa [Finset.sum_erase_add _ _ hi] at hr
    · have hsmall : ∀ t ∈ s, t.val < j := by
        intro t ht
        have htj := hs t ht
        have hne : t.val ≠ j := by
          intro he
          have hti : t=i := Fin.ext he
          exact hi (hti ▸ ht)
        omega
      exact hstay i _ (ih hjL s hsmall)

/-- Only reachability overapproximations are needed; their exact computation
or a faithful external SAT encoding is not assumed by this theorem. -/
theorem zero_free_of_reachability {G : Type*} [AddCommGroup G] {L : ℕ}
    (k : Fin L → G) (R : ℕ → G → Prop) (h0 : R 0 0)
    (hstay : ∀ i : Fin L, ∀ x, R i.val x → R (i.val+1) x)
    (hmove : ∀ i : Fin L, ∀ x, R i.val x → R (i.val+1) (x+k i))
    (havoid : ∀ i : Fin L, ¬ R i.val (-k i)) :
    ∀ s : Finset (Fin L), s.Nonempty → ∑ i ∈ s, k i ≠ 0 := by
  classical
  intro s hs hz
  let i := s.max' hs
  have hi : i ∈ s := Finset.max'_mem s hs
  have hsmall : ∀ t ∈ s.erase i, t.val < i.val := by
    intro t ht
    obtain ⟨hti,hts⟩ := Finset.mem_erase.mp ht
    have hle : t ≤ i := Finset.le_max' s t hts
    have hlt : t < i := lt_of_le_of_ne hle hti
    exact hlt
  have hr := prefix_sum_reachable k R h0 hstay hmove i.val i.isLt.le (s.erase i) hsmall
  have he : (∑ t ∈ s.erase i, k t) = -k i := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [Finset.sum_erase_add _ _ hi]
    exact hz
  rw [he] at hr
  exact havoid i hr

/-- Arithmetic wrapper for a fully checked reachability certificate. -/
theorem not_arithmetic_cover {N L : ℕ} [NeZero N]
    (m : Fin L → ℕ) (a : Fin L → ℤ) (k : Fin L → ZMod N)
    (hk : ∀ i, (m i : ZMod N)*k i=0)
    (R : ℕ → ZMod N → Prop) (h0 : R 0 0)
    (hstay : ∀ i : Fin L, ∀ x, R i.val x → R (i.val+1) x)
    (hmove : ∀ i : Fin L, ∀ x, R i.val x → R (i.val+1) (x+k i))
    (havoid : ∀ i : Fin L, ¬ R i.val (-k i)) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) :=
  Erdos7ZeroSum.not_arithmetic_cover m a k hk
    (zero_free_of_reachability k R h0 hstay hmove havoid)

#print axioms prefix_sum_reachable
#print axioms zero_free_of_reachability
#print axioms not_arithmetic_cover
end Erdos7ReachabilityZeroSum
