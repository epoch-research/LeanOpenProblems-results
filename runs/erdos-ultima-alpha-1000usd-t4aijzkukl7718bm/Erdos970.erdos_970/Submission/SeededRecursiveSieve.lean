import Submission.RecursiveSieve

/-! A first-hit sieve with externally verified lower sources at recursive
nodes. Soundness retains all source hypotheses and gives no quadratic bound. -/
namespace Erdos970.RecursiveSieve
open Finset

noncomputable def seededEnvelope (lo hi : Finset ℕ → ℝ)
    (seed : ℕ → Finset ℕ → ℝ) (k : ℕ) (T : Finset ℕ) : ℝ × ℝ :=
  (max (seed k T) (max 0 (lo T-∑ i : Fin k,
      (seededEnvelope lo hi seed i.val (insert i.val T)).2)),
    hi T-∑ i : Fin k, (seededEnvelope lo hi seed i.val (insert i.val T)).1)
termination_by k

/-- All recursive sources are checked only at the disjoint prefix/intersection
nodes that can actually be reached from the given node. -/
theorem seededEnvelope_sound {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (hw : ∀ a ∈ A, 0 ≤ w a)
    (lo hi : Finset ℕ → ℝ) (seed : ℕ → Finset ℕ → ℝ)
    (hlo : ∀ T, lo T ≤ moment A w ω T)
    (hhi : ∀ T, moment A w ω T ≤ hi T)
    (k : ℕ)
    (hseed : ∀ n ≤ k, ∀ T : Finset ℕ, (∀ i ∈ T, n ≤ i) →
      seed n T ≤ sifted A w ω T n)
    (T : Finset ℕ) (hT : ∀ i ∈ T, k ≤ i) :
    (seededEnvelope lo hi seed k T).1 ≤ sifted A w ω T k ∧
      sifted A w ω T k ≤ (seededEnvelope lo hi seed k T).2 := by
  induction k using Nat.strong_induction_on generalizing T with
  | h k ih =>
    have hc (i : Fin k) := ih i.val i.isLt
      (fun n hn U hU => hseed n (hn.trans i.isLt.le) U hU)
      (insert i.val T) (by
        intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · rfl
        · exact i.isLt.le.trans (hT j hj))
    have hsl := sum_le_sum (s := (univ : Finset (Fin k))) (fun i _ => (hc i).1)
    have hsu := sum_le_sum (s := (univ : Finset (Fin k))) (fun i _ => (hc i).2)
    have he := sifted_first_hit A w ω T k
    have hn := sifted_nonneg A w ω hw T k
    rw [seededEnvelope]
    dsimp only
    constructor
    · apply max_le (hseed k le_rfl T hT)
      apply max_le hn
      linarith [hlo T]
    · linarith [hhi T]

/-- A positive seeded lower envelope forces an actual surviving member of the
weighted population. No arithmetic source is silently assumed here. -/
theorem weighted_survivor_of_positive_seededEnvelope {α : Type*}
    (A : Finset α) (w : α → ℝ) (ω : α → ℕ → Bool) (hw : ∀ a ∈ A, 0 ≤ w a)
    (lo hi : Finset ℕ → ℝ) (seed : ℕ → Finset ℕ → ℝ)
    (hlo : ∀ T, lo T ≤ moment A w ω T)
    (hhi : ∀ T, moment A w ω T ≤ hi T)
    (k : ℕ)
    (hseed : ∀ n ≤ k, ∀ T : Finset ℕ, (∀ i ∈ T, n ≤ i) →
      seed n T ≤ sifted A w ω T n)
    (hpos : 0 < (seededEnvelope lo hi seed k ∅).1) :
    ∃ a ∈ A, ∀ i < k, ω a i = false := by
  have hs := hpos.trans_le
    (seededEnvelope_sound A w ω hw lo hi seed hlo hhi k hseed ∅ (by simp)).1
  by_contra hbad
  push_neg at hbad
  have hz : sifted A w ω ∅ k = 0 := by
    apply sum_eq_zero
    intro a ha
    obtain ⟨i,hi,hh⟩ := hbad a ha
    have hn : ¬∀ i < k, ω a i = false := fun h => hh (h i hi)
    simp [avoid,hn]
  rw [hz] at hs
  exact lt_irrefl _ hs

#print axioms seededEnvelope_sound
#print axioms weighted_survivor_of_positive_seededEnvelope
end Erdos970.RecursiveSieve
