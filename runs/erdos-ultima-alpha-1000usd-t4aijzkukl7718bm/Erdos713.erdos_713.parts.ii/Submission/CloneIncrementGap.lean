import FormalConjecturesUtil
import Submission.CompactSymmRootsAudit

/-! A limitation of local cloning comparisons, not a disproof of Erdős 713.
For C4 every safe partial clone adds at most one edge, whereas the global
extremal-number increments are unbounded on every tail. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713CloneIncrementGap
open Erdos713C4 Erdos713PartialCloning

lemma safe_partial_card_le_one {V : Type*} (G : SimpleGraph V) (v : V)
    (Q : Finset V) (hQ : ∀ w ∈ Q, G.Adj v w)
    (hsafe : K22.Free (partialClone G Q)) : Q.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply Option.some.inj
  apply unique_common_of_free hsafe (u := none) (v := some v)
    (by simp : (none : Option V) ≠ some v)
  · exact ha
  · exact hQ a ha
  · exact hb
  · exact hQ b hb

lemma bounded_increments_linear_bigO (f : ℕ → ℕ) (N D : ℕ)
    (h : ∀ n, N ≤ n → f (n+1) ≤ f n + D) :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^ (1 : ℝ)) := by
  have hb : ∀ n, N ≤ n → f n ≤ f N + D*n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => omega
    | succ n hn ih =>
      have hh := h n hn
      nlinarith
  apply IsBigO.of_bound (f N + D : ℝ)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  rw [Real.norm_natCast, Real.rpow_one, Real.norm_natCast]
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hh : f n ≤ (f N + D)*n := by
    have hm := Nat.mul_le_mul_left (f N) hn1
    nlinarith [hb n hnN]
  exact_mod_cast hh

lemma c4_cofinal_large_increment (N D : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ extremalNumber n K22 + D < extremalNumber (n+1) K22 := by
  by_contra h
  push_neg at h
  have hh := bounded_increments_linear_bigO (fun n => extremalNumber n K22) N D h
  have hr := lower_exponent_of_prime_bound hh extremal_lower_prime
  norm_num at hr

/-- Even from an exactly extremal C4-free host, every safe partial clone
can be arbitrarily far below the next global extremal number. The graph
and all the comparisons in the conclusion concern the same order n. -/
theorem exact_hosts_local_gap (N D : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n ∧ K22.Free G ∧
      Nat.card G.edgeSet = extremalNumber n K22 ∧
      extremalNumber n K22 + D + 1 < extremalNumber (n+1) K22 ∧
      ∀ (v : Fin n) (Q : Finset (Fin n)), (∀ w ∈ Q, G.Adj v w) →
        K22.Free (partialClone G Q) →
          Nat.card (partialClone G Q).edgeSet + D < extremalNumber (n+1) K22 := by
  obtain ⟨n,hn,hinc⟩ := c4_cofinal_large_increment N (D+1)
  have hedge : ∃ a b, K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [K22,completeBipartiteGraph]⟩
  obtain ⟨G,hG,he⟩ := Erdos713CloneSymm.exists_ordinary_optimal K22 hedge n
  refine ⟨n,G,hn,hG.free,he,by omega,?_⟩
  intro v Q hQ hsafe
  have hcard := safe_partial_card_le_one G v Q hQ hsafe
  rw [card_edges,he]
  omega

#print axioms safe_partial_card_le_one
#print axioms bounded_increments_linear_bigO
#print axioms c4_cofinal_large_increment
#print axioms exact_hosts_local_gap
end Erdos713CloneIncrementGap
