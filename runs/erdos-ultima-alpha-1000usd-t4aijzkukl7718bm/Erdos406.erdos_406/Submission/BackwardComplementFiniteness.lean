import Submission.ThresholdGuardFiniteness

/-! A backward-closed covering set gives a forward invariant by complementation.
These are sufficient criteria only; no such covering set is supplied here. -/
namespace Erdos406BackwardComplement

/-- A backward-closed cover of the positive good integers, rejecting a genuine
power-of-four seed, suffices. The extra guard is any forward-closed predicate. -/
theorem finite_of_backward_cover (E : ℕ) (Q G : ℕ → Prop)
    (hGseed : G (4 ^ E))
    (hGstep : ∀ n, G n → G (4 * n))
    (hseed : ¬ Q (4 ^ E))
    (hback : ∀ n, 4 ^ E ≤ n → G n → Q (4 * n) → Q n)
    (hcover : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Erdos406ThresholdGuard.finite_of_threshold_guard 0 E (Nat.zero_le E)
    (fun n => G n ∧ ¬ Q n) ⟨hGseed, hseed⟩
  · intro n hn _ hp
    exact ⟨hGstep n hp.1, fun hq => hp.2 (hback n hn hp.1 hq)⟩
  · apply (Set.finite_singleton (0 : ℕ)).subset
    intro n hn
    have hz : n = 0 := by
      by_contra hne
      exact hn.1.2 (hcover n (Nat.pos_of_ne_zero hne) hn.2)
    simpa using hz

/-- In the absence of an extra guard, only the numerical threshold remains. -/
theorem finite_of_backward_cover_above (E : ℕ) (Q : ℕ → Prop)
    (hseed : ¬ Q (4 ^ E))
    (hback : ∀ n, 4 ^ E ≤ n → Q (4 * n) → Q n)
    (hcover : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q n) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  exact finite_of_backward_cover E Q (fun _ => True) trivial (fun _ _ => trivial)
    hseed (fun n hn _ => hback n hn) hcover

/-- A covering set satisfying these hypotheses rejects the entire seed orbit.
This is the contrapositive induction used by complement-NFA synthesis. -/
lemma rejects_orbit (E : ℕ) (Q G : ℕ → Prop)
    (hGseed : G (4 ^ E))
    (hGstep : ∀ n, G n → G (4 * n))
    (hseed : ¬ Q (4 ^ E))
    (hback : ∀ n, 4 ^ E ≤ n → G n → Q (4 * n) → Q n) (j : ℕ) :
    G (4 ^ (E + j)) ∧ ¬ Q (4 ^ (E + j)) := by
  induction j with
  | zero => simpa using And.intro hGseed hseed
  | succ j ih =>
    have hlarge : 4 ^ E ≤ 4 ^ (E + j) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hh : G (4 * 4 ^ (E + j)) ∧ ¬ Q (4 * 4 ^ (E + j)) :=
      ⟨hGstep _ ih.1, fun hq => ih.2 (hback _ hlarge ih.1 hq)⟩
    simpa only [Nat.add_succ, pow_succ'] using hh

/-- Exact positive-sample certificates can use any finite good iterate. -/
lemma backward_iterate (E : ℕ) (Q G : ℕ → Prop)
    (hGstep : ∀ n, G n → G (4 * n))
    (hback : ∀ n, 4 ^ E ≤ n → G n → Q (4 * n) → Q n)
    (j n : ℕ) (hn : 4 ^ E ≤ n) (hg : G n) (hq : Q (4 ^ j * n)) : Q n := by
  induction j generalizing n with
  | zero => simpa using hq
  | succ j ih =>
    have he : 4 ^ (j + 1) * n = 4 ^ j * (4 * n) := by rw [pow_succ]; ring
    rw [he] at hq
    exact hback n hn hg (ih (4 * n) (by omega) (hGstep n hg) hq)

lemma good_iterate_forces_cover (E : ℕ) (Q G : ℕ → Prop)
    (hGstep : ∀ n, G n → G (4 * n))
    (hback : ∀ n, 4 ^ E ≤ n → G n → Q (4 * n) → Q n)
    (hcover : ∀ n, 0 < n → Nat.digits 3 n ⊆ [0, 1] → Q n)
    (j n : ℕ) (hn : 4 ^ E ≤ n) (hg : G n)
    (hgood : Nat.digits 3 (4 ^ j * n) ⊆ [0, 1]) : Q n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < 4 ^ E) hn
  exact backward_iterate E Q G hGstep hback j n hn hg
    (hcover _ (by positivity) hgood)

#print axioms backward_iterate
#print axioms good_iterate_forces_cover
#print axioms finite_of_backward_cover
#print axioms finite_of_backward_cover_above
#print axioms rejects_orbit
end Erdos406BackwardComplement
