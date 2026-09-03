import Submission.OptimalCoverCore

/-! Count information from smaller cardinalities, and a limitation of inserting
that information into a subtractive first-hit recurrence. Neither theorem is a
quadratic upper bound for the Jacobsthal function. -/
namespace Erdos970.CardinalityBootstrap
open OptimalCoverCore

/-- The fresh-prime budget works for any finite prime set, not just primes below
an interval's length. -/
theorem bound_lt_budget {j m : ℕ} (h : IsJacobsthalBound j m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) :
    j < P.card + (survivors m P r).card := by
  classical
  by_contra hbad
  have hcover : ∀ i < m, i ∉ survivors m P r → ∃ p ∈ P, i ≡ r p [MOD p] := by
    intro i him hi
    have hh : ¬∀ p ∈ P, ¬i ≡ r p [MOD p] := by
      intro hh
      exact hi ((mem_survivors m P r i).mpr ⟨him, hh⟩)
    push_neg at hh
    exact hh
  obtain ⟨Q, hQ, hsize, s, hs⟩ := extend_cover_by_fresh_primes m
    (survivors m P r) P hP r hcover
  exact ((not_isJacobsthalBound_iff_cover j m).mpr
    ⟨Q, hQ, hsize.trans (by omega), s, hs⟩) h

/-- A smaller-cardinality bound gives a quantitative survivor count, by assigning
one fresh prime to each survivor. -/
theorem count_lower_of_bound {j g m : ℕ} (h : IsJacobsthalBound j g) (hgm : g ≤ m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) :
    j + 1 - P.card ≤ (survivors m P r).card := by
  have hh := bound_lt_budget (isJacobsthalBound_mono h hgm) P hP r
  omega

/-- This is exactly the single-block profile used by a hypothetical strong
induction. The bound at the terminal cardinality `K` is not assumed. -/
theorem count_lower_of_smaller_quadratic {C K : ℕ}
    (h : ∀ j, 0 < j → j < K → IsJacobsthalBound j (C * j ^ 2))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ)
    (j m : ℕ) (hj : 0 < j) (hjK : j < K) (hm : C * j ^ 2 ≤ m) :
    j + 1 - P.card ≤ (survivors m P r).card :=
  count_lower_of_bound (h j hj hjK) hm P hP r

/-- Every positive-length interval can contain a survivor for a suitable residue
vector. Consequently a residue-uniform upper bound is always at least one. -/
theorem upper_one_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℕ → ℕ) (hu : ∀ m r, (survivors m P r).card ≤ u m)
    {m : ℕ} (hm : 0 < m) : 1 ≤ u m := by
  classical
  have hzero : 0 ∈ survivors m P (fun _ => 1) := by
    apply (mem_survivors m P (fun _ => 1) 0).mpr
    refine ⟨hm, fun p hp hmod => ?_⟩
    have he := hmod.eq_of_lt_of_lt (hP p hp).pos (hP p hp).one_lt
    omega
  have hc : 0 < (survivors m P (fun _ => 1)).card :=
    Finset.card_pos.mpr ⟨0, hzero⟩
  have hh := hu m (fun _ => 1)
  omega

/-- A scalar recurrence with injected lower bounds. `b (i+1)` is inserted after
subtracting the cost `u i`; `b 0` is immaterial. -/
def forcedRun (u b : ℕ → ℕ) (v : ℕ) : ℕ → ℕ
  | 0 => v
  | n + 1 => max (forcedRun u b v n - u n) (b (n + 1))

def plainRun (u : ℕ → ℕ) (v : ℕ) : ℕ → ℕ
  | 0 => v
  | n + 1 => plainRun u v n - u n

lemma plainRun_eq_sub_sum (u : ℕ → ℕ) (v n : ℕ) :
    plainRun u v n = v - ∑ i ∈ Finset.range n, u i := by
  induction n with
  | zero => simp [plainRun]
  | succ n ih => simp only [plainRun, ih, Finset.sum_range_succ, Nat.sub_sub]

lemma plainRun_le_forcedRun (u b : ℕ → ℕ) (v n : ℕ) :
    plainRun u v n ≤ forcedRun u b v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (Nat.sub_le_sub_right ih (u n)).trans (le_max_left _ _)

/-- Intermediate injections bounded by the number of remaining subtractions
cannot add more than that number to the ordinary recurrence's maximum. -/
lemma forcedRun_le_max {u b : ℕ → ℕ} {v K : ℕ}
    (hu : ∀ i < K, 1 ≤ u i) (hb : ∀ i ≤ K, b i ≤ K - i) :
    ∀ n ≤ K, forcedRun u b v n ≤ max (plainRun u v n) (K - n) := by
  intro n
  induction n with
  | zero => intro _; exact le_max_left _ _
  | succ n ih =>
    intro hn
    have hih := ih (by omega)
    have hui := hu n (by omega)
    have hbi := hb (n + 1) hn
    simp only [forcedRun, plainRun]
    omega

/-- Exact terminal redundancy: if every subtraction costs at least one, any
injection no larger than the remaining cardinality budget is completely
consumed before the terminal stage. The costs `u` are held FIXED here; this
does not claim that recursive child costs are unchanged by an injection. -/
theorem forcedRun_terminal_eq {u b : ℕ → ℕ} {v K : ℕ}
    (hu : ∀ i < K, 1 ≤ u i) (hb : ∀ i ≤ K, b i ≤ K - i) :
    forcedRun u b v K = v - ∑ i ∈ Finset.range K, u i := by
  rw [← plainRun_eq_sub_sum]
  apply le_antisymm _ (plainRun_le_forcedRun u b v K)
  simpa only [Nat.sub_self, max_eq_left (Nat.zero_le _)] using
    forcedRun_le_max hu hb K le_rfl

/-- At any length, all single-block consequences of smaller-cardinality bounds
are at most the number of primes remaining. -/
lemma smaller_cardinality_profile_le (K i j : ℕ) (hj : j < K) :
    j + 1 - i ≤ K - i := by omega

#print axioms count_lower_of_smaller_quadratic
#print axioms upper_one_le
#print axioms forcedRun_terminal_eq
end Erdos970.CardinalityBootstrap
