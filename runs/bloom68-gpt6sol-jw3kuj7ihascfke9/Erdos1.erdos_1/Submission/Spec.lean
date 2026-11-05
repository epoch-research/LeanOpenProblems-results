import FormalConjecturesUtil
import Submission.Geometry
import Submission.Transfer

/-!
# Erdős Problem 1

*Reference:* [erdosproblems.com/1](https://www.erdosproblems.com/1)
-/

open Filter

open scoped Topology Real

namespace Erdos1

/--
A finite set of naturals $A$ is said to be a sum-distinct set for $N \in \mathbb{N}$ if
$A\subseteq\{1, ..., N\}$ and the sums $\sum_{a\in S}a$ are distinct for all $S\subseteq A$
-/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/--
If $A\subseteq\{1, ..., N\}$ with $|A| = n$ is such that the subset sums $\sum_{a\in S}a$ are
distinct for all $S\subseteq A$ then
$$
  N \gg 2 ^ n.
$$
-/
theorem erdos_1 : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/--
A finite set of real numbers is said to be sum-distinct if all the subset sums differ by
at least $1$.
-/
abbrev IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
  ↑A ⊆ Set.Ioc (0 : ℝ) N ∧ (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
    1 ≤ dist (S₁.sum id) (S₂.sum id)

end Erdos1

theorem Erdos1.erdos_1.disproof : ¬ (type_of% @Erdos1.erdos_1) := by
  rintro ⟨C, hC, hconj⟩
  obtain ⟨ε, hεpos, hεC⟩ := exists_rat_btwn hC
  have hε0 : (0 : ℚ) < ε := by exact_mod_cast hεpos
  obtain ⟨d, hd, B, hBdet, hBε, hgood⟩ :=
    Erdos1Aux.exists_small_admissible ε hε0
  obtain ⟨N, A, hA, hInj, hN, hsmall⟩ :=
    Erdos1Aux.transfer_to_small_family hd B hBdet hgood ε hBε
  have hlarge := hconj N A ⟨hA, hInj⟩ hN
  have hεCmul : (ε : ℝ) * 2 ^ A.card < C * 2 ^ A.card :=
    mul_lt_mul_of_pos_right hεC (by positivity)
  linarith
