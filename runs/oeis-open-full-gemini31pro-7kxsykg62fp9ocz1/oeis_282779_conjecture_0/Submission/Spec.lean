import FormalConjectures.Util.ProblemImports
import Submission.ValidPeriod
import Submission.ValidPeriodN
import Submission.FinalDvd
import Submission.Divisibility
import Submission.SumIdent
import Submission.TGeExpected

open Nat Set Classical

/--
A282779: Period of cubes mod $n$.
The $n$-th term $a(n)$ is the smallest positive integer $T$ such that $\forall k \in \mathbb{N}$, $(k+T)^3 \equiv k^3 \pmod n$.
-/
noncomputable def A282779 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Handle the non-sequence index n=0
  else
    -- sInf computes the infimum of the set, which is the minimum since ℕ is well-ordered.
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ 3 % n = k ^ 3 % n }

/--
The length of the minimal positive period of the sequence $k^p \pmod n$.
$a_p(n) = \min \{ T \in \mathbb{N}^+ \mid \forall k \in \mathbb{N}, (k+T)^p \equiv k^p \pmod n \}$.
-/
noncomputable def period_of_power_mod (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    sInf { T : ℕ | 0 < T ∧ ∀ k : ℕ, (k + T) ^ p % n = k ^ p % n }

/--
oeis_282779_conjecture_0: Conjecture: let a_p(n) be the length of the period of the sequence k^p mod n where p is a prime,
then a_p(n) = n/p if n == 0 (mod p^2) else a_p(n) = n.
-/
theorem oeis_282779_conjecture_0 (p n : ℕ) (hp : Nat.Prime p) (hn : n > 0) :
    period_of_power_mod p n = if p ^ 2 ∣ n then n / p else n := by
  rw [period_of_power_mod, if_neg (by omega)]
  by_cases hp2 : p ^ 2 ∣ n
  · rw [if_pos hp2]
    apply le_antisymm
    · apply csInf_le (OrderBot.bddBelow _)
      simp only [mem_setOf_eq]
      refine ⟨?_, ?_⟩
      · have hpn : p ∣ n := by
          have : p^2 = p * p := by ring
          rw [this] at hp2
          exact dvd_trans (dvd_mul_right p p) hp2
        have h_pos : n / p > 0 := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
        exact h_pos
      · intro k
        rcases hp2 with ⟨c, hc⟩
        have hsq : p^2 = p * p := by ring
        rw [hsq] at hc
        have h_n : n = p^2 * c := by
          rw [hc, hsq]
        have h_div : n / p = p * c := by
          rw [h_n, hsq, mul_assoc]
          exact Nat.mul_div_cancel_left (p * c) hp.pos
        rw [h_div, h_n]
        exact valid_period_pc p c k
    · apply le_csInf
      · exact ⟨n, hn, fun k => valid_period_n p n k⟩
      · intro T hT
        simp only [mem_setOf_eq] at hT
        have := T_ge_expected p n T hp hT.1 hT.2
        rw [if_pos hp2] at this
        exact this
  · rw [if_neg hp2]
    apply le_antisymm
    · apply csInf_le (OrderBot.bddBelow _)
      simp only [mem_setOf_eq]
      exact ⟨hn, fun k => valid_period_n p n k⟩
    · apply le_csInf
      · exact ⟨n, hn, fun k => valid_period_n p n k⟩
      · intro T hT
        simp only [mem_setOf_eq] at hT
        have := T_ge_expected p n T hp hT.1 hT.2
        rw [if_neg hp2] at this
        exact this

theorem oeis_282779_conjecture_0.disproof : ¬ (type_of% @oeis_282779_conjecture_0) := sorry
