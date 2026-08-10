import FormalConjectures.Util.ProblemImports

open Nat

/--
A000040: The prime numbers.
The $n$-th prime number $p_n$, where $p_1 = 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | (n' + 1) => nth Nat.Prime n'

/--
A000040 Conjecture: log log a(n+1) - log log a(n) < 1/n. - _Thomas Ordowski_, Feb 17 2023
-/
theorem oeis_40_conjecture_5 (n : ℕ) (hn : 0 < n) :
  Real.log (Real.log ((a (n + 1)).cast : ℝ)) - Real.log (Real.log ((a n).cast : ℝ)) < 1 / (n.cast : ℝ) :=
by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  show Real.log (Real.log ((nth Nat.Prime (m+1) : ℕ).cast : ℝ))
      - Real.log (Real.log ((nth Nat.Prime m : ℕ).cast : ℝ)) < 1 / (((m+1 : ℕ)).cast : ℝ)
  set P := nth Nat.Prime m with hPdef
  set Q := nth Nat.Prime (m+1) with hQdef
  have hP2 : 2 ≤ P := by have := Nat.add_two_le_nth_prime m; omega
  have hPQnat : P < Q := (nth_lt_nth Nat.infinite_setOf_prime).2 (by omega)
  have hp1 : (1:ℝ) < (P:ℝ) := by exact_mod_cast hP2
  have hpq : (P:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hPQnat.le
  have hred : Real.log (Real.log (Q:ℝ)) - Real.log (Real.log (P:ℝ))
      ≤ ((Q:ℝ) - (P:ℝ)) / ((P:ℝ) * Real.log (P:ℝ)) := by
    have hp0 : (0:ℝ) < (P:ℝ) := by linarith
    have hlogp : 0 < Real.log (P:ℝ) := Real.log_pos hp1
    have hlogq : 0 < Real.log (Q:ℝ) := Real.log_pos (by linarith)
    have hlogpq : Real.log (P:ℝ) ≤ Real.log (Q:ℝ) := Real.log_le_log hp0 hpq
    have hPne : (P:ℝ) ≠ 0 := ne_of_gt hp0
    have hQne : (Q:ℝ) ≠ 0 := by linarith
    rw [← Real.log_div (ne_of_gt hlogq) (ne_of_gt hlogp)]
    have h1 : Real.log (Real.log (Q:ℝ) / Real.log (P:ℝ)) ≤ Real.log (Q:ℝ) / Real.log (P:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log (Q:ℝ) - Real.log (P:ℝ) ≤ ((Q:ℝ) - (P:ℝ)) / (P:ℝ) := by
      rw [← Real.log_div hQne hPne]
      have h := Real.log_le_sub_one_of_pos (x := (Q:ℝ)/(P:ℝ)) (by positivity)
      have heq : (Q:ℝ) / (P:ℝ) - 1 = ((Q:ℝ) - (P:ℝ)) / (P:ℝ) := by field_simp
      linarith [heq ▸ h]
    have h2 : Real.log (Q:ℝ) / Real.log (P:ℝ) - 1
        = (Real.log (Q:ℝ) - Real.log (P:ℝ)) / Real.log (P:ℝ) := by field_simp
    have h4 : (Real.log (Q:ℝ) - Real.log (P:ℝ)) / Real.log (P:ℝ)
        ≤ (((Q:ℝ) - (P:ℝ))/(P:ℝ)) / Real.log (P:ℝ) := by gcongr
    have h5 : (((Q:ℝ) - (P:ℝ))/(P:ℝ)) / Real.log (P:ℝ)
        = ((Q:ℝ) - (P:ℝ))/((P:ℝ) * Real.log (P:ℝ)) := by rw [div_div]
    linarith [h1, h2 ▸ h1, h4, h5 ▸ h4]
  have gapbound : ((Q:ℝ) - (P:ℝ)) / ((P:ℝ) * Real.log (P:ℝ)) < 1 / (((m+1 : ℕ)).cast : ℝ) := by
    sorry
  linarith [hred, gapbound]
