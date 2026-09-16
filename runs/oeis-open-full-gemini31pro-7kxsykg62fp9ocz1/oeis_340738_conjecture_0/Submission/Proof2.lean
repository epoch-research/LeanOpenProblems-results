import Mathlib
import Submission.Spec

open Polynomial Real Nat MeasureTheory intervalIntegral Filter Asymptotics Topology Set

-- I_n as a real sequence
noncomputable def I_seq (n : ℕ) : ℝ :=
  if n % 2 == 1 then
    let k := (n + 1) / 2
    ∫ x in (0:ℝ)..1, ((X ^ k * (1 - X) ^ k : ℝ[X]).eval x / (k ! : ℝ)) * exp (1 - x)
  else
    0

theorem J_seq_rel (n : ℕ) :
  (A340737 n : ℝ) - (A340738 n : ℝ) * exp 1 =
  if n % 2 == 1 then
    (-1) ^ ((n - 1) / 2) * I_seq n
  else
    ( (-1) ^ (n / 2) * I_seq (n + 1) - (n + 1 : ℝ) * (-1) ^ (n / 2 - 1) * I_seq (n - 1) ) / 2
  := by sorry

theorem I_seq_lim : Tendsto I_seq atTop (nhds 0) := by sorry

theorem limit_conjecture :
  Tendsto (fun n => (A340737 n : ℝ) / (A340738 n : ℝ)) atTop (nhds (exp 1)) := by sorry
