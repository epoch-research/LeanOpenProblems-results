import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma q_dvd_x_seq_q_sq_small (q : ℕ) (hq : Nat.Prime q) (hq_lt : q < 43) : q ∣ x_seq (q * q - 1) := by
  interval_cases q
  · contradiction -- 0
  · contradiction -- 1
  · decide -- 2
  · decide -- 3
  · contradiction -- 4
  · decide -- 5
  · contradiction -- 6
  · decide -- 7
  · contradiction -- 8
  · contradiction -- 9
  · contradiction -- 10
  · decide -- 11
  · contradiction -- 12
  · decide -- 13
  · contradiction -- 14
  · contradiction -- 15
  · contradiction -- 16
  · decide -- 17
  · contradiction -- 18
  · decide -- 19
  · contradiction -- 20
  · contradiction -- 21
  · contradiction -- 22
  · decide -- 23
  · contradiction -- 24
  · contradiction -- 25
  · contradiction -- 26
  · contradiction -- 27
  · contradiction -- 28
  · decide -- 29
  · contradiction -- 30
  · decide -- 31
  · contradiction -- 32
  · contradiction -- 33
  · contradiction -- 34
  · contradiction -- 35
  · contradiction -- 36
  · decide -- 37
  · contradiction -- 38
  · contradiction -- 39
  · contradiction -- 40
  · decide -- 41
  · contradiction -- 42
