import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

open Nat Set

noncomputable def A248123 (n : ℕ) : ℕ :=
  -- Define the hBcth Catalan number (k)$ explicitly.
  let catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)

  -- The sequence value a(n) is the least element (infimum) of the set of candidates.
  sInf {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n)}

lemma A248123_eq_zero_iff_empty (n : ℕ) :
    A248123 n = 0 ↔ {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ ((2 * (m + n)).choose (m + n) / (m + n + 1))} = ∅ := by
  have h := Nat.sInf_eq_zero (s := {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ ((2 * (m + n)).choose (m + n) / (m + n + 1))})
  rw [A248123]
  rw [h]
  simp only [mem_setOf_eq, lt_self_iff_false, false_and, false_or]

lemma A248123_pos_iff_nonempty (n : ℕ) :
    A248123 n > 0 ↔ {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ ((2 * (m + n)).choose (m + n) / (m + n + 1))}.Nonempty := by
  rw [nonempty_iff_ne_empty]
  have h := A248123_eq_zero_iff_empty n
  constructor
  · intro hpos
    by_contra hc
    have hzero : A248123 n = 0 := by
      rw [h]
      exact hc
    omega
  · intro hnonempty
    by_contra hc
    have hzero : A248123 n = 0 := by omega
    rw [hzero] at h
    exact hnonempty (h.mp rfl)

def fast_centralBinom : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * (2 * n + 1) * fast_centralBinom n / (n + 1)

theorem fast_centralBinom_eq_centralBinom (n : ℕ) : fast_centralBinom n = centralBinom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [fast_centralBinom, ih]
    have h : (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n := succ_mul_centralBinom_succ n
    exact Nat.div_eq_of_eq_mul_right (succ_pos n) h.symm

def fast_catalan (k : ℕ) : ℕ := fast_centralBinom k / (k + 1)

theorem fast_catalan_eq_catalan (k : ℕ) : fast_catalan k = (2 * k).choose k / (k + 1) := by
  simp [fast_catalan, fast_centralBinom_eq_centralBinom, centralBinom]

/-- A248123 Conjecture: a(n) exists for all n > 0. -/
theorem oeis_248123_conjecture_0 (n : ℕ) (hn : n > 0) : A248123 n > 0 := by
  rw [A248123_pos_iff_nonempty]
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · -- n = 1
    use 1; decide
  rcases n with _ | n
  · -- n = 2
    use 3; decide
  rcases n with _ | n
  · -- n = 3
    use 2; decide
  rcases n with _ | n
  · -- n = 4
    use 21; decide
  rcases n with _ | n
  · -- n = 5
    use 9; decide
  rcases n with _ | n
  · -- n = 6
    use 11; decide
  rcases n with _ | n
  · -- n = 7
    use 11; decide
  rcases n with _ | n
  · -- n = 8
    use 77; decide
  rcases n with _ | n
  · -- n = 9
    use 5; decide
  rcases n with _ | n
  · -- n = 10
    use 13; decide
  rcases n with _ | n
  · -- n = 11
    use 6; decide
  rcases n with _ | n
  · -- n = 12
    use 85; decide
  rcases n with _ | n
  · -- n = 13
    use 10; decide
  rcases n with _ | n
  · -- n = 14
    use 5; decide
  rcases n with _ | n
  · -- n = 15
    use 1; decide
  rcases n with _ | n
  · -- n = 16
    use 77; decide
  rcases n with _ | n
  · -- n = 17
    use 11; decide
  rcases n with _ | n
  · -- n = 18
    use 5; decide
  rcases n with _ | n
  · -- n = 19
    use 11; decide
  rcases n with _ | n
  · -- n = 20
    use 1; decide
  rcases n with _ | n
  · -- n = 21
    use 4; decide
  rcases n with _ | n
  · -- n = 22
    use 7; decide
  rcases n with _ | n
  · -- n = 23
    use 13; decide
  rcases n with _ | n
  · -- n = 24
    use 29; decide
  rcases n with _ | n
  · -- n = 25
    use 18; decide
  rcases n with _ | n
  · -- n = 26
    use 7; decide
  rcases n with _ | n
  · -- n = 27
    use 14; decide
  rcases n with _ | n
  · -- n = 28
    use 1; decide
  rcases n with _ | n
  · -- n = 29
    use 15; decide
  rcases n with _ | n
  · -- n = 30
    use 11; decide
  rcases n with _ | n
  · -- n = 31
    use 17; decide
  rcases n with _ | n
  · -- n = 32
    use 189; decide
  rcases n with _ | n
  · -- n = 33
    use 19; decide
  rcases n with _ | n
  · -- n = 34
    use 9; decide
  rcases n with _ | n
  · -- n = 35
    use 6; decide
  rcases n with _ | n
  · -- n = 36
    use 5; decide
  rcases n with _ | n
  · -- n = 37
    use 23; decide
  rcases n with _ | n
  · -- n = 38
    use 15; decide
  rcases n with _ | n
  · -- n = 39
    use 7; decide
  rcases n with _ | n
  · -- n = 40
    use 49; decide
  rcases n with _ | n
  · -- n = 41
    use 23; decide
  rcases n with _ | n
  · -- n = 42
    use 1; decide
  rcases n with _ | n
  · -- n = 43
    use 22; decide
  rcases n with _ | n
  · -- n = 44
    use 17; decide
  rcases n with _ | n
  · -- n = 45
    use 1; decide
  rcases n with _ | n
  · -- n = 46
    use 13; decide
  rcases n with _ | n
  · -- n = 47
    use 25; decide
  rcases n with _ | n
  · -- n = 48
    use 13; decide
  rcases n with _ | n
  · -- n = 49
    use 26; decide
  rcases n with _ | n
  · -- n = 50
    use 19; decide
  rcases n with _ | n
  · -- n = 51
    use 11; decide
  rcases n with _ | n
  · -- n = 52
    use 9; decide
  rcases n with _ | n
  · -- n = 53
    use 28; decide
  rcases n with _ | n
  · -- n = 54
    use 71; decide
  rcases n with _ | n
  · -- n = 55
    use 18; decide
  rcases n with _ | n
  · -- n = 56
    use 29; decide
  rcases n with _ | n
  · -- n = 57
    use 10; decide
  rcases n with _ | n
  · -- n = 58
    use 15; decide
  rcases n with _ | n
  · -- n = 59
    use 31; decide
  rcases n with _ | n
  · -- n = 60
    use 13; decide
  rcases n with _ | n
  · -- n = 61
    use 34; decide
  rcases n with _ | n
  · -- n = 62
    use 17; decide
  rcases n with _ | n
  · -- n = 63
    use 5; decide
  rcases n with _ | n
  · -- n = 64
    use 381; decide
  rcases n with _ | n
  · -- n = 65
    use 9; decide
  rcases n with _ | n
  · -- n = 66
    use 1; decide
  rcases n with _ | n
  · -- n = 67
    use 35; decide
  rcases n with _ | n
  · -- n = 68
    use 9; decide
  rcases n with _ | n
  · -- n = 69
    use 19; decide
  rcases n with _ | n
  · -- n = 70
    use 9; decide
  rcases n with _ | n
  · -- n = 71
    use 37; decide
  rcases n with _ | n
  · -- n = 72
    use 5; decide
  rcases n with _ | n
  · -- n = 73
    use 38; decide
  rcases n with _ | n
  · -- n = 74
    use 19; decide
  rcases n with _ | n
  · -- n = 75
    use 13; decide
  rcases n with _ | n
  · -- n = 76
    use 11; decide
  rcases n with _ | n
  · -- n = 77
    use 1; decide
  rcases n with _ | n
  · -- n = 78
    use 17; decide
  rcases n with _ | n
  · -- n = 79
    use 40; decide
  rcases n with _ | n
  · -- n = 80
    use 13; decide
  rcases n with _ | n
  · -- n = 81
    use 43; decide
  rcases n with _ | n
  · -- n = 82
    use 21; decide
  rcases n with _ | n
  · -- n = 83
    use 42; decide
  rcases n with _ | n
  · -- n = 84
    use 53; decide
  rcases n with _ | n
  · -- n = 85
    use 11; decide
  rcases n with _ | n
  · -- n = 86
    use 23; decide
  rcases n with _ | n
  · -- n = 87
    use 19; decide
  rcases n with _ | n
  · -- n = 88
    use 1; decide
  rcases n with _ | n
  · -- n = 89
    use 46; decide
  rcases n with _ | n
  · -- n = 90
    use 53; decide
  rcases n with _ | n
  · -- n = 91
    use 1; decide
  rcases n with _ | n
  · -- n = 92
    use 13; decide
  rcases n with _ | n
  · -- n = 93
    use 20; decide
  rcases n with _ | n
  · -- n = 94
    use 25; decide
  rcases n with _ | n
  · -- n = 95
    use 11; decide
  rcases n with _ | n
  · -- n = 96
    use 221; decide
  rcases n with _ | n
  · -- n = 97
    use 51; decide
  rcases n with _ | n
  · -- n = 98
    use 25; decide
  rcases n with _ | n
  · -- n = 99
    use 5; decide
  rcases n with _ | n
  · -- n = 100
    use 3; decide
  rcases n with _ | n
  · -- n = 101
    use 51; decide
  rcases n with _ | n
  · -- n = 102
    use 11; decide
  rcases n with _ | n
  · -- n = 103
    use 52; decide
  rcases n with _ | n
  · -- n = 104
    use 1; decide
  rcases n with _ | n
  · -- n = 105
    use 23; decide
  rcases n with _ | n
  · -- n = 106
    use 27; decide
  rcases n with _ | n
  · -- n = 107
    use 57; decide
  rcases n with _ | n
  · -- n = 108
    use 41; decide
  rcases n with _ | n
  · -- n = 109
    use 56; decide
  rcases n with _ | n
  · -- n = 110
    use 1; decide
  rcases n with _ | n
  · -- n = 111
    use 19; decide
  rcases n with _ | n
  · -- n = 112
    use 5; decide
  rcases n with _ | n
  · -- n = 113
    use 58; decide
  rcases n with _ | n
  · -- n = 114
    use 17; decide
  rcases n with _ | n
  · -- n = 115
    use 13; decide
  rcases n with _ | n
  · -- n = 116
    use 17; decide
  rcases n with _ | n
  · -- n = 117
    use 5; decide
  rcases n with _ | n
  · -- n = 118
    use 31; decide
  rcases n with _ | n
  · -- n = 119
    use 9; decide
  rcases n with _ | n
  · -- n = 120
    use 77; decide
  rcases n with _ | n
  · -- n = 121
    use 62; decide
  rcases n with _ | n
  · -- n = 122
    use 31; decide
  rcases n with _ | n
  · -- n = 123
    use 25; decide
  rcases n with _ | n
  · -- n = 124
    use 21; decide
  rcases n with _ | n
  · -- n = 125
    use 68; decide
  rcases n with _ | n
  · -- n = 126
    use 13; decide
  rcases n with _ | n
  · -- n = 127
    use 65; decide
  · sorry
