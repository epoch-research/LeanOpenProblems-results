import FormalConjectures.Util.ProblemImports

open Nat

theorem base_cases (n : ℕ) (h : n < 200) : ∃ x y z w : ℕ,
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    x ≥ y ∧
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt =
      x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  interval_cases n
  · -- Case 0
    use 0, 0, 0, 0
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 1
    use 0, 0, 0, 1
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 2
    use 0, 0, 1, 1
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 3
    use 1, 1, 0, 1
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 4
    use 0, 0, 0, 2
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 5
    use 0, 0, 1, 2
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 6
    use 1, 1, 0, 2
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 7
    use 1, 1, 1, 2
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 8
    use 0, 0, 2, 2
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 9
    use 0, 0, 0, 3
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 10
    use 0, 0, 1, 3
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 11
    use 1, 1, 0, 3
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 12
    use 1, 1, 1, 3
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 13
    use 0, 0, 2, 3
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 14
    use 3, 0, 1, 2
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 15
    use 3, 1, 2, 1
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 16
    use 0, 0, 0, 4
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 17
    use 0, 0, 1, 4
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 18
    use 0, 0, 3, 3
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 19
    use 1, 1, 1, 4
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 20
    use 0, 0, 2, 4
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 21
    use 2, 2, 2, 3
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 22
    use 3, 3, 0, 2
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 23
    use 3, 1, 2, 3
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 24
    use 2, 2, 0, 4
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 25
    use 0, 0, 0, 5
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 26
    use 0, 0, 1, 5
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 27
    use 1, 1, 0, 5
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 28
    use 1, 1, 1, 5
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 29
    use 0, 0, 2, 5
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 30
    use 3, 1, 2, 4
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 31
    use 3, 3, 3, 2
    refine ⟨by decide, by decide, ?_⟩
    change (15 * 15).sqrt * (15 * 15).sqrt = 15 * 15
    rw [Nat.sqrt_eq]
  · -- Case 32
    use 0, 0, 4, 4
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 33
    use 2, 2, 0, 5
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 34
    use 0, 0, 3, 5
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 35
    use 3, 0, 1, 5
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 36
    use 0, 0, 0, 6
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 37
    use 0, 0, 1, 6
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 38
    use 1, 1, 0, 6
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 39
    use 1, 1, 1, 6
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 40
    use 0, 0, 2, 6
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 41
    use 0, 0, 4, 5
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 42
    use 3, 2, 5, 2
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 43
    use 3, 3, 0, 5
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 44
    use 2, 2, 0, 6
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 45
    use 0, 0, 3, 6
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 46
    use 3, 0, 1, 6
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 47
    use 3, 2, 5, 3
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 48
    use 2, 2, 2, 6
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 49
    use 0, 0, 0, 7
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 50
    use 0, 0, 1, 7
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 51
    use 1, 1, 0, 7
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 52
    use 0, 0, 4, 6
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 53
    use 0, 0, 2, 7
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 54
    use 3, 2, 5, 4
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 55
    use 5, 5, 2, 1
    refine ⟨by decide, by decide, ?_⟩
    change (17 * 17).sqrt * (17 * 17).sqrt = 17 * 17
    rw [Nat.sqrt_eq]
  · -- Case 56
    use 6, 0, 2, 4
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 57
    use 2, 2, 0, 7
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 58
    use 0, 0, 3, 7
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 59
    use 3, 0, 1, 7
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 60
    use 6, 2, 4, 2
    refine ⟨by decide, by decide, ?_⟩
    change (18 * 18).sqrt * (18 * 18).sqrt = 18 * 18
    rw [Nat.sqrt_eq]
  · -- Case 61
    use 0, 0, 5, 6
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 62
    use 7, 2, 0, 3
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 63
    use 3, 1, 2, 7
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 64
    use 0, 0, 0, 8
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 65
    use 0, 0, 1, 8
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 66
    use 1, 1, 0, 8
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 67
    use 1, 1, 1, 8
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 68
    use 0, 0, 2, 8
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 69
    use 5, 2, 2, 6
    refine ⟨by decide, by decide, ?_⟩
    change (11 * 11).sqrt * (11 * 11).sqrt = 11 * 11
    rw [Nat.sqrt_eq]
  · -- Case 70
    use 4, 2, 1, 7
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 71
    use 7, 2, 3, 3
    refine ⟨by decide, by decide, ?_⟩
    change (15 * 15).sqrt * (15 * 15).sqrt = 15 * 15
    rw [Nat.sqrt_eq]
  · -- Case 72
    use 0, 0, 6, 6
    refine ⟨by decide, by decide, ?_⟩
    change (24 * 24).sqrt * (24 * 24).sqrt = 24 * 24
    rw [Nat.sqrt_eq]
  · -- Case 73
    use 0, 0, 3, 8
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 74
    use 0, 0, 5, 7
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 75
    use 5, 5, 0, 5
    refine ⟨by decide, by decide, ?_⟩
    change (15 * 15).sqrt * (15 * 15).sqrt = 15 * 15
    rw [Nat.sqrt_eq]
  · -- Case 76
    use 2, 2, 2, 8
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 77
    use 5, 4, 6, 0
    refine ⟨by decide, by decide, ?_⟩
    change (27 * 27).sqrt * (27 * 27).sqrt = 27 * 27
    rw [Nat.sqrt_eq]
  · -- Case 78
    use 3, 1, 2, 8
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 79
    use 5, 2, 7, 1
    refine ⟨by decide, by decide, ?_⟩
    change (29 * 29).sqrt * (29 * 29).sqrt = 29 * 29
    rw [Nat.sqrt_eq]
  · -- Case 80
    use 0, 0, 4, 8
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 81
    use 0, 0, 0, 9
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 82
    use 0, 0, 1, 9
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 83
    use 1, 1, 0, 9
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 84
    use 1, 1, 1, 9
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 85
    use 0, 0, 2, 9
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 86
    use 5, 4, 6, 3
    refine ⟨by decide, by decide, ?_⟩
    change (27 * 27).sqrt * (27 * 27).sqrt = 27 * 27
    rw [Nat.sqrt_eq]
  · -- Case 87
    use 3, 2, 5, 7
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 88
    use 6, 6, 0, 4
    refine ⟨by decide, by decide, ?_⟩
    change (18 * 18).sqrt * (18 * 18).sqrt = 18 * 18
    rw [Nat.sqrt_eq]
  · -- Case 89
    use 0, 0, 5, 8
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 90
    use 0, 0, 3, 9
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 91
    use 3, 0, 1, 9
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 92
    use 6, 2, 4, 6
    refine ⟨by decide, by decide, ?_⟩
    change (18 * 18).sqrt * (18 * 18).sqrt = 18 * 18
    rw [Nat.sqrt_eq]
  · -- Case 93
    use 2, 2, 2, 9
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 94
    use 5, 2, 7, 4
    refine ⟨by decide, by decide, ?_⟩
    change (29 * 29).sqrt * (29 * 29).sqrt = 29 * 29
    rw [Nat.sqrt_eq]
  · -- Case 95
    use 3, 1, 2, 9
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 96
    use 4, 4, 0, 8
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 97
    use 0, 0, 4, 9
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 98
    use 0, 0, 7, 7
    refine ⟨by decide, by decide, ?_⟩
    change (28 * 28).sqrt * (28 * 28).sqrt = 28 * 28
    rw [Nat.sqrt_eq]
  · -- Case 99
    use 3, 3, 0, 9
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 100
    use 0, 0, 0, 10
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 101
    use 0, 0, 1, 10
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 102
    use 1, 1, 0, 10
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 103
    use 1, 1, 1, 10
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 104
    use 0, 0, 2, 10
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 105
    use 6, 2, 4, 7
    refine ⟨by decide, by decide, ?_⟩
    change (18 * 18).sqrt * (18 * 18).sqrt = 18 * 18
    rw [Nat.sqrt_eq]
  · -- Case 106
    use 0, 0, 5, 9
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 107
    use 7, 3, 0, 7
    refine ⟨by decide, by decide, ?_⟩
    change (11 * 11).sqrt * (11 * 11).sqrt = 11 * 11
    rw [Nat.sqrt_eq]
  · -- Case 108
    use 2, 2, 0, 10
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 109
    use 0, 0, 3, 10
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 110
    use 3, 0, 1, 10
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 111
    use 5, 5, 5, 6
    refine ⟨by decide, by decide, ?_⟩
    change (25 * 25).sqrt * (25 * 25).sqrt = 25 * 25
    rw [Nat.sqrt_eq]
  · -- Case 112
    use 2, 2, 2, 10
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 113
    use 0, 0, 7, 8
    refine ⟨by decide, by decide, ?_⟩
    change (28 * 28).sqrt * (28 * 28).sqrt = 28 * 28
    rw [Nat.sqrt_eq]
  · -- Case 114
    use 3, 1, 2, 10
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 115
    use 5, 0, 3, 9
    refine ⟨by decide, by decide, ?_⟩
    change (13 * 13).sqrt * (13 * 13).sqrt = 13 * 13
    rw [Nat.sqrt_eq]
  · -- Case 116
    use 0, 0, 4, 10
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 117
    use 0, 0, 6, 9
    refine ⟨by decide, by decide, ?_⟩
    change (24 * 24).sqrt * (24 * 24).sqrt = 24 * 24
    rw [Nat.sqrt_eq]
  · -- Case 118
    use 3, 3, 0, 10
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 119
    use 3, 2, 5, 9
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 120
    use 6, 2, 4, 8
    refine ⟨by decide, by decide, ?_⟩
    change (18 * 18).sqrt * (18 * 18).sqrt = 18 * 18
    rw [Nat.sqrt_eq]
  · -- Case 121
    use 0, 0, 0, 11
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 122
    use 0, 0, 1, 11
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 123
    use 1, 1, 0, 11
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 124
    use 1, 1, 1, 11
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 125
    use 0, 0, 2, 11
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 126
    use 5, 4, 6, 7
    refine ⟨by decide, by decide, ?_⟩
    change (27 * 27).sqrt * (27 * 27).sqrt = 27 * 27
    rw [Nat.sqrt_eq]
  · -- Case 127
    use 3, 3, 3, 10
    refine ⟨by decide, by decide, ?_⟩
    change (15 * 15).sqrt * (15 * 15).sqrt = 15 * 15
    rw [Nat.sqrt_eq]
  · -- Case 128
    use 0, 0, 8, 8
    refine ⟨by decide, by decide, ?_⟩
    change (32 * 32).sqrt * (32 * 32).sqrt = 32 * 32
    rw [Nat.sqrt_eq]
  · -- Case 129
    use 2, 2, 0, 11
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 130
    use 0, 0, 3, 11
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 131
    use 3, 0, 1, 11
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 132
    use 4, 4, 0, 10
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 133
    use 2, 2, 2, 11
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 134
    use 3, 3, 10, 4
    refine ⟨by decide, by decide, ?_⟩
    change (41 * 41).sqrt * (41 * 41).sqrt = 41 * 41
    rw [Nat.sqrt_eq]
  · -- Case 135
    use 3, 1, 2, 11
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 136
    use 0, 0, 6, 10
    refine ⟨by decide, by decide, ?_⟩
    change (24 * 24).sqrt * (24 * 24).sqrt = 24 * 24
    rw [Nat.sqrt_eq]
  · -- Case 137
    use 0, 0, 4, 11
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 138
    use 3, 2, 5, 10
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 139
    use 3, 3, 0, 11
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 140
    use 5, 5, 9, 3
    refine ⟨by decide, by decide, ?_⟩
    change (39 * 39).sqrt * (39 * 39).sqrt = 39 * 39
    rw [Nat.sqrt_eq]
  · -- Case 141
    use 5, 4, 6, 8
    refine ⟨by decide, by decide, ?_⟩
    change (27 * 27).sqrt * (27 * 27).sqrt = 27 * 27
    rw [Nat.sqrt_eq]
  · -- Case 142
    use 4, 2, 1, 11
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 143
    use 3, 3, 10, 5
    refine ⟨by decide, by decide, ?_⟩
    change (41 * 41).sqrt * (41 * 41).sqrt = 41 * 41
    rw [Nat.sqrt_eq]
  · -- Case 144
    use 0, 0, 0, 12
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 145
    use 0, 0, 1, 12
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 146
    use 0, 0, 5, 11
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 147
    use 1, 1, 1, 12
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 148
    use 0, 0, 2, 12
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 149
    use 0, 0, 7, 10
    refine ⟨by decide, by decide, ?_⟩
    change (28 * 28).sqrt * (28 * 28).sqrt = 28 * 28
    rw [Nat.sqrt_eq]
  · -- Case 150
    use 5, 5, 0, 10
    refine ⟨by decide, by decide, ?_⟩
    change (15 * 15).sqrt * (15 * 15).sqrt = 15 * 15
    rw [Nat.sqrt_eq]
  · -- Case 151
    use 7, 7, 7, 2
    refine ⟨by decide, by decide, ?_⟩
    change (35 * 35).sqrt * (35 * 35).sqrt = 35 * 35
    rw [Nat.sqrt_eq]
  · -- Case 152
    use 2, 2, 0, 12
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 153
    use 0, 0, 3, 12
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 154
    use 3, 0, 1, 12
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 155
    use 5, 0, 3, 11
    refine ⟨by decide, by decide, ?_⟩
    change (13 * 13).sqrt * (13 * 13).sqrt = 13 * 13
    rw [Nat.sqrt_eq]
  · -- Case 156
    use 2, 2, 2, 12
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 157
    use 0, 0, 6, 11
    refine ⟨by decide, by decide, ?_⟩
    change (24 * 24).sqrt * (24 * 24).sqrt = 24 * 24
    rw [Nat.sqrt_eq]
  · -- Case 158
    use 3, 1, 2, 12
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 159
    use 3, 2, 5, 11
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 160
    use 0, 0, 4, 12
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 161
    use 6, 0, 2, 11
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 162
    use 0, 0, 9, 9
    refine ⟨by decide, by decide, ?_⟩
    change (36 * 36).sqrt * (36 * 36).sqrt = 36 * 36
    rw [Nat.sqrt_eq]
  · -- Case 163
    use 5, 1, 4, 11
    refine ⟨by decide, by decide, ?_⟩
    change (17 * 17).sqrt * (17 * 17).sqrt = 17 * 17
    rw [Nat.sqrt_eq]
  · -- Case 164
    use 0, 0, 8, 10
    refine ⟨by decide, by decide, ?_⟩
    change (32 * 32).sqrt * (32 * 32).sqrt = 32 * 32
    rw [Nat.sqrt_eq]
  · -- Case 165
    use 4, 2, 1, 12
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 166
    use 7, 0, 6, 9
    refine ⟨by decide, by decide, ?_⟩
    change (25 * 25).sqrt * (25 * 25).sqrt = 25 * 25
    rw [Nat.sqrt_eq]
  · -- Case 167
    use 3, 3, 10, 7
    refine ⟨by decide, by decide, ?_⟩
    change (41 * 41).sqrt * (41 * 41).sqrt = 41 * 41
    rw [Nat.sqrt_eq]
  · -- Case 168
    use 6, 4, 10, 4
    refine ⟨by decide, by decide, ?_⟩
    change (42 * 42).sqrt * (42 * 42).sqrt = 42 * 42
    rw [Nat.sqrt_eq]
  · -- Case 169
    use 0, 0, 0, 13
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 170
    use 0, 0, 1, 13
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 171
    use 1, 1, 0, 13
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 172
    use 1, 1, 1, 13
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 173
    use 0, 0, 2, 13
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 174
    use 7, 2, 0, 11
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 175
    use 5, 5, 2, 11
    refine ⟨by decide, by decide, ?_⟩
    change (17 * 17).sqrt * (17 * 17).sqrt = 17 * 17
    rw [Nat.sqrt_eq]
  · -- Case 176
    use 4, 4, 0, 12
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 177
    use 2, 2, 0, 13
    refine ⟨by decide, by decide, ?_⟩
    change (6 * 6).sqrt * (6 * 6).sqrt = 6 * 6
    rw [Nat.sqrt_eq]
  · -- Case 178
    use 0, 0, 3, 13
    refine ⟨by decide, by decide, ?_⟩
    change (12 * 12).sqrt * (12 * 12).sqrt = 12 * 12
    rw [Nat.sqrt_eq]
  · -- Case 179
    use 3, 0, 1, 13
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
  · -- Case 180
    use 0, 0, 6, 12
    refine ⟨by decide, by decide, ?_⟩
    change (24 * 24).sqrt * (24 * 24).sqrt = 24 * 24
    rw [Nat.sqrt_eq]
  · -- Case 181
    use 0, 0, 9, 10
    refine ⟨by decide, by decide, ?_⟩
    change (36 * 36).sqrt * (36 * 36).sqrt = 36 * 36
    rw [Nat.sqrt_eq]
  · -- Case 182
    use 3, 2, 5, 12
    refine ⟨by decide, by decide, ?_⟩
    change (21 * 21).sqrt * (21 * 21).sqrt = 21 * 21
    rw [Nat.sqrt_eq]
  · -- Case 183
    use 3, 1, 2, 13
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 184
    use 6, 0, 2, 12
    refine ⟨by decide, by decide, ?_⟩
    change (10 * 10).sqrt * (10 * 10).sqrt = 10 * 10
    rw [Nat.sqrt_eq]
  · -- Case 185
    use 0, 0, 4, 13
    refine ⟨by decide, by decide, ?_⟩
    change (16 * 16).sqrt * (16 * 16).sqrt = 16 * 16
    rw [Nat.sqrt_eq]
  · -- Case 186
    use 5, 1, 4, 12
    refine ⟨by decide, by decide, ?_⟩
    change (17 * 17).sqrt * (17 * 17).sqrt = 17 * 17
    rw [Nat.sqrt_eq]
  · -- Case 187
    use 3, 3, 0, 13
    refine ⟨by decide, by decide, ?_⟩
    change (9 * 9).sqrt * (9 * 9).sqrt = 9 * 9
    rw [Nat.sqrt_eq]
  · -- Case 188
    use 6, 4, 10, 6
    refine ⟨by decide, by decide, ?_⟩
    change (42 * 42).sqrt * (42 * 42).sqrt = 42 * 42
    rw [Nat.sqrt_eq]
  · -- Case 189
    use 6, 6, 6, 9
    refine ⟨by decide, by decide, ?_⟩
    change (30 * 30).sqrt * (30 * 30).sqrt = 30 * 30
    rw [Nat.sqrt_eq]
  · -- Case 190
    use 4, 2, 1, 13
    refine ⟨by decide, by decide, ?_⟩
    change (8 * 8).sqrt * (8 * 8).sqrt = 8 * 8
    rw [Nat.sqrt_eq]
  · -- Case 191
    use 9, 3, 1, 10
    refine ⟨by decide, by decide, ?_⟩
    change (13 * 13).sqrt * (13 * 13).sqrt = 13 * 13
    rw [Nat.sqrt_eq]
  · -- Case 192
    use 4, 4, 4, 12
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 193
    use 0, 0, 7, 12
    refine ⟨by decide, by decide, ?_⟩
    change (28 * 28).sqrt * (28 * 28).sqrt = 28 * 28
    rw [Nat.sqrt_eq]
  · -- Case 194
    use 0, 0, 5, 13
    refine ⟨by decide, by decide, ?_⟩
    change (20 * 20).sqrt * (20 * 20).sqrt = 20 * 20
    rw [Nat.sqrt_eq]
  · -- Case 195
    use 5, 5, 9, 8
    refine ⟨by decide, by decide, ?_⟩
    change (39 * 39).sqrt * (39 * 39).sqrt = 39 * 39
    rw [Nat.sqrt_eq]
  · -- Case 196
    use 0, 0, 0, 14
    refine ⟨by decide, by decide, ?_⟩
    change (0 * 0).sqrt * (0 * 0).sqrt = 0 * 0
    rw [Nat.sqrt_eq]
  · -- Case 197
    use 0, 0, 1, 14
    refine ⟨by decide, by decide, ?_⟩
    change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
    rw [Nat.sqrt_eq]
  · -- Case 198
    use 1, 1, 0, 14
    refine ⟨by decide, by decide, ?_⟩
    change (3 * 3).sqrt * (3 * 3).sqrt = 3 * 3
    rw [Nat.sqrt_eq]
  · -- Case 199
    use 1, 1, 1, 14
    refine ⟨by decide, by decide, ?_⟩
    change (5 * 5).sqrt * (5 * 5).sqrt = 5 * 5
    rw [Nat.sqrt_eq]
