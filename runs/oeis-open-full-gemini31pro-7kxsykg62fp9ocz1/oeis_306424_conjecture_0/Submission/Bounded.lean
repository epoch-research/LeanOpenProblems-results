lemma bounded_cases (k : ℕ) (hk1 : 43 < k) (hk2 : k < 289) : ∃ B, 3 ≤ B ∧ B < k ∧ ((Nat.digits B k).toFinset.card) > 2 := by
  interval_cases k
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 0 3 2 44
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 1 3 2 45
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 1 0 2 1 46
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 2 0 2 1 47
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 0 1 2 1 48
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 1 0 3 49
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 2 0 3 50
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 0 2 2 1 51
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 0 1 3 52
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 3 0 2 53
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 2 1 3 54
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 1 0 0 2 55
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 0 2 3 56
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 0 1 0 2 57
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 3 1 2 58
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 2 1 0 2 59
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 4 1 60
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 1 2 0 2 61
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 2 4 1 62
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 3 4 1 63
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 1 0 1 2 64
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 2 0 1 2 65
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 0 1 1 2 66
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 0 1 67
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 2 5 1 68
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 0 2 1 2 69
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 0 1 70
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 0 1 71
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 0 1 72
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 1 0 2 2 73
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 4 3 1 74
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 0 1 2 2 75
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 0 1 76
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 0 1 77
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 0 1 78
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 4 0 3 79
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 1 3 80
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 3 1 2 81
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 1 1 82
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 1 1 83
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 4 1 3 84
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 2 3 85
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 2 3 86
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 3 5 1 87
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 1 1 88
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 4 2 3 89
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 3 2 90
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 1 1 91
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 1 1 92
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 2 6 1 93
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 1 1 94
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 4 3 95
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 4 3 96
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 2 1 97
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 0 2 1 98
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 2 1 99
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 2 1 100
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 0 4 101
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 2 0 4 102
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 2 1 103
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 2 1 104
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 1 4 105
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 4 5 2 106
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 2 2 1 107
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 2 1 108
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 2 1 109
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 3 2 1 110
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 2 4 111
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 4 0 3 112
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 3 1 113
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 3 1 114
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 3 1 115
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 3 1 116
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 2 3 4 117
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 3 1 118
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 5 1 3 119
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 3 1 120
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 3 1 121
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 2 7 1 122
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 2 3 1 123
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 3 1 124
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 5 2 3 125
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 3 3 1 126
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 0 0 1 127
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 0 0 1 128
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 0 2 129
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 9
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 9 4 5 1 130
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 0 2 131
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 0 2 132
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 1 0 1 133
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 0 2 134
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 0 2 135
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 2 0 1 136
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 0 2 137
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 0 1 138
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 0 2 139
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 0 2 140
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 0 2 141
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 0 2 142
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 3 6 2 143
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 3 0 1 144
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 1 2 145
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 1 2 146
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 1 2 147
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 1 2 148
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 5 0 4 149
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 1 4 150
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 1 1 2 151
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 1 2 152
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 0 1 1 153
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 0 1 1 154
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 1 2 155
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 1 2 156
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 3 1 2 157
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 1 2 158
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 3 2 4 159
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 2 1 1 160
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 2 2 161
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 3 4 162
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 2 2 163
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 2 2 164
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 3 1 1 165
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 5 2 3 166
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 2 2 167
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 0 5 2 168
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 3 1 1 169
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 4 1 1 170
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 3 5 2 171
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 2 2 172
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 2 2 173
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 5 4 174
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 1 5 4 175
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 0 2 1 176
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 3 2 177
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 3 2 178
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 3 2 179
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 3 2 180
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 1 0 5 181
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 3 2 182
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 1 3 2 183
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 3 2 184
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 3 2 185
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 1 5 186
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 3 7 2 187
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 3 2 188
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 3 3 2 189
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 3 2 1 190
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 3 2 1 191
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 3 2 1 192
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 0 3 193
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 0 0 3 194
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 4 2 1 195
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 0 3 196
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 4 2 1 197
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 0 3 198
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 0 3 199
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 0 3 200
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 0 3 201
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 0 3 1 202
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 0 3 203
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 0 3 1 204
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 0 3 205
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 0 3 206
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 1 3 1 207
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 5 1 4 208
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 1 3 209
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 1 3 210
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 1 3 211
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 1 3 212
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 2 3 1 213
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 1 1 3 214
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 3 3 1 215
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 1 3 216
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 2 1 3 217
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 6 2 0 0 1 218
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 1 3 219
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 1 3 220
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 4 3 1 221
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 1 3 222
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 4 3 1 223
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 2 1 0 1 224
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 2 3 225
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 0 2 3 226
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 2 3 227
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 2 3 228
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 0 4 1 229
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 1 2 3 230
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 2 3 231
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 2 3 232
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 2 2 3 233
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 6 0 3 0 1 234
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 2 4 1 235
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 2 3 236
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 2 3 237
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 4 1 238
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 2 4 1 239
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 3 4 1 240
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 3 3 241
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 3 3 242
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 3 4 0 1 243
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 3 3 244
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 4 4 1 245
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 3 3 246
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 4 4 1 247
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 3 3 248
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 3 3 249
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 5 0 1 250
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 1 0 0 2 251
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 0 1 5 252
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 0 0 2 253
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 0 0 2 254
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 1 0 2 255
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 0 1 1 256
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 1 0 2 257
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 1 0 2 258
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 1 0 2 259
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 1 2 5 260
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 2 0 2 261
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 3 2 5 262
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 0 2 263
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 2 0 2 264
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 3 0 2 265
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 3 0 2 266
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 3 0 2 267
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 2 1 1 268
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 3 0 2 269
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 4 0 2 270
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 4 0 2 271
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 4 0 2 272
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 4 0 2 273
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 3 1 1 274
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 5 3 1 1 275
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 1 0 1 2 276
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 0 1 2 277
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 0 1 2 278
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 0 1 2 279
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 1 1 2 280
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 5 4 1 1 281
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 0 5 1 1 282
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 1 1 2 283
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 1 1 2 284
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 2 1 2 285
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 5 1 1 286
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 0 6 5 287
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 1 2 288
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
