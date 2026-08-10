import Submission.Cases

theorem a_le_a081512_of_ge_six (n : ℕ) : a (n + 6) ≤ a081512 (n + 6) := by
  rcases n with _|n
  · exact a_six_le_a081512_six
  rcases n with _|n
  · exact a_seven_le_a081512_seven
  rcases n with _|n
  · exact a_eight_le_a081512_eight
  rcases n with _|n
  · exact a_nine_le_a081512_nine
  rcases n with _|n
  · exact a_ten_le_a081512_ten
  rcases n with _|n
  · exact a_eleven_le_a081512_eleven
  rcases n with _|n
  · exact a_twelve_le_a081512_twelve
  rcases n with _|n
  · exact a_thirteen_le_a081512_thirteen
  rcases n with _|n
  · exact a_fourteen_le_a081512_fourteen
  rcases n with _|n
  · exact a_fifteen_le_a081512_fifteen
  rcases n with _|n
  · exact a_sixteen_le_a081512_sixteen
  rcases n with _|n
  · exact a_seventeen_le_a081512_seventeen
  rcases n with _|n
  · exact a_eighteen_le_a081512_eighteen
  rcases n with _|n
  · exact a_nineteen_le_a081512_nineteen
  rcases n with _|n
  · exact a_twenty_le_a081512_twenty
  rcases n with _|n
  · exact a_twentyone_le_a081512_twentyone
  rcases n with _|n
  · exact a_twentytwo_le_a081512_twentytwo
  rcases n with _|n
  · exact a_twentythree_le_a081512_twentythree
  rcases n with _|n
  · exact a_twentyfour_le_a081512_twentyfour
  rcases n with _|n
  · exact a_twentyfive_le_a081512_twentyfive
  rcases n with _|n
  · exact a_twentysix_le_a081512_twentysix
  rcases n with _|n
  · exact a_twentyseven_le_a081512_twentyseven
  rcases n with _|n
  · exact a_twentyeight_le_a081512_twentyeight
  rcases n with _|n
  · exact a_twentynine_le_a081512_twentynine
  rcases n with _|n
  · exact a_thirty_le_a081512_thirty
  rcases n with _|n
  · exact a_thirtyone_le_a081512_thirtyone
  rcases n with _|n
  · exact a_thirtytwo_le_a081512_thirtytwo
  · sorry

lemma a_le_a081512_of_ne_four_five (n : ℕ) (h4 : n ≠ 4) (h5 : n ≠ 5) : a n ≤ a081512 n := by
  rcases n with _|n
  · exact a_zero_le_a081512_zero
  rcases n with _|n
  · exact a_one_le_a081512_one
  rcases n with _|n
  · exact a_two_le_a081512_two
  rcases n with _|n
  · exact a_three_le_a081512_three
  rcases n with _|n
  · contradiction
  rcases n with _|n
  · contradiction
  · exact a_le_a081512_of_ge_six n

theorem oeis_355228_conjecture_0 (n : ℕ) : (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · intro h
    by_contra h_not
    push_neg at h_not
    have h_le := a_le_a081512_of_ne_four_five n h_not.1 h_not.2
    omega
  · rintro (rfl | rfl)
    · exact a_four_gt_a081512_four
    · exact a_five_gt_a081512_five

#print axioms oeis_355228_conjecture_0
