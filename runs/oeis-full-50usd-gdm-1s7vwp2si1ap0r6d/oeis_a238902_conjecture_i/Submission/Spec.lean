import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

set_option maxHeartbeats 20000000
set_option maxRecDepth 2000000

/--
A238902: $a(n) = |\{0 < k \le n: \pi(\pi(k \cdot n)) \text{ is a square}\}|$,
where $\pi(x)$ denotes the number of primes not exceeding $x$.
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem a_pos_of_exists (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
    (h_sq : (π (π (k * n))).sqrt ^ 2 = π (π (k * n))) : a n > 0 := by
  unfold a
  apply Finset.card_pos.mpr
  use k
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hk1, hk2⟩, h_sq⟩

theorem primeCounting_double_mono : Monotone (fun x => π (π x)) := by
  intro x y hxy
  exact Nat.monotone_primeCounting (Nat.monotone_primeCounting hxy)

theorem pi_pi_eq_of_mono (x L R : ℕ) (S : ℕ) (h_L : L ≤ x) (h_R : x ≤ R)
    (h_pi_L : π (π L) = S ^ 2) (h_pi_R : π (π R) = S ^ 2) : π (π x) = S ^ 2 := by
  have h1 : π (π L) ≤ π (π x) := primeCounting_double_mono h_L
  have h2 : π (π x) ≤ π (π R) := primeCounting_double_mono h_R
  omega

theorem a_pos_of_in_interval (n : ℕ) (k : ℕ) (S : ℕ) (L R : ℕ)
    (h_L : L ≤ k * n) (h_R : k * n ≤ R)
    (hk1 : 1 ≤ k) (hk2 : k ≤ n)
    (h_pi_L : π (π L) = S ^ 2) (h_pi_R : π (π R) = S ^ 2) : a n > 0 := by
  have h_eq : π (π (k * n)) = S ^ 2 := pi_pi_eq_of_mono (k * n) L R S h_L h_R h_pi_L h_pi_R
  have h_sq : (π (π (k * n))).sqrt ^ 2 = π (π (k * n)) := by
    rw [h_eq]
    rw [Nat.sqrt_eq' S]
  exact a_pos_of_exists n k hk1 hk2 h_sq

theorem pi_pi_83 : π (π 83) = 3^2 := by decide
theorem pi_pi_108 : π (π 108) = 3^2 := by decide
theorem pi_pi_241 : π (π 241) = 4^2 := by decide
theorem pi_pi_276 : π (π 276) = 4^2 := by decide
theorem pi_pi_509 : π (π 509) = 5^2 := by decide
theorem pi_pi_546 : π (π 546) = 5^2 := by decide
theorem pi_pi_877 : π (π 877) = 6^2 := by decide
theorem pi_pi_918 : π (π 918) = 6^2 := by decide
theorem pi_pi_1433 : π (π 1433) = 7^2 := by decide
theorem pi_pi_1446 : π (π 1446) = 7^2 := by decide
theorem pi_pi_2063 : π (π 2063) = 8^2 := by decide
theorem pi_pi_2080 : π (π 2080) = 8^2 := by decide
theorem pi_pi_2897 : π (π 2897) = 9^2 := by decide
theorem pi_pi_2908 : π (π 2908) = 9^2 := by decide
theorem pi_pi_3911 : π (π 3911) = 10^2 := by decide
theorem pi_pi_3942 : π (π 3942) = 10^2 := by decide
theorem pi_pi_4943 : π (π 4943) = 11^2 := by decide
theorem pi_pi_5020 : π (π 5020) = 11^2 := by decide
theorem pi_pi_6353 : π (π 6353) = 12^2 := by decide
theorem pi_pi_6360 : π (π 6360) = 12^2 := by decide
theorem pi_pi_8011 : π (π 8011) = 13^2 := by decide
theorem pi_pi_8058 : π (π 8058) = 13^2 := by decide
theorem pi_pi_9661 : π (π 9661) = 14^2 := by decide
theorem pi_pi_9738 : π (π 9738) = 14^2 := by decide
theorem pi_pi_11909 : π (π 11909) = 15^2 := by decide
theorem pi_pi_11926 : π (π 11926) = 15^2 := by decide
theorem pi_pi_13693 : π (π 13693) = 16^2 := by decide
theorem pi_pi_13708 : π (π 13708) = 16^2 := by decide
theorem pi_pi_16141 : π (π 16141) = 17^2 := by decide
theorem pi_pi_16252 : π (π 16252) = 17^2 := by decide
theorem pi_pi_18787 : π (π 18787) = 18^2 := by decide
theorem pi_pi_18916 : π (π 18916) = 18^2 := by decide
theorem pi_pi_21727 : π (π 21727) = 19^2 := by decide
theorem pi_pi_21756 : π (π 21756) = 19^2 := by decide
theorem pi_pi_24781 : π (π 24781) = 20^2 := by decide
theorem pi_pi_24858 : π (π 24858) = 20^2 := by decide
theorem pi_pi_28307 : π (π 28307) = 21^2 := by decide
theorem pi_pi_28392 : π (π 28392) = 21^2 := by decide
theorem pi_pi_32261 : π (π 32261) = 22^2 := by decide
theorem pi_pi_32298 : π (π 32298) = 22^2 := by decide
theorem pi_pi_35801 : π (π 35801) = 23^2 := by decide
theorem pi_pi_35976 : π (π 35976) = 23^2 := by decide
theorem pi_pi_40093 : π (π 40093) = 24^2 := by decide
theorem pi_pi_40150 : π (π 40150) = 24^2 := by decide
theorem pi_pi_64853 : π (π 64853) = 29^2 := by decide
theorem pi_pi_64950 : π (π 64950) = 29^2 := by decide
theorem pi_pi_83617 : π (π 83617) = 32^2 := by decide
theorem pi_pi_83688 : π (π 83688) = 32^2 := by decide
theorem pi_pi_90203 : π (π 90203) = 33^2 := by decide
theorem pi_pi_90246 : π (π 90246) = 33^2 := by decide
theorem pi_pi_112097 : π (π 112097) = 36^2 := by decide
theorem pi_pi_112128 : π (π 112128) = 36^2 := by decide
theorem pi_pi_120223 : π (π 120223) = 37^2 := by decide
theorem pi_pi_120330 : π (π 120330) = 37^2 := by decide
theorem pi_pi_128683 : π (π 128683) = 38^2 := by decide
theorem pi_pi_128968 : π (π 128968) = 38^2 := by decide

/--
Conjecture (i): a(n) > 0 for all n > 0.
-/
theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  rcases lt_or_ge n 547 with h_lt | h_ge
  · interval_cases n
    · exact a_pos_of_exists 1 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 2 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 3 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 4 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 5 4 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 6 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 7 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 8 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 9 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 10 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 11 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 12 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 13 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 14 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 15 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 16 6 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 17 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 18 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 19 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 20 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 21 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 22 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 23 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 24 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 25 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 26 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 27 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 28 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 29 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 30 1 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 31 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 32 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 33 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 34 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 35 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 36 3 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 37 7 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 38 7 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 39 7 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 40 13 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 41 6 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 42 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 43 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 44 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 45 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 46 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 47 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 48 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 49 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 50 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 51 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 52 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 53 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 54 2 (by decide) (by decide) (by decide)
    · exact a_pos_of_exists 55 5 (by decide) (by decide) (by decide)
    · exact a_pos_of_in_interval 56 16 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 57 9 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 58 9 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 59 9 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 60 9 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 61 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 62 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 63 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 64 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 65 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 66 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 67 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 68 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 69 4 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 70 13 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 71 70 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 72 20 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 73 7 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 74 7 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 75 7 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 76 7 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 77 7 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 78 7 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 79 63 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 80 11 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 81 3 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 82 3 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 83 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 84 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 85 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 86 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 87 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 88 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 89 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 90 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 91 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 92 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 93 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 94 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 95 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 96 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 97 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 98 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 99 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 100 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 101 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 102 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 103 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 104 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 105 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 106 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 107 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 108 1 3 83 108 (by decide) (by decide) (by decide) (by decide) pi_pi_83 pi_pi_108
    · exact a_pos_of_in_interval 109 5 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 110 8 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 111 8 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 112 8 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 113 8 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 114 8 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 115 18 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 116 25 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 117 83 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 118 42 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 119 33 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 120 12 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 121 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 122 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 123 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 124 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 125 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 126 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 127 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 128 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 129 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 130 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 131 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 132 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 133 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 134 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 135 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 136 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 137 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 138 2 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 139 36 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 140 28 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 141 57 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 142 35 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 143 35 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 144 10 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 145 20 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 146 27 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 147 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 148 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 149 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 150 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 151 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 152 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 153 6 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 154 63 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 155 32 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 156 32 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 157 25 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 158 51 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 159 13 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 160 9 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 161 18 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 162 60 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 163 24 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 164 24 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 165 30 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 166 30 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 167 30 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 168 112 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 169 96 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 170 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 171 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 172 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 173 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 174 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 175 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 176 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 177 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 178 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 179 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 180 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 181 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 182 3 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 183 5 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 184 27 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 185 27 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 186 52 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 187 21 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 188 11 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 189 11 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 190 51 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 191 26 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 192 26 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 193 26 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 194 50 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 195 83 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 196 20 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 197 20 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 198 25 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 199 25 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 200 25 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 201 40 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 202 48 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 203 80 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 204 139 21 28307 28392 (by decide) (by decide) (by decide) (by decide) pi_pi_28307 pi_pi_28392
    · exact a_pos_of_in_interval 205 7 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 206 7 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 207 10 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 208 10 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 209 24 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 210 77 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 211 38 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 212 30 12 6353 6360 (by decide) (by decide) (by decide) (by decide) pi_pi_6353 pi_pi_6360
    · exact a_pos_of_in_interval 213 76 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 214 64 16 13693 13708 (by decide) (by decide) (by decide) (by decide) pi_pi_13693 pi_pi_13708
    · exact a_pos_of_in_interval 215 23 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 216 23 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 217 23 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 218 18 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 219 18 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 220 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 221 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 222 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 223 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 224 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 225 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 226 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 227 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 228 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 229 4 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 230 9 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 231 9 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 232 70 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 233 81 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 234 69 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 235 69 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 236 21 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 237 21 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 238 21 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 239 6 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 240 6 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 241 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 242 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 243 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 244 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 245 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 246 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 247 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 248 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 249 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 250 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 251 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 252 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 253 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 254 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 255 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 256 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 257 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 258 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 259 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 260 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 261 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 262 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 263 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 264 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 265 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 266 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 267 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 268 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 269 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 270 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 271 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 272 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 273 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 274 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 275 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 276 1 4 241 276 (by decide) (by decide) (by decide) (by decide) pi_pi_241 pi_pi_276
    · exact a_pos_of_in_interval 277 18 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 278 18 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 279 58 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 280 14 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 281 14 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 282 67 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 283 114 22 32261 32298 (by decide) (by decide) (by decide) (by decide) pi_pi_32261 pi_pi_32298
    · exact a_pos_of_in_interval 284 57 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 285 34 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 286 34 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 287 5 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 288 5 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 289 5 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 290 10 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 291 17 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 292 17 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 293 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 294 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 295 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 296 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 297 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 298 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 299 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 300 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 301 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 302 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 303 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 304 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 305 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 306 3 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 307 117 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 308 61 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 309 16 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 310 16 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 311 16 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 312 16 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 313 16 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 314 31 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 315 60 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 316 127 24 40093 40150 (by decide) (by decide) (by decide) (by decide) pi_pi_40093 pi_pi_40150
    · exact a_pos_of_in_interval 317 51 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 318 20 12 6353 6360 (by decide) (by decide) (by decide) (by decide) pi_pi_6353 pi_pi_6360
    · exact a_pos_of_in_interval 319 59 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 320 59 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 321 25 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 322 9 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 323 9 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 324 30 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 325 50 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 326 12 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 327 12 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 328 12 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 329 109 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 330 15 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 331 15 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 332 15 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 333 15 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 334 15 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 335 24 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 336 56 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 337 48 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 338 48 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 339 106 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 340 73 20 24781 24858 (by decide) (by decide) (by decide) (by decide) pi_pi_24781 pi_pi_24858
    · exact a_pos_of_in_interval 341 105 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 342 55 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 343 55 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 344 6 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 345 6 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 346 6 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 347 28 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 348 54 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 349 23 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 350 23 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 351 46 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 352 46 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 353 18 12 6353 6360 (by decide) (by decide) (by decide) (by decide) pi_pi_6353 pi_pi_6360
    · exact a_pos_of_in_interval 354 14 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 355 14 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 356 11 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 357 11 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 358 11 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 359 4 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 360 4 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 361 4 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 362 52 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 363 8 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 364 78 21 28307 28392 (by decide) (by decide) (by decide) (by decide) pi_pi_28307 pi_pi_28392
    · exact a_pos_of_in_interval 365 22 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 366 22 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 367 44 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 368 44 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 369 44 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 370 51 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 371 67 20 24781 24858 (by decide) (by decide) (by decide) (by decide) pi_pi_24781 pi_pi_24858
    · exact a_pos_of_in_interval 372 26 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 373 26 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 374 17 12 6353 6360 (by decide) (by decide) (by decide) (by decide) pi_pi_6353 pi_pi_6360
    · exact a_pos_of_in_interval 375 58 19 21727 21756 (by decide) (by decide) (by decide) (by decide) pi_pi_21727 pi_pi_21756
    · exact a_pos_of_in_interval 376 43 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 377 43 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 378 50 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 379 340 38 128683 128968 (by decide) (by decide) (by decide) (by decide) pi_pi_128683 pi_pi_128968
    · exact a_pos_of_in_interval 380 295 36 112097 112128 (by decide) (by decide) (by decide) (by decide) pi_pi_112097 pi_pi_112128
    · exact a_pos_of_in_interval 381 13 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 382 13 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 383 13 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 384 13 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 385 13 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 386 13 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 387 25 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 388 25 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 389 25 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 390 92 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 391 92 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 392 10 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 393 10 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 394 10 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 395 41 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 396 41 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 397 30 15 11909 11926 (by decide) (by decide) (by decide) (by decide) pi_pi_11909 pi_pi_11926
    · exact a_pos_of_in_interval 398 90 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 399 71 21 28307 28392 (by decide) (by decide) (by decide) (by decide) pi_pi_28307 pi_pi_28392
    · exact a_pos_of_in_interval 400 47 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 401 20 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 402 20 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 403 24 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 404 24 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 405 24 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 406 40 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 407 61 20 24781 24858 (by decide) (by decide) (by decide) (by decide) pi_pi_24781 pi_pi_24858
    · exact a_pos_of_in_interval 408 88 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 409 46 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 410 46 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 411 29 15 11909 11926 (by decide) (by decide) (by decide) (by decide) pi_pi_11909 pi_pi_11926
    · exact a_pos_of_in_interval 412 12 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 413 5 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 414 5 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 415 5 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 416 5 8 2063 2080 (by decide) (by decide) (by decide) (by decide) pi_pi_2063 pi_pi_2080
    · exact a_pos_of_in_interval 417 12 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 418 12 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 419 45 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 420 45 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 421 23 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 422 19 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 423 19 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 424 15 12 6353 6360 (by decide) (by decide) (by decide) (by decide) pi_pi_6353 pi_pi_6360
    · exact a_pos_of_in_interval 425 38 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 426 38 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 427 38 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 428 32 16 13693 13708 (by decide) (by decide) (by decide) (by decide) pi_pi_13693 pi_pi_13708
    · exact a_pos_of_in_interval 429 44 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 430 66 21 28307 28392 (by decide) (by decide) (by decide) (by decide) pi_pi_28307 pi_pi_28392
    · exact a_pos_of_in_interval 431 279 37 120223 120330 (by decide) (by decide) (by decide) (by decide) pi_pi_120223 pi_pi_120330
    · exact a_pos_of_in_interval 432 83 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 433 83 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 434 297 38 128683 128968 (by decide) (by decide) (by decide) (by decide) pi_pi_128683 pi_pi_128968
    · exact a_pos_of_in_interval 435 9 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 436 9 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 437 9 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 438 9 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 439 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 440 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 441 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 442 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 443 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 444 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 445 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 446 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 447 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 448 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 449 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 450 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 451 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 452 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 453 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 454 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 455 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 456 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 457 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 458 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 459 2 6 877 918 (by decide) (by decide) (by decide) (by decide) pi_pi_877 pi_pi_918
    · exact a_pos_of_in_interval 460 41 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 461 21 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 462 21 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 463 21 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 464 35 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 465 61 21 28307 28392 (by decide) (by decide) (by decide) (by decide) pi_pi_28307 pi_pi_28392
    · exact a_pos_of_in_interval 466 77 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 467 77 23 35801 35976 (by decide) (by decide) (by decide) (by decide) pi_pi_35801 pi_pi_35976
    · exact a_pos_of_in_interval 468 53 20 24781 24858 (by decide) (by decide) (by decide) (by decide) pi_pi_24781 pi_pi_24858
    · exact a_pos_of_in_interval 469 53 20 24781 24858 (by decide) (by decide) (by decide) (by decide) pi_pi_24781 pi_pi_24858
    · exact a_pos_of_in_interval 470 40 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 471 40 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 472 17 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 473 17 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 474 17 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 475 34 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 476 34 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 477 25 15 11909 11926 (by decide) (by decide) (by decide) (by decide) pi_pi_11909 pi_pi_11926
    · exact a_pos_of_in_interval 478 3 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 479 3 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 480 3 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 481 3 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 482 3 7 1433 1446 (by decide) (by decide) (by decide) (by decide) pi_pi_1433 pi_pi_1446
    · exact a_pos_of_in_interval 483 6 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 484 6 9 2897 2908 (by decide) (by decide) (by decide) (by decide) pi_pi_2897 pi_pi_2908
    · exact a_pos_of_in_interval 485 20 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 486 20 14 9661 9738 (by decide) (by decide) (by decide) (by decide) pi_pi_9661 pi_pi_9738
    · exact a_pos_of_in_interval 487 51 20 24781 24858 (by decide) (by decide) (by decide) (by decide) pi_pi_24781 pi_pi_24858
    · exact a_pos_of_in_interval 488 133 29 64853 64950 (by decide) (by decide) (by decide) (by decide) pi_pi_64853 pi_pi_64950
    · exact a_pos_of_in_interval 489 8 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 490 8 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 491 8 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 492 8 10 3911 3942 (by decide) (by decide) (by decide) (by decide) pi_pi_3911 pi_pi_3942
    · exact a_pos_of_in_interval 493 183 33 90203 90246 (by decide) (by decide) (by decide) (by decide) pi_pi_90203 pi_pi_90246
    · exact a_pos_of_in_interval 494 44 19 21727 21756 (by decide) (by decide) (by decide) (by decide) pi_pi_21727 pi_pi_21756
    · exact a_pos_of_in_interval 495 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 496 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 497 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 498 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 499 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 500 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 501 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 502 10 11 4943 5020 (by decide) (by decide) (by decide) (by decide) pi_pi_4943 pi_pi_5020
    · exact a_pos_of_in_interval 503 16 13 8011 8058 (by decide) (by decide) (by decide) (by decide) pi_pi_8011 pi_pi_8058
    · exact a_pos_of_in_interval 504 166 32 83617 83688 (by decide) (by decide) (by decide) (by decide) pi_pi_83617 pi_pi_83688
    · exact a_pos_of_in_interval 505 32 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 506 32 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 507 32 17 16141 16252 (by decide) (by decide) (by decide) (by decide) pi_pi_16141 pi_pi_16252
    · exact a_pos_of_in_interval 508 37 18 18787 18916 (by decide) (by decide) (by decide) (by decide) pi_pi_18787 pi_pi_18916
    · exact a_pos_of_in_interval 509 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 510 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 511 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 512 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 513 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 514 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 515 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 516 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 517 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 518 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 519 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 520 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 521 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 522 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 523 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 524 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 525 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 526 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 527 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 528 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 529 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 530 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 531 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 532 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 533 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 534 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 535 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 536 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 537 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 538 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 539 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 540 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 541 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 542 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 543 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 544 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 545 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
    · exact a_pos_of_in_interval 546 1 5 509 546 (by decide) (by decide) (by decide) (by decide) pi_pi_509 pi_pi_546
  · sorry
