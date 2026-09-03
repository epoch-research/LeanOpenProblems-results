import FormalConjecturesUtil

/-!
A three-edge obstruction to odd edge-sum colorings on either factor-count
fiber of squarefree roots coprime to 210 with sufficiently large exact factor count. This does not exclude ordinary
proper colorings and does not settle the positive-density cube-Sidon conjecture.
-/
namespace Erdos1206.ExactFactorCountOddColorObstruction

private lemma lucas_of_list (p : ℕ) (a : ZMod p) (L : List ℕ)
    (hprod : L.prod = p-1) (hL : ∀ q ∈ L, Nat.Prime q)
    (ha : a^(p-1)=1) (hd : ∀ q ∈ L, a^((p-1)/q) ≠ 1) : Nat.Prime p := by
  apply lucas_primality p a ha
  intro q hq hqd
  apply hd q
  apply mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
    (fun r hr => Nat.prime_iff.mp (hL r hr))
  rwa [hprod]

private lemma prime_2 : Nat.Prime 2 := by
  norm_num

private lemma prime_3 : Nat.Prime 3 := by
  norm_num

private lemma prime_5 : Nat.Prime 5 := by
  norm_num

private lemma prime_7 : Nat.Prime 7 := by
  norm_num

private lemma prime_11 : Nat.Prime 11 := by
  norm_num

private lemma prime_13 : Nat.Prime 13 := by
  norm_num

private lemma prime_17 : Nat.Prime 17 := by
  norm_num

private lemma prime_19 : Nat.Prime 19 := by
  norm_num

private lemma prime_23 : Nat.Prime 23 := by
  norm_num

private lemma prime_29 : Nat.Prime 29 := by
  norm_num

private lemma prime_31 : Nat.Prime 31 := by
  norm_num

private lemma prime_41 : Nat.Prime 41 := by
  norm_num

private lemma prime_43 : Nat.Prime 43 := by
  norm_num

private lemma prime_47 : Nat.Prime 47 := by
  norm_num

private lemma prime_53 : Nat.Prime 53 := by
  norm_num

private lemma prime_59 : Nat.Prime 59 := by
  norm_num

private lemma prime_71 : Nat.Prime 71 := by
  norm_num

private lemma prime_79 : Nat.Prime 79 := by
  norm_num

private lemma prime_89 : Nat.Prime 89 := by
  norm_num

private lemma prime_101 : Nat.Prime 101 := by
  norm_num

private lemma prime_109 : Nat.Prime 109 := by
  norm_num

private lemma prime_113 : Nat.Prime 113 := by
  norm_num

private lemma prime_131 : Nat.Prime 131 := by
  norm_num

private lemma prime_163 : Nat.Prime 163 := by
  norm_num

private lemma prime_173 : Nat.Prime 173 := by
  norm_num

private lemma prime_179 : Nat.Prime 179 := by
  norm_num

private lemma prime_199 : Nat.Prime 199 := by
  norm_num

private lemma prime_271 : Nat.Prime 271 := by
  norm_num

private lemma prime_313 : Nat.Prime 313 := by
  norm_num

private lemma prime_349 : Nat.Prime 349 := by
  norm_num

private lemma prime_367 : Nat.Prime 367 := by
  norm_num

private lemma prime_383 : Nat.Prime 383 := by
  norm_num

private lemma prime_389 : Nat.Prime 389 := by
  norm_num

private lemma prime_461 : Nat.Prime 461 := by
  norm_num

private lemma prime_487 : Nat.Prime 487 := by
  norm_num

private lemma prime_577 : Nat.Prime 577 := by
  norm_num

private lemma prime_631 : Nat.Prime 631 := by
  norm_num

private lemma prime_647 : Nat.Prime 647 := by
  norm_num

private lemma prime_653 : Nat.Prime 653 := by
  norm_num

private lemma prime_859 : Nat.Prime 859 := by
  norm_num

private lemma prime_937 : Nat.Prime 937 := by
  norm_num

private lemma prime_1009 : Nat.Prime 1009 := by
  apply lucas_of_list 1009 (11 : ZMod 1009) [2, 2, 2, 2, 3, 3, 7]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1021 : Nat.Prime 1021 := by
  apply lucas_of_list 1021 (10 : ZMod 1021) [2, 2, 3, 5, 17]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_17
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1069 : Nat.Prime 1069 := by
  apply lucas_of_list 1069 (6 : ZMod 1069) [2, 2, 3, 89]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_89
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1201 : Nat.Prime 1201 := by
  apply lucas_of_list 1201 (11 : ZMod 1201) [2, 2, 2, 2, 3, 5, 5]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1321 : Nat.Prime 1321 := by
  apply lucas_of_list 1321 (13 : ZMod 1321) [2, 2, 2, 3, 5, 11]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1409 : Nat.Prime 1409 := by
  apply lucas_of_list 1409 (3 : ZMod 1409) [2, 2, 2, 2, 2, 2, 2, 11]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1667 : Nat.Prime 1667 := by
  apply lucas_of_list 1667 (2 : ZMod 1667) [2, 7, 7, 17]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_7
    · exact prime_17
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_2203 : Nat.Prime 2203 := by
  apply lucas_of_list 2203 (5 : ZMod 2203) [2, 3, 367]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_367
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_2711 : Nat.Prime 2711 := by
  apply lucas_of_list 2711 (7 : ZMod 2711) [2, 5, 271]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_271
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_2767 : Nat.Prime 2767 := by
  apply lucas_of_list 2767 (3 : ZMod 2767) [2, 3, 461]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_461
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_2819 : Nat.Prime 2819 := by
  apply lucas_of_list 2819 (2 : ZMod 2819) [2, 1409]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_1409
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_5639 : Nat.Prime 5639 := by
  apply lucas_of_list 5639 (7 : ZMod 5639) [2, 2819]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2819
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_6229 : Nat.Prime 6229 := by
  apply lucas_of_list 6229 (2 : ZMod 6229) [2, 2, 3, 3, 173]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_173
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_6551 : Nat.Prime 6551 := by
  apply lucas_of_list 6551 (17 : ZMod 6551) [2, 5, 5, 131]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_131
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_7927 : Nat.Prime 7927 := by
  apply lucas_of_list 7927 (3 : ZMod 7927) [2, 3, 1321]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1321
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_18379 : Nat.Prime 18379 := by
  apply lucas_of_list 18379 (3 : ZMod 18379) [2, 3, 3, 1021]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_1021
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_24677 : Nat.Prime 24677 := by
  apply lucas_of_list 24677 (2 : ZMod 24677) [2, 2, 31, 199]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_31
    · exact prime_199
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_42131 : Nat.Prime 42131 := by
  apply lucas_of_list 42131 (2 : ZMod 42131) [2, 5, 11, 383]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_383
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_60013 : Nat.Prime 60013 := by
  apply lucas_of_list 60013 (6 : ZMod 60013) [2, 2, 3, 3, 1667]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_1667
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_73517 : Nat.Prime 73517 := by
  apply lucas_of_list 73517 (2 : ZMod 73517) [2, 2, 18379]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_18379
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_84263 : Nat.Prime 84263 := by
  apply lucas_of_list 84263 (5 : ZMod 84263) [2, 42131]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_42131
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_168527 : Nat.Prime 168527 := by
  apply lucas_of_list 168527 (5 : ZMod 168527) [2, 84263]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_84263
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_208609 : Nat.Prime 208609 := by
  apply lucas_of_list 208609 (13 : ZMod 208609) [2, 2, 2, 2, 2, 3, 41, 53]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_41
    · exact prime_53
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_223211 : Nat.Prime 223211 := by
  apply lucas_of_list 223211 (6 : ZMod 223211) [2, 5, 13, 17, 101]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_17
    · exact prime_101
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_460871 : Nat.Prime 460871 := by
  apply lucas_of_list 460871 (11 : ZMod 460871) [2, 5, 17, 2711]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_2711
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_493541 : Nat.Prime 493541 := by
  apply lucas_of_list 493541 (3 : ZMod 493541) [2, 2, 5, 24677]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_24677
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_791891 : Nat.Prime 791891 := by
  apply lucas_of_list 791891 (6 : ZMod 791891) [2, 5, 11, 23, 313]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_23
    · exact prime_313
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1323307 : Nat.Prime 1323307 := by
  apply lucas_of_list 1323307 (2 : ZMod 1323307) [2, 3, 3, 73517]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_73517
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_2547473 : Nat.Prime 2547473 := by
  apply lucas_of_list 2547473 (3 : ZMod 2547473) [2, 2, 2, 2, 113, 1409]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_113
    · exact prime_1409
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_2927189 : Nat.Prime 2927189 := by
  apply lucas_of_list 2927189 (2 : ZMod 2927189) [2, 2, 11, 71, 937]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_71
    · exact prime_937
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_3754963 : Nat.Prime 3754963 := by
  apply lucas_of_list 3754963 (3 : ZMod 3754963) [2, 3, 3, 208609]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_208609
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_17434601 : Nat.Prime 17434601 := by
  apply lucas_of_list 17434601 (6 : ZMod 17434601) [2, 2, 2, 5, 5, 179, 487]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_179
    · exact prime_487
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_26438413 : Nat.Prime 26438413 := by
  apply lucas_of_list 26438413 (2 : ZMod 26438413) [2, 2, 3, 7, 11, 13, 31, 71]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_71
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_49134353 : Nat.Prime 49134353 := by
  apply lucas_of_list 49134353 (3 : ZMod 49134353) [2, 2, 2, 2, 17, 29, 6229]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_17
    · exact prime_29
    · exact prime_6229
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_66826043 : Nat.Prime 66826043 := by
  apply lucas_of_list 66826043 (2 : ZMod 66826043) [2, 43, 647, 1201]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_43
    · exact prime_647
    · exact prime_1201
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_231921689 : Nat.Prime 231921689 := by
  apply lucas_of_list 231921689 (3 : ZMod 231921689) [2, 2, 2, 47, 577, 1069]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_47
    · exact prime_577
    · exact prime_1069
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_638043223 : Nat.Prime 638043223 := by
  apply lucas_of_list 638043223 (5 : ZMod 638043223) [2, 3, 631, 168527]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_631
    · exact prime_168527
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_687880943 : Nat.Prime 687880943 := by
  apply lucas_of_list 687880943 (5 : ZMod 687880943) [2, 7, 49134353]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_49134353
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1375761887 : Nat.Prime 1375761887 := by
  apply lucas_of_list 1375761887 (5 : ZMod 1375761887) [2, 687880943]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_687880943
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1439768357 : Nat.Prime 1439768357 := by
  apply lucas_of_list 1439768357 (2 : ZMod 1439768357) [2, 2, 13, 109, 389, 653]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_13
    · exact prime_109
    · exact prime_389
    · exact prime_653
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1450776839 : Nat.Prime 1450776839 := by
  apply lucas_of_list 1450776839 (7 : ZMod 1450776839) [2, 7, 17, 2203, 2767]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_2203
    · exact prime_2767
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_3520747387 : Nat.Prime 3520747387 := by
  apply lucas_of_list 3520747387 (3 : ZMod 3520747387) [2, 3, 3, 13, 19, 791891]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_19
    · exact prime_791891
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_3992685797 : Nat.Prime 3992685797 := by
  apply lucas_of_list 3992685797 (2 : ZMod 3992685797) [2, 2, 11, 31, 2927189]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_31
    · exact prime_2927189
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_4174590403 : Nat.Prime 4174590403 := by
  apply lucas_of_list 4174590403 (2 : ZMod 4174590403) [2, 3, 3, 231921689]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_231921689
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_23956114783 : Nat.Prime 23956114783 := by
  apply lucas_of_list 23956114783 (3 : ZMod 23956114783) [2, 3, 3992685797]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3992685797
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_59327798773 : Nat.Prime 59327798773 := by
  apply lucas_of_list 59327798773 (5 : ZMod 59327798773) [2, 2, 3, 11, 17, 26438413]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_26438413
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_72894789101 : Nat.Prime 72894789101 := by
  apply lucas_of_list 72894789101 (3 : ZMod 72894789101) [2, 2, 5, 5, 7, 59, 313, 5639]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_7
    · exact prime_59
    · exact prime_313
    · exact prime_5639
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_132073141153 : Nat.Prime 132073141153 := by
  apply lucas_of_list 132073141153 (13 : ZMod 132073141153) [2, 2, 2, 2, 2, 3, 1375761887]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_1375761887
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_202985101499 : Nat.Prime 202985101499 := by
  apply lucas_of_list 202985101499 (2 : ZMod 202985101499) [2, 349, 631, 460871]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_349
    · exact prime_631
    · exact prime_460871
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_583158312809 : Nat.Prime 583158312809 := by
  apply lucas_of_list 583158312809 (3 : ZMod 583158312809) [2, 2, 2, 72894789101]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_72894789101
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1732227545767 : Nat.Prime 1732227545767 := by
  apply lucas_of_list 1732227545767 (3 : ZMod 1732227545767) [2, 3, 199, 1450776839]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_199
    · exact prime_1450776839
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_10301448360449 : Nat.Prime 10301448360449 := by
  apply lucas_of_list 10301448360449 (6 : ZMod 10301448360449) [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 79, 163, 223211]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_79
    · exact prime_163
    · exact prime_223211
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_81905463706861 : Nat.Prime 81905463706861 := by
  apply lucas_of_list 81905463706861 (2 : ZMod 81905463706861) [2, 2, 3, 3, 5, 109, 4174590403]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_109
    · exact prime_4174590403
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1228871804474947 : Nat.Prime 1228871804474947 := by
  apply lucas_of_list 1228871804474947 (2 : ZMod 1228871804474947) [2, 3, 1009, 202985101499]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1009
    · exact prime_202985101499
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_29492923307398729 : Nat.Prime 29492923307398729 := by
  apply lucas_of_list 29492923307398729 (7 : ZMod 29492923307398729) [2, 2, 2, 3, 1228871804474947]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_1228871804474947
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_7276932019288047971 : Nat.Prime 7276932019288047971 := by
  apply lucas_of_list 7276932019288047971 (2 : ZMod 7276932019288047971) [2, 5, 7, 60013, 1732227545767]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_60013
    · exact prime_1732227545767
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_16069372021164472291 : Nat.Prime 16069372021164472291 := by
  apply lucas_of_list 16069372021164472291 (10 : ZMod 16069372021164472291) [2, 3, 3, 3, 3, 3, 3, 5, 7, 493541, 638043223]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_493541
    · exact prime_638043223
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_17517903101921768537 : Nat.Prime 17517903101921768537 := by
  apply lucas_of_list 17517903101921768537 (3 : ZMod 17517903101921768537) [2, 2, 2, 3754963, 583158312809]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3754963
    · exact prime_583158312809
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

def source (r : ℕ) : Set ℕ :=
  {n | Squarefree n ∧ Nat.Coprime n 210 ∧ n.primeFactors.card = r}

private lemma witness_4075931005843319029687996465355712523077586706559282680422363 : 4075931005843319029687996465355712523077586706559282680422363 ∈ source 8 := by
  have he : (4075931005843319029687996465355712523077586706559282680422363 : ℕ) = 13 * (577 * (859 * (7927 * (1439768357 * (23956114783 * (132073141153 * (17517903101921768537))))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_577.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_859.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_1439768357.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_132073141153.squarefree, ?_⟩
    exact prime_17517903101921768537.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_577.primeFactors, prime_859.primeFactors, prime_7927.primeFactors, prime_1439768357.primeFactors, prime_23956114783.primeFactors, prime_132073141153.primeFactors, prime_17517903101921768537.primeFactors]
    decide +kernel

private lemma witness_3738897931129102982013631576254351490068689545396569741376409 : 3738897931129102982013631576254351490068689545396569741376409 ∈ source 8 := by
  have he : (3738897931129102982013631576254351490068689545396569741376409 : ℕ) = 13 * (577 * (859 * (7927 * (1439768357 * (23956114783 * (132073141153 * (16069372021164472291))))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_577.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_859.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_1439768357.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_132073141153.squarefree, ?_⟩
    exact prime_16069372021164472291.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_577.primeFactors, prime_859.primeFactors, prime_7927.primeFactors, prime_1439768357.primeFactors, prime_23956114783.primeFactors, prime_132073141153.primeFactors, prime_16069372021164472291.primeFactors]
    decide +kernel

private lemma witness_7730156005004406346761304853015901152216404550070389662946371 : 7730156005004406346761304853015901152216404550070389662946371 ∈ source 8 := by
  have he : (7730156005004406346761304853015901152216404550070389662946371 : ℕ) = 29 * (577 * (859 * (6551 * (1439768357 * (59327798773 * (132073141153 * (7276932019288047971))))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_29.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_577.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_859.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_1439768357.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_132073141153.squarefree, ?_⟩
    exact prime_7276932019288047971.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_29.primeFactors, prime_577.primeFactors, prime_859.primeFactors, prime_6551.primeFactors, prime_1439768357.primeFactors, prime_59327798773.primeFactors, prime_132073141153.primeFactors, prime_7276932019288047971.primeFactors]
    decide +kernel

private lemma witness_7643009618266689271774321705942342629145424860648080869784257 : 7643009618266689271774321705942342629145424860648080869784257 ∈ source 8 := by
  have he : (7643009618266689271774321705942342629145424860648080869784257 : ℕ) = 577 * (859 * (6551 * (2547473 * (1439768357 * (59327798773 * (132073141153 * (81905463706861))))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_577.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_859.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_2547473.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_1439768357.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_132073141153.squarefree, ?_⟩
    exact prime_81905463706861.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_577.primeFactors, prime_859.primeFactors, prime_6551.primeFactors, prime_2547473.primeFactors, prime_1439768357.primeFactors, prime_59327798773.primeFactors, prime_132073141153.primeFactors, prime_81905463706861.primeFactors]
    decide +kernel

private lemma witness_2502410809950365571285893904048340785665820151183761956284111 : 2502410809950365571285893904048340785665820151183761956284111 ∈ source 8 := by
  have he : (2502410809950365571285893904048340785665820151183761956284111 : ℕ) = 13 * (6551 * (7927 * (1323307 * (66826043 * (23956114783 * (59327798773 * (29492923307398729))))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_1323307.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_66826043.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    exact prime_29492923307398729.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_6551.primeFactors, prime_7927.primeFactors, prime_1323307.primeFactors, prime_66826043.primeFactors, prime_23956114783.primeFactors, prime_59327798773.primeFactors, prime_29492923307398729.primeFactors]
    decide +kernel

private lemma witness_606707828165955795995905885403892680063436908411995579213517 : 606707828165955795995905885403892680063436908411995579213517 ∈ source 8 := by
  have he : (606707828165955795995905885403892680063436908411995579213517 : ℕ) = 13 * (6551 * (7927 * (17434601 * (3520747387 * (23956114783 * (59327798773 * (10301448360449))))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_17434601.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_3520747387.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    exact prime_10301448360449.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_6551.primeFactors, prime_7927.primeFactors, prime_17434601.primeFactors, prime_3520747387.primeFactors, prime_23956114783.primeFactors, prime_59327798773.primeFactors, prime_10301448360449.primeFactors]
    decide +kernel

private lemma parity_triangle (a b c d e f : ZMod 2)
    (h₁ : a+b+c+d=1) (h₂ : a+b+e+f=1) (h₃ : c+d+e+f=1) : False := by
  have h : 2*(a+b+c+d+e+f)=(3 : ZMod 2) := by
    linear_combination h₁+h₂+h₃
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul] at h
  exact (by decide : (0 : ZMod 2) ≠ 3) h

private lemma exists_squarefree_coprime_count (N k : ℕ) (hN : 0 < N) :
    ∃ q : ℕ, Squarefree q ∧ Nat.Coprime q N ∧ q.primeFactors.card = k := by
  induction k with
  | zero => exact ⟨1, squarefree_one, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨q, hsq, hqN, hqk⟩ := ih
    have hq : 0 < q := Nat.pos_of_ne_zero hsq.ne_zero
    obtain ⟨p, hpbig, hp⟩ := Nat.exists_infinite_primes (q*N+1)
    have hpq : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd hq hd
      have := Nat.le_mul_of_pos_right q hN
      omega)
    have hpN : Nat.Coprime p N := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd hN hd
      have := Nat.le_mul_of_pos_left N hq
      omega)
    refine ⟨p*q, (Nat.squarefree_mul hpq).mpr ⟨hp.squarefree, hsq⟩,
      hpN.mul_left hqN, ?_⟩
    rw [Nat.primeFactors_mul hp.ne_zero hsq.ne_zero,
      Finset.card_union_of_disjoint ((Nat.disjoint_primeFactors hp.ne_zero hsq.ne_zero).mpr hpq),
      hp.primeFactors, Finset.card_singleton, hqk]
    omega

/-- For every k ≥ 8, the squarefree roots coprime to 210 with exactly k
prime factors have no Boolean coloring with odd sum on every cubic collision.
This does not rule out ordinary proper coloring or settle Erdős 1206. -/
theorem no_odd_coloring_exact_count (k : ℕ) (hk : 8 ≤ k) :
    ¬ ∃ c : ℕ → ZMod 2, ∀ a b d e : ℕ,
      a ∈ source k → b ∈ source k → d ∈ source k → e ∈ source k →
      a < b → b < d → d < e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=1 := by
  rintro ⟨c,hc⟩
  let N : ℕ := 287065233971591457718749988763400285821567969160209937729106887614987120779063781477347810603684733584464935795456343698055949236383592844237506963738896205685700524251902842915270729506023539516751292069219914636659893476565728358786657691660265794871925528104019455468273049741217523401569191880422386326420836783914473287531824268147320364414216530777007724592230
  obtain ⟨q, hsq, hqN, hqk⟩ := exists_squarefree_coprime_count N (k-8) (by norm_num [N])
  have hq : 0 < q := Nat.pos_of_ne_zero hsq.ne_zero
  have hq210 : Nat.Coprime q 210 := hqN.of_dvd_right (by norm_num [N])
  have hmem (n : ℕ) (hn : n ∈ source 8) (hd : n ∣ N) : q*n ∈ source k := by
    have hqn := hqN.of_dvd_right hd
    have hn0 : n ≠ 0 := hn.1.ne_zero
    refine ⟨(Nat.squarefree_mul hqn).mpr ⟨hsq, hn.1⟩,
      hq210.mul_left hn.2.1, ?_⟩
    rw [Nat.primeFactors_mul hsq.ne_zero hn0,
      Finset.card_union_of_disjoint ((Nat.disjoint_primeFactors hsq.ne_zero hn0).mpr hqn),
      hqk, hn.2.2]
    omega
  have h0 : q*606707828165955795995905885403892680063436908411995579213517 ∈ source k := hmem 606707828165955795995905885403892680063436908411995579213517 witness_606707828165955795995905885403892680063436908411995579213517 (by norm_num [N])
  have h1 : q*2502410809950365571285893904048340785665820151183761956284111 ∈ source k := hmem 2502410809950365571285893904048340785665820151183761956284111 witness_2502410809950365571285893904048340785665820151183761956284111 (by norm_num [N])
  have h2 : q*3738897931129102982013631576254351490068689545396569741376409 ∈ source k := hmem 3738897931129102982013631576254351490068689545396569741376409 witness_3738897931129102982013631576254351490068689545396569741376409 (by norm_num [N])
  have h3 : q*4075931005843319029687996465355712523077586706559282680422363 ∈ source k := hmem 4075931005843319029687996465355712523077586706559282680422363 witness_4075931005843319029687996465355712523077586706559282680422363 (by norm_num [N])
  have h4 : q*7643009618266689271774321705942342629145424860648080869784257 ∈ source k := hmem 7643009618266689271774321705942342629145424860648080869784257 witness_7643009618266689271774321705942342629145424860648080869784257 (by norm_num [N])
  have h5 : q*7730156005004406346761304853015901152216404550070389662946371 ∈ source k := hmem 7730156005004406346761304853015901152216404550070389662946371 witness_7730156005004406346761304853015901152216404550070389662946371 (by norm_num [N])
  have he1 := hc (q*606707828165955795995905885403892680063436908411995579213517) (q*2502410809950365571285893904048340785665820151183761956284111) (q*3738897931129102982013631576254351490068689545396569741376409) (q*4075931005843319029687996465355712523077586706559282680422363) h0 h1 h2 h3
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (by simpa only [mul_pow, ←mul_add] using
      congrArg (fun n : ℕ => q^3*n) (by norm_num : (606707828165955795995905885403892680063436908411995579213517:ℕ)^3+4075931005843319029687996465355712523077586706559282680422363^3=2502410809950365571285893904048340785665820151183761956284111^3+3738897931129102982013631576254351490068689545396569741376409^3))
  have he2 := hc (q*606707828165955795995905885403892680063436908411995579213517) (q*2502410809950365571285893904048340785665820151183761956284111) (q*7643009618266689271774321705942342629145424860648080869784257) (q*7730156005004406346761304853015901152216404550070389662946371) h0 h1 h4 h5
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (by simpa only [mul_pow, ←mul_add] using
      congrArg (fun n : ℕ => q^3*n) (by norm_num : (606707828165955795995905885403892680063436908411995579213517:ℕ)^3+7730156005004406346761304853015901152216404550070389662946371^3=2502410809950365571285893904048340785665820151183761956284111^3+7643009618266689271774321705942342629145424860648080869784257^3))
  have he3 := hc (q*3738897931129102982013631576254351490068689545396569741376409) (q*4075931005843319029687996465355712523077586706559282680422363) (q*7643009618266689271774321705942342629145424860648080869784257) (q*7730156005004406346761304853015901152216404550070389662946371) h2 h3 h4 h5
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (Nat.mul_lt_mul_of_pos_left (by norm_num) hq)
    (by simpa only [mul_pow, ←mul_add] using
      congrArg (fun n : ℕ => q^3*n) (by norm_num : (3738897931129102982013631576254351490068689545396569741376409:ℕ)^3+7730156005004406346761304853015901152216404550070389662946371^3=4075931005843319029687996465355712523077586706559282680422363^3+7643009618266689271774321705942342629145424860648080869784257^3))
  exact parity_triangle _ _ _ _ _ _ he1 he2 he3

#print axioms no_odd_coloring_exact_count
end Erdos1206.ExactFactorCountOddColorObstruction
