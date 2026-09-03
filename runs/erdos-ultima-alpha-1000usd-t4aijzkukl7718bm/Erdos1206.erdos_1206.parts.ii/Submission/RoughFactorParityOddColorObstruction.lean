import FormalConjecturesUtil

/-!
A three-edge obstruction to odd edge-sum colorings on either factor-count
parity class of squarefree roots coprime to 210. This does not exclude ordinary
proper colorings and does not settle the positive-density cube-Sidon conjecture.
-/
namespace Erdos1206.RoughFactorParityOddColorObstruction

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

private lemma prime_29 : Nat.Prime 29 := by
  norm_num

private lemma prime_31 : Nat.Prime 31 := by
  norm_num

private lemma prime_41 : Nat.Prime 41 := by
  norm_num

private lemma prime_47 : Nat.Prime 47 := by
  norm_num

private lemma prime_53 : Nat.Prime 53 := by
  norm_num

private lemma prime_59 : Nat.Prime 59 := by
  norm_num

private lemma prime_71 : Nat.Prime 71 := by
  norm_num

private lemma prime_73 : Nat.Prime 73 := by
  norm_num

private lemma prime_89 : Nat.Prime 89 := by
  norm_num

private lemma prime_109 : Nat.Prime 109 := by
  norm_num

private lemma prime_113 : Nat.Prime 113 := by
  norm_num

private lemma prime_131 : Nat.Prime 131 := by
  norm_num

private lemma prime_199 : Nat.Prime 199 := by
  norm_num

private lemma prime_313 : Nat.Prime 313 := by
  norm_num

private lemma prime_367 : Nat.Prime 367 := by
  norm_num

private lemma prime_383 : Nat.Prime 383 := by
  norm_num

private lemma prime_461 : Nat.Prime 461 := by
  norm_num

private lemma prime_577 : Nat.Prime 577 := by
  norm_num

private lemma prime_631 : Nat.Prime 631 := by
  norm_num

private lemma prime_937 : Nat.Prime 937 := by
  norm_num

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

private lemma prime_3943 : Nat.Prime 3943 := by
  apply lucas_of_list 3943 (3 : ZMod 3943) [2, 3, 3, 3, 73]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_73
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_4861 : Nat.Prime 4861 := by
  apply lucas_of_list 4861 (11 : ZMod 4861) [2, 2, 3, 3, 3, 3, 3, 5]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private lemma prime_15773 : Nat.Prime 15773 := by
  apply lucas_of_list 15773 (2 : ZMod 15773) [2, 2, 3943]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3943
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
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

private lemma prime_29167 : Nat.Prime 29167 := by
  apply lucas_of_list 29167 (3 : ZMod 29167) [2, 3, 4861]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_4861
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
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
  {n | Squarefree n ∧ Nat.Coprime n 210 ∧ n.primeFactors.card % 2 = r}

private lemma witness_27985056751587216951076441196377553 : 27985056751587216951076441196377553 ∈ source 0 := by
  have he : (27985056751587216951076441196377553 : ℕ) = 13 * (6551 * (7927 * (29167 * (23956114783 * (59327798773))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_29167.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_59327798773.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_6551.primeFactors, prime_7927.primeFactors, prime_29167.primeFactors, prime_23956114783.primeFactors, prime_59327798773.primeFactors]
    decide +kernel

private lemma witness_15133825904028017038753684197567907 : 15133825904028017038753684197567907 ∈ source 0 := by
  have he : (15133825904028017038753684197567907 : ℕ) = 13 * (6551 * (7927 * (15773 * (23956114783 * (59327798773))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_15773.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_59327798773.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_6551.primeFactors, prime_7927.primeFactors, prime_15773.primeFactors, prime_23956114783.primeFactors, prime_59327798773.primeFactors]
    decide +kernel

private lemma witness_43246475144883114992132083423619021 : 43246475144883114992132083423619021 ∈ source 0 := by
  have he : (43246475144883114992132083423619021 : ℕ) = 13 * (7927 * (23956114783 * (17517903101921768537))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_17517903101921768537.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_7927.primeFactors, prime_23956114783.primeFactors, prime_17517903101921768537.primeFactors]
    decide +kernel

private lemma witness_39670484170615831748036120486729503 : 39670484170615831748036120486729503 ∈ source 0 := by
  have he : (39670484170615831748036120486729503 : ℕ) = 13 * (7927 * (23956114783 * (16069372021164472291))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_16069372021164472291.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_13.primeFactors, prime_7927.primeFactors, prime_23956114783.primeFactors, prime_16069372021164472291.primeFactors]
    decide +kernel

private lemma witness_82018561908244126742857501883038757 : 82018561908244126742857501883038757 ∈ source 0 := by
  have he : (82018561908244126742857501883038757 : ℕ) = 29 * (6551 * (59327798773 * (7276932019288047971))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_29.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    exact prime_7276932019288047971.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_29.primeFactors, prime_6551.primeFactors, prime_59327798773.primeFactors, prime_7276932019288047971.primeFactors]
    decide +kernel

private lemma witness_81093920631780889498415793873742519 : 81093920631780889498415793873742519 ∈ source 0 := by
  have he : (81093920631780889498415793873742519 : ℕ) = 6551 * (2547473 * (59327798773 * (81905463706861))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_2547473.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    exact prime_81905463706861.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_6551.primeFactors, prime_2547473.primeFactors, prime_59327798773.primeFactors, prime_81905463706861.primeFactors]
    decide +kernel

private lemma witness_166472084944308187426290526173246977 : 166472084944308187426290526173246977 ∈ source 1 := by
  have he : (166472084944308187426290526173246977 : ℕ) = 11 * (13 * (6551 * (7927 * (15773 * (23956114783 * (59327798773)))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_15773.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_59327798773.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_11.primeFactors, prime_13.primeFactors, prime_6551.primeFactors, prime_7927.primeFactors, prime_15773.primeFactors, prime_23956114783.primeFactors, prime_59327798773.primeFactors]
    decide +kernel

private lemma witness_307835624267459386461840853160153083 : 307835624267459386461840853160153083 ∈ source 1 := by
  have he : (307835624267459386461840853160153083 : ℕ) = 11 * (13 * (6551 * (7927 * (29167 * (23956114783 * (59327798773)))))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_29167.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_59327798773.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_11.primeFactors, prime_13.primeFactors, prime_6551.primeFactors, prime_7927.primeFactors, prime_29167.primeFactors, prime_23956114783.primeFactors, prime_59327798773.primeFactors]
    decide +kernel

private lemma witness_436375325876774149228397325354024533 : 436375325876774149228397325354024533 ∈ source 1 := by
  have he : (436375325876774149228397325354024533 : ℕ) = 11 * (13 * (7927 * (23956114783 * (16069372021164472291)))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_16069372021164472291.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_11.primeFactors, prime_13.primeFactors, prime_7927.primeFactors, prime_23956114783.primeFactors, prime_16069372021164472291.primeFactors]
    decide +kernel

private lemma witness_475711226593714264913452917659809231 : 475711226593714264913452917659809231 ∈ source 1 := by
  have he : (475711226593714264913452917659809231 : ℕ) = 11 * (13 * (7927 * (23956114783 * (17517903101921768537)))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_13.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_7927.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_23956114783.squarefree, ?_⟩
    exact prime_17517903101921768537.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_11.primeFactors, prime_13.primeFactors, prime_7927.primeFactors, prime_23956114783.primeFactors, prime_17517903101921768537.primeFactors]
    decide +kernel

private lemma witness_892033126949589784482573732611167709 : 892033126949589784482573732611167709 ∈ source 1 := by
  have he : (892033126949589784482573732611167709 : ℕ) = 11 * (6551 * (2547473 * (59327798773 * (81905463706861)))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_2547473.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    exact prime_81905463706861.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_11.primeFactors, prime_6551.primeFactors, prime_2547473.primeFactors, prime_59327798773.primeFactors, prime_81905463706861.primeFactors]
    decide +kernel

private lemma witness_902204180990685394171432520713426327 : 902204180990685394171432520713426327 ∈ source 1 := by
  have he : (902204180990685394171432520713426327 : ℕ) = 11 * (29 * (6551 * (59327798773 * (7276932019288047971)))) := by norm_num
  refine ⟨?_, by norm_num [Nat.Coprime], ?_⟩
  · rw [he]
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_29.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_6551.squarefree, ?_⟩
    refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_59327798773.squarefree, ?_⟩
    exact prime_7276932019288047971.squarefree
  · rw [he]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [prime_11.primeFactors, prime_29.primeFactors, prime_6551.primeFactors, prime_59327798773.primeFactors, prime_7276932019288047971.primeFactors]
    decide +kernel

private lemma parity_triangle (a b c d e f : ZMod 2)
    (h₁ : a+b+c+d=1) (h₂ : a+b+e+f=1) (h₃ : c+d+e+f=1) : False := by
  have h : 2*(a+b+c+d+e+f)=(3 : ZMod 2) := by
    linear_combination h₁+h₂+h₃
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul] at h
  exact (by decide : (0 : ZMod 2) ≠ 3) h

/-- Even after excluding 2, 3, 5, and 7 and fixing factor-count parity,
there is no Boolean coloring whose sum is odd on every strict cubic collision.
This condition is stronger than ordinary nonmonochromatic coloring. -/
theorem no_odd_parity_refinement (r : ℕ) (hr : r < 2) :
    ¬ ∃ c : ℕ → ZMod 2, ∀ a b d e : ℕ,
      a ∈ source r → b ∈ source r → d ∈ source r → e ∈ source r →
      a < b → b < d → d < e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=1 := by
  rintro ⟨c,hc⟩
  interval_cases r
  ·
    have he1 := hc 15133825904028017038753684197567907 27985056751587216951076441196377553 39670484170615831748036120486729503 43246475144883114992132083423619021
      witness_15133825904028017038753684197567907 witness_27985056751587216951076441196377553 witness_39670484170615831748036120486729503 witness_43246475144883114992132083423619021
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he2 := hc 15133825904028017038753684197567907 27985056751587216951076441196377553 81093920631780889498415793873742519 82018561908244126742857501883038757
      witness_15133825904028017038753684197567907 witness_27985056751587216951076441196377553 witness_81093920631780889498415793873742519 witness_82018561908244126742857501883038757
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he3 := hc 39670484170615831748036120486729503 43246475144883114992132083423619021 81093920631780889498415793873742519 82018561908244126742857501883038757
      witness_39670484170615831748036120486729503 witness_43246475144883114992132083423619021 witness_81093920631780889498415793873742519 witness_82018561908244126742857501883038757
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact parity_triangle _ _ _ _ _ _ he1 he2 he3
  ·
    have he1 := hc 166472084944308187426290526173246977 307835624267459386461840853160153083 436375325876774149228397325354024533 475711226593714264913452917659809231
      witness_166472084944308187426290526173246977 witness_307835624267459386461840853160153083 witness_436375325876774149228397325354024533 witness_475711226593714264913452917659809231
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he2 := hc 166472084944308187426290526173246977 307835624267459386461840853160153083 892033126949589784482573732611167709 902204180990685394171432520713426327
      witness_166472084944308187426290526173246977 witness_307835624267459386461840853160153083 witness_892033126949589784482573732611167709 witness_902204180990685394171432520713426327
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he3 := hc 436375325876774149228397325354024533 475711226593714264913452917659809231 892033126949589784482573732611167709 902204180990685394171432520713426327
      witness_436375325876774149228397325354024533 witness_475711226593714264913452917659809231 witness_892033126949589784482573732611167709 witness_902204180990685394171432520713426327
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact parity_triangle _ _ _ _ _ _ he1 he2 he3

#print axioms no_odd_parity_refinement
end Erdos1206.RoughFactorParityOddColorObstruction
