import FormalConjecturesUtil

/-! A squarefree, coprime-to-210 odd-parity obstruction. This does not
exclude ordinary proper colorings and does not settle the density conjecture. -/

namespace Erdos1206.SquarefreeRoughParityObstruction

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

private lemma prime_23 : Nat.Prime 23 := by
  norm_num

private lemma prime_31 : Nat.Prime 31 := by
  norm_num

private lemma prime_47 : Nat.Prime 47 := by
  norm_num

private lemma prime_61 : Nat.Prime 61 := by
  norm_num

private lemma prime_71 : Nat.Prime 71 := by
  norm_num

private lemma prime_73 : Nat.Prime 73 := by
  norm_num

private lemma prime_211 : Nat.Prime 211 := by
  norm_num

private lemma prime_317 : Nat.Prime 317 := by
  norm_num

private lemma prime_601 : Nat.Prime 601 := by
  norm_num

private lemma prime_683 : Nat.Prime 683 := by
  norm_num

private lemma prime_797 : Nat.Prime 797 := by
  norm_num

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

private lemma prime_1367 : Nat.Prime 1367 := by
  apply lucas_of_list 1367 (5 : ZMod 1367) [2, 683]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_683
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1381 : Nat.Prime 1381 := by
  apply lucas_of_list 1381 (2 : ZMod 1381) [2, 2, 3, 5, 23]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1607 : Nat.Prime 1607 := by
  apply lucas_of_list 1607 (5 : ZMod 1607) [2, 11, 73]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_73
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1951 : Nat.Prime 1951 := by
  apply lucas_of_list 1951 (3 : ZMod 1951) [2, 3, 5, 5, 13]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_13
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
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

private lemma prime_9829 : Nat.Prime 9829 := by
  apply lucas_of_list 9829 (10 : ZMod 9829) [2, 2, 3, 3, 3, 7, 13]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_13
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private lemma prime_38569 : Nat.Prime 38569 := by
  apply lucas_of_list 38569 (14 : ZMod 38569) [2, 2, 2, 3, 1607]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_1607
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_144983 : Nat.Prime 144983 := by
  apply lucas_of_list 144983 (5 : ZMod 144983) [2, 71, 1021]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_71
    · exact prime_1021
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_169483 : Nat.Prime 169483 := by
  apply lucas_of_list 169483 (3 : ZMod 169483) [2, 3, 47, 601]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_601
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_869899 : Nat.Prime 869899 := by
  apply lucas_of_list 869899 (2 : ZMod 869899) [2, 3, 144983]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_144983
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_1694831 : Nat.Prime 1694831 := by
  apply lucas_of_list 1694831 (26 : ZMod 1694831) [2, 5, 169483]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_169483
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_10168987 : Nat.Prime 10168987 := by
  apply lucas_of_list 10168987 (26 : ZMod 10168987) [2, 3, 1694831]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1694831
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_61013923 : Nat.Prime 61013923 := by
  apply lucas_of_list 61013923 (2 : ZMod 61013923) [2, 3, 10168987]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10168987
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_70638151 : Nat.Prime 70638151 := by
  apply lucas_of_list 70638151 (3 : ZMod 70638151) [2, 3, 5, 5, 11, 31, 1381]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_11
    · exact prime_31
    · exact prime_1381
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_9577347927583549 : Nat.Prime 9577347927583549 := by
  apply lucas_of_list 9577347927583549 (17 : ZMod 9577347927583549) [2, 2, 3, 7, 1367, 1367, 61013923]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_1367
    · exact prime_1367
    · exact prime_61013923
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma prime_68627966441445241 : Nat.Prime 68627966441445241 := by
  apply lucas_of_list 68627966441445241 (7 : ZMod 68627966441445241) [2, 2, 2, 3, 5, 211, 317, 9829, 869899]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_211
    · exact prime_317
    · exact prime_9829
    · exact prime_869899
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num only [Nat.reduceSub, Nat.reduceDiv]
    all_goals (reduce_mod_char; decide +kernel)

private lemma squarefree_54167872992585091 : Squarefree (54167872992585091 : ℕ) := by
  have he : (54167872992585091 : ℕ) = 61 * (797 * (70638151 * (15773))) := by norm_num
  rw [he]
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_61.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_797.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_70638151.squarefree, ?_⟩
  exact prime_15773.squarefree

private lemma squarefree_68627966441445241 : Squarefree (68627966441445241 : ℕ) := by
  exact prime_68627966441445241.squarefree

private lemma squarefree_100165748530699889 : Squarefree (100165748530699889 : ℕ) := by
  have he : (100165748530699889 : ℕ) = 61 * (797 * (70638151 * (29167))) := by norm_num
  rw [he]
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_61.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_797.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_70638151.squarefree, ?_⟩
  exact prime_29167.squarefree

private lemma squarefree_105350827203419039 : Squarefree (105350827203419039 : ℕ) := by
  have he : (105350827203419039 : ℕ) = 11 * (9577347927583549) := by norm_num
  rw [he]
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_11.squarefree, ?_⟩
  exact prime_9577347927583549.squarefree

private lemma squarefree_113902608479367889 : Squarefree (113902608479367889 : ℕ) := by
  have he : (113902608479367889 : ℕ) = 17 * (61 * (797 * (1951 * (70638151)))) := by norm_num
  rw [he]
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_17.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_61.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_797.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_1951.squarefree, ?_⟩
  exact prime_70638151.squarefree

private lemma squarefree_132454237840044023 : Squarefree (132454237840044023 : ℕ) := by
  have he : (132454237840044023 : ℕ) = 61 * (797 * (38569 * (70638151))) := by norm_num
  rw [he]
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_61.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_797.squarefree, ?_⟩
  refine (Nat.squarefree_mul (by norm_num [Nat.Coprime])).2 ⟨prime_38569.squarefree, ?_⟩
  exact prime_70638151.squarefree

def source : Set ℕ := {n | Squarefree n ∧ Nat.Coprime n 210}

lemma source_witnesses :
    54167872992585091 ∈ source ∧
    68627966441445241 ∈ source ∧
    100165748530699889 ∈ source ∧
    105350827203419039 ∈ source ∧
    113902608479367889 ∈ source ∧
    132454237840044023 ∈ source := by
  constructor
  · exact ⟨squarefree_54167872992585091, by norm_num [Nat.Coprime]⟩
  constructor
  · exact ⟨squarefree_68627966441445241, by norm_num [Nat.Coprime]⟩
  constructor
  · exact ⟨squarefree_100165748530699889, by norm_num [Nat.Coprime]⟩
  constructor
  · exact ⟨squarefree_105350827203419039, by norm_num [Nat.Coprime]⟩
  constructor
  · exact ⟨squarefree_113902608479367889, by norm_num [Nat.Coprime]⟩
  exact ⟨squarefree_132454237840044023, by norm_num [Nat.Coprime]⟩

lemma three_differences :
    (100165748530699889 : ℕ)^3-54167872992585091^3 = 846043579199798306600801513348186984803243047823798 ∧
    (105350827203419039 : ℕ)^3-68627966441445241^3 = 846043579199798306600801513348186984803243047823798 ∧
    (132454237840044023 : ℕ)^3-113902608479367889^3 = 846043579199798306600801513348186984803243047823798 := by
  norm_num

private lemma parity_triangle (a b c d e f : ZMod 2)
    (h₁ : a+b+c+d=1) (h₂ : b+d+e+f=1) (h₃ : a+c+e+f=1) : False := by
  have h : 2*(a+b+c+d+e+f)=(3 : ZMod 2) := by
    linear_combination h₁+h₂+h₃
  have htwo : (2 : ZMod 2)=0 := by decide
  rw [htwo, zero_mul] at h
  exact (by decide : (0 : ZMod 2) ≠ 3) h

/-- Removing the primes 5 and 7 in addition to 2 and 3 does not make the entire
squarefree cubic collision hypergraph odd-parity colorable. This is stronger
than merely finding a collision, but weaker than ruling out proper coloring. -/
theorem no_odd_parity_coloring :
    ¬ ∃ c : ℕ → ZMod 2, ∀ a b d e : ℕ,
      a ∈ source → b ∈ source → d ∈ source → e ∈ source →
      a < b → b < d → d < e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=1 := by
  rintro ⟨c,hc⟩
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := source_witnesses
  have he1 := hc 54167872992585091 68627966441445241 100165748530699889 105350827203419039 h₁ h₂ h₃ h₄
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he2 := hc 68627966441445241 105350827203419039 113902608479367889 132454237840044023 h₂ h₄ h₅ h₆
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he3 := hc 54167872992585091 100165748530699889 113902608479367889 132454237840044023 h₁ h₃ h₅ h₆
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact parity_triangle _ _ _ _ _ _ he1 he2 he3

#print axioms source_witnesses
#print axioms three_differences
#print axioms no_odd_parity_coloring

end Erdos1206.SquarefreeRoughParityObstruction
