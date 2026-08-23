import FormalConjectures.Util.ProblemImports
open Nat
private lemma prime_dvd_list_prod {q : ℕ} (hq : q.Prime) :
    ∀ (ps : List ℕ), q ∣ ps.prod → ∃ p ∈ ps, q ∣ p
  | [], h => by
    simp at h
    exact (hq.ne_one h).elim
  | p :: ps, h => by
    rw [List.prod_cons] at h
    rcases hq.dvd_mul.mp h with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨p', hp', hq'⟩ := prime_dvd_list_prod hq ps h
      exact ⟨p', List.mem_cons_of_mem _ hp', hq'⟩
private lemma prime_eq_of_dvd_prime_pow {q p : ℕ} {e : ℕ} (hq : q.Prime) (hp : p.Prime)
    (h : q ∣ p ^ e) : q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)
private lemma prime_101063 : Nat.Prime 101063 := by norm_num
private lemma prime_21652427 : Nat.Prime 21652427 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_1583 : Nat.Prime 1583 := by norm_num
private lemma prime_8669 : Nat.Prime 8669 := by norm_num
private lemma prime_27830298757_sub1 : (27830298757 - 1 : ℕ) = 2 ^ 2 * 3 * 13 ^ 2 * 1583 * 8669 := by norm_num
private lemma prime_27830298757_pow : (5 : ZMod 27830298757) ^ (27830298757 - 1) = 1 := by
  reduce_mod_char
private lemma prime_27830298757_div_2 : (5 : ZMod 27830298757) ^ ((27830298757 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27830298757_div_3 : (5 : ZMod 27830298757) ^ ((27830298757 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27830298757_div_13 : (5 : ZMod 27830298757) ^ ((27830298757 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27830298757_div_1583 : (5 : ZMod 27830298757) ^ ((27830298757 - 1) / 1583) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27830298757_div_8669 : (5 : ZMod 27830298757) ^ ((27830298757 - 1) / 8669) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27830298757 : Nat.Prime 27830298757 := by
  refine lucas_primality 27830298757 (5 : ZMod 27830298757) prime_27830298757_pow ?_
  intro q hq hqd
  rw [prime_27830298757_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 13 ^ 2, 1583, 8669].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_27830298757_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_27830298757_div_3
  · have : q = 13 := prime_eq_of_dvd_prime_pow hq prime_13 hdf
    subst this; exact prime_27830298757_div_13
  · have : q = 1583 := (Nat.prime_dvd_prime_iff_eq hq prime_1583).mp hdf
    subst this; exact prime_27830298757_div_1583
  · have : q = 8669 := (Nat.prime_dvd_prime_iff_eq hq prime_8669).mp hdf
    subst this; exact prime_27830298757_div_8669
private lemma prime_7477 : Nat.Prime 7477 := by norm_num
private lemma prime_1237 : Nat.Prime 1237 := by norm_num
private lemma prime_57527 : Nat.Prime 57527 := by norm_num
private lemma prime_1423217981_sub1 : (1423217981 - 1 : ℕ) = 2 ^ 2 * 5 * 1237 * 57527 := by norm_num
private lemma prime_1423217981_pow : (2 : ZMod 1423217981) ^ (1423217981 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1423217981_div_2 : (2 : ZMod 1423217981) ^ ((1423217981 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1423217981_div_5 : (2 : ZMod 1423217981) ^ ((1423217981 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1423217981_div_1237 : (2 : ZMod 1423217981) ^ ((1423217981 - 1) / 1237) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1423217981_div_57527 : (2 : ZMod 1423217981) ^ ((1423217981 - 1) / 57527) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1423217981 : Nat.Prime 1423217981 := by
  refine lucas_primality 1423217981 (2 : ZMod 1423217981) prime_1423217981_pow ?_
  intro q hq hqd
  rw [prime_1423217981_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 1237, 57527].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1423217981_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1423217981_div_5
  · have : q = 1237 := (Nat.prime_dvd_prime_iff_eq hq prime_1237).mp hdf
    subst this; exact prime_1423217981_div_1237
  · have : q = 57527 := (Nat.prime_dvd_prime_iff_eq hq prime_57527).mp hdf
    subst this; exact prime_1423217981_div_57527
private lemma prime_148979611815119_sub1 : (148979611815119 - 1 : ℕ) = 2 * 7 * 7477 * 1423217981 := by norm_num
private lemma prime_148979611815119_pow : (7 : ZMod 148979611815119) ^ (148979611815119 - 1) = 1 := by
  reduce_mod_char
private lemma prime_148979611815119_div_2 : (7 : ZMod 148979611815119) ^ ((148979611815119 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_148979611815119_div_7 : (7 : ZMod 148979611815119) ^ ((148979611815119 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_148979611815119_div_7477 : (7 : ZMod 148979611815119) ^ ((148979611815119 - 1) / 7477) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_148979611815119_div_1423217981 : (7 : ZMod 148979611815119) ^ ((148979611815119 - 1) / 1423217981) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_148979611815119 : Nat.Prime 148979611815119 := by
  refine lucas_primality 148979611815119 (7 : ZMod 148979611815119) prime_148979611815119_pow ?_
  intro q hq hqd
  rw [prime_148979611815119_sub1] at hqd
  have : q ∣ [2, 7, 7477, 1423217981].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_148979611815119_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_148979611815119_div_7
  · have : q = 7477 := (Nat.prime_dvd_prime_iff_eq hq prime_7477).mp hdf
    subst this; exact prime_148979611815119_div_7477
  · have : q = 1423217981 := (Nat.prime_dvd_prime_iff_eq hq prime_1423217981).mp hdf
    subst this; exact prime_148979611815119_div_1423217981
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_631 : Nat.Prime 631 := by norm_num
private lemma prime_84956561 : Nat.Prime 84956561 := by norm_num
private lemma prime_169913123_sub1 : (169913123 - 1 : ℕ) = 2 * 84956561 := by norm_num
private lemma prime_169913123_pow : (2 : ZMod 169913123) ^ (169913123 - 1) = 1 := by
  reduce_mod_char
private lemma prime_169913123_div_2 : (2 : ZMod 169913123) ^ ((169913123 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_169913123_div_84956561 : (2 : ZMod 169913123) ^ ((169913123 - 1) / 84956561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_169913123 : Nat.Prime 169913123 := by
  refine lucas_primality 169913123 (2 : ZMod 169913123) prime_169913123_pow ?_
  intro q hq hqd
  rw [prime_169913123_sub1] at hqd
  have : q ∣ [2, 84956561].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_169913123_div_2
  · have : q = 84956561 := (Nat.prime_dvd_prime_iff_eq hq prime_84956561).mp hdf
    subst this; exact prime_169913123_div_84956561
private lemma prime_30584362141_sub1 : (30584362141 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 * 169913123 := by norm_num
private lemma prime_30584362141_pow : (6 : ZMod 30584362141) ^ (30584362141 - 1) = 1 := by
  reduce_mod_char
private lemma prime_30584362141_div_2 : (6 : ZMod 30584362141) ^ ((30584362141 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30584362141_div_3 : (6 : ZMod 30584362141) ^ ((30584362141 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30584362141_div_5 : (6 : ZMod 30584362141) ^ ((30584362141 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30584362141_div_169913123 : (6 : ZMod 30584362141) ^ ((30584362141 - 1) / 169913123) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30584362141 : Nat.Prime 30584362141 := by
  refine lucas_primality 30584362141 (6 : ZMod 30584362141) prime_30584362141_pow ?_
  intro q hq hqd
  rw [prime_30584362141_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 5, 169913123].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_30584362141_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_30584362141_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_30584362141_div_5
  · have : q = 169913123 := (Nat.prime_dvd_prime_iff_eq hq prime_169913123).mp hdf
    subst this; exact prime_30584362141_div_169913123
private lemma prime_3303111111229_sub1 : (3303111111229 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 30584362141 := by norm_num
private lemma prime_3303111111229_pow : (6 : ZMod 3303111111229) ^ (3303111111229 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3303111111229_div_2 : (6 : ZMod 3303111111229) ^ ((3303111111229 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3303111111229_div_3 : (6 : ZMod 3303111111229) ^ ((3303111111229 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3303111111229_div_30584362141 : (6 : ZMod 3303111111229) ^ ((3303111111229 - 1) / 30584362141) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3303111111229 : Nat.Prime 3303111111229 := by
  refine lucas_primality 3303111111229 (6 : ZMod 3303111111229) prime_3303111111229_pow ?_
  intro q hq hqd
  rw [prime_3303111111229_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 30584362141].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3303111111229_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_3303111111229_div_3
  · have : q = 30584362141 := (Nat.prime_dvd_prime_iff_eq hq prime_30584362141).mp hdf
    subst this; exact prime_3303111111229_div_30584362141
private lemma prime_108548422830540787921_sub1 : (108548422830540787921 - 1 : ℕ) = 2 ^ 4 * 3 * 5 * 7 * 31 * 631 * 3303111111229 := by norm_num
private lemma prime_108548422830540787921_pow : (11 : ZMod 108548422830540787921) ^ (108548422830540787921 - 1) = 1 := by
  reduce_mod_char
private lemma prime_108548422830540787921_div_2 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921_div_3 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921_div_5 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921_div_7 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921_div_31 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921_div_631 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 631) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921_div_3303111111229 : (11 : ZMod 108548422830540787921) ^ ((108548422830540787921 - 1) / 3303111111229) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_108548422830540787921 : Nat.Prime 108548422830540787921 := by
  refine lucas_primality 108548422830540787921 (11 : ZMod 108548422830540787921) prime_108548422830540787921_pow ?_
  intro q hq hqd
  rw [prime_108548422830540787921_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 5, 7, 31, 631, 3303111111229].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_108548422830540787921_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_108548422830540787921_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_108548422830540787921_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_108548422830540787921_div_7
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_108548422830540787921_div_31
  · have : q = 631 := (Nat.prime_dvd_prime_iff_eq hq prime_631).mp hdf
    subst this; exact prime_108548422830540787921_div_631
  · have : q = 3303111111229 := (Nat.prime_dvd_prime_iff_eq hq prime_3303111111229).mp hdf
    subst this; exact prime_108548422830540787921_div_3303111111229
private lemma prime_194058022757248408479739862884531189_sub1 : (194058022757248408479739862884531189 - 1 : ℕ) = 2 ^ 2 * 3 * 148979611815119 * 108548422830540787921 := by norm_num
private lemma prime_194058022757248408479739862884531189_pow : (7 : ZMod 194058022757248408479739862884531189) ^ (194058022757248408479739862884531189 - 1) = 1 := by
  reduce_mod_char
private lemma prime_194058022757248408479739862884531189_div_2 : (7 : ZMod 194058022757248408479739862884531189) ^ ((194058022757248408479739862884531189 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_194058022757248408479739862884531189_div_3 : (7 : ZMod 194058022757248408479739862884531189) ^ ((194058022757248408479739862884531189 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_194058022757248408479739862884531189_div_148979611815119 : (7 : ZMod 194058022757248408479739862884531189) ^ ((194058022757248408479739862884531189 - 1) / 148979611815119) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_194058022757248408479739862884531189_div_108548422830540787921 : (7 : ZMod 194058022757248408479739862884531189) ^ ((194058022757248408479739862884531189 - 1) / 108548422830540787921) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_194058022757248408479739862884531189 : Nat.Prime 194058022757248408479739862884531189 := by
  refine lucas_primality 194058022757248408479739862884531189 (7 : ZMod 194058022757248408479739862884531189) prime_194058022757248408479739862884531189_pow ?_
  intro q hq hqd
  rw [prime_194058022757248408479739862884531189_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 148979611815119, 108548422830540787921].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_194058022757248408479739862884531189_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_194058022757248408479739862884531189_div_3
  · have : q = 148979611815119 := (Nat.prime_dvd_prime_iff_eq hq prime_148979611815119).mp hdf
    subst this; exact prime_194058022757248408479739862884531189_div_148979611815119
  · have : q = 108548422830540787921 := (Nat.prime_dvd_prime_iff_eq hq prime_108548422830540787921).mp hdf
    subst this; exact prime_194058022757248408479739862884531189_div_108548422830540787921
private lemma prime_A_77_sub1 : (827268102990819696904779987451100004682319981429101651034111 - 1 : ℕ) = 2 * 5 * 7 * 101063 * 21652427 * 27830298757 * 194058022757248408479739862884531189 := by norm_num
private lemma prime_A_77_pow : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ (827268102990819696904779987451100004682319981429101651034111 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_77_div_2 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77_div_5 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77_div_7 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77_div_101063 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 101063) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77_div_21652427 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 21652427) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77_div_27830298757 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 27830298757) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77_div_194058022757248408479739862884531189 : (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) ^ ((827268102990819696904779987451100004682319981429101651034111 - 1) / 194058022757248408479739862884531189) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_77 : Nat.Prime 827268102990819696904779987451100004682319981429101651034111 := by
  refine lucas_primality 827268102990819696904779987451100004682319981429101651034111 (17 : ZMod 827268102990819696904779987451100004682319981429101651034111) prime_A_77_pow ?_
  intro q hq hqd
  rw [prime_A_77_sub1] at hqd
  have : q ∣ [2, 5, 7, 101063, 21652427, 27830298757, 194058022757248408479739862884531189].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_77_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_77_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_77_div_7
  · have : q = 101063 := (Nat.prime_dvd_prime_iff_eq hq prime_101063).mp hdf
    subst this; exact prime_A_77_div_101063
  · have : q = 21652427 := (Nat.prime_dvd_prime_iff_eq hq prime_21652427).mp hdf
    subst this; exact prime_A_77_div_21652427
  · have : q = 27830298757 := (Nat.prime_dvd_prime_iff_eq hq prime_27830298757).mp hdf
    subst this; exact prime_A_77_div_27830298757
  · have : q = 194058022757248408479739862884531189 := (Nat.prime_dvd_prime_iff_eq hq prime_194058022757248408479739862884531189).mp hdf
    subst this; exact prime_A_77_div_194058022757248408479739862884531189
private lemma prime_9521 : Nat.Prime 9521 := by norm_num
private lemma prime_773 : Nat.Prime 773 := by norm_num
private lemma prime_211 : Nat.Prime 211 := by norm_num
private lemma prime_445433 : Nat.Prime 445433 := by norm_num
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_3121 : Nat.Prime 3121 := by norm_num
private lemma prime_5779 : Nat.Prime 5779 := by norm_num
private lemma prime_396797699_sub1 : (396797699 - 1 : ℕ) = 2 * 11 * 3121 * 5779 := by norm_num
private lemma prime_396797699_pow : (2 : ZMod 396797699) ^ (396797699 - 1) = 1 := by
  reduce_mod_char
private lemma prime_396797699_div_2 : (2 : ZMod 396797699) ^ ((396797699 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_396797699_div_11 : (2 : ZMod 396797699) ^ ((396797699 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_396797699_div_3121 : (2 : ZMod 396797699) ^ ((396797699 - 1) / 3121) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_396797699_div_5779 : (2 : ZMod 396797699) ^ ((396797699 - 1) / 5779) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_396797699 : Nat.Prime 396797699 := by
  refine lucas_primality 396797699 (2 : ZMod 396797699) prime_396797699_pow ?_
  intro q hq hqd
  rw [prime_396797699_sub1] at hqd
  have : q ∣ [2, 11, 3121, 5779].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_396797699_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_396797699_div_11
  · have : q = 3121 := (Nat.prime_dvd_prime_iff_eq hq prime_3121).mp hdf
    subst this; exact prime_396797699_div_3121
  · have : q = 5779 := (Nat.prime_dvd_prime_iff_eq hq prime_5779).mp hdf
    subst this; exact prime_396797699_div_5779
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_271 : Nat.Prime 271 := by norm_num
private lemma prime_2393927 : Nat.Prime 2393927 := by norm_num
private lemma prime_554036101319_sub1 : (554036101319 - 1 : ℕ) = 2 * 7 * 61 * 271 * 2393927 := by norm_num
private lemma prime_554036101319_pow : (7 : ZMod 554036101319) ^ (554036101319 - 1) = 1 := by
  reduce_mod_char
private lemma prime_554036101319_div_2 : (7 : ZMod 554036101319) ^ ((554036101319 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554036101319_div_7 : (7 : ZMod 554036101319) ^ ((554036101319 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554036101319_div_61 : (7 : ZMod 554036101319) ^ ((554036101319 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554036101319_div_271 : (7 : ZMod 554036101319) ^ ((554036101319 - 1) / 271) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554036101319_div_2393927 : (7 : ZMod 554036101319) ^ ((554036101319 - 1) / 2393927) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554036101319 : Nat.Prime 554036101319 := by
  refine lucas_primality 554036101319 (7 : ZMod 554036101319) prime_554036101319_pow ?_
  intro q hq hqd
  rw [prime_554036101319_sub1] at hqd
  have : q ∣ [2, 7, 61, 271, 2393927].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_554036101319_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_554036101319_div_7
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_554036101319_div_61
  · have : q = 271 := (Nat.prime_dvd_prime_iff_eq hq prime_271).mp hdf
    subst this; exact prime_554036101319_div_271
  · have : q = 2393927 := (Nat.prime_dvd_prime_iff_eq hq prime_2393927).mp hdf
    subst this; exact prime_554036101319_div_2393927
private lemma prime_41323971108283256275715708207_sub1 : (41323971108283256275715708207 - 1 : ℕ) = 2 * 211 * 445433 * 396797699 * 554036101319 := by norm_num
private lemma prime_41323971108283256275715708207_pow : (5 : ZMod 41323971108283256275715708207) ^ (41323971108283256275715708207 - 1) = 1 := by
  reduce_mod_char
private lemma prime_41323971108283256275715708207_div_2 : (5 : ZMod 41323971108283256275715708207) ^ ((41323971108283256275715708207 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41323971108283256275715708207_div_211 : (5 : ZMod 41323971108283256275715708207) ^ ((41323971108283256275715708207 - 1) / 211) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41323971108283256275715708207_div_445433 : (5 : ZMod 41323971108283256275715708207) ^ ((41323971108283256275715708207 - 1) / 445433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41323971108283256275715708207_div_396797699 : (5 : ZMod 41323971108283256275715708207) ^ ((41323971108283256275715708207 - 1) / 396797699) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41323971108283256275715708207_div_554036101319 : (5 : ZMod 41323971108283256275715708207) ^ ((41323971108283256275715708207 - 1) / 554036101319) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41323971108283256275715708207 : Nat.Prime 41323971108283256275715708207 := by
  refine lucas_primality 41323971108283256275715708207 (5 : ZMod 41323971108283256275715708207) prime_41323971108283256275715708207_pow ?_
  intro q hq hqd
  rw [prime_41323971108283256275715708207_sub1] at hqd
  have : q ∣ [2, 211, 445433, 396797699, 554036101319].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_41323971108283256275715708207_div_2
  · have : q = 211 := (Nat.prime_dvd_prime_iff_eq hq prime_211).mp hdf
    subst this; exact prime_41323971108283256275715708207_div_211
  · have : q = 445433 := (Nat.prime_dvd_prime_iff_eq hq prime_445433).mp hdf
    subst this; exact prime_41323971108283256275715708207_div_445433
  · have : q = 396797699 := (Nat.prime_dvd_prime_iff_eq hq prime_396797699).mp hdf
    subst this; exact prime_41323971108283256275715708207_div_396797699
  · have : q = 554036101319 := (Nat.prime_dvd_prime_iff_eq hq prime_554036101319).mp hdf
    subst this; exact prime_41323971108283256275715708207_div_554036101319
private lemma prime_191660578000217742606769454664067_sub1 : (191660578000217742606769454664067 - 1 : ℕ) = 2 * 3 * 773 * 41323971108283256275715708207 := by norm_num
private lemma prime_191660578000217742606769454664067_pow : (2 : ZMod 191660578000217742606769454664067) ^ (191660578000217742606769454664067 - 1) = 1 := by
  reduce_mod_char
private lemma prime_191660578000217742606769454664067_div_2 : (2 : ZMod 191660578000217742606769454664067) ^ ((191660578000217742606769454664067 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_191660578000217742606769454664067_div_3 : (2 : ZMod 191660578000217742606769454664067) ^ ((191660578000217742606769454664067 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_191660578000217742606769454664067_div_773 : (2 : ZMod 191660578000217742606769454664067) ^ ((191660578000217742606769454664067 - 1) / 773) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_191660578000217742606769454664067_div_41323971108283256275715708207 : (2 : ZMod 191660578000217742606769454664067) ^ ((191660578000217742606769454664067 - 1) / 41323971108283256275715708207) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_191660578000217742606769454664067 : Nat.Prime 191660578000217742606769454664067 := by
  refine lucas_primality 191660578000217742606769454664067 (2 : ZMod 191660578000217742606769454664067) prime_191660578000217742606769454664067_pow ?_
  intro q hq hqd
  rw [prime_191660578000217742606769454664067_sub1] at hqd
  have : q ∣ [2, 3, 773, 41323971108283256275715708207].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_191660578000217742606769454664067_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_191660578000217742606769454664067_div_3
  · have : q = 773 := (Nat.prime_dvd_prime_iff_eq hq prime_773).mp hdf
    subst this; exact prime_191660578000217742606769454664067_div_773
  · have : q = 41323971108283256275715708207 := (Nat.prime_dvd_prime_iff_eq hq prime_41323971108283256275715708207).mp hdf
    subst this; exact prime_191660578000217742606769454664067_div_41323971108283256275715708207
private lemma prime_B_77_sub1 : (827268102990819696904779987451100004682319981429101651034113 - 1 : ℕ) = 2 ^ 77 * 3 * 9521 * 191660578000217742606769454664067 := by norm_num
private lemma prime_B_77_pow : (5 : ZMod 827268102990819696904779987451100004682319981429101651034113) ^ (827268102990819696904779987451100004682319981429101651034113 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_77_div_2 : (5 : ZMod 827268102990819696904779987451100004682319981429101651034113) ^ ((827268102990819696904779987451100004682319981429101651034113 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_77_div_3 : (5 : ZMod 827268102990819696904779987451100004682319981429101651034113) ^ ((827268102990819696904779987451100004682319981429101651034113 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_77_div_9521 : (5 : ZMod 827268102990819696904779987451100004682319981429101651034113) ^ ((827268102990819696904779987451100004682319981429101651034113 - 1) / 9521) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_77_div_191660578000217742606769454664067 : (5 : ZMod 827268102990819696904779987451100004682319981429101651034113) ^ ((827268102990819696904779987451100004682319981429101651034113 - 1) / 191660578000217742606769454664067) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_77 : Nat.Prime 827268102990819696904779987451100004682319981429101651034113 := by
  refine lucas_primality 827268102990819696904779987451100004682319981429101651034113 (5 : ZMod 827268102990819696904779987451100004682319981429101651034113) prime_B_77_pow ?_
  intro q hq hqd
  rw [prime_B_77_sub1] at hqd
  have : q ∣ [2 ^ 77, 3, 9521, 191660578000217742606769454664067].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_77_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_77_div_3
  · have : q = 9521 := (Nat.prime_dvd_prime_iff_eq hq prime_9521).mp hdf
    subst this; exact prime_B_77_div_9521
  · have : q = 191660578000217742606769454664067 := (Nat.prime_dvd_prime_iff_eq hq prime_191660578000217742606769454664067).mp hdf
    subst this; exact prime_B_77_div_191660578000217742606769454664067
private lemma pair_77 :
    Nat.Prime ((3 ^ 77 - 6042) * (2 ^ 77) - 1) ∧
    Nat.Prime ((3 ^ 77 - 6042) * (2 ^ 77) + 1) := by
  constructor
  · convert prime_A_77
  · convert prime_B_77
