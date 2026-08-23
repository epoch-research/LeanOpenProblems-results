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

/- Pair for n = 26 -/
private lemma prime_26828203 : Nat.Prime 26828203 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_2826413 : Nat.Prime 2826413 := by norm_num
private lemma prime_1074036941_sub1 : (1074036941 - 1 : ℕ) = 2 ^ 2 * 5 * 19 * 2826413 := by norm_num
private lemma prime_1074036941_pow : (2 : ZMod 1074036941) ^ (1074036941 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1074036941_div_2 : (2 : ZMod 1074036941) ^ ((1074036941 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074036941_div_5 : (2 : ZMod 1074036941) ^ ((1074036941 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074036941_div_19 : (2 : ZMod 1074036941) ^ ((1074036941 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074036941_div_2826413 : (2 : ZMod 1074036941) ^ ((1074036941 - 1) / 2826413) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074036941 : Nat.Prime 1074036941 := by
  refine lucas_primality 1074036941 (2 : ZMod 1074036941) prime_1074036941_pow ?_
  intro q hq hqd
  rw [prime_1074036941_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 19, 2826413].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1074036941_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1074036941_div_5
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_1074036941_div_19
  · have : q = 2826413 := (Nat.prime_dvd_prime_iff_eq hq prime_2826413).mp hdf
    subst this; exact prime_1074036941_div_2826413
private lemma prime_2148073883_sub1 : (2148073883 - 1 : ℕ) = 2 * 1074036941 := by norm_num
private lemma prime_2148073883_pow : (2 : ZMod 2148073883) ^ (2148073883 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2148073883_div_2 : (2 : ZMod 2148073883) ^ ((2148073883 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2148073883_div_1074036941 : (2 : ZMod 2148073883) ^ ((2148073883 - 1) / 1074036941) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2148073883 : Nat.Prime 2148073883 := by
  refine lucas_primality 2148073883 (2 : ZMod 2148073883) prime_2148073883_pow ?_
  intro q hq hqd
  rw [prime_2148073883_sub1] at hqd
  have : q ∣ [2, 1074036941].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2148073883_div_2
  · have : q = 1074036941 := (Nat.prime_dvd_prime_iff_eq hq prime_1074036941).mp hdf
    subst this; exact prime_2148073883_div_1074036941
private lemma prime_4296147767_sub1 : (4296147767 - 1 : ℕ) = 2 * 2148073883 := by norm_num
private lemma prime_4296147767_pow : (5 : ZMod 4296147767) ^ (4296147767 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4296147767_div_2 : (5 : ZMod 4296147767) ^ ((4296147767 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4296147767_div_2148073883 : (5 : ZMod 4296147767) ^ ((4296147767 - 1) / 2148073883) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4296147767 : Nat.Prime 4296147767 := by
  refine lucas_primality 4296147767 (5 : ZMod 4296147767) prime_4296147767_pow ?_
  intro q hq hqd
  rw [prime_4296147767_sub1] at hqd
  have : q ∣ [2, 2148073883].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4296147767_div_2
  · have : q = 2148073883 := (Nat.prime_dvd_prime_iff_eq hq prime_2148073883).mp hdf
    subst this; exact prime_4296147767_div_2148073883
private lemma prime_3179149347581_sub1 : (3179149347581 - 1 : ℕ) = 2 ^ 2 * 5 * 37 * 4296147767 := by norm_num
private lemma prime_3179149347581_pow : (2 : ZMod 3179149347581) ^ (3179149347581 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3179149347581_div_2 : (2 : ZMod 3179149347581) ^ ((3179149347581 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3179149347581_div_5 : (2 : ZMod 3179149347581) ^ ((3179149347581 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3179149347581_div_37 : (2 : ZMod 3179149347581) ^ ((3179149347581 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3179149347581_div_4296147767 : (2 : ZMod 3179149347581) ^ ((3179149347581 - 1) / 4296147767) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3179149347581 : Nat.Prime 3179149347581 := by
  refine lucas_primality 3179149347581 (2 : ZMod 3179149347581) prime_3179149347581_pow ?_
  intro q hq hqd
  rw [prime_3179149347581_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 37, 4296147767].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3179149347581_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_3179149347581_div_5
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_3179149347581_div_37
  · have : q = 4296147767 := (Nat.prime_dvd_prime_iff_eq hq prime_4296147767).mp hdf
    subst this; exact prime_3179149347581_div_4296147767
private lemma prime_A_26_sub1 : (170581728128441253887 - 1 : ℕ) = 2 * 26828203 * 3179149347581 := by norm_num
private lemma prime_A_26_pow : (5 : ZMod 170581728128441253887) ^ (170581728128441253887 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_26_div_2 : (5 : ZMod 170581728128441253887) ^ ((170581728128441253887 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_26_div_26828203 : (5 : ZMod 170581728128441253887) ^ ((170581728128441253887 - 1) / 26828203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_26_div_3179149347581 : (5 : ZMod 170581728128441253887) ^ ((170581728128441253887 - 1) / 3179149347581) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_26 : Nat.Prime 170581728128441253887 := by
  refine lucas_primality 170581728128441253887 (5 : ZMod 170581728128441253887) prime_A_26_pow ?_
  intro q hq hqd
  rw [prime_A_26_sub1] at hqd
  have : q ∣ [2, 26828203, 3179149347581].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_26_div_2
  · have : q = 26828203 := (Nat.prime_dvd_prime_iff_eq hq prime_26828203).mp hdf
    subst this; exact prime_A_26_div_26828203
  · have : q = 3179149347581 := (Nat.prime_dvd_prime_iff_eq hq prime_3179149347581).mp hdf
    subst this; exact prime_A_26_div_3179149347581
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_2713 : Nat.Prime 2713 := by norm_num
private lemma prime_57241 : Nat.Prime 57241 := by norm_num
private lemma prime_2484717329_sub1 : (2484717329 - 1 : ℕ) = 2 ^ 4 * 2713 * 57241 := by norm_num
private lemma prime_2484717329_pow : (3 : ZMod 2484717329) ^ (2484717329 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2484717329_div_2 : (3 : ZMod 2484717329) ^ ((2484717329 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2484717329_div_2713 : (3 : ZMod 2484717329) ^ ((2484717329 - 1) / 2713) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2484717329_div_57241 : (3 : ZMod 2484717329) ^ ((2484717329 - 1) / 57241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2484717329 : Nat.Prime 2484717329 := by
  refine lucas_primality 2484717329 (3 : ZMod 2484717329) prime_2484717329_pow ?_
  intro q hq hqd
  rw [prime_2484717329_sub1] at hqd
  have : q ∣ [2 ^ 4, 2713, 57241].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2484717329_div_2
  · have : q = 2713 := (Nat.prime_dvd_prime_iff_eq hq prime_2713).mp hdf
    subst this; exact prime_2484717329_div_2713
  · have : q = 57241 := (Nat.prime_dvd_prime_iff_eq hq prime_57241).mp hdf
    subst this; exact prime_2484717329_div_57241
private lemma prime_B_26_sub1 : (170581728128441253889 - 1 : ℕ) = 2 ^ 26 * 3 * 11 * 31 * 2484717329 := by norm_num
private lemma prime_B_26_pow : (7 : ZMod 170581728128441253889) ^ (170581728128441253889 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_26_div_2 : (7 : ZMod 170581728128441253889) ^ ((170581728128441253889 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_26_div_3 : (7 : ZMod 170581728128441253889) ^ ((170581728128441253889 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_26_div_11 : (7 : ZMod 170581728128441253889) ^ ((170581728128441253889 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_26_div_31 : (7 : ZMod 170581728128441253889) ^ ((170581728128441253889 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_26_div_2484717329 : (7 : ZMod 170581728128441253889) ^ ((170581728128441253889 - 1) / 2484717329) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_26 : Nat.Prime 170581728128441253889 := by
  refine lucas_primality 170581728128441253889 (7 : ZMod 170581728128441253889) prime_B_26_pow ?_
  intro q hq hqd
  rw [prime_B_26_sub1] at hqd
  have : q ∣ [2 ^ 26, 3, 11, 31, 2484717329].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_26_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_26_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_26_div_11
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_B_26_div_31
  · have : q = 2484717329 := (Nat.prime_dvd_prime_iff_eq hq prime_2484717329).mp hdf
    subst this; exact prime_B_26_div_2484717329
private lemma pair_26 :
    Nat.Prime ((3 ^ 26 - 762) * (2 ^ 26) - 1) ∧
    Nat.Prime ((3 ^ 26 - 762) * (2 ^ 26) + 1) := by
  constructor
  · convert prime_A_26
  · convert prime_B_26

/- Pair for n = 27 -/
private lemma prime_733 : Nat.Prime 733 := by norm_num
private lemma prime_7121 : Nat.Prime 7121 := by norm_num
private lemma prime_131 : Nat.Prime 131 := by norm_num
private lemma prime_1319 : Nat.Prime 1319 := by norm_num
private lemma prime_1929947 : Nat.Prime 1929947 := by norm_num
private lemma prime_2000841673099_sub1 : (2000841673099 - 1 : ℕ) = 2 * 3 * 131 * 1319 * 1929947 := by norm_num
private lemma prime_2000841673099_pow : (2 : ZMod 2000841673099) ^ (2000841673099 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2000841673099_div_2 : (2 : ZMod 2000841673099) ^ ((2000841673099 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2000841673099_div_3 : (2 : ZMod 2000841673099) ^ ((2000841673099 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2000841673099_div_131 : (2 : ZMod 2000841673099) ^ ((2000841673099 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2000841673099_div_1319 : (2 : ZMod 2000841673099) ^ ((2000841673099 - 1) / 1319) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2000841673099_div_1929947 : (2 : ZMod 2000841673099) ^ ((2000841673099 - 1) / 1929947) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2000841673099 : Nat.Prime 2000841673099 := by
  refine lucas_primality 2000841673099 (2 : ZMod 2000841673099) prime_2000841673099_pow ?_
  intro q hq hqd
  rw [prime_2000841673099_sub1] at hqd
  have : q ∣ [2, 3, 131, 1319, 1929947].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2000841673099_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_2000841673099_div_3
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_2000841673099_div_131
  · have : q = 1319 := (Nat.prime_dvd_prime_iff_eq hq prime_1319).mp hdf
    subst this; exact prime_2000841673099_div_1319
  · have : q = 1929947 := (Nat.prime_dvd_prime_iff_eq hq prime_1929947).mp hdf
    subst this; exact prime_2000841673099_div_1929947
private lemma prime_A_27_sub1 : (1023490368967947583487 - 1 : ℕ) = 2 * 7 ^ 2 * 733 * 7121 * 2000841673099 := by norm_num
private lemma prime_A_27_pow : (5 : ZMod 1023490368967947583487) ^ (1023490368967947583487 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_27_div_2 : (5 : ZMod 1023490368967947583487) ^ ((1023490368967947583487 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_27_div_7 : (5 : ZMod 1023490368967947583487) ^ ((1023490368967947583487 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_27_div_733 : (5 : ZMod 1023490368967947583487) ^ ((1023490368967947583487 - 1) / 733) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_27_div_7121 : (5 : ZMod 1023490368967947583487) ^ ((1023490368967947583487 - 1) / 7121) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_27_div_2000841673099 : (5 : ZMod 1023490368967947583487) ^ ((1023490368967947583487 - 1) / 2000841673099) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_27 : Nat.Prime 1023490368967947583487 := by
  refine lucas_primality 1023490368967947583487 (5 : ZMod 1023490368967947583487) prime_A_27_pow ?_
  intro q hq hqd
  rw [prime_A_27_sub1] at hqd
  have : q ∣ [2, 7 ^ 2, 733, 7121, 2000841673099].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_27_div_2
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_A_27_div_7
  · have : q = 733 := (Nat.prime_dvd_prime_iff_eq hq prime_733).mp hdf
    subst this; exact prime_A_27_div_733
  · have : q = 7121 := (Nat.prime_dvd_prime_iff_eq hq prime_7121).mp hdf
    subst this; exact prime_A_27_div_7121
  · have : q = 2000841673099 := (Nat.prime_dvd_prime_iff_eq hq prime_2000841673099).mp hdf
    subst this; exact prime_A_27_div_2000841673099
private lemma prime_307 : Nat.Prime 307 := by norm_num
private lemma prime_5101 : Nat.Prime 5101 := by norm_num
private lemma prime_85429 : Nat.Prime 85429 := by norm_num
private lemma prime_B_27_sub1 : (1023490368967947583489 - 1 : ℕ) = 2 ^ 27 * 3 * 19 * 307 * 5101 * 85429 := by norm_num
private lemma prime_B_27_pow : (7 : ZMod 1023490368967947583489) ^ (1023490368967947583489 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_27_div_2 : (7 : ZMod 1023490368967947583489) ^ ((1023490368967947583489 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_27_div_3 : (7 : ZMod 1023490368967947583489) ^ ((1023490368967947583489 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_27_div_19 : (7 : ZMod 1023490368967947583489) ^ ((1023490368967947583489 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_27_div_307 : (7 : ZMod 1023490368967947583489) ^ ((1023490368967947583489 - 1) / 307) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_27_div_5101 : (7 : ZMod 1023490368967947583489) ^ ((1023490368967947583489 - 1) / 5101) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_27_div_85429 : (7 : ZMod 1023490368967947583489) ^ ((1023490368967947583489 - 1) / 85429) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_27 : Nat.Prime 1023490368967947583489 := by
  refine lucas_primality 1023490368967947583489 (7 : ZMod 1023490368967947583489) prime_B_27_pow ?_
  intro q hq hqd
  rw [prime_B_27_sub1] at hqd
  have : q ∣ [2 ^ 27, 3, 19, 307, 5101, 85429].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_27_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_27_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_27_div_19
  · have : q = 307 := (Nat.prime_dvd_prime_iff_eq hq prime_307).mp hdf
    subst this; exact prime_B_27_div_307
  · have : q = 5101 := (Nat.prime_dvd_prime_iff_eq hq prime_5101).mp hdf
    subst this; exact prime_B_27_div_5101
  · have : q = 85429 := (Nat.prime_dvd_prime_iff_eq hq prime_85429).mp hdf
    subst this; exact prime_B_27_div_85429
private lemma pair_27 :
    Nat.Prime ((3 ^ 27 - 816) * (2 ^ 27) - 1) ∧
    Nat.Prime ((3 ^ 27 - 816) * (2 ^ 27) + 1) := by
  constructor
  · convert prime_A_27
  · convert prime_B_27

/- Pair for n = 28 -/
private lemma prime_32341 : Nat.Prime 32341 := by norm_num
private lemma prime_3146161 : Nat.Prime 3146161 := by norm_num
private lemma prime_1753 : Nat.Prime 1753 := by norm_num
private lemma prime_111781 : Nat.Prime 111781 := by norm_num
private lemma prime_30176622323_sub1 : (30176622323 - 1 : ℕ) = 2 * 7 * 11 * 1753 * 111781 := by norm_num
private lemma prime_30176622323_pow : (5 : ZMod 30176622323) ^ (30176622323 - 1) = 1 := by
  reduce_mod_char
private lemma prime_30176622323_div_2 : (5 : ZMod 30176622323) ^ ((30176622323 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30176622323_div_7 : (5 : ZMod 30176622323) ^ ((30176622323 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30176622323_div_11 : (5 : ZMod 30176622323) ^ ((30176622323 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30176622323_div_1753 : (5 : ZMod 30176622323) ^ ((30176622323 - 1) / 1753) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30176622323_div_111781 : (5 : ZMod 30176622323) ^ ((30176622323 - 1) / 111781) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30176622323 : Nat.Prime 30176622323 := by
  refine lucas_primality 30176622323 (5 : ZMod 30176622323) prime_30176622323_pow ?_
  intro q hq hqd
  rw [prime_30176622323_sub1] at hqd
  have : q ∣ [2, 7, 11, 1753, 111781].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_30176622323_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_30176622323_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_30176622323_div_11
  · have : q = 1753 := (Nat.prime_dvd_prime_iff_eq hq prime_1753).mp hdf
    subst this; exact prime_30176622323_div_1753
  · have : q = 111781 := (Nat.prime_dvd_prime_iff_eq hq prime_111781).mp hdf
    subst this; exact prime_30176622323_div_111781
private lemma prime_A_28_sub1 : (6140942214282816258047 - 1 : ℕ) = 2 * 32341 * 3146161 * 30176622323 := by norm_num
private lemma prime_A_28_pow : (5 : ZMod 6140942214282816258047) ^ (6140942214282816258047 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_28_div_2 : (5 : ZMod 6140942214282816258047) ^ ((6140942214282816258047 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_28_div_32341 : (5 : ZMod 6140942214282816258047) ^ ((6140942214282816258047 - 1) / 32341) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_28_div_3146161 : (5 : ZMod 6140942214282816258047) ^ ((6140942214282816258047 - 1) / 3146161) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_28_div_30176622323 : (5 : ZMod 6140942214282816258047) ^ ((6140942214282816258047 - 1) / 30176622323) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_28 : Nat.Prime 6140942214282816258047 := by
  refine lucas_primality 6140942214282816258047 (5 : ZMod 6140942214282816258047) prime_A_28_pow ?_
  intro q hq hqd
  rw [prime_A_28_sub1] at hqd
  have : q ∣ [2, 32341, 3146161, 30176622323].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_28_div_2
  · have : q = 32341 := (Nat.prime_dvd_prime_iff_eq hq prime_32341).mp hdf
    subst this; exact prime_A_28_div_32341
  · have : q = 3146161 := (Nat.prime_dvd_prime_iff_eq hq prime_3146161).mp hdf
    subst this; exact prime_A_28_div_3146161
  · have : q = 30176622323 := (Nat.prime_dvd_prime_iff_eq hq prime_30176622323).mp hdf
    subst this; exact prime_A_28_div_30176622323
private lemma prime_885383 : Nat.Prime 885383 := by norm_num
private lemma prime_8612767 : Nat.Prime 8612767 := by norm_num
private lemma prime_B_28_sub1 : (6140942214282816258049 - 1 : ℕ) = 2 ^ 28 * 3 * 885383 * 8612767 := by norm_num
private lemma prime_B_28_pow : (17 : ZMod 6140942214282816258049) ^ (6140942214282816258049 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_28_div_2 : (17 : ZMod 6140942214282816258049) ^ ((6140942214282816258049 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_28_div_3 : (17 : ZMod 6140942214282816258049) ^ ((6140942214282816258049 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_28_div_885383 : (17 : ZMod 6140942214282816258049) ^ ((6140942214282816258049 - 1) / 885383) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_28_div_8612767 : (17 : ZMod 6140942214282816258049) ^ ((6140942214282816258049 - 1) / 8612767) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_28 : Nat.Prime 6140942214282816258049 := by
  refine lucas_primality 6140942214282816258049 (17 : ZMod 6140942214282816258049) prime_B_28_pow ?_
  intro q hq hqd
  rw [prime_B_28_sub1] at hqd
  have : q ∣ [2 ^ 28, 3, 885383, 8612767].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_28_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_28_div_3
  · have : q = 885383 := (Nat.prime_dvd_prime_iff_eq hq prime_885383).mp hdf
    subst this; exact prime_B_28_div_885383
  · have : q = 8612767 := (Nat.prime_dvd_prime_iff_eq hq prime_8612767).mp hdf
    subst this; exact prime_B_28_div_8612767
private lemma pair_28 :
    Nat.Prime ((3 ^ 28 - 678) * (2 ^ 28) - 1) ∧
    Nat.Prime ((3 ^ 28 - 678) * (2 ^ 28) + 1) := by
  constructor
  · convert prime_A_28
  · convert prime_B_28

/- Pair for n = 29 -/
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_43 : Nat.Prime 43 := by norm_num
private lemma prime_320833 : Nat.Prime 320833 := by norm_num
private lemma prime_165549829_sub1 : (165549829 - 1 : ℕ) = 2 ^ 2 * 3 * 43 * 320833 := by norm_num
private lemma prime_165549829_pow : (2 : ZMod 165549829) ^ (165549829 - 1) = 1 := by
  reduce_mod_char
private lemma prime_165549829_div_2 : (2 : ZMod 165549829) ^ ((165549829 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_165549829_div_3 : (2 : ZMod 165549829) ^ ((165549829 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_165549829_div_43 : (2 : ZMod 165549829) ^ ((165549829 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_165549829_div_320833 : (2 : ZMod 165549829) ^ ((165549829 - 1) / 320833) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_165549829 : Nat.Prime 165549829 := by
  refine lucas_primality 165549829 (2 : ZMod 165549829) prime_165549829_pow ?_
  intro q hq hqd
  rw [prime_165549829_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 43, 320833].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_165549829_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_165549829_div_3
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_165549829_div_43
  · have : q = 320833 := (Nat.prime_dvd_prime_iff_eq hq prime_320833).mp hdf
    subst this; exact prime_165549829_div_320833
private lemma prime_3319 : Nat.Prime 3319 := by norm_num
private lemma prime_39353257 : Nat.Prime 39353257 := by norm_num
private lemma prime_1567361519797_sub1 : (1567361519797 - 1 : ℕ) = 2 ^ 2 * 3 * 3319 * 39353257 := by norm_num
private lemma prime_1567361519797_pow : (2 : ZMod 1567361519797) ^ (1567361519797 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1567361519797_div_2 : (2 : ZMod 1567361519797) ^ ((1567361519797 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1567361519797_div_3 : (2 : ZMod 1567361519797) ^ ((1567361519797 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1567361519797_div_3319 : (2 : ZMod 1567361519797) ^ ((1567361519797 - 1) / 3319) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1567361519797_div_39353257 : (2 : ZMod 1567361519797) ^ ((1567361519797 - 1) / 39353257) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1567361519797 : Nat.Prime 1567361519797 := by
  refine lucas_primality 1567361519797 (2 : ZMod 1567361519797) prime_1567361519797_pow ?_
  intro q hq hqd
  rw [prime_1567361519797_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 3319, 39353257].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1567361519797_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1567361519797_div_3
  · have : q = 3319 := (Nat.prime_dvd_prime_iff_eq hq prime_3319).mp hdf
    subst this; exact prime_1567361519797_div_3319
  · have : q = 39353257 := (Nat.prime_dvd_prime_iff_eq hq prime_39353257).mp hdf
    subst this; exact prime_1567361519797_div_39353257
private lemma prime_A_29_sub1 : (36845653284867431989247 - 1 : ℕ) = 2 * 71 * 165549829 * 1567361519797 := by norm_num
private lemma prime_A_29_pow : (5 : ZMod 36845653284867431989247) ^ (36845653284867431989247 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_29_div_2 : (5 : ZMod 36845653284867431989247) ^ ((36845653284867431989247 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_29_div_71 : (5 : ZMod 36845653284867431989247) ^ ((36845653284867431989247 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_29_div_165549829 : (5 : ZMod 36845653284867431989247) ^ ((36845653284867431989247 - 1) / 165549829) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_29_div_1567361519797 : (5 : ZMod 36845653284867431989247) ^ ((36845653284867431989247 - 1) / 1567361519797) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_29 : Nat.Prime 36845653284867431989247 := by
  refine lucas_primality 36845653284867431989247 (5 : ZMod 36845653284867431989247) prime_A_29_pow ?_
  intro q hq hqd
  rw [prime_A_29_sub1] at hqd
  have : q ∣ [2, 71, 165549829, 1567361519797].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_29_div_2
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_A_29_div_71
  · have : q = 165549829 := (Nat.prime_dvd_prime_iff_eq hq prime_165549829).mp hdf
    subst this; exact prime_A_29_div_165549829
  · have : q = 1567361519797 := (Nat.prime_dvd_prime_iff_eq hq prime_1567361519797).mp hdf
    subst this; exact prime_A_29_div_1567361519797
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_1181 : Nat.Prime 1181 := by norm_num
private lemma prime_4261697551_sub1 : (4261697551 - 1 : ℕ) = 2 * 3 ^ 8 * 5 ^ 2 * 11 * 1181 := by norm_num
private lemma prime_4261697551_pow : (3 : ZMod 4261697551) ^ (4261697551 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4261697551_div_2 : (3 : ZMod 4261697551) ^ ((4261697551 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4261697551_div_3 : (3 : ZMod 4261697551) ^ ((4261697551 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4261697551_div_5 : (3 : ZMod 4261697551) ^ ((4261697551 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4261697551_div_11 : (3 : ZMod 4261697551) ^ ((4261697551 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4261697551_div_1181 : (3 : ZMod 4261697551) ^ ((4261697551 - 1) / 1181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4261697551 : Nat.Prime 4261697551 := by
  refine lucas_primality 4261697551 (3 : ZMod 4261697551) prime_4261697551_pow ?_
  intro q hq hqd
  rw [prime_4261697551_sub1] at hqd
  have : q ∣ [2, 3 ^ 8, 5 ^ 2, 11, 1181].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4261697551_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_4261697551_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_4261697551_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_4261697551_div_11
  · have : q = 1181 := (Nat.prime_dvd_prime_iff_eq hq prime_1181).mp hdf
    subst this; exact prime_4261697551_div_1181
private lemma prime_B_29_sub1 : (36845653284867431989249 - 1 : ℕ) = 2 ^ 32 * 3 * 11 * 61 * 4261697551 := by norm_num
private lemma prime_B_29_pow : (7 : ZMod 36845653284867431989249) ^ (36845653284867431989249 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_29_div_2 : (7 : ZMod 36845653284867431989249) ^ ((36845653284867431989249 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_29_div_3 : (7 : ZMod 36845653284867431989249) ^ ((36845653284867431989249 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_29_div_11 : (7 : ZMod 36845653284867431989249) ^ ((36845653284867431989249 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_29_div_61 : (7 : ZMod 36845653284867431989249) ^ ((36845653284867431989249 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_29_div_4261697551 : (7 : ZMod 36845653284867431989249) ^ ((36845653284867431989249 - 1) / 4261697551) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_29 : Nat.Prime 36845653284867431989249 := by
  refine lucas_primality 36845653284867431989249 (7 : ZMod 36845653284867431989249) prime_B_29_pow ?_
  intro q hq hqd
  rw [prime_B_29_sub1] at hqd
  have : q ∣ [2 ^ 32, 3, 11, 61, 4261697551].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_29_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_29_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_29_div_11
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_B_29_div_61
  · have : q = 4261697551 := (Nat.prime_dvd_prime_iff_eq hq prime_4261697551).mp hdf
    subst this; exact prime_B_29_div_4261697551
private lemma pair_29 :
    Nat.Prime ((3 ^ 29 - 3579) * (2 ^ 29) - 1) ∧
    Nat.Prime ((3 ^ 29 - 3579) * (2 ^ 29) + 1) := by
  constructor
  · convert prime_A_29
  · convert prime_B_29

/- Pair for n = 30 -/
private lemma prime_6469 : Nat.Prime 6469 := by norm_num
private lemma prime_19477 : Nat.Prime 19477 := by norm_num
private lemma prime_7001 : Nat.Prime 7001 := by norm_num
private lemma prime_7003729 : Nat.Prime 7003729 := by norm_num
private lemma prime_98066213459_sub1 : (98066213459 - 1 : ℕ) = 2 * 7001 * 7003729 := by norm_num
private lemma prime_98066213459_pow : (2 : ZMod 98066213459) ^ (98066213459 - 1) = 1 := by
  reduce_mod_char
private lemma prime_98066213459_div_2 : (2 : ZMod 98066213459) ^ ((98066213459 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_98066213459_div_7001 : (2 : ZMod 98066213459) ^ ((98066213459 - 1) / 7001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_98066213459_div_7003729 : (2 : ZMod 98066213459) ^ ((98066213459 - 1) / 7003729) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_98066213459 : Nat.Prime 98066213459 := by
  refine lucas_primality 98066213459 (2 : ZMod 98066213459) prime_98066213459_pow ?_
  intro q hq hqd
  rw [prime_98066213459_sub1] at hqd
  have : q ∣ [2, 7001, 7003729].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_98066213459_div_2
  · have : q = 7001 := (Nat.prime_dvd_prime_iff_eq hq prime_7001).mp hdf
    subst this; exact prime_98066213459_div_7001
  · have : q = 7003729 := (Nat.prime_dvd_prime_iff_eq hq prime_7003729).mp hdf
    subst this; exact prime_98066213459_div_7003729
private lemma prime_1765191842263_sub1 : (1765191842263 - 1 : ℕ) = 2 * 3 ^ 2 * 98066213459 := by norm_num
private lemma prime_1765191842263_pow : (3 : ZMod 1765191842263) ^ (1765191842263 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1765191842263_div_2 : (3 : ZMod 1765191842263) ^ ((1765191842263 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1765191842263_div_3 : (3 : ZMod 1765191842263) ^ ((1765191842263 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1765191842263_div_98066213459 : (3 : ZMod 1765191842263) ^ ((1765191842263 - 1) / 98066213459) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1765191842263 : Nat.Prime 1765191842263 := by
  refine lucas_primality 1765191842263 (3 : ZMod 1765191842263) prime_1765191842263_pow ?_
  intro q hq hqd
  rw [prime_1765191842263_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 98066213459].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1765191842263_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1765191842263_div_3
  · have : q = 98066213459 := (Nat.prime_dvd_prime_iff_eq hq prime_98066213459).mp hdf
    subst this; exact prime_1765191842263_div_98066213459
private lemma prime_A_30_sub1 : (221073919719915166629887 - 1 : ℕ) = 2 * 7 * 71 * 6469 * 19477 * 1765191842263 := by norm_num
private lemma prime_A_30_pow : (5 : ZMod 221073919719915166629887) ^ (221073919719915166629887 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_30_div_2 : (5 : ZMod 221073919719915166629887) ^ ((221073919719915166629887 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_30_div_7 : (5 : ZMod 221073919719915166629887) ^ ((221073919719915166629887 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_30_div_71 : (5 : ZMod 221073919719915166629887) ^ ((221073919719915166629887 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_30_div_6469 : (5 : ZMod 221073919719915166629887) ^ ((221073919719915166629887 - 1) / 6469) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_30_div_19477 : (5 : ZMod 221073919719915166629887) ^ ((221073919719915166629887 - 1) / 19477) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_30_div_1765191842263 : (5 : ZMod 221073919719915166629887) ^ ((221073919719915166629887 - 1) / 1765191842263) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_30 : Nat.Prime 221073919719915166629887 := by
  refine lucas_primality 221073919719915166629887 (5 : ZMod 221073919719915166629887) prime_A_30_pow ?_
  intro q hq hqd
  rw [prime_A_30_sub1] at hqd
  have : q ∣ [2, 7, 71, 6469, 19477, 1765191842263].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_30_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_30_div_7
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_A_30_div_71
  · have : q = 6469 := (Nat.prime_dvd_prime_iff_eq hq prime_6469).mp hdf
    subst this; exact prime_A_30_div_6469
  · have : q = 19477 := (Nat.prime_dvd_prime_iff_eq hq prime_19477).mp hdf
    subst this; exact prime_A_30_div_19477
  · have : q = 1765191842263 := (Nat.prime_dvd_prime_iff_eq hq prime_1765191842263).mp hdf
    subst this; exact prime_A_30_div_1765191842263
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_135899 : Nat.Prime 135899 := by norm_num
private lemma prime_1829747 : Nat.Prime 1829747 := by norm_num
private lemma prime_68630377364629_sub1 : (68630377364629 - 1 : ℕ) = 2 ^ 2 * 3 * 23 * 135899 * 1829747 := by norm_num
private lemma prime_68630377364629_pow : (2 : ZMod 68630377364629) ^ (68630377364629 - 1) = 1 := by
  reduce_mod_char
private lemma prime_68630377364629_div_2 : (2 : ZMod 68630377364629) ^ ((68630377364629 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_68630377364629_div_3 : (2 : ZMod 68630377364629) ^ ((68630377364629 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_68630377364629_div_23 : (2 : ZMod 68630377364629) ^ ((68630377364629 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_68630377364629_div_135899 : (2 : ZMod 68630377364629) ^ ((68630377364629 - 1) / 135899) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_68630377364629_div_1829747 : (2 : ZMod 68630377364629) ^ ((68630377364629 - 1) / 1829747) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_68630377364629 : Nat.Prime 68630377364629 := by
  refine lucas_primality 68630377364629 (2 : ZMod 68630377364629) prime_68630377364629_pow ?_
  intro q hq hqd
  rw [prime_68630377364629_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 23, 135899, 1829747].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_68630377364629_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_68630377364629_div_3
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_68630377364629_div_23
  · have : q = 135899 := (Nat.prime_dvd_prime_iff_eq hq prime_135899).mp hdf
    subst this; exact prime_68630377364629_div_135899
  · have : q = 1829747 := (Nat.prime_dvd_prime_iff_eq hq prime_1829747).mp hdf
    subst this; exact prime_68630377364629_div_1829747
private lemma prime_B_30_sub1 : (221073919719915166629889 - 1 : ℕ) = 2 ^ 30 * 3 * 68630377364629 := by norm_num
private lemma prime_B_30_pow : (13 : ZMod 221073919719915166629889) ^ (221073919719915166629889 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_30_div_2 : (13 : ZMod 221073919719915166629889) ^ ((221073919719915166629889 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_30_div_3 : (13 : ZMod 221073919719915166629889) ^ ((221073919719915166629889 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_30_div_68630377364629 : (13 : ZMod 221073919719915166629889) ^ ((221073919719915166629889 - 1) / 68630377364629) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_30 : Nat.Prime 221073919719915166629889 := by
  refine lucas_primality 221073919719915166629889 (13 : ZMod 221073919719915166629889) prime_B_30_pow ?_
  intro q hq hqd
  rw [prime_B_30_sub1] at hqd
  have : q ∣ [2 ^ 30, 3, 68630377364629].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_30_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_30_div_3
  · have : q = 68630377364629 := (Nat.prime_dvd_prime_iff_eq hq prime_68630377364629).mp hdf
    subst this; exact prime_B_30_div_68630377364629
private lemma pair_30 :
    Nat.Prime ((3 ^ 30 - 762) * (2 ^ 30) - 1) ∧
    Nat.Prime ((3 ^ 30 - 762) * (2 ^ 30) + 1) := by
  constructor
  · convert prime_A_30
  · convert prime_B_30

/- Pair for n = 31 -/
private lemma prime_571 : Nat.Prime 571 := by norm_num
private lemma prime_1193 : Nat.Prime 1193 := by norm_num
private lemma prime_642133 : Nat.Prime 642133 := by norm_num
private lemma prime_191 : Nat.Prime 191 := by norm_num
private lemma prime_306259 : Nat.Prime 306259 := by norm_num
private lemma prime_1403891257_sub1 : (1403891257 - 1 : ℕ) = 2 ^ 3 * 3 * 191 * 306259 := by norm_num
private lemma prime_1403891257_pow : (5 : ZMod 1403891257) ^ (1403891257 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1403891257_div_2 : (5 : ZMod 1403891257) ^ ((1403891257 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1403891257_div_3 : (5 : ZMod 1403891257) ^ ((1403891257 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1403891257_div_191 : (5 : ZMod 1403891257) ^ ((1403891257 - 1) / 191) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1403891257_div_306259 : (5 : ZMod 1403891257) ^ ((1403891257 - 1) / 306259) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1403891257 : Nat.Prime 1403891257 := by
  refine lucas_primality 1403891257 (5 : ZMod 1403891257) prime_1403891257_pow ?_
  intro q hq hqd
  rw [prime_1403891257_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 191, 306259].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1403891257_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1403891257_div_3
  · have : q = 191 := (Nat.prime_dvd_prime_iff_eq hq prime_191).mp hdf
    subst this; exact prime_1403891257_div_191
  · have : q = 306259 := (Nat.prime_dvd_prime_iff_eq hq prime_306259).mp hdf
    subst this; exact prime_1403891257_div_306259
private lemma prime_25270042627_sub1 : (25270042627 - 1 : ℕ) = 2 * 3 ^ 2 * 1403891257 := by norm_num
private lemma prime_25270042627_pow : (2 : ZMod 25270042627) ^ (25270042627 - 1) = 1 := by
  reduce_mod_char
private lemma prime_25270042627_div_2 : (2 : ZMod 25270042627) ^ ((25270042627 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_25270042627_div_3 : (2 : ZMod 25270042627) ^ ((25270042627 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_25270042627_div_1403891257 : (2 : ZMod 25270042627) ^ ((25270042627 - 1) / 1403891257) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_25270042627 : Nat.Prime 25270042627 := by
  refine lucas_primality 25270042627 (2 : ZMod 25270042627) prime_25270042627_pow ?_
  intro q hq hqd
  rw [prime_25270042627_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 1403891257].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_25270042627_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_25270042627_div_3
  · have : q = 1403891257 := (Nat.prime_dvd_prime_iff_eq hq prime_1403891257).mp hdf
    subst this; exact prime_25270042627_div_1403891257
private lemma prime_973603696932203461_sub1 : (973603696932203461 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 642133 * 25270042627 := by norm_num
private lemma prime_973603696932203461_pow : (2 : ZMod 973603696932203461) ^ (973603696932203461 - 1) = 1 := by
  reduce_mod_char
private lemma prime_973603696932203461_div_2 : (2 : ZMod 973603696932203461) ^ ((973603696932203461 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_973603696932203461_div_3 : (2 : ZMod 973603696932203461) ^ ((973603696932203461 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_973603696932203461_div_5 : (2 : ZMod 973603696932203461) ^ ((973603696932203461 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_973603696932203461_div_642133 : (2 : ZMod 973603696932203461) ^ ((973603696932203461 - 1) / 642133) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_973603696932203461_div_25270042627 : (2 : ZMod 973603696932203461) ^ ((973603696932203461 - 1) / 25270042627) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_973603696932203461 : Nat.Prime 973603696932203461 := by
  refine lucas_primality 973603696932203461 (2 : ZMod 973603696932203461) prime_973603696932203461_pow ?_
  intro q hq hqd
  rw [prime_973603696932203461_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 642133, 25270042627].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_973603696932203461_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_973603696932203461_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_973603696932203461_div_5
  · have : q = 642133 := (Nat.prime_dvd_prime_iff_eq hq prime_642133).mp hdf
    subst this; exact prime_973603696932203461_div_642133
  · have : q = 25270042627 := (Nat.prime_dvd_prime_iff_eq hq prime_25270042627).mp hdf
    subst this; exact prime_973603696932203461_div_25270042627
private lemma prime_A_31_sub1 : (1326443518322615588487167 - 1 : ℕ) = 2 * 571 * 1193 * 973603696932203461 := by norm_num
private lemma prime_A_31_pow : (5 : ZMod 1326443518322615588487167) ^ (1326443518322615588487167 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_31_div_2 : (5 : ZMod 1326443518322615588487167) ^ ((1326443518322615588487167 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_31_div_571 : (5 : ZMod 1326443518322615588487167) ^ ((1326443518322615588487167 - 1) / 571) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_31_div_1193 : (5 : ZMod 1326443518322615588487167) ^ ((1326443518322615588487167 - 1) / 1193) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_31_div_973603696932203461 : (5 : ZMod 1326443518322615588487167) ^ ((1326443518322615588487167 - 1) / 973603696932203461) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_31 : Nat.Prime 1326443518322615588487167 := by
  refine lucas_primality 1326443518322615588487167 (5 : ZMod 1326443518322615588487167) prime_A_31_pow ?_
  intro q hq hqd
  rw [prime_A_31_sub1] at hqd
  have : q ∣ [2, 571, 1193, 973603696932203461].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_31_div_2
  · have : q = 571 := (Nat.prime_dvd_prime_iff_eq hq prime_571).mp hdf
    subst this; exact prime_A_31_div_571
  · have : q = 1193 := (Nat.prime_dvd_prime_iff_eq hq prime_1193).mp hdf
    subst this; exact prime_A_31_div_1193
  · have : q = 973603696932203461 := (Nat.prime_dvd_prime_iff_eq hq prime_973603696932203461).mp hdf
    subst this; exact prime_A_31_div_973603696932203461
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_617 : Nat.Prime 617 := by norm_num
private lemma prime_72469 : Nat.Prime 72469 := by norm_num
private lemma prime_123140629243_sub1 : (123140629243 - 1 : ℕ) = 2 * 3 ^ 4 * 17 * 617 * 72469 := by norm_num
private lemma prime_123140629243_pow : (2 : ZMod 123140629243) ^ (123140629243 - 1) = 1 := by
  reduce_mod_char
private lemma prime_123140629243_div_2 : (2 : ZMod 123140629243) ^ ((123140629243 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123140629243_div_3 : (2 : ZMod 123140629243) ^ ((123140629243 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123140629243_div_17 : (2 : ZMod 123140629243) ^ ((123140629243 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123140629243_div_617 : (2 : ZMod 123140629243) ^ ((123140629243 - 1) / 617) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123140629243_div_72469 : (2 : ZMod 123140629243) ^ ((123140629243 - 1) / 72469) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123140629243 : Nat.Prime 123140629243 := by
  refine lucas_primality 123140629243 (2 : ZMod 123140629243) prime_123140629243_pow ?_
  intro q hq hqd
  rw [prime_123140629243_sub1] at hqd
  have : q ∣ [2, 3 ^ 4, 17, 617, 72469].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_123140629243_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_123140629243_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_123140629243_div_17
  · have : q = 617 := (Nat.prime_dvd_prime_iff_eq hq prime_617).mp hdf
    subst this; exact prime_123140629243_div_617
  · have : q = 72469 := (Nat.prime_dvd_prime_iff_eq hq prime_72469).mp hdf
    subst this; exact prime_123140629243_div_72469
private lemma prime_2709093843347_sub1 : (2709093843347 - 1 : ℕ) = 2 * 11 * 123140629243 := by norm_num
private lemma prime_2709093843347_pow : (2 : ZMod 2709093843347) ^ (2709093843347 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2709093843347_div_2 : (2 : ZMod 2709093843347) ^ ((2709093843347 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2709093843347_div_11 : (2 : ZMod 2709093843347) ^ ((2709093843347 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2709093843347_div_123140629243 : (2 : ZMod 2709093843347) ^ ((2709093843347 - 1) / 123140629243) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2709093843347 : Nat.Prime 2709093843347 := by
  refine lucas_primality 2709093843347 (2 : ZMod 2709093843347) prime_2709093843347_pow ?_
  intro q hq hqd
  rw [prime_2709093843347_sub1] at hqd
  have : q ∣ [2, 11, 123140629243].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2709093843347_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_2709093843347_div_11
  · have : q = 123140629243 := (Nat.prime_dvd_prime_iff_eq hq prime_123140629243).mp hdf
    subst this; exact prime_2709093843347_div_123140629243
private lemma prime_B_31_sub1 : (1326443518322615588487169 - 1 : ℕ) = 2 ^ 33 * 3 * 19 * 2709093843347 := by norm_num
private lemma prime_B_31_pow : (11 : ZMod 1326443518322615588487169) ^ (1326443518322615588487169 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_31_div_2 : (11 : ZMod 1326443518322615588487169) ^ ((1326443518322615588487169 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_31_div_3 : (11 : ZMod 1326443518322615588487169) ^ ((1326443518322615588487169 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_31_div_19 : (11 : ZMod 1326443518322615588487169) ^ ((1326443518322615588487169 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_31_div_2709093843347 : (11 : ZMod 1326443518322615588487169) ^ ((1326443518322615588487169 - 1) / 2709093843347) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_31 : Nat.Prime 1326443518322615588487169 := by
  refine lucas_primality 1326443518322615588487169 (11 : ZMod 1326443518322615588487169) prime_B_31_pow ?_
  intro q hq hqd
  rw [prime_B_31_sub1] at hqd
  have : q ∣ [2 ^ 33, 3, 19, 2709093843347].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_31_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_31_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_31_div_19
  · have : q = 2709093843347 := (Nat.prime_dvd_prime_iff_eq hq prime_2709093843347).mp hdf
    subst this; exact prime_B_31_div_2709093843347
private lemma pair_31 :
    Nat.Prime ((3 ^ 31 - 831) * (2 ^ 31) - 1) ∧
    Nat.Prime ((3 ^ 31 - 831) * (2 ^ 31) + 1) := by
  constructor
  · convert prime_A_31
  · convert prime_B_31

/- Pair for n = 32 -/
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_5689 : Nat.Prime 5689 := by norm_num
private lemma prime_81299 : Nat.Prime 81299 := by norm_num
private lemma prime_217379705171_sub1 : (217379705171 - 1 : ℕ) = 2 * 5 * 47 * 5689 * 81299 := by norm_num
private lemma prime_217379705171_pow : (2 : ZMod 217379705171) ^ (217379705171 - 1) = 1 := by
  reduce_mod_char
private lemma prime_217379705171_div_2 : (2 : ZMod 217379705171) ^ ((217379705171 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_217379705171_div_5 : (2 : ZMod 217379705171) ^ ((217379705171 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_217379705171_div_47 : (2 : ZMod 217379705171) ^ ((217379705171 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_217379705171_div_5689 : (2 : ZMod 217379705171) ^ ((217379705171 - 1) / 5689) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_217379705171_div_81299 : (2 : ZMod 217379705171) ^ ((217379705171 - 1) / 81299) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_217379705171 : Nat.Prime 217379705171 := by
  refine lucas_primality 217379705171 (2 : ZMod 217379705171) prime_217379705171_pow ?_
  intro q hq hqd
  rw [prime_217379705171_sub1] at hqd
  have : q ∣ [2, 5, 47, 5689, 81299].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_217379705171_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_217379705171_div_5
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_217379705171_div_47
  · have : q = 5689 := (Nat.prime_dvd_prime_iff_eq hq prime_5689).mp hdf
    subst this; exact prime_217379705171_div_5689
  · have : q = 81299 := (Nat.prime_dvd_prime_iff_eq hq prime_81299).mp hdf
    subst this; exact prime_217379705171_div_81299
private lemma prime_99737917 : Nat.Prime 99737917 := by norm_num
private lemma prime_481734139111_sub1 : (481734139111 - 1 : ℕ) = 2 * 3 * 5 * 7 * 23 * 99737917 := by norm_num
private lemma prime_481734139111_pow : (6 : ZMod 481734139111) ^ (481734139111 - 1) = 1 := by
  reduce_mod_char
private lemma prime_481734139111_div_2 : (6 : ZMod 481734139111) ^ ((481734139111 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_481734139111_div_3 : (6 : ZMod 481734139111) ^ ((481734139111 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_481734139111_div_5 : (6 : ZMod 481734139111) ^ ((481734139111 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_481734139111_div_7 : (6 : ZMod 481734139111) ^ ((481734139111 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_481734139111_div_23 : (6 : ZMod 481734139111) ^ ((481734139111 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_481734139111_div_99737917 : (6 : ZMod 481734139111) ^ ((481734139111 - 1) / 99737917) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_481734139111 : Nat.Prime 481734139111 := by
  refine lucas_primality 481734139111 (6 : ZMod 481734139111) prime_481734139111_pow ?_
  intro q hq hqd
  rw [prime_481734139111_sub1] at hqd
  have : q ∣ [2, 3, 5, 7, 23, 99737917].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_481734139111_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_481734139111_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_481734139111_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_481734139111_div_7
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_481734139111_div_23
  · have : q = 99737917 := (Nat.prime_dvd_prime_iff_eq hq prime_99737917).mp hdf
    subst this; exact prime_481734139111_div_99737917
private lemma prime_3979330554968677841633279_sub1 : (3979330554968677841633279 - 1 : ℕ) = 2 * 19 * 217379705171 * 481734139111 := by norm_num
private lemma prime_3979330554968677841633279_pow : (13 : ZMod 3979330554968677841633279) ^ (3979330554968677841633279 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3979330554968677841633279_div_2 : (13 : ZMod 3979330554968677841633279) ^ ((3979330554968677841633279 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3979330554968677841633279_div_19 : (13 : ZMod 3979330554968677841633279) ^ ((3979330554968677841633279 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3979330554968677841633279_div_217379705171 : (13 : ZMod 3979330554968677841633279) ^ ((3979330554968677841633279 - 1) / 217379705171) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3979330554968677841633279_div_481734139111 : (13 : ZMod 3979330554968677841633279) ^ ((3979330554968677841633279 - 1) / 481734139111) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3979330554968677841633279 : Nat.Prime 3979330554968677841633279 := by
  refine lucas_primality 3979330554968677841633279 (13 : ZMod 3979330554968677841633279) prime_3979330554968677841633279_pow ?_
  intro q hq hqd
  rw [prime_3979330554968677841633279_sub1] at hqd
  have : q ∣ [2, 19, 217379705171, 481734139111].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3979330554968677841633279_div_2
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_3979330554968677841633279_div_19
  · have : q = 217379705171 := (Nat.prime_dvd_prime_iff_eq hq prime_217379705171).mp hdf
    subst this; exact prime_3979330554968677841633279_div_217379705171
  · have : q = 481734139111 := (Nat.prime_dvd_prime_iff_eq hq prime_481734139111).mp hdf
    subst this; exact prime_3979330554968677841633279_div_481734139111
private lemma prime_A_32_sub1 : (7958661109937355683266559 - 1 : ℕ) = 2 * 3979330554968677841633279 := by norm_num
private lemma prime_A_32_pow : (7 : ZMod 7958661109937355683266559) ^ (7958661109937355683266559 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_32_div_2 : (7 : ZMod 7958661109937355683266559) ^ ((7958661109937355683266559 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_32_div_3979330554968677841633279 : (7 : ZMod 7958661109937355683266559) ^ ((7958661109937355683266559 - 1) / 3979330554968677841633279) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_32 : Nat.Prime 7958661109937355683266559 := by
  refine lucas_primality 7958661109937355683266559 (7 : ZMod 7958661109937355683266559) prime_A_32_pow ?_
  intro q hq hqd
  rw [prime_A_32_sub1] at hqd
  have : q ∣ [2, 3979330554968677841633279].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_32_div_2
  · have : q = 3979330554968677841633279 := (Nat.prime_dvd_prime_iff_eq hq prime_3979330554968677841633279).mp hdf
    subst this; exact prime_A_32_div_3979330554968677841633279
private lemma prime_397 : Nat.Prime 397 := by norm_num
private lemma prime_773 : Nat.Prime 773 := by norm_num
private lemma prime_1481 : Nat.Prime 1481 := by norm_num
private lemma prime_10067 : Nat.Prime 10067 := by norm_num
private lemma prime_B_32_sub1 : (7958661109937355683266561 - 1 : ℕ) = 2 ^ 32 * 3 ^ 4 * 5 * 397 * 773 * 1481 * 10067 := by norm_num
private lemma prime_B_32_pow : (7 : ZMod 7958661109937355683266561) ^ (7958661109937355683266561 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_32_div_2 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32_div_3 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32_div_5 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32_div_397 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 397) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32_div_773 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 773) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32_div_1481 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 1481) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32_div_10067 : (7 : ZMod 7958661109937355683266561) ^ ((7958661109937355683266561 - 1) / 10067) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_32 : Nat.Prime 7958661109937355683266561 := by
  refine lucas_primality 7958661109937355683266561 (7 : ZMod 7958661109937355683266561) prime_B_32_pow ?_
  intro q hq hqd
  rw [prime_B_32_sub1] at hqd
  have : q ∣ [2 ^ 32, 3 ^ 4, 5, 397, 773, 1481, 10067].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_32_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_32_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_32_div_5
  · have : q = 397 := (Nat.prime_dvd_prime_iff_eq hq prime_397).mp hdf
    subst this; exact prime_B_32_div_397
  · have : q = 773 := (Nat.prime_dvd_prime_iff_eq hq prime_773).mp hdf
    subst this; exact prime_B_32_div_773
  · have : q = 1481 := (Nat.prime_dvd_prime_iff_eq hq prime_1481).mp hdf
    subst this; exact prime_B_32_div_1481
  · have : q = 10067 := (Nat.prime_dvd_prime_iff_eq hq prime_10067).mp hdf
    subst this; exact prime_B_32_div_10067
private lemma pair_32 :
    Nat.Prime ((3 ^ 32 - 2106) * (2 ^ 32) - 1) ∧
    Nat.Prime ((3 ^ 32 - 2106) * (2 ^ 32) + 1) := by
  constructor
  · convert prime_A_32
  · convert prime_B_32

/- Pair for n = 33 -/
private lemma prime_7960223 : Nat.Prime 7960223 := by norm_num
private lemma prime_53668717 : Nat.Prime 53668717 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_85451 : Nat.Prime 85451 := by norm_num
private lemma prime_1299709711_sub1 : (1299709711 - 1 : ℕ) = 2 * 3 ^ 2 * 5 * 13 ^ 2 * 85451 := by norm_num
private lemma prime_1299709711_pow : (3 : ZMod 1299709711) ^ (1299709711 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1299709711_div_2 : (3 : ZMod 1299709711) ^ ((1299709711 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1299709711_div_3 : (3 : ZMod 1299709711) ^ ((1299709711 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1299709711_div_5 : (3 : ZMod 1299709711) ^ ((1299709711 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1299709711_div_13 : (3 : ZMod 1299709711) ^ ((1299709711 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1299709711_div_85451 : (3 : ZMod 1299709711) ^ ((1299709711 - 1) / 85451) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1299709711 : Nat.Prime 1299709711 := by
  refine lucas_primality 1299709711 (3 : ZMod 1299709711) prime_1299709711_pow ?_
  intro q hq hqd
  rw [prime_1299709711_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 5, 13 ^ 2, 85451].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1299709711_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1299709711_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1299709711_div_5
  · have : q = 13 := prime_eq_of_dvd_prime_pow hq prime_13 hdf
    subst this; exact prime_1299709711_div_13
  · have : q = 85451 := (Nat.prime_dvd_prime_iff_eq hq prime_85451).mp hdf
    subst this; exact prime_1299709711_div_85451
private lemma prime_A_33_sub1 : (47751966659637740555993087 - 1 : ℕ) = 2 * 43 * 7960223 * 53668717 * 1299709711 := by norm_num
private lemma prime_A_33_pow : (5 : ZMod 47751966659637740555993087) ^ (47751966659637740555993087 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_33_div_2 : (5 : ZMod 47751966659637740555993087) ^ ((47751966659637740555993087 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_33_div_43 : (5 : ZMod 47751966659637740555993087) ^ ((47751966659637740555993087 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_33_div_7960223 : (5 : ZMod 47751966659637740555993087) ^ ((47751966659637740555993087 - 1) / 7960223) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_33_div_53668717 : (5 : ZMod 47751966659637740555993087) ^ ((47751966659637740555993087 - 1) / 53668717) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_33_div_1299709711 : (5 : ZMod 47751966659637740555993087) ^ ((47751966659637740555993087 - 1) / 1299709711) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_33 : Nat.Prime 47751966659637740555993087 := by
  refine lucas_primality 47751966659637740555993087 (5 : ZMod 47751966659637740555993087) prime_A_33_pow ?_
  intro q hq hqd
  rw [prime_A_33_sub1] at hqd
  have : q ∣ [2, 43, 7960223, 53668717, 1299709711].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_33_div_2
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_A_33_div_43
  · have : q = 7960223 := (Nat.prime_dvd_prime_iff_eq hq prime_7960223).mp hdf
    subst this; exact prime_A_33_div_7960223
  · have : q = 53668717 := (Nat.prime_dvd_prime_iff_eq hq prime_53668717).mp hdf
    subst this; exact prime_A_33_div_53668717
  · have : q = 1299709711 := (Nat.prime_dvd_prime_iff_eq hq prime_1299709711).mp hdf
    subst this; exact prime_A_33_div_1299709711
private lemma prime_1113961 : Nat.Prime 1113961 := by norm_num
private lemma prime_3960599 : Nat.Prime 3960599 := by norm_num
private lemma prime_554483861_sub1 : (554483861 - 1 : ℕ) = 2 ^ 2 * 5 * 7 * 3960599 := by norm_num
private lemma prime_554483861_pow : (2 : ZMod 554483861) ^ (554483861 - 1) = 1 := by
  reduce_mod_char
private lemma prime_554483861_div_2 : (2 : ZMod 554483861) ^ ((554483861 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554483861_div_5 : (2 : ZMod 554483861) ^ ((554483861 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554483861_div_7 : (2 : ZMod 554483861) ^ ((554483861 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554483861_div_3960599 : (2 : ZMod 554483861) ^ ((554483861 - 1) / 3960599) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_554483861 : Nat.Prime 554483861 := by
  refine lucas_primality 554483861 (2 : ZMod 554483861) prime_554483861_pow ?_
  intro q hq hqd
  rw [prime_554483861_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 7, 3960599].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_554483861_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_554483861_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_554483861_div_7
  · have : q = 3960599 := (Nat.prime_dvd_prime_iff_eq hq prime_3960599).mp hdf
    subst this; exact prime_554483861_div_3960599
private lemma prime_B_33_sub1 : (47751966659637740555993089 - 1 : ℕ) = 2 ^ 33 * 3 ^ 2 * 1113961 * 554483861 := by norm_num
private lemma prime_B_33_pow : (7 : ZMod 47751966659637740555993089) ^ (47751966659637740555993089 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_33_div_2 : (7 : ZMod 47751966659637740555993089) ^ ((47751966659637740555993089 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_33_div_3 : (7 : ZMod 47751966659637740555993089) ^ ((47751966659637740555993089 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_33_div_1113961 : (7 : ZMod 47751966659637740555993089) ^ ((47751966659637740555993089 - 1) / 1113961) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_33_div_554483861 : (7 : ZMod 47751966659637740555993089) ^ ((47751966659637740555993089 - 1) / 554483861) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_33 : Nat.Prime 47751966659637740555993089 := by
  refine lucas_primality 47751966659637740555993089 (7 : ZMod 47751966659637740555993089) prime_B_33_pow ?_
  intro q hq hqd
  rw [prime_B_33_sub1] at hqd
  have : q ∣ [2 ^ 33, 3 ^ 2, 1113961, 554483861].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_33_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_33_div_3
  · have : q = 1113961 := (Nat.prime_dvd_prime_iff_eq hq prime_1113961).mp hdf
    subst this; exact prime_B_33_div_1113961
  · have : q = 554483861 := (Nat.prime_dvd_prime_iff_eq hq prime_554483861).mp hdf
    subst this; exact prime_B_33_div_554483861
private lemma pair_33 :
    Nat.Prime ((3 ^ 33 - 4734) * (2 ^ 33) - 1) ∧
    Nat.Prime ((3 ^ 33 - 4734) * (2 ^ 33) + 1) := by
  constructor
  · convert prime_A_33
  · convert prime_B_33

/- Pair for n = 34 -/
private lemma prime_42863 : Nat.Prime 42863 := by norm_num
private lemma prime_60127 : Nat.Prime 60127 := by norm_num
private lemma prime_75289 : Nat.Prime 75289 := by norm_num
private lemma prime_29077 : Nat.Prime 29077 := by norm_num
private lemma prime_230827 : Nat.Prime 230827 := by norm_num
private lemma prime_147658646939_sub1 : (147658646939 - 1 : ℕ) = 2 * 11 * 29077 * 230827 := by norm_num
private lemma prime_147658646939_pow : (2 : ZMod 147658646939) ^ (147658646939 - 1) = 1 := by
  reduce_mod_char
private lemma prime_147658646939_div_2 : (2 : ZMod 147658646939) ^ ((147658646939 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147658646939_div_11 : (2 : ZMod 147658646939) ^ ((147658646939 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147658646939_div_29077 : (2 : ZMod 147658646939) ^ ((147658646939 - 1) / 29077) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147658646939_div_230827 : (2 : ZMod 147658646939) ^ ((147658646939 - 1) / 230827) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147658646939 : Nat.Prime 147658646939 := by
  refine lucas_primality 147658646939 (2 : ZMod 147658646939) prime_147658646939_pow ?_
  intro q hq hqd
  rw [prime_147658646939_sub1] at hqd
  have : q ∣ [2, 11, 29077, 230827].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_147658646939_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_147658646939_div_11
  · have : q = 29077 := (Nat.prime_dvd_prime_iff_eq hq prime_29077).mp hdf
    subst this; exact prime_147658646939_div_29077
  · have : q = 230827 := (Nat.prime_dvd_prime_iff_eq hq prime_230827).mp hdf
    subst this; exact prime_147658646939_div_230827
private lemma prime_A_34_sub1 : (286511799958060536233459711 - 1 : ℕ) = 2 * 5 * 42863 * 60127 * 75289 * 147658646939 := by norm_num
private lemma prime_A_34_pow : (13 : ZMod 286511799958060536233459711) ^ (286511799958060536233459711 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_34_div_2 : (13 : ZMod 286511799958060536233459711) ^ ((286511799958060536233459711 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_34_div_5 : (13 : ZMod 286511799958060536233459711) ^ ((286511799958060536233459711 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_34_div_42863 : (13 : ZMod 286511799958060536233459711) ^ ((286511799958060536233459711 - 1) / 42863) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_34_div_60127 : (13 : ZMod 286511799958060536233459711) ^ ((286511799958060536233459711 - 1) / 60127) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_34_div_75289 : (13 : ZMod 286511799958060536233459711) ^ ((286511799958060536233459711 - 1) / 75289) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_34_div_147658646939 : (13 : ZMod 286511799958060536233459711) ^ ((286511799958060536233459711 - 1) / 147658646939) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_34 : Nat.Prime 286511799958060536233459711 := by
  refine lucas_primality 286511799958060536233459711 (13 : ZMod 286511799958060536233459711) prime_A_34_pow ?_
  intro q hq hqd
  rw [prime_A_34_sub1] at hqd
  have : q ∣ [2, 5, 42863, 60127, 75289, 147658646939].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_34_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_34_div_5
  · have : q = 42863 := (Nat.prime_dvd_prime_iff_eq hq prime_42863).mp hdf
    subst this; exact prime_A_34_div_42863
  · have : q = 60127 := (Nat.prime_dvd_prime_iff_eq hq prime_60127).mp hdf
    subst this; exact prime_A_34_div_60127
  · have : q = 75289 := (Nat.prime_dvd_prime_iff_eq hq prime_75289).mp hdf
    subst this; exact prime_A_34_div_75289
  · have : q = 147658646939 := (Nat.prime_dvd_prime_iff_eq hq prime_147658646939).mp hdf
    subst this; exact prime_A_34_div_147658646939
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_257 : Nat.Prime 257 := by norm_num
private lemma prime_15227 : Nat.Prime 15227 := by norm_num
private lemma prime_589681 : Nat.Prime 589681 := by norm_num
private lemma prime_B_34_sub1 : (286511799958060536233459713 - 1 : ℕ) = 2 ^ 34 * 3 ^ 2 * 11 * 73 * 257 * 15227 * 589681 := by norm_num
private lemma prime_B_34_pow : (10 : ZMod 286511799958060536233459713) ^ (286511799958060536233459713 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_34_div_2 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34_div_3 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34_div_11 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34_div_73 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34_div_257 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 257) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34_div_15227 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 15227) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34_div_589681 : (10 : ZMod 286511799958060536233459713) ^ ((286511799958060536233459713 - 1) / 589681) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_34 : Nat.Prime 286511799958060536233459713 := by
  refine lucas_primality 286511799958060536233459713 (10 : ZMod 286511799958060536233459713) prime_B_34_pow ?_
  intro q hq hqd
  rw [prime_B_34_sub1] at hqd
  have : q ∣ [2 ^ 34, 3 ^ 2, 11, 73, 257, 15227, 589681].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_34_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_34_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_34_div_11
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_B_34_div_73
  · have : q = 257 := (Nat.prime_dvd_prime_iff_eq hq prime_257).mp hdf
    subst this; exact prime_B_34_div_257
  · have : q = 15227 := (Nat.prime_dvd_prime_iff_eq hq prime_15227).mp hdf
    subst this; exact prime_B_34_div_15227
  · have : q = 589681 := (Nat.prime_dvd_prime_iff_eq hq prime_589681).mp hdf
    subst this; exact prime_B_34_div_589681
private lemma pair_34 :
    Nat.Prime ((3 ^ 34 - 576) * (2 ^ 34) - 1) ∧
    Nat.Prime ((3 ^ 34 - 576) * (2 ^ 34) + 1) := by
  constructor
  · convert prime_A_34
  · convert prime_B_34

/- Pair for n = 35 -/
private lemma prime_40531 : Nat.Prime 40531 := by norm_num
private lemma prime_134639 : Nat.Prime 134639 := by norm_num
private lemma prime_1099487 : Nat.Prime 1099487 := by norm_num
private lemma prime_52093409 : Nat.Prime 52093409 := by norm_num
private lemma prime_2604670451_sub1 : (2604670451 - 1 : ℕ) = 2 * 5 ^ 2 * 52093409 := by norm_num
private lemma prime_2604670451_pow : (2 : ZMod 2604670451) ^ (2604670451 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2604670451_div_2 : (2 : ZMod 2604670451) ^ ((2604670451 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2604670451_div_5 : (2 : ZMod 2604670451) ^ ((2604670451 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2604670451_div_52093409 : (2 : ZMod 2604670451) ^ ((2604670451 - 1) / 52093409) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2604670451 : Nat.Prime 2604670451 := by
  refine lucas_primality 2604670451 (2 : ZMod 2604670451) prime_2604670451_pow ?_
  intro q hq hqd
  rw [prime_2604670451_sub1] at hqd
  have : q ∣ [2, 5 ^ 2, 52093409].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2604670451_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_2604670451_div_5
  · have : q = 52093409 := (Nat.prime_dvd_prime_iff_eq hq prime_52093409).mp hdf
    subst this; exact prime_2604670451_div_52093409
private lemma prime_A_35_sub1 : (1719070799748411149235781631 - 1 : ℕ) = 2 * 5 * 11 * 40531 * 134639 * 1099487 * 2604670451 := by norm_num
private lemma prime_A_35_pow : (11 : ZMod 1719070799748411149235781631) ^ (1719070799748411149235781631 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_35_div_2 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35_div_5 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35_div_11 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35_div_40531 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 40531) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35_div_134639 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 134639) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35_div_1099487 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 1099487) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35_div_2604670451 : (11 : ZMod 1719070799748411149235781631) ^ ((1719070799748411149235781631 - 1) / 2604670451) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_35 : Nat.Prime 1719070799748411149235781631 := by
  refine lucas_primality 1719070799748411149235781631 (11 : ZMod 1719070799748411149235781631) prime_A_35_pow ?_
  intro q hq hqd
  rw [prime_A_35_sub1] at hqd
  have : q ∣ [2, 5, 11, 40531, 134639, 1099487, 2604670451].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_35_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_35_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_35_div_11
  · have : q = 40531 := (Nat.prime_dvd_prime_iff_eq hq prime_40531).mp hdf
    subst this; exact prime_A_35_div_40531
  · have : q = 134639 := (Nat.prime_dvd_prime_iff_eq hq prime_134639).mp hdf
    subst this; exact prime_A_35_div_134639
  · have : q = 1099487 := (Nat.prime_dvd_prime_iff_eq hq prime_1099487).mp hdf
    subst this; exact prime_A_35_div_1099487
  · have : q = 2604670451 := (Nat.prime_dvd_prime_iff_eq hq prime_2604670451).mp hdf
    subst this; exact prime_A_35_div_2604670451
private lemma prime_5333 : Nat.Prime 5333 := by norm_num
private lemma prime_277 : Nat.Prime 277 := by norm_num
private lemma prime_40189 : Nat.Prime 40189 := by norm_num
private lemma prime_30658500163_sub1 : (30658500163 - 1 : ℕ) = 2 * 3 ^ 4 * 17 * 277 * 40189 := by norm_num
private lemma prime_30658500163_pow : (2 : ZMod 30658500163) ^ (30658500163 - 1) = 1 := by
  reduce_mod_char
private lemma prime_30658500163_div_2 : (2 : ZMod 30658500163) ^ ((30658500163 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30658500163_div_3 : (2 : ZMod 30658500163) ^ ((30658500163 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30658500163_div_17 : (2 : ZMod 30658500163) ^ ((30658500163 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30658500163_div_277 : (2 : ZMod 30658500163) ^ ((30658500163 - 1) / 277) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30658500163_div_40189 : (2 : ZMod 30658500163) ^ ((30658500163 - 1) / 40189) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30658500163 : Nat.Prime 30658500163 := by
  refine lucas_primality 30658500163 (2 : ZMod 30658500163) prime_30658500163_pow ?_
  intro q hq hqd
  rw [prime_30658500163_sub1] at hqd
  have : q ∣ [2, 3 ^ 4, 17, 277, 40189].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_30658500163_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_30658500163_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_30658500163_div_17
  · have : q = 277 := (Nat.prime_dvd_prime_iff_eq hq prime_277).mp hdf
    subst this; exact prime_30658500163_div_277
  · have : q = 40189 := (Nat.prime_dvd_prime_iff_eq hq prime_40189).mp hdf
    subst this; exact prime_30658500163_div_40189
private lemma prime_B_35_sub1 : (1719070799748411149235781633 - 1 : ℕ) = 2 ^ 36 * 3 ^ 2 * 17 * 5333 * 30658500163 := by norm_num
private lemma prime_B_35_pow : (5 : ZMod 1719070799748411149235781633) ^ (1719070799748411149235781633 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_35_div_2 : (5 : ZMod 1719070799748411149235781633) ^ ((1719070799748411149235781633 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_35_div_3 : (5 : ZMod 1719070799748411149235781633) ^ ((1719070799748411149235781633 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_35_div_17 : (5 : ZMod 1719070799748411149235781633) ^ ((1719070799748411149235781633 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_35_div_5333 : (5 : ZMod 1719070799748411149235781633) ^ ((1719070799748411149235781633 - 1) / 5333) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_35_div_30658500163 : (5 : ZMod 1719070799748411149235781633) ^ ((1719070799748411149235781633 - 1) / 30658500163) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_35 : Nat.Prime 1719070799748411149235781633 := by
  refine lucas_primality 1719070799748411149235781633 (5 : ZMod 1719070799748411149235781633) prime_B_35_pow ?_
  intro q hq hqd
  rw [prime_B_35_sub1] at hqd
  have : q ∣ [2 ^ 36, 3 ^ 2, 17, 5333, 30658500163].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_35_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_35_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_B_35_div_17
  · have : q = 5333 := (Nat.prime_dvd_prime_iff_eq hq prime_5333).mp hdf
    subst this; exact prime_B_35_div_5333
  · have : q = 30658500163 := (Nat.prime_dvd_prime_iff_eq hq prime_30658500163).mp hdf
    subst this; exact prime_B_35_div_30658500163
private lemma pair_35 :
    Nat.Prime ((3 ^ 35 - 333) * (2 ^ 35) - 1) ∧
    Nat.Prime ((3 ^ 35 - 333) * (2 ^ 35) + 1) := by
  constructor
  · convert prime_A_35
  · convert prime_B_35
