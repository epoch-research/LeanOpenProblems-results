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

/- Pair for n = 46 -/
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_351031 : Nat.Prime 351031 := by norm_num
private lemma prime_353 : Nat.Prime 353 := by norm_num
private lemma prime_409 : Nat.Prime 409 := by norm_num
private lemma prime_918067 : Nat.Prime 918067 := by norm_num
private lemma prime_22529364181_sub1 : (22529364181 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 409 * 918067 := by norm_num
private lemma prime_22529364181_pow : (6 : ZMod 22529364181) ^ (22529364181 - 1) = 1 := by
  reduce_mod_char
private lemma prime_22529364181_div_2 : (6 : ZMod 22529364181) ^ ((22529364181 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22529364181_div_3 : (6 : ZMod 22529364181) ^ ((22529364181 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22529364181_div_5 : (6 : ZMod 22529364181) ^ ((22529364181 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22529364181_div_409 : (6 : ZMod 22529364181) ^ ((22529364181 - 1) / 409) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22529364181_div_918067 : (6 : ZMod 22529364181) ^ ((22529364181 - 1) / 918067) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22529364181 : Nat.Prime 22529364181 := by
  refine lucas_primality 22529364181 (6 : ZMod 22529364181) prime_22529364181_pow ?_
  intro q hq hqd
  rw [prime_22529364181_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 409, 918067].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_22529364181_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_22529364181_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_22529364181_div_5
  · have : q = 409 := (Nat.prime_dvd_prime_iff_eq hq prime_409).mp hdf
    subst this; exact prime_22529364181_div_409
  · have : q = 918067 := (Nat.prime_dvd_prime_iff_eq hq prime_918067).mp hdf
    subst this; exact prime_22529364181_div_918067
private lemma prime_47717193335359_sub1 : (47717193335359 - 1 : ℕ) = 2 * 3 * 353 * 22529364181 := by norm_num
private lemma prime_47717193335359_pow : (6 : ZMod 47717193335359) ^ (47717193335359 - 1) = 1 := by
  reduce_mod_char
private lemma prime_47717193335359_div_2 : (6 : ZMod 47717193335359) ^ ((47717193335359 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_47717193335359_div_3 : (6 : ZMod 47717193335359) ^ ((47717193335359 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_47717193335359_div_353 : (6 : ZMod 47717193335359) ^ ((47717193335359 - 1) / 353) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_47717193335359_div_22529364181 : (6 : ZMod 47717193335359) ^ ((47717193335359 - 1) / 22529364181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_47717193335359 : Nat.Prime 47717193335359 := by
  refine lucas_primality 47717193335359 (6 : ZMod 47717193335359) prime_47717193335359_pow ?_
  intro q hq hqd
  rw [prime_47717193335359_sub1] at hqd
  have : q ∣ [2, 3, 353, 22529364181].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_47717193335359_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_47717193335359_div_3
  · have : q = 353 := (Nat.prime_dvd_prime_iff_eq hq prime_353).mp hdf
    subst this; exact prime_47717193335359_div_353
  · have : q = 22529364181 := (Nat.prime_dvd_prime_iff_eq hq prime_22529364181).mp hdf
    subst this; exact prime_47717193335359_div_22529364181
private lemma prime_103 : Nat.Prime 103 := by norm_num
private lemma prime_113 : Nat.Prime 113 := by norm_num
private lemma prime_521 : Nat.Prime 521 := by norm_num
private lemma prime_881 : Nat.Prime 881 := by norm_num
private lemma prime_264384577_sub1 : (264384577 - 1 : ℕ) = 2 ^ 6 * 3 ^ 2 * 521 * 881 := by norm_num
private lemma prime_264384577_pow : (10 : ZMod 264384577) ^ (264384577 - 1) = 1 := by
  reduce_mod_char
private lemma prime_264384577_div_2 : (10 : ZMod 264384577) ^ ((264384577 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_264384577_div_3 : (10 : ZMod 264384577) ^ ((264384577 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_264384577_div_521 : (10 : ZMod 264384577) ^ ((264384577 - 1) / 521) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_264384577_div_881 : (10 : ZMod 264384577) ^ ((264384577 - 1) / 881) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_264384577 : Nat.Prime 264384577 := by
  refine lucas_primality 264384577 (10 : ZMod 264384577) prime_264384577_pow ?_
  intro q hq hqd
  rw [prime_264384577_sub1] at hqd
  have : q ∣ [2 ^ 6, 3 ^ 2, 521, 881].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_264384577_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_264384577_div_3
  · have : q = 521 := (Nat.prime_dvd_prime_iff_eq hq prime_521).mp hdf
    subst this; exact prime_264384577_div_521
  · have : q = 881 := (Nat.prime_dvd_prime_iff_eq hq prime_881).mp hdf
    subst this; exact prime_264384577_div_881
private lemma prime_153858604585151_sub1 : (153858604585151 - 1 : ℕ) = 2 * 5 ^ 2 * 103 * 113 * 264384577 := by norm_num
private lemma prime_153858604585151_pow : (7 : ZMod 153858604585151) ^ (153858604585151 - 1) = 1 := by
  reduce_mod_char
private lemma prime_153858604585151_div_2 : (7 : ZMod 153858604585151) ^ ((153858604585151 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_153858604585151_div_5 : (7 : ZMod 153858604585151) ^ ((153858604585151 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_153858604585151_div_103 : (7 : ZMod 153858604585151) ^ ((153858604585151 - 1) / 103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_153858604585151_div_113 : (7 : ZMod 153858604585151) ^ ((153858604585151 - 1) / 113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_153858604585151_div_264384577 : (7 : ZMod 153858604585151) ^ ((153858604585151 - 1) / 264384577) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_153858604585151 : Nat.Prime 153858604585151 := by
  refine lucas_primality 153858604585151 (7 : ZMod 153858604585151) prime_153858604585151_pow ?_
  intro q hq hqd
  rw [prime_153858604585151_sub1] at hqd
  have : q ∣ [2, 5 ^ 2, 103, 113, 264384577].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_153858604585151_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_153858604585151_div_5
  · have : q = 103 := (Nat.prime_dvd_prime_iff_eq hq prime_103).mp hdf
    subst this; exact prime_153858604585151_div_103
  · have : q = 113 := (Nat.prime_dvd_prime_iff_eq hq prime_113).mp hdf
    subst this; exact prime_153858604585151_div_113
  · have : q = 264384577 := (Nat.prime_dvd_prime_iff_eq hq prime_264384577).mp hdf
    subst this; exact prime_153858604585151_div_264384577
private lemma prime_A_46_sub1 : (623673825204293256324352720156753919 - 1 : ℕ) = 2 * 11 ^ 2 * 351031 * 47717193335359 * 153858604585151 := by norm_num
private lemma prime_A_46_pow : (7 : ZMod 623673825204293256324352720156753919) ^ (623673825204293256324352720156753919 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_46_div_2 : (7 : ZMod 623673825204293256324352720156753919) ^ ((623673825204293256324352720156753919 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_46_div_11 : (7 : ZMod 623673825204293256324352720156753919) ^ ((623673825204293256324352720156753919 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_46_div_351031 : (7 : ZMod 623673825204293256324352720156753919) ^ ((623673825204293256324352720156753919 - 1) / 351031) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_46_div_47717193335359 : (7 : ZMod 623673825204293256324352720156753919) ^ ((623673825204293256324352720156753919 - 1) / 47717193335359) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_46_div_153858604585151 : (7 : ZMod 623673825204293256324352720156753919) ^ ((623673825204293256324352720156753919 - 1) / 153858604585151) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_46 : Nat.Prime 623673825204293256324352720156753919 := by
  refine lucas_primality 623673825204293256324352720156753919 (7 : ZMod 623673825204293256324352720156753919) prime_A_46_pow ?_
  intro q hq hqd
  rw [prime_A_46_sub1] at hqd
  have : q ∣ [2, 11 ^ 2, 351031, 47717193335359, 153858604585151].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_46_div_2
  · have : q = 11 := prime_eq_of_dvd_prime_pow hq prime_11 hdf
    subst this; exact prime_A_46_div_11
  · have : q = 351031 := (Nat.prime_dvd_prime_iff_eq hq prime_351031).mp hdf
    subst this; exact prime_A_46_div_351031
  · have : q = 47717193335359 := (Nat.prime_dvd_prime_iff_eq hq prime_47717193335359).mp hdf
    subst this; exact prime_A_46_div_47717193335359
  · have : q = 153858604585151 := (Nat.prime_dvd_prime_iff_eq hq prime_153858604585151).mp hdf
    subst this; exact prime_A_46_div_153858604585151
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_2777 : Nat.Prime 2777 := by norm_num
private lemma prime_443 : Nat.Prime 443 := by norm_num
private lemma prime_1871 : Nat.Prime 1871 := by norm_num
private lemma prime_8581 : Nat.Prime 8581 := by norm_num
private lemma prime_3285923067967_sub1 : (3285923067967 - 1 : ℕ) = 2 * 3 * 7 * 11 * 443 * 1871 * 8581 := by norm_num
private lemma prime_3285923067967_pow : (3 : ZMod 3285923067967) ^ (3285923067967 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3285923067967_div_2 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967_div_3 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967_div_7 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967_div_11 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967_div_443 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 443) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967_div_1871 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 1871) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967_div_8581 : (3 : ZMod 3285923067967) ^ ((3285923067967 - 1) / 8581) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3285923067967 : Nat.Prime 3285923067967 := by
  refine lucas_primality 3285923067967 (3 : ZMod 3285923067967) prime_3285923067967_pow ?_
  intro q hq hqd
  rw [prime_3285923067967_sub1] at hqd
  have : q ∣ [2, 3, 7, 11, 443, 1871, 8581].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3285923067967_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_3285923067967_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_3285923067967_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_3285923067967_div_11
  · have : q = 443 := (Nat.prime_dvd_prime_iff_eq hq prime_443).mp hdf
    subst this; exact prime_3285923067967_div_443
  · have : q = 1871 := (Nat.prime_dvd_prime_iff_eq hq prime_1871).mp hdf
    subst this; exact prime_3285923067967_div_1871
  · have : q = 8581 := (Nat.prime_dvd_prime_iff_eq hq prime_8581).mp hdf
    subst this; exact prime_3285923067967_div_8581
private lemma prime_109500100316932309_sub1 : (109500100316932309 - 1 : ℕ) = 2 ^ 2 * 3 * 2777 * 3285923067967 := by norm_num
private lemma prime_109500100316932309_pow : (2 : ZMod 109500100316932309) ^ (109500100316932309 - 1) = 1 := by
  reduce_mod_char
private lemma prime_109500100316932309_div_2 : (2 : ZMod 109500100316932309) ^ ((109500100316932309 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_109500100316932309_div_3 : (2 : ZMod 109500100316932309) ^ ((109500100316932309 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_109500100316932309_div_2777 : (2 : ZMod 109500100316932309) ^ ((109500100316932309 - 1) / 2777) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_109500100316932309_div_3285923067967 : (2 : ZMod 109500100316932309) ^ ((109500100316932309 - 1) / 3285923067967) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_109500100316932309 : Nat.Prime 109500100316932309 := by
  refine lucas_primality 109500100316932309 (2 : ZMod 109500100316932309) prime_109500100316932309_pow ?_
  intro q hq hqd
  rw [prime_109500100316932309_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 2777, 3285923067967].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_109500100316932309_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_109500100316932309_div_3
  · have : q = 2777 := (Nat.prime_dvd_prime_iff_eq hq prime_2777).mp hdf
    subst this; exact prime_109500100316932309_div_2777
  · have : q = 3285923067967 := (Nat.prime_dvd_prime_iff_eq hq prime_3285923067967).mp hdf
    subst this; exact prime_109500100316932309_div_3285923067967
private lemma prime_15549014245004387879_sub1 : (15549014245004387879 - 1 : ℕ) = 2 * 71 * 109500100316932309 := by norm_num
private lemma prime_15549014245004387879_pow : (7 : ZMod 15549014245004387879) ^ (15549014245004387879 - 1) = 1 := by
  reduce_mod_char
private lemma prime_15549014245004387879_div_2 : (7 : ZMod 15549014245004387879) ^ ((15549014245004387879 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_15549014245004387879_div_71 : (7 : ZMod 15549014245004387879) ^ ((15549014245004387879 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_15549014245004387879_div_109500100316932309 : (7 : ZMod 15549014245004387879) ^ ((15549014245004387879 - 1) / 109500100316932309) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_15549014245004387879 : Nat.Prime 15549014245004387879 := by
  refine lucas_primality 15549014245004387879 (7 : ZMod 15549014245004387879) prime_15549014245004387879_pow ?_
  intro q hq hqd
  rw [prime_15549014245004387879_sub1] at hqd
  have : q ∣ [2, 71, 109500100316932309].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_15549014245004387879_div_2
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_15549014245004387879_div_71
  · have : q = 109500100316932309 := (Nat.prime_dvd_prime_iff_eq hq prime_109500100316932309).mp hdf
    subst this; exact prime_15549014245004387879_div_109500100316932309
private lemma prime_B_46_sub1 : (623673825204293256324352720156753921 - 1 : ℕ) = 2 ^ 47 * 3 * 5 * 19 * 15549014245004387879 := by norm_num
private lemma prime_B_46_pow : (17 : ZMod 623673825204293256324352720156753921) ^ (623673825204293256324352720156753921 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_46_div_2 : (17 : ZMod 623673825204293256324352720156753921) ^ ((623673825204293256324352720156753921 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_46_div_3 : (17 : ZMod 623673825204293256324352720156753921) ^ ((623673825204293256324352720156753921 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_46_div_5 : (17 : ZMod 623673825204293256324352720156753921) ^ ((623673825204293256324352720156753921 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_46_div_19 : (17 : ZMod 623673825204293256324352720156753921) ^ ((623673825204293256324352720156753921 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_46_div_15549014245004387879 : (17 : ZMod 623673825204293256324352720156753921) ^ ((623673825204293256324352720156753921 - 1) / 15549014245004387879) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_46 : Nat.Prime 623673825204293256324352720156753921 := by
  refine lucas_primality 623673825204293256324352720156753921 (17 : ZMod 623673825204293256324352720156753921) prime_B_46_pow ?_
  intro q hq hqd
  rw [prime_B_46_sub1] at hqd
  have : q ∣ [2 ^ 47, 3, 5, 19, 15549014245004387879].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_46_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_46_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_46_div_5
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_46_div_19
  · have : q = 15549014245004387879 := (Nat.prime_dvd_prime_iff_eq hq prime_15549014245004387879).mp hdf
    subst this; exact prime_B_46_div_15549014245004387879
private lemma pair_46 :
    Nat.Prime ((3 ^ 46 - 4899) * (2 ^ 46) - 1) ∧
    Nat.Prime ((3 ^ 46 - 4899) * (2 ^ 46) + 1) := by
  constructor
  · convert prime_A_46
  · convert prime_B_46

/- Pair for n = 47 -/
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_4783 : Nat.Prime 4783 := by norm_num
private lemma prime_167393 : Nat.Prime 167393 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_15791 : Nat.Prime 15791 := by norm_num
private lemma prime_397 : Nat.Prime 397 := by norm_num
private lemma prime_3263639 : Nat.Prime 3263639 := by norm_num
private lemma prime_23088744651061_sub1 : (23088744651061 - 1 : ℕ) = 2 ^ 2 * 3 ^ 4 * 5 * 11 * 397 * 3263639 := by norm_num
private lemma prime_23088744651061_pow : (7 : ZMod 23088744651061) ^ (23088744651061 - 1) = 1 := by
  reduce_mod_char
private lemma prime_23088744651061_div_2 : (7 : ZMod 23088744651061) ^ ((23088744651061 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23088744651061_div_3 : (7 : ZMod 23088744651061) ^ ((23088744651061 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23088744651061_div_5 : (7 : ZMod 23088744651061) ^ ((23088744651061 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23088744651061_div_11 : (7 : ZMod 23088744651061) ^ ((23088744651061 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23088744651061_div_397 : (7 : ZMod 23088744651061) ^ ((23088744651061 - 1) / 397) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23088744651061_div_3263639 : (7 : ZMod 23088744651061) ^ ((23088744651061 - 1) / 3263639) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23088744651061 : Nat.Prime 23088744651061 := by
  refine lucas_primality 23088744651061 (7 : ZMod 23088744651061) prime_23088744651061_pow ?_
  intro q hq hqd
  rw [prime_23088744651061_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 4, 5, 11, 397, 3263639].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_23088744651061_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_23088744651061_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_23088744651061_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_23088744651061_div_11
  · have : q = 397 := (Nat.prime_dvd_prime_iff_eq hq prime_397).mp hdf
    subst this; exact prime_23088744651061_div_397
  · have : q = 3263639 := (Nat.prime_dvd_prime_iff_eq hq prime_3263639).mp hdf
    subst this; exact prime_23088744651061_div_3263639
private lemma prime_2199233220446542442033_sub1 : (2199233220446542442033 - 1 : ℕ) = 2 ^ 4 * 13 * 29 * 15791 * 23088744651061 := by norm_num
private lemma prime_2199233220446542442033_pow : (3 : ZMod 2199233220446542442033) ^ (2199233220446542442033 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2199233220446542442033_div_2 : (3 : ZMod 2199233220446542442033) ^ ((2199233220446542442033 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2199233220446542442033_div_13 : (3 : ZMod 2199233220446542442033) ^ ((2199233220446542442033 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2199233220446542442033_div_29 : (3 : ZMod 2199233220446542442033) ^ ((2199233220446542442033 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2199233220446542442033_div_15791 : (3 : ZMod 2199233220446542442033) ^ ((2199233220446542442033 - 1) / 15791) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2199233220446542442033_div_23088744651061 : (3 : ZMod 2199233220446542442033) ^ ((2199233220446542442033 - 1) / 23088744651061) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2199233220446542442033 : Nat.Prime 2199233220446542442033 := by
  refine lucas_primality 2199233220446542442033 (3 : ZMod 2199233220446542442033) prime_2199233220446542442033_pow ?_
  intro q hq hqd
  rw [prime_2199233220446542442033_sub1] at hqd
  have : q ∣ [2 ^ 4, 13, 29, 15791, 23088744651061].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2199233220446542442033_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_2199233220446542442033_div_13
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_2199233220446542442033_div_29
  · have : q = 15791 := (Nat.prime_dvd_prime_iff_eq hq prime_15791).mp hdf
    subst this; exact prime_2199233220446542442033_div_15791
  · have : q = 23088744651061 := (Nat.prime_dvd_prime_iff_eq hq prime_23088744651061).mp hdf
    subst this; exact prime_2199233220446542442033_div_23088744651061
private lemma prime_80989974223445777379830593181_sub1 : (80989974223445777379830593181 - 1 : ℕ) = 2 ^ 2 * 5 * 11 * 167393 * 2199233220446542442033 := by norm_num
private lemma prime_80989974223445777379830593181_pow : (2 : ZMod 80989974223445777379830593181) ^ (80989974223445777379830593181 - 1) = 1 := by
  reduce_mod_char
private lemma prime_80989974223445777379830593181_div_2 : (2 : ZMod 80989974223445777379830593181) ^ ((80989974223445777379830593181 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_80989974223445777379830593181_div_5 : (2 : ZMod 80989974223445777379830593181) ^ ((80989974223445777379830593181 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_80989974223445777379830593181_div_11 : (2 : ZMod 80989974223445777379830593181) ^ ((80989974223445777379830593181 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_80989974223445777379830593181_div_167393 : (2 : ZMod 80989974223445777379830593181) ^ ((80989974223445777379830593181 - 1) / 167393) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_80989974223445777379830593181_div_2199233220446542442033 : (2 : ZMod 80989974223445777379830593181) ^ ((80989974223445777379830593181 - 1) / 2199233220446542442033) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_80989974223445777379830593181 : Nat.Prime 80989974223445777379830593181 := by
  refine lucas_primality 80989974223445777379830593181 (2 : ZMod 80989974223445777379830593181) prime_80989974223445777379830593181_pow ?_
  intro q hq hqd
  rw [prime_80989974223445777379830593181_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 11, 167393, 2199233220446542442033].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_80989974223445777379830593181_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_80989974223445777379830593181_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_80989974223445777379830593181_div_11
  · have : q = 167393 := (Nat.prime_dvd_prime_iff_eq hq prime_167393).mp hdf
    subst this; exact prime_80989974223445777379830593181_div_167393
  · have : q = 2199233220446542442033 := (Nat.prime_dvd_prime_iff_eq hq prime_2199233220446542442033).mp hdf
    subst this; exact prime_80989974223445777379830593181_div_2199233220446542442033
private lemma prime_374204295122575953998666916460442419_sub1 : (374204295122575953998666916460442419 - 1 : ℕ) = 2 * 3 * 7 * 23 * 4783 * 80989974223445777379830593181 := by norm_num
private lemma prime_374204295122575953998666916460442419_pow : (2 : ZMod 374204295122575953998666916460442419) ^ (374204295122575953998666916460442419 - 1) = 1 := by
  reduce_mod_char
private lemma prime_374204295122575953998666916460442419_div_2 : (2 : ZMod 374204295122575953998666916460442419) ^ ((374204295122575953998666916460442419 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_374204295122575953998666916460442419_div_3 : (2 : ZMod 374204295122575953998666916460442419) ^ ((374204295122575953998666916460442419 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_374204295122575953998666916460442419_div_7 : (2 : ZMod 374204295122575953998666916460442419) ^ ((374204295122575953998666916460442419 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_374204295122575953998666916460442419_div_23 : (2 : ZMod 374204295122575953998666916460442419) ^ ((374204295122575953998666916460442419 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_374204295122575953998666916460442419_div_4783 : (2 : ZMod 374204295122575953998666916460442419) ^ ((374204295122575953998666916460442419 - 1) / 4783) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_374204295122575953998666916460442419_div_80989974223445777379830593181 : (2 : ZMod 374204295122575953998666916460442419) ^ ((374204295122575953998666916460442419 - 1) / 80989974223445777379830593181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_374204295122575953998666916460442419 : Nat.Prime 374204295122575953998666916460442419 := by
  refine lucas_primality 374204295122575953998666916460442419 (2 : ZMod 374204295122575953998666916460442419) prime_374204295122575953998666916460442419_pow ?_
  intro q hq hqd
  rw [prime_374204295122575953998666916460442419_sub1] at hqd
  have : q ∣ [2, 3, 7, 23, 4783, 80989974223445777379830593181].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_374204295122575953998666916460442419_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_374204295122575953998666916460442419_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_374204295122575953998666916460442419_div_7
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_374204295122575953998666916460442419_div_23
  · have : q = 4783 := (Nat.prime_dvd_prime_iff_eq hq prime_4783).mp hdf
    subst this; exact prime_374204295122575953998666916460442419_div_4783
  · have : q = 80989974223445777379830593181 := (Nat.prime_dvd_prime_iff_eq hq prime_80989974223445777379830593181).mp hdf
    subst this; exact prime_374204295122575953998666916460442419_div_80989974223445777379830593181
private lemma prime_A_47_sub1 : (3742042951225759539986669164604424191 - 1 : ℕ) = 2 * 5 * 374204295122575953998666916460442419 := by norm_num
private lemma prime_A_47_pow : (13 : ZMod 3742042951225759539986669164604424191) ^ (3742042951225759539986669164604424191 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_47_div_2 : (13 : ZMod 3742042951225759539986669164604424191) ^ ((3742042951225759539986669164604424191 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_47_div_5 : (13 : ZMod 3742042951225759539986669164604424191) ^ ((3742042951225759539986669164604424191 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_47_div_374204295122575953998666916460442419 : (13 : ZMod 3742042951225759539986669164604424191) ^ ((3742042951225759539986669164604424191 - 1) / 374204295122575953998666916460442419) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_47 : Nat.Prime 3742042951225759539986669164604424191 := by
  refine lucas_primality 3742042951225759539986669164604424191 (13 : ZMod 3742042951225759539986669164604424191) prime_A_47_pow ?_
  intro q hq hqd
  rw [prime_A_47_sub1] at hqd
  have : q ∣ [2, 5, 374204295122575953998666916460442419].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_47_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_47_div_5
  · have : q = 374204295122575953998666916460442419 := (Nat.prime_dvd_prime_iff_eq hq prime_374204295122575953998666916460442419).mp hdf
    subst this; exact prime_A_47_div_374204295122575953998666916460442419
private lemma prime_163 : Nat.Prime 163 := by norm_num
private lemma prime_701 : Nat.Prime 701 := by norm_num
private lemma prime_4232653 : Nat.Prime 4232653 := by norm_num
private lemma prime_27766139 : Nat.Prime 27766139 := by norm_num
private lemma prime_2954312706550833698621_sub1 : (2954312706550833698621 - 1 : ℕ) = 2 ^ 2 * 5 * 11 * 163 * 701 * 4232653 * 27766139 := by norm_num
private lemma prime_2954312706550833698621_pow : (2 : ZMod 2954312706550833698621) ^ (2954312706550833698621 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2954312706550833698621_div_2 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621_div_5 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621_div_11 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621_div_163 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 163) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621_div_701 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 701) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621_div_4232653 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 4232653) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621_div_27766139 : (2 : ZMod 2954312706550833698621) ^ ((2954312706550833698621 - 1) / 27766139) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2954312706550833698621 : Nat.Prime 2954312706550833698621 := by
  refine lucas_primality 2954312706550833698621 (2 : ZMod 2954312706550833698621) prime_2954312706550833698621_pow ?_
  intro q hq hqd
  rw [prime_2954312706550833698621_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 11, 163, 701, 4232653, 27766139].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2954312706550833698621_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_2954312706550833698621_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_2954312706550833698621_div_11
  · have : q = 163 := (Nat.prime_dvd_prime_iff_eq hq prime_163).mp hdf
    subst this; exact prime_2954312706550833698621_div_163
  · have : q = 701 := (Nat.prime_dvd_prime_iff_eq hq prime_701).mp hdf
    subst this; exact prime_2954312706550833698621_div_701
  · have : q = 4232653 := (Nat.prime_dvd_prime_iff_eq hq prime_4232653).mp hdf
    subst this; exact prime_2954312706550833698621_div_4232653
  · have : q = 27766139 := (Nat.prime_dvd_prime_iff_eq hq prime_27766139).mp hdf
    subst this; exact prime_2954312706550833698621_div_27766139
private lemma prime_B_47_sub1 : (3742042951225759539986669164604424193 - 1 : ℕ) = 2 ^ 47 * 3 ^ 2 * 2954312706550833698621 := by norm_num
private lemma prime_B_47_pow : (7 : ZMod 3742042951225759539986669164604424193) ^ (3742042951225759539986669164604424193 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_47_div_2 : (7 : ZMod 3742042951225759539986669164604424193) ^ ((3742042951225759539986669164604424193 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_47_div_3 : (7 : ZMod 3742042951225759539986669164604424193) ^ ((3742042951225759539986669164604424193 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_47_div_2954312706550833698621 : (7 : ZMod 3742042951225759539986669164604424193) ^ ((3742042951225759539986669164604424193 - 1) / 2954312706550833698621) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_47 : Nat.Prime 3742042951225759539986669164604424193 := by
  refine lucas_primality 3742042951225759539986669164604424193 (7 : ZMod 3742042951225759539986669164604424193) prime_B_47_pow ?_
  intro q hq hqd
  rw [prime_B_47_sub1] at hqd
  have : q ∣ [2 ^ 47, 3 ^ 2, 2954312706550833698621].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_47_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_47_div_3
  · have : q = 2954312706550833698621 := (Nat.prime_dvd_prime_iff_eq hq prime_2954312706550833698621).mp hdf
    subst this; exact prime_B_47_div_2954312706550833698621
private lemma pair_47 :
    Nat.Prime ((3 ^ 47 - 198) * (2 ^ 47) - 1) ∧
    Nat.Prime ((3 ^ 47 - 198) * (2 ^ 47) + 1) := by
  constructor
  · convert prime_A_47
  · convert prime_B_47

/- Pair for n = 48 -/
private lemma prime_941429 : Nat.Prime 941429 := by norm_num
private lemma prime_51027721 : Nat.Prime 51027721 := by norm_num
private lemma prime_306166327_sub1 : (306166327 - 1 : ℕ) = 2 * 3 * 51027721 := by norm_num
private lemma prime_306166327_pow : (3 : ZMod 306166327) ^ (306166327 - 1) = 1 := by
  reduce_mod_char
private lemma prime_306166327_div_2 : (3 : ZMod 306166327) ^ ((306166327 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_306166327_div_3 : (3 : ZMod 306166327) ^ ((306166327 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_306166327_div_51027721 : (3 : ZMod 306166327) ^ ((306166327 - 1) / 51027721) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_306166327 : Nat.Prime 306166327 := by
  refine lucas_primality 306166327 (3 : ZMod 306166327) prime_306166327_pow ?_
  intro q hq hqd
  rw [prime_306166327_sub1] at hqd
  have : q ∣ [2, 3, 51027721].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_306166327_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_306166327_div_3
  · have : q = 51027721 := (Nat.prime_dvd_prime_iff_eq hq prime_51027721).mp hdf
    subst this; exact prime_306166327_div_51027721
private lemma prime_79 : Nat.Prime 79 := by norm_num
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_21503 : Nat.Prime 21503 := by norm_num
private lemma prime_60737 : Nat.Prime 60737 := by norm_num
private lemma prime_66697 : Nat.Prime 66697 := by norm_num
private lemma prime_8101951379_sub1 : (8101951379 - 1 : ℕ) = 2 * 60737 * 66697 := by norm_num
private lemma prime_8101951379_pow : (2 : ZMod 8101951379) ^ (8101951379 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8101951379_div_2 : (2 : ZMod 8101951379) ^ ((8101951379 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8101951379_div_60737 : (2 : ZMod 8101951379) ^ ((8101951379 - 1) / 60737) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8101951379_div_66697 : (2 : ZMod 8101951379) ^ ((8101951379 - 1) / 66697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8101951379 : Nat.Prime 8101951379 := by
  refine lucas_primality 8101951379 (2 : ZMod 8101951379) prime_8101951379_pow ?_
  intro q hq hqd
  rw [prime_8101951379_sub1] at hqd
  have : q ∣ [2, 60737, 66697].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8101951379_div_2
  · have : q = 60737 := (Nat.prime_dvd_prime_iff_eq hq prime_60737).mp hdf
    subst this; exact prime_8101951379_div_60737
  · have : q = 66697 := (Nat.prime_dvd_prime_iff_eq hq prime_66697).mp hdf
    subst this; exact prime_8101951379_div_66697
private lemma prime_41084375416773867889_sub1 : (41084375416773867889 - 1 : ℕ) = 2 ^ 4 * 3 * 17 ^ 3 * 21503 * 8101951379 := by norm_num
private lemma prime_41084375416773867889_pow : (11 : ZMod 41084375416773867889) ^ (41084375416773867889 - 1) = 1 := by
  reduce_mod_char
private lemma prime_41084375416773867889_div_2 : (11 : ZMod 41084375416773867889) ^ ((41084375416773867889 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41084375416773867889_div_3 : (11 : ZMod 41084375416773867889) ^ ((41084375416773867889 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41084375416773867889_div_17 : (11 : ZMod 41084375416773867889) ^ ((41084375416773867889 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41084375416773867889_div_21503 : (11 : ZMod 41084375416773867889) ^ ((41084375416773867889 - 1) / 21503) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41084375416773867889_div_8101951379 : (11 : ZMod 41084375416773867889) ^ ((41084375416773867889 - 1) / 8101951379) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_41084375416773867889 : Nat.Prime 41084375416773867889 := by
  refine lucas_primality 41084375416773867889 (11 : ZMod 41084375416773867889) prime_41084375416773867889_pow ?_
  intro q hq hqd
  rw [prime_41084375416773867889_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 17 ^ 3, 21503, 8101951379].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_41084375416773867889_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_41084375416773867889_div_3
  · have : q = 17 := prime_eq_of_dvd_prime_pow hq prime_17 hdf
    subst this; exact prime_41084375416773867889_div_17
  · have : q = 21503 := (Nat.prime_dvd_prime_iff_eq hq prime_21503).mp hdf
    subst this; exact prime_41084375416773867889_div_21503
  · have : q = 8101951379 := (Nat.prime_dvd_prime_iff_eq hq prime_8101951379).mp hdf
    subst this; exact prime_41084375416773867889_div_8101951379
private lemma prime_38947987895101626758773_sub1 : (38947987895101626758773 - 1 : ℕ) = 2 ^ 2 * 3 * 79 * 41084375416773867889 := by norm_num
private lemma prime_38947987895101626758773_pow : (2 : ZMod 38947987895101626758773) ^ (38947987895101626758773 - 1) = 1 := by
  reduce_mod_char
private lemma prime_38947987895101626758773_div_2 : (2 : ZMod 38947987895101626758773) ^ ((38947987895101626758773 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38947987895101626758773_div_3 : (2 : ZMod 38947987895101626758773) ^ ((38947987895101626758773 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38947987895101626758773_div_79 : (2 : ZMod 38947987895101626758773) ^ ((38947987895101626758773 - 1) / 79) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38947987895101626758773_div_41084375416773867889 : (2 : ZMod 38947987895101626758773) ^ ((38947987895101626758773 - 1) / 41084375416773867889) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38947987895101626758773 : Nat.Prime 38947987895101626758773 := by
  refine lucas_primality 38947987895101626758773 (2 : ZMod 38947987895101626758773) prime_38947987895101626758773_pow ?_
  intro q hq hqd
  rw [prime_38947987895101626758773_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 79, 41084375416773867889].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_38947987895101626758773_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_38947987895101626758773_div_3
  · have : q = 79 := (Nat.prime_dvd_prime_iff_eq hq prime_79).mp hdf
    subst this; exact prime_38947987895101626758773_div_79
  · have : q = 41084375416773867889 := (Nat.prime_dvd_prime_iff_eq hq prime_41084375416773867889).mp hdf
    subst this; exact prime_38947987895101626758773_div_41084375416773867889
private lemma prime_A_48_sub1 : (22452257707354557240068633775329771519 - 1 : ℕ) = 2 * 941429 * 306166327 * 38947987895101626758773 := by norm_num
private lemma prime_A_48_pow : (7 : ZMod 22452257707354557240068633775329771519) ^ (22452257707354557240068633775329771519 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_48_div_2 : (7 : ZMod 22452257707354557240068633775329771519) ^ ((22452257707354557240068633775329771519 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_48_div_941429 : (7 : ZMod 22452257707354557240068633775329771519) ^ ((22452257707354557240068633775329771519 - 1) / 941429) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_48_div_306166327 : (7 : ZMod 22452257707354557240068633775329771519) ^ ((22452257707354557240068633775329771519 - 1) / 306166327) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_48_div_38947987895101626758773 : (7 : ZMod 22452257707354557240068633775329771519) ^ ((22452257707354557240068633775329771519 - 1) / 38947987895101626758773) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_48 : Nat.Prime 22452257707354557240068633775329771519 := by
  refine lucas_primality 22452257707354557240068633775329771519 (7 : ZMod 22452257707354557240068633775329771519) prime_A_48_pow ?_
  intro q hq hqd
  rw [prime_A_48_sub1] at hqd
  have : q ∣ [2, 941429, 306166327, 38947987895101626758773].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_48_div_2
  · have : q = 941429 := (Nat.prime_dvd_prime_iff_eq hq prime_941429).mp hdf
    subst this; exact prime_A_48_div_941429
  · have : q = 306166327 := (Nat.prime_dvd_prime_iff_eq hq prime_306166327).mp hdf
    subst this; exact prime_A_48_div_306166327
  · have : q = 38947987895101626758773 := (Nat.prime_dvd_prime_iff_eq hq prime_38947987895101626758773).mp hdf
    subst this; exact prime_A_48_div_38947987895101626758773
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_39317 : Nat.Prime 39317 := by norm_num
private lemma prime_233 : Nat.Prime 233 := by norm_num
private lemma prime_239 : Nat.Prime 239 := by norm_num
private lemma prime_2078221 : Nat.Prime 2078221 := by norm_num
private lemma prime_167808344599151_sub1 : (167808344599151 - 1 : ℕ) = 2 * 5 ^ 2 * 29 * 233 * 239 * 2078221 := by norm_num
private lemma prime_167808344599151_pow : (7 : ZMod 167808344599151) ^ (167808344599151 - 1) = 1 := by
  reduce_mod_char
private lemma prime_167808344599151_div_2 : (7 : ZMod 167808344599151) ^ ((167808344599151 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167808344599151_div_5 : (7 : ZMod 167808344599151) ^ ((167808344599151 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167808344599151_div_29 : (7 : ZMod 167808344599151) ^ ((167808344599151 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167808344599151_div_233 : (7 : ZMod 167808344599151) ^ ((167808344599151 - 1) / 233) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167808344599151_div_239 : (7 : ZMod 167808344599151) ^ ((167808344599151 - 1) / 239) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167808344599151_div_2078221 : (7 : ZMod 167808344599151) ^ ((167808344599151 - 1) / 2078221) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167808344599151 : Nat.Prime 167808344599151 := by
  refine lucas_primality 167808344599151 (7 : ZMod 167808344599151) prime_167808344599151_pow ?_
  intro q hq hqd
  rw [prime_167808344599151_sub1] at hqd
  have : q ∣ [2, 5 ^ 2, 29, 233, 239, 2078221].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_167808344599151_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_167808344599151_div_5
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_167808344599151_div_29
  · have : q = 233 := (Nat.prime_dvd_prime_iff_eq hq prime_233).mp hdf
    subst this; exact prime_167808344599151_div_233
  · have : q = 239 := (Nat.prime_dvd_prime_iff_eq hq prime_239).mp hdf
    subst this; exact prime_167808344599151_div_239
  · have : q = 2078221 := (Nat.prime_dvd_prime_iff_eq hq prime_2078221).mp hdf
    subst this; exact prime_167808344599151_div_2078221
private lemma prime_335616689198303_sub1 : (335616689198303 - 1 : ℕ) = 2 * 167808344599151 := by norm_num
private lemma prime_335616689198303_pow : (5 : ZMod 335616689198303) ^ (335616689198303 - 1) = 1 := by
  reduce_mod_char
private lemma prime_335616689198303_div_2 : (5 : ZMod 335616689198303) ^ ((335616689198303 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_335616689198303_div_167808344599151 : (5 : ZMod 335616689198303) ^ ((335616689198303 - 1) / 167808344599151) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_335616689198303 : Nat.Prime 335616689198303 := by
  refine lucas_primality 335616689198303 (5 : ZMod 335616689198303) prime_335616689198303_pow ?_
  intro q hq hqd
  rw [prime_335616689198303_sub1] at hqd
  have : q ∣ [2, 167808344599151].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_335616689198303_div_2
  · have : q = 167808344599151 := (Nat.prime_dvd_prime_iff_eq hq prime_167808344599151).mp hdf
    subst this; exact prime_335616689198303_div_167808344599151
private lemma prime_B_48_sub1 : (22452257707354557240068633775329771521 - 1 : ℕ) = 2 ^ 48 * 3 * 5 * 13 * 31 * 39317 * 335616689198303 := by norm_num
private lemma prime_B_48_pow : (29 : ZMod 22452257707354557240068633775329771521) ^ (22452257707354557240068633775329771521 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_48_div_2 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48_div_3 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48_div_5 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48_div_13 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48_div_31 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48_div_39317 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 39317) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48_div_335616689198303 : (29 : ZMod 22452257707354557240068633775329771521) ^ ((22452257707354557240068633775329771521 - 1) / 335616689198303) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_48 : Nat.Prime 22452257707354557240068633775329771521 := by
  refine lucas_primality 22452257707354557240068633775329771521 (29 : ZMod 22452257707354557240068633775329771521) prime_B_48_pow ?_
  intro q hq hqd
  rw [prime_B_48_sub1] at hqd
  have : q ∣ [2 ^ 48, 3, 5, 13, 31, 39317, 335616689198303].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_48_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_48_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_48_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_48_div_13
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_B_48_div_31
  · have : q = 39317 := (Nat.prime_dvd_prime_iff_eq hq prime_39317).mp hdf
    subst this; exact prime_B_48_div_39317
  · have : q = 335616689198303 := (Nat.prime_dvd_prime_iff_eq hq prime_335616689198303).mp hdf
    subst this; exact prime_B_48_div_335616689198303
private lemma pair_48 :
    Nat.Prime ((3 ^ 48 - 66) * (2 ^ 48) - 1) ∧
    Nat.Prime ((3 ^ 48 - 66) * (2 ^ 48) + 1) := by
  constructor
  · convert prime_A_48
  · convert prime_B_48

/- Pair for n = 49 -/
private lemma prime_17829611 : Nat.Prime 17829611 := by norm_num
private lemma prime_34469 : Nat.Prime 34469 := by norm_num
private lemma prime_482039 : Nat.Prime 482039 := by norm_num
private lemma prime_99692413747_sub1 : (99692413747 - 1 : ℕ) = 2 * 3 * 34469 * 482039 := by norm_num
private lemma prime_99692413747_pow : (2 : ZMod 99692413747) ^ (99692413747 - 1) = 1 := by
  reduce_mod_char
private lemma prime_99692413747_div_2 : (2 : ZMod 99692413747) ^ ((99692413747 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_99692413747_div_3 : (2 : ZMod 99692413747) ^ ((99692413747 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_99692413747_div_34469 : (2 : ZMod 99692413747) ^ ((99692413747 - 1) / 34469) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_99692413747_div_482039 : (2 : ZMod 99692413747) ^ ((99692413747 - 1) / 482039) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_99692413747 : Nat.Prime 99692413747 := by
  refine lucas_primality 99692413747 (2 : ZMod 99692413747) prime_99692413747_pow ?_
  intro q hq hqd
  rw [prime_99692413747_sub1] at hqd
  have : q ∣ [2, 3, 34469, 482039].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_99692413747_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_99692413747_div_3
  · have : q = 34469 := (Nat.prime_dvd_prime_iff_eq hq prime_34469).mp hdf
    subst this; exact prime_99692413747_div_34469
  · have : q = 482039 := (Nat.prime_dvd_prime_iff_eq hq prime_482039).mp hdf
    subst this; exact prime_99692413747_div_482039
private lemma prime_84530729 : Nat.Prime 84530729 := by norm_num
private lemma prime_173 : Nat.Prime 173 := by norm_num
private lemma prime_93481 : Nat.Prime 93481 := by norm_num
private lemma prime_485166391_sub1 : (485166391 - 1 : ℕ) = 2 * 3 * 5 * 173 * 93481 := by norm_num
private lemma prime_485166391_pow : (6 : ZMod 485166391) ^ (485166391 - 1) = 1 := by
  reduce_mod_char
private lemma prime_485166391_div_2 : (6 : ZMod 485166391) ^ ((485166391 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_485166391_div_3 : (6 : ZMod 485166391) ^ ((485166391 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_485166391_div_5 : (6 : ZMod 485166391) ^ ((485166391 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_485166391_div_173 : (6 : ZMod 485166391) ^ ((485166391 - 1) / 173) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_485166391_div_93481 : (6 : ZMod 485166391) ^ ((485166391 - 1) / 93481) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_485166391 : Nat.Prime 485166391 := by
  refine lucas_primality 485166391 (6 : ZMod 485166391) prime_485166391_pow ?_
  intro q hq hqd
  rw [prime_485166391_sub1] at hqd
  have : q ∣ [2, 3, 5, 173, 93481].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_485166391_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_485166391_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_485166391_div_5
  · have : q = 173 := (Nat.prime_dvd_prime_iff_eq hq prime_173).mp hdf
    subst this; exact prime_485166391_div_173
  · have : q = 93481 := (Nat.prime_dvd_prime_iff_eq hq prime_93481).mp hdf
    subst this; exact prime_485166391_div_93481
private lemma prime_82022937435058079_sub1 : (82022937435058079 - 1 : ℕ) = 2 * 84530729 * 485166391 := by norm_num
private lemma prime_82022937435058079_pow : (11 : ZMod 82022937435058079) ^ (82022937435058079 - 1) = 1 := by
  reduce_mod_char
private lemma prime_82022937435058079_div_2 : (11 : ZMod 82022937435058079) ^ ((82022937435058079 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_82022937435058079_div_84530729 : (11 : ZMod 82022937435058079) ^ ((82022937435058079 - 1) / 84530729) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_82022937435058079_div_485166391 : (11 : ZMod 82022937435058079) ^ ((82022937435058079 - 1) / 485166391) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_82022937435058079 : Nat.Prime 82022937435058079 := by
  refine lucas_primality 82022937435058079 (11 : ZMod 82022937435058079) prime_82022937435058079_pow ?_
  intro q hq hqd
  rw [prime_82022937435058079_sub1] at hqd
  have : q ∣ [2, 84530729, 485166391].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_82022937435058079_div_2
  · have : q = 84530729 := (Nat.prime_dvd_prime_iff_eq hq prime_84530729).mp hdf
    subst this; exact prime_82022937435058079_div_84530729
  · have : q = 485166391 := (Nat.prime_dvd_prime_iff_eq hq prime_485166391).mp hdf
    subst this; exact prime_82022937435058079_div_485166391
private lemma prime_539686264624326927006438792859_sub1 : (539686264624326927006438792859 - 1 : ℕ) = 2 * 3 * 11 * 99692413747 * 82022937435058079 := by norm_num
private lemma prime_539686264624326927006438792859_pow : (3 : ZMod 539686264624326927006438792859) ^ (539686264624326927006438792859 - 1) = 1 := by
  reduce_mod_char
private lemma prime_539686264624326927006438792859_div_2 : (3 : ZMod 539686264624326927006438792859) ^ ((539686264624326927006438792859 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_539686264624326927006438792859_div_3 : (3 : ZMod 539686264624326927006438792859) ^ ((539686264624326927006438792859 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_539686264624326927006438792859_div_11 : (3 : ZMod 539686264624326927006438792859) ^ ((539686264624326927006438792859 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_539686264624326927006438792859_div_99692413747 : (3 : ZMod 539686264624326927006438792859) ^ ((539686264624326927006438792859 - 1) / 99692413747) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_539686264624326927006438792859_div_82022937435058079 : (3 : ZMod 539686264624326927006438792859) ^ ((539686264624326927006438792859 - 1) / 82022937435058079) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_539686264624326927006438792859 : Nat.Prime 539686264624326927006438792859 := by
  refine lucas_primality 539686264624326927006438792859 (3 : ZMod 539686264624326927006438792859) prime_539686264624326927006438792859_pow ?_
  intro q hq hqd
  rw [prime_539686264624326927006438792859_sub1] at hqd
  have : q ∣ [2, 3, 11, 99692413747, 82022937435058079].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_539686264624326927006438792859_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_539686264624326927006438792859_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_539686264624326927006438792859_div_11
  · have : q = 99692413747 := (Nat.prime_dvd_prime_iff_eq hq prime_99692413747).mp hdf
    subst this; exact prime_539686264624326927006438792859_div_99692413747
  · have : q = 82022937435058079 := (Nat.prime_dvd_prime_iff_eq hq prime_82022937435058079).mp hdf
    subst this; exact prime_539686264624326927006438792859_div_82022937435058079
private lemma prime_A_49_sub1 : (134713546244127343434902774407797669887 - 1 : ℕ) = 2 * 7 * 17829611 * 539686264624326927006438792859 := by norm_num
private lemma prime_A_49_pow : (5 : ZMod 134713546244127343434902774407797669887) ^ (134713546244127343434902774407797669887 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_49_div_2 : (5 : ZMod 134713546244127343434902774407797669887) ^ ((134713546244127343434902774407797669887 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_49_div_7 : (5 : ZMod 134713546244127343434902774407797669887) ^ ((134713546244127343434902774407797669887 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_49_div_17829611 : (5 : ZMod 134713546244127343434902774407797669887) ^ ((134713546244127343434902774407797669887 - 1) / 17829611) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_49_div_539686264624326927006438792859 : (5 : ZMod 134713546244127343434902774407797669887) ^ ((134713546244127343434902774407797669887 - 1) / 539686264624326927006438792859) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_49 : Nat.Prime 134713546244127343434902774407797669887 := by
  refine lucas_primality 134713546244127343434902774407797669887 (5 : ZMod 134713546244127343434902774407797669887) prime_A_49_pow ?_
  intro q hq hqd
  rw [prime_A_49_sub1] at hqd
  have : q ∣ [2, 7, 17829611, 539686264624326927006438792859].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_49_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_49_div_7
  · have : q = 17829611 := (Nat.prime_dvd_prime_iff_eq hq prime_17829611).mp hdf
    subst this; exact prime_A_49_div_17829611
  · have : q = 539686264624326927006438792859 := (Nat.prime_dvd_prime_iff_eq hq prime_539686264624326927006438792859).mp hdf
    subst this; exact prime_A_49_div_539686264624326927006438792859
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_101 : Nat.Prime 101 := by norm_num
private lemma prime_280591 : Nat.Prime 280591 := by norm_num
private lemma prime_67568341 : Nat.Prime 67568341 := by norm_num
private lemma prime_1307646607817582128853_sub1 : (1307646607817582128853 - 1 : ℕ) = 2 ^ 2 * 7 * 29 ^ 3 * 101 * 280591 * 67568341 := by norm_num
private lemma prime_1307646607817582128853_pow : (3 : ZMod 1307646607817582128853) ^ (1307646607817582128853 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1307646607817582128853_div_2 : (3 : ZMod 1307646607817582128853) ^ ((1307646607817582128853 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1307646607817582128853_div_7 : (3 : ZMod 1307646607817582128853) ^ ((1307646607817582128853 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1307646607817582128853_div_29 : (3 : ZMod 1307646607817582128853) ^ ((1307646607817582128853 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1307646607817582128853_div_101 : (3 : ZMod 1307646607817582128853) ^ ((1307646607817582128853 - 1) / 101) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1307646607817582128853_div_280591 : (3 : ZMod 1307646607817582128853) ^ ((1307646607817582128853 - 1) / 280591) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1307646607817582128853_div_67568341 : (3 : ZMod 1307646607817582128853) ^ ((1307646607817582128853 - 1) / 67568341) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1307646607817582128853 : Nat.Prime 1307646607817582128853 := by
  refine lucas_primality 1307646607817582128853 (3 : ZMod 1307646607817582128853) prime_1307646607817582128853_pow ?_
  intro q hq hqd
  rw [prime_1307646607817582128853_sub1] at hqd
  have : q ∣ [2 ^ 2, 7, 29 ^ 3, 101, 280591, 67568341].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1307646607817582128853_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_1307646607817582128853_div_7
  · have : q = 29 := prime_eq_of_dvd_prime_pow hq prime_29 hdf
    subst this; exact prime_1307646607817582128853_div_29
  · have : q = 101 := (Nat.prime_dvd_prime_iff_eq hq prime_101).mp hdf
    subst this; exact prime_1307646607817582128853_div_101
  · have : q = 280591 := (Nat.prime_dvd_prime_iff_eq hq prime_280591).mp hdf
    subst this; exact prime_1307646607817582128853_div_280591
  · have : q = 67568341 := (Nat.prime_dvd_prime_iff_eq hq prime_67568341).mp hdf
    subst this; exact prime_1307646607817582128853_div_67568341
private lemma prime_B_49_sub1 : (134713546244127343434902774407797669889 - 1 : ℕ) = 2 ^ 49 * 3 * 61 * 1307646607817582128853 := by norm_num
private lemma prime_B_49_pow : (7 : ZMod 134713546244127343434902774407797669889) ^ (134713546244127343434902774407797669889 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_49_div_2 : (7 : ZMod 134713546244127343434902774407797669889) ^ ((134713546244127343434902774407797669889 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_49_div_3 : (7 : ZMod 134713546244127343434902774407797669889) ^ ((134713546244127343434902774407797669889 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_49_div_61 : (7 : ZMod 134713546244127343434902774407797669889) ^ ((134713546244127343434902774407797669889 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_49_div_1307646607817582128853 : (7 : ZMod 134713546244127343434902774407797669889) ^ ((134713546244127343434902774407797669889 - 1) / 1307646607817582128853) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_49 : Nat.Prime 134713546244127343434902774407797669889 := by
  refine lucas_primality 134713546244127343434902774407797669889 (7 : ZMod 134713546244127343434902774407797669889) prime_B_49_pow ?_
  intro q hq hqd
  rw [prime_B_49_sub1] at hqd
  have : q ∣ [2 ^ 49, 3, 61, 1307646607817582128853].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_49_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_49_div_3
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_B_49_div_61
  · have : q = 1307646607817582128853 := (Nat.prime_dvd_prime_iff_eq hq prime_1307646607817582128853).mp hdf
    subst this; exact prime_B_49_div_1307646607817582128853
private lemma pair_49 :
    Nat.Prime ((3 ^ 49 - 9984) * (2 ^ 49) - 1) ∧
    Nat.Prime ((3 ^ 49 - 9984) * (2 ^ 49) + 1) := by
  constructor
  · convert prime_A_49
  · convert prime_B_49

/- Pair for n = 50 -/
private lemma prime_87317 : Nat.Prime 87317 := by norm_num
private lemma prime_8863927 : Nat.Prime 8863927 := by norm_num
private lemma prime_448157 : Nat.Prime 448157 := by norm_num
private lemma prime_563 : Nat.Prime 563 := by norm_num
private lemma prime_338137 : Nat.Prime 338137 := by norm_num
private lemma prime_51310783 : Nat.Prime 51310783 := by norm_num
private lemma prime_2774138068986382733_sub1 : (2774138068986382733 - 1 : ℕ) = 2 ^ 2 * 71 * 563 * 338137 * 51310783 := by norm_num
private lemma prime_2774138068986382733_pow : (2 : ZMod 2774138068986382733) ^ (2774138068986382733 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2774138068986382733_div_2 : (2 : ZMod 2774138068986382733) ^ ((2774138068986382733 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2774138068986382733_div_71 : (2 : ZMod 2774138068986382733) ^ ((2774138068986382733 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2774138068986382733_div_563 : (2 : ZMod 2774138068986382733) ^ ((2774138068986382733 - 1) / 563) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2774138068986382733_div_338137 : (2 : ZMod 2774138068986382733) ^ ((2774138068986382733 - 1) / 338137) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2774138068986382733_div_51310783 : (2 : ZMod 2774138068986382733) ^ ((2774138068986382733 - 1) / 51310783) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2774138068986382733 : Nat.Prime 2774138068986382733 := by
  refine lucas_primality 2774138068986382733 (2 : ZMod 2774138068986382733) prime_2774138068986382733_pow ?_
  intro q hq hqd
  rw [prime_2774138068986382733_sub1] at hqd
  have : q ∣ [2 ^ 2, 71, 563, 338137, 51310783].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2774138068986382733_div_2
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_2774138068986382733_div_71
  · have : q = 563 := (Nat.prime_dvd_prime_iff_eq hq prime_563).mp hdf
    subst this; exact prime_2774138068986382733_div_563
  · have : q = 338137 := (Nat.prime_dvd_prime_iff_eq hq prime_338137).mp hdf
    subst this; exact prime_2774138068986382733_div_338137
  · have : q = 51310783 := (Nat.prime_dvd_prime_iff_eq hq prime_51310783).mp hdf
    subst this; exact prime_2774138068986382733_div_51310783
private lemma prime_5548276137972765467_sub1 : (5548276137972765467 - 1 : ℕ) = 2 * 2774138068986382733 := by norm_num
private lemma prime_5548276137972765467_pow : (2 : ZMod 5548276137972765467) ^ (5548276137972765467 - 1) = 1 := by
  reduce_mod_char
private lemma prime_5548276137972765467_div_2 : (2 : ZMod 5548276137972765467) ^ ((5548276137972765467 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5548276137972765467_div_2774138068986382733 : (2 : ZMod 5548276137972765467) ^ ((5548276137972765467 - 1) / 2774138068986382733) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5548276137972765467 : Nat.Prime 5548276137972765467 := by
  refine lucas_primality 5548276137972765467 (2 : ZMod 5548276137972765467) prime_5548276137972765467_pow ?_
  intro q hq hqd
  rw [prime_5548276137972765467_sub1] at hqd
  have : q ∣ [2, 2774138068986382733].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_5548276137972765467_div_2
  · have : q = 2774138068986382733 := (Nat.prime_dvd_prime_iff_eq hq prime_2774138068986382733).mp hdf
    subst this; exact prime_5548276137972765467_div_2774138068986382733
private lemma prime_74594963674963819601829571_sub1 : (74594963674963819601829571 - 1 : ℕ) = 2 * 3 * 5 * 448157 * 5548276137972765467 := by norm_num
private lemma prime_74594963674963819601829571_pow : (2 : ZMod 74594963674963819601829571) ^ (74594963674963819601829571 - 1) = 1 := by
  reduce_mod_char
private lemma prime_74594963674963819601829571_div_2 : (2 : ZMod 74594963674963819601829571) ^ ((74594963674963819601829571 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_74594963674963819601829571_div_3 : (2 : ZMod 74594963674963819601829571) ^ ((74594963674963819601829571 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_74594963674963819601829571_div_5 : (2 : ZMod 74594963674963819601829571) ^ ((74594963674963819601829571 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_74594963674963819601829571_div_448157 : (2 : ZMod 74594963674963819601829571) ^ ((74594963674963819601829571 - 1) / 448157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_74594963674963819601829571_div_5548276137972765467 : (2 : ZMod 74594963674963819601829571) ^ ((74594963674963819601829571 - 1) / 5548276137972765467) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_74594963674963819601829571 : Nat.Prime 74594963674963819601829571 := by
  refine lucas_primality 74594963674963819601829571 (2 : ZMod 74594963674963819601829571) prime_74594963674963819601829571_pow ?_
  intro q hq hqd
  rw [prime_74594963674963819601829571_sub1] at hqd
  have : q ∣ [2, 3, 5, 448157, 5548276137972765467].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_74594963674963819601829571_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_74594963674963819601829571_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_74594963674963819601829571_div_5
  · have : q = 448157 := (Nat.prime_dvd_prime_iff_eq hq prime_448157).mp hdf
    subst this; exact prime_74594963674963819601829571_div_448157
  · have : q = 5548276137972765467 := (Nat.prime_dvd_prime_iff_eq hq prime_5548276137972765467).mp hdf
    subst this; exact prime_74594963674963819601829571_div_5548276137972765467
private lemma prime_A_50_sub1 : (808281277464764060639934163421755342847 - 1 : ℕ) = 2 * 7 * 87317 * 8863927 * 74594963674963819601829571 := by norm_num
private lemma prime_A_50_pow : (5 : ZMod 808281277464764060639934163421755342847) ^ (808281277464764060639934163421755342847 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_50_div_2 : (5 : ZMod 808281277464764060639934163421755342847) ^ ((808281277464764060639934163421755342847 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_50_div_7 : (5 : ZMod 808281277464764060639934163421755342847) ^ ((808281277464764060639934163421755342847 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_50_div_87317 : (5 : ZMod 808281277464764060639934163421755342847) ^ ((808281277464764060639934163421755342847 - 1) / 87317) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_50_div_8863927 : (5 : ZMod 808281277464764060639934163421755342847) ^ ((808281277464764060639934163421755342847 - 1) / 8863927) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_50_div_74594963674963819601829571 : (5 : ZMod 808281277464764060639934163421755342847) ^ ((808281277464764060639934163421755342847 - 1) / 74594963674963819601829571) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_50 : Nat.Prime 808281277464764060639934163421755342847 := by
  refine lucas_primality 808281277464764060639934163421755342847 (5 : ZMod 808281277464764060639934163421755342847) prime_A_50_pow ?_
  intro q hq hqd
  rw [prime_A_50_sub1] at hqd
  have : q ∣ [2, 7, 87317, 8863927, 74594963674963819601829571].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_50_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_50_div_7
  · have : q = 87317 := (Nat.prime_dvd_prime_iff_eq hq prime_87317).mp hdf
    subst this; exact prime_A_50_div_87317
  · have : q = 8863927 := (Nat.prime_dvd_prime_iff_eq hq prime_8863927).mp hdf
    subst this; exact prime_A_50_div_8863927
  · have : q = 74594963674963819601829571 := (Nat.prime_dvd_prime_iff_eq hq prime_74594963674963819601829571).mp hdf
    subst this; exact prime_A_50_div_74594963674963819601829571
private lemma prime_983 : Nat.Prime 983 := by norm_num
private lemma prime_3079 : Nat.Prime 3079 := by norm_num
private lemma prime_435838609_sub1 : (435838609 - 1 : ℕ) = 2 ^ 4 * 3 ^ 2 * 983 * 3079 := by norm_num
private lemma prime_435838609_pow : (11 : ZMod 435838609) ^ (435838609 - 1) = 1 := by
  reduce_mod_char
private lemma prime_435838609_div_2 : (11 : ZMod 435838609) ^ ((435838609 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_435838609_div_3 : (11 : ZMod 435838609) ^ ((435838609 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_435838609_div_983 : (11 : ZMod 435838609) ^ ((435838609 - 1) / 983) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_435838609_div_3079 : (11 : ZMod 435838609) ^ ((435838609 - 1) / 3079) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_435838609 : Nat.Prime 435838609 := by
  refine lucas_primality 435838609 (11 : ZMod 435838609) prime_435838609_pow ?_
  intro q hq hqd
  rw [prime_435838609_sub1] at hqd
  have : q ∣ [2 ^ 4, 3 ^ 2, 983, 3079].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_435838609_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_435838609_div_3
  · have : q = 983 := (Nat.prime_dvd_prime_iff_eq hq prime_983).mp hdf
    subst this; exact prime_435838609_div_983
  · have : q = 3079 := (Nat.prime_dvd_prime_iff_eq hq prime_3079).mp hdf
    subst this; exact prime_435838609_div_3079
private lemma prime_499 : Nat.Prime 499 := by norm_num
private lemma prime_1087 : Nat.Prime 1087 := by norm_num
private lemma prime_58579 : Nat.Prime 58579 := by norm_num
private lemma prime_953220333811_sub1 : (953220333811 - 1 : ℕ) = 2 * 3 * 5 * 499 * 1087 * 58579 := by norm_num
private lemma prime_953220333811_pow : (2 : ZMod 953220333811) ^ (953220333811 - 1) = 1 := by
  reduce_mod_char
private lemma prime_953220333811_div_2 : (2 : ZMod 953220333811) ^ ((953220333811 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_953220333811_div_3 : (2 : ZMod 953220333811) ^ ((953220333811 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_953220333811_div_5 : (2 : ZMod 953220333811) ^ ((953220333811 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_953220333811_div_499 : (2 : ZMod 953220333811) ^ ((953220333811 - 1) / 499) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_953220333811_div_1087 : (2 : ZMod 953220333811) ^ ((953220333811 - 1) / 1087) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_953220333811_div_58579 : (2 : ZMod 953220333811) ^ ((953220333811 - 1) / 58579) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_953220333811 : Nat.Prime 953220333811 := by
  refine lucas_primality 953220333811 (2 : ZMod 953220333811) prime_953220333811_pow ?_
  intro q hq hqd
  rw [prime_953220333811_sub1] at hqd
  have : q ∣ [2, 3, 5, 499, 1087, 58579].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_953220333811_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_953220333811_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_953220333811_div_5
  · have : q = 499 := (Nat.prime_dvd_prime_iff_eq hq prime_499).mp hdf
    subst this; exact prime_953220333811_div_499
  · have : q = 1087 := (Nat.prime_dvd_prime_iff_eq hq prime_1087).mp hdf
    subst this; exact prime_953220333811_div_1087
  · have : q = 58579 := (Nat.prime_dvd_prime_iff_eq hq prime_58579).mp hdf
    subst this; exact prime_953220333811_div_58579
private lemma prime_45754576022929_sub1 : (45754576022929 - 1 : ℕ) = 2 ^ 4 * 3 * 953220333811 := by norm_num
private lemma prime_45754576022929_pow : (13 : ZMod 45754576022929) ^ (45754576022929 - 1) = 1 := by
  reduce_mod_char
private lemma prime_45754576022929_div_2 : (13 : ZMod 45754576022929) ^ ((45754576022929 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45754576022929_div_3 : (13 : ZMod 45754576022929) ^ ((45754576022929 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45754576022929_div_953220333811 : (13 : ZMod 45754576022929) ^ ((45754576022929 - 1) / 953220333811) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45754576022929 : Nat.Prime 45754576022929 := by
  refine lucas_primality 45754576022929 (13 : ZMod 45754576022929) prime_45754576022929_pow ?_
  intro q hq hqd
  rw [prime_45754576022929_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 953220333811].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_45754576022929_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_45754576022929_div_3
  · have : q = 953220333811 := (Nat.prime_dvd_prime_iff_eq hq prime_953220333811).mp hdf
    subst this; exact prime_45754576022929_div_953220333811
private lemma prime_119649664615308764794567_sub1 : (119649664615308764794567 - 1 : ℕ) = 2 * 3 * 435838609 * 45754576022929 := by norm_num
private lemma prime_119649664615308764794567_pow : (3 : ZMod 119649664615308764794567) ^ (119649664615308764794567 - 1) = 1 := by
  reduce_mod_char
private lemma prime_119649664615308764794567_div_2 : (3 : ZMod 119649664615308764794567) ^ ((119649664615308764794567 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_119649664615308764794567_div_3 : (3 : ZMod 119649664615308764794567) ^ ((119649664615308764794567 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_119649664615308764794567_div_435838609 : (3 : ZMod 119649664615308764794567) ^ ((119649664615308764794567 - 1) / 435838609) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_119649664615308764794567_div_45754576022929 : (3 : ZMod 119649664615308764794567) ^ ((119649664615308764794567 - 1) / 45754576022929) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_119649664615308764794567 : Nat.Prime 119649664615308764794567 := by
  refine lucas_primality 119649664615308764794567 (3 : ZMod 119649664615308764794567) prime_119649664615308764794567_pow ?_
  intro q hq hqd
  rw [prime_119649664615308764794567_sub1] at hqd
  have : q ∣ [2, 3, 435838609, 45754576022929].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_119649664615308764794567_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_119649664615308764794567_div_3
  · have : q = 435838609 := (Nat.prime_dvd_prime_iff_eq hq prime_435838609).mp hdf
    subst this; exact prime_119649664615308764794567_div_435838609
  · have : q = 45754576022929 := (Nat.prime_dvd_prime_iff_eq hq prime_45754576022929).mp hdf
    subst this; exact prime_119649664615308764794567_div_45754576022929
private lemma prime_B_50_sub1 : (808281277464764060639934163421755342849 - 1 : ℕ) = 2 ^ 51 * 3 * 119649664615308764794567 := by norm_num
private lemma prime_B_50_pow : (13 : ZMod 808281277464764060639934163421755342849) ^ (808281277464764060639934163421755342849 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_50_div_2 : (13 : ZMod 808281277464764060639934163421755342849) ^ ((808281277464764060639934163421755342849 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_50_div_3 : (13 : ZMod 808281277464764060639934163421755342849) ^ ((808281277464764060639934163421755342849 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_50_div_119649664615308764794567 : (13 : ZMod 808281277464764060639934163421755342849) ^ ((808281277464764060639934163421755342849 - 1) / 119649664615308764794567) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_50 : Nat.Prime 808281277464764060639934163421755342849 := by
  refine lucas_primality 808281277464764060639934163421755342849 (13 : ZMod 808281277464764060639934163421755342849) prime_B_50_pow ?_
  intro q hq hqd
  rw [prime_B_50_sub1] at hqd
  have : q ∣ [2 ^ 51, 3, 119649664615308764794567].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_50_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_50_div_3
  · have : q = 119649664615308764794567 := (Nat.prime_dvd_prime_iff_eq hq prime_119649664615308764794567).mp hdf
    subst this; exact prime_B_50_div_119649664615308764794567
private lemma pair_50 :
    Nat.Prime ((3 ^ 50 - 2847) * (2 ^ 50) - 1) ∧
    Nat.Prime ((3 ^ 50 - 2847) * (2 ^ 50) + 1) := by
  constructor
  · convert prime_A_50
  · convert prime_B_50

/- Pair for n = 51 -/
private lemma prime_126827 : Nat.Prime 126827 := by norm_num
private lemma prime_2688467 : Nat.Prime 2688467 := by norm_num
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_42299 : Nat.Prime 42299 := by norm_num
private lemma prime_3558784067_sub1 : (3558784067 - 1 : ℕ) = 2 * 23 * 31 * 59 * 42299 := by norm_num
private lemma prime_3558784067_pow : (2 : ZMod 3558784067) ^ (3558784067 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3558784067_div_2 : (2 : ZMod 3558784067) ^ ((3558784067 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3558784067_div_23 : (2 : ZMod 3558784067) ^ ((3558784067 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3558784067_div_31 : (2 : ZMod 3558784067) ^ ((3558784067 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3558784067_div_59 : (2 : ZMod 3558784067) ^ ((3558784067 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3558784067_div_42299 : (2 : ZMod 3558784067) ^ ((3558784067 - 1) / 42299) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3558784067 : Nat.Prime 3558784067 := by
  refine lucas_primality 3558784067 (2 : ZMod 3558784067) prime_3558784067_pow ?_
  intro q hq hqd
  rw [prime_3558784067_sub1] at hqd
  have : q ∣ [2, 23, 31, 59, 42299].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3558784067_div_2
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_3558784067_div_23
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_3558784067_div_31
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_3558784067_div_59
  · have : q = 42299 := (Nat.prime_dvd_prime_iff_eq hq prime_42299).mp hdf
    subst this; exact prime_3558784067_div_42299
private lemma prime_199291907753_sub1 : (199291907753 - 1 : ℕ) = 2 ^ 3 * 7 * 3558784067 := by norm_num
private lemma prime_199291907753_pow : (3 : ZMod 199291907753) ^ (199291907753 - 1) = 1 := by
  reduce_mod_char
private lemma prime_199291907753_div_2 : (3 : ZMod 199291907753) ^ ((199291907753 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_199291907753_div_7 : (3 : ZMod 199291907753) ^ ((199291907753 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_199291907753_div_3558784067 : (3 : ZMod 199291907753) ^ ((199291907753 - 1) / 3558784067) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_199291907753 : Nat.Prime 199291907753 := by
  refine lucas_primality 199291907753 (3 : ZMod 199291907753) prime_199291907753_pow ?_
  intro q hq hqd
  rw [prime_199291907753_sub1] at hqd
  have : q ∣ [2 ^ 3, 7, 3558784067].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_199291907753_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_199291907753_div_7
  · have : q = 3558784067 := (Nat.prime_dvd_prime_iff_eq hq prime_3558784067).mp hdf
    subst this; exact prime_199291907753_div_3558784067
private lemma prime_8768843941133_sub1 : (8768843941133 - 1 : ℕ) = 2 ^ 2 * 11 * 199291907753 := by norm_num
private lemma prime_8768843941133_pow : (2 : ZMod 8768843941133) ^ (8768843941133 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8768843941133_div_2 : (2 : ZMod 8768843941133) ^ ((8768843941133 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8768843941133_div_11 : (2 : ZMod 8768843941133) ^ ((8768843941133 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8768843941133_div_199291907753 : (2 : ZMod 8768843941133) ^ ((8768843941133 - 1) / 199291907753) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8768843941133 : Nat.Prime 8768843941133 := by
  refine lucas_primality 8768843941133 (2 : ZMod 8768843941133) prime_8768843941133_pow ?_
  intro q hq hqd
  rw [prime_8768843941133_sub1] at hqd
  have : q ∣ [2 ^ 2, 11, 199291907753].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_8768843941133_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_8768843941133_div_11
  · have : q = 199291907753 := (Nat.prime_dvd_prime_iff_eq hq prime_199291907753).mp hdf
    subst this; exact prime_8768843941133_div_199291907753
private lemma prime_307 : Nat.Prime 307 := by norm_num
private lemma prime_1889 : Nat.Prime 1889 := by norm_num
private lemma prime_198647 : Nat.Prime 198647 := by norm_num
private lemma prime_1151999641811_sub1 : (1151999641811 - 1 : ℕ) = 2 * 5 * 307 * 1889 * 198647 := by norm_num
private lemma prime_1151999641811_pow : (2 : ZMod 1151999641811) ^ (1151999641811 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1151999641811_div_2 : (2 : ZMod 1151999641811) ^ ((1151999641811 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1151999641811_div_5 : (2 : ZMod 1151999641811) ^ ((1151999641811 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1151999641811_div_307 : (2 : ZMod 1151999641811) ^ ((1151999641811 - 1) / 307) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1151999641811_div_1889 : (2 : ZMod 1151999641811) ^ ((1151999641811 - 1) / 1889) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1151999641811_div_198647 : (2 : ZMod 1151999641811) ^ ((1151999641811 - 1) / 198647) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1151999641811 : Nat.Prime 1151999641811 := by
  refine lucas_primality 1151999641811 (2 : ZMod 1151999641811) prime_1151999641811_pow ?_
  intro q hq hqd
  rw [prime_1151999641811_sub1] at hqd
  have : q ∣ [2, 5, 307, 1889, 198647].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1151999641811_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1151999641811_div_5
  · have : q = 307 := (Nat.prime_dvd_prime_iff_eq hq prime_307).mp hdf
    subst this; exact prime_1151999641811_div_307
  · have : q = 1889 := (Nat.prime_dvd_prime_iff_eq hq prime_1889).mp hdf
    subst this; exact prime_1151999641811_div_1889
  · have : q = 198647 := (Nat.prime_dvd_prime_iff_eq hq prime_198647).mp hdf
    subst this; exact prime_1151999641811_div_198647
private lemma prime_36863988537953_sub1 : (36863988537953 - 1 : ℕ) = 2 ^ 5 * 1151999641811 := by norm_num
private lemma prime_36863988537953_pow : (3 : ZMod 36863988537953) ^ (36863988537953 - 1) = 1 := by
  reduce_mod_char
private lemma prime_36863988537953_div_2 : (3 : ZMod 36863988537953) ^ ((36863988537953 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_36863988537953_div_1151999641811 : (3 : ZMod 36863988537953) ^ ((36863988537953 - 1) / 1151999641811) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_36863988537953 : Nat.Prime 36863988537953 := by
  refine lucas_primality 36863988537953 (3 : ZMod 36863988537953) prime_36863988537953_pow ?_
  intro q hq hqd
  rw [prime_36863988537953_sub1] at hqd
  have : q ∣ [2 ^ 5, 1151999641811].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_36863988537953_div_2
  · have : q = 1151999641811 := (Nat.prime_dvd_prime_iff_eq hq prime_1151999641811).mp hdf
    subst this; exact prime_36863988537953_div_1151999641811
private lemma prime_2424843832394292181929108052995320315903_sub1 : (2424843832394292181929108052995320315903 - 1 : ℕ) = 2 * 11 * 126827 * 2688467 * 8768843941133 * 36863988537953 := by norm_num
private lemma prime_2424843832394292181929108052995320315903_pow : (5 : ZMod 2424843832394292181929108052995320315903) ^ (2424843832394292181929108052995320315903 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2424843832394292181929108052995320315903_div_2 : (5 : ZMod 2424843832394292181929108052995320315903) ^ ((2424843832394292181929108052995320315903 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2424843832394292181929108052995320315903_div_11 : (5 : ZMod 2424843832394292181929108052995320315903) ^ ((2424843832394292181929108052995320315903 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2424843832394292181929108052995320315903_div_126827 : (5 : ZMod 2424843832394292181929108052995320315903) ^ ((2424843832394292181929108052995320315903 - 1) / 126827) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2424843832394292181929108052995320315903_div_2688467 : (5 : ZMod 2424843832394292181929108052995320315903) ^ ((2424843832394292181929108052995320315903 - 1) / 2688467) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2424843832394292181929108052995320315903_div_8768843941133 : (5 : ZMod 2424843832394292181929108052995320315903) ^ ((2424843832394292181929108052995320315903 - 1) / 8768843941133) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2424843832394292181929108052995320315903_div_36863988537953 : (5 : ZMod 2424843832394292181929108052995320315903) ^ ((2424843832394292181929108052995320315903 - 1) / 36863988537953) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2424843832394292181929108052995320315903 : Nat.Prime 2424843832394292181929108052995320315903 := by
  refine lucas_primality 2424843832394292181929108052995320315903 (5 : ZMod 2424843832394292181929108052995320315903) prime_2424843832394292181929108052995320315903_pow ?_
  intro q hq hqd
  rw [prime_2424843832394292181929108052995320315903_sub1] at hqd
  have : q ∣ [2, 11, 126827, 2688467, 8768843941133, 36863988537953].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2424843832394292181929108052995320315903_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_2424843832394292181929108052995320315903_div_11
  · have : q = 126827 := (Nat.prime_dvd_prime_iff_eq hq prime_126827).mp hdf
    subst this; exact prime_2424843832394292181929108052995320315903_div_126827
  · have : q = 2688467 := (Nat.prime_dvd_prime_iff_eq hq prime_2688467).mp hdf
    subst this; exact prime_2424843832394292181929108052995320315903_div_2688467
  · have : q = 8768843941133 := (Nat.prime_dvd_prime_iff_eq hq prime_8768843941133).mp hdf
    subst this; exact prime_2424843832394292181929108052995320315903_div_8768843941133
  · have : q = 36863988537953 := (Nat.prime_dvd_prime_iff_eq hq prime_36863988537953).mp hdf
    subst this; exact prime_2424843832394292181929108052995320315903_div_36863988537953
private lemma prime_A_51_sub1 : (4849687664788584363858216105990640631807 - 1 : ℕ) = 2 * 2424843832394292181929108052995320315903 := by norm_num
private lemma prime_A_51_pow : (5 : ZMod 4849687664788584363858216105990640631807) ^ (4849687664788584363858216105990640631807 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_51_div_2 : (5 : ZMod 4849687664788584363858216105990640631807) ^ ((4849687664788584363858216105990640631807 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_51_div_2424843832394292181929108052995320315903 : (5 : ZMod 4849687664788584363858216105990640631807) ^ ((4849687664788584363858216105990640631807 - 1) / 2424843832394292181929108052995320315903) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_51 : Nat.Prime 4849687664788584363858216105990640631807 := by
  refine lucas_primality 4849687664788584363858216105990640631807 (5 : ZMod 4849687664788584363858216105990640631807) prime_A_51_pow ?_
  intro q hq hqd
  rw [prime_A_51_sub1] at hqd
  have : q ∣ [2, 2424843832394292181929108052995320315903].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_51_div_2
  · have : q = 2424843832394292181929108052995320315903 := (Nat.prime_dvd_prime_iff_eq hq prime_2424843832394292181929108052995320315903).mp hdf
    subst this; exact prime_A_51_div_2424843832394292181929108052995320315903
private lemma prime_23333 : Nat.Prime 23333 := by norm_num
private lemma prime_977 : Nat.Prime 977 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_159629 : Nat.Prime 159629 := by norm_num
private lemma prime_6602255441_sub1 : (6602255441 - 1 : ℕ) = 2 ^ 4 * 5 * 11 * 47 * 159629 := by norm_num
private lemma prime_6602255441_pow : (7 : ZMod 6602255441) ^ (6602255441 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6602255441_div_2 : (7 : ZMod 6602255441) ^ ((6602255441 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6602255441_div_5 : (7 : ZMod 6602255441) ^ ((6602255441 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6602255441_div_11 : (7 : ZMod 6602255441) ^ ((6602255441 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6602255441_div_47 : (7 : ZMod 6602255441) ^ ((6602255441 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6602255441_div_159629 : (7 : ZMod 6602255441) ^ ((6602255441 - 1) / 159629) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6602255441 : Nat.Prime 6602255441 := by
  refine lucas_primality 6602255441 (7 : ZMod 6602255441) prime_6602255441_pow ?_
  intro q hq hqd
  rw [prime_6602255441_sub1] at hqd
  have : q ∣ [2 ^ 4, 5, 11, 47, 159629].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_6602255441_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_6602255441_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_6602255441_div_11
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_6602255441_div_47
  · have : q = 159629 := (Nat.prime_dvd_prime_iff_eq hq prime_159629).mp hdf
    subst this; exact prime_6602255441_div_159629
private lemma prime_6540709215778999_sub1 : (6540709215778999 - 1 : ℕ) = 2 * 3 * 13 ^ 2 * 977 * 6602255441 := by norm_num
private lemma prime_6540709215778999_pow : (3 : ZMod 6540709215778999) ^ (6540709215778999 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6540709215778999_div_2 : (3 : ZMod 6540709215778999) ^ ((6540709215778999 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6540709215778999_div_3 : (3 : ZMod 6540709215778999) ^ ((6540709215778999 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6540709215778999_div_13 : (3 : ZMod 6540709215778999) ^ ((6540709215778999 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6540709215778999_div_977 : (3 : ZMod 6540709215778999) ^ ((6540709215778999 - 1) / 977) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6540709215778999_div_6602255441 : (3 : ZMod 6540709215778999) ^ ((6540709215778999 - 1) / 6602255441) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6540709215778999 : Nat.Prime 6540709215778999 := by
  refine lucas_primality 6540709215778999 (3 : ZMod 6540709215778999) prime_6540709215778999_pow ?_
  intro q hq hqd
  rw [prime_6540709215778999_sub1] at hqd
  have : q ∣ [2, 3, 13 ^ 2, 977, 6602255441].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_6540709215778999_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_6540709215778999_div_3
  · have : q = 13 := prime_eq_of_dvd_prime_pow hq prime_13 hdf
    subst this; exact prime_6540709215778999_div_13
  · have : q = 977 := (Nat.prime_dvd_prime_iff_eq hq prime_977).mp hdf
    subst this; exact prime_6540709215778999_div_977
  · have : q = 6602255441 := (Nat.prime_dvd_prime_iff_eq hq prime_6602255441).mp hdf
    subst this; exact prime_6540709215778999_div_6602255441
private lemma prime_1220914945054171069337_sub1 : (1220914945054171069337 - 1 : ℕ) = 2 ^ 3 * 23333 * 6540709215778999 := by norm_num
private lemma prime_1220914945054171069337_pow : (3 : ZMod 1220914945054171069337) ^ (1220914945054171069337 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1220914945054171069337_div_2 : (3 : ZMod 1220914945054171069337) ^ ((1220914945054171069337 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1220914945054171069337_div_23333 : (3 : ZMod 1220914945054171069337) ^ ((1220914945054171069337 - 1) / 23333) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1220914945054171069337_div_6540709215778999 : (3 : ZMod 1220914945054171069337) ^ ((1220914945054171069337 - 1) / 6540709215778999) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1220914945054171069337 : Nat.Prime 1220914945054171069337 := by
  refine lucas_primality 1220914945054171069337 (3 : ZMod 1220914945054171069337) prime_1220914945054171069337_pow ?_
  intro q hq hqd
  rw [prime_1220914945054171069337_sub1] at hqd
  have : q ∣ [2 ^ 3, 23333, 6540709215778999].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1220914945054171069337_div_2
  · have : q = 23333 := (Nat.prime_dvd_prime_iff_eq hq prime_23333).mp hdf
    subst this; exact prime_1220914945054171069337_div_23333
  · have : q = 6540709215778999 := (Nat.prime_dvd_prime_iff_eq hq prime_6540709215778999).mp hdf
    subst this; exact prime_1220914945054171069337_div_6540709215778999
private lemma prime_717897987691852588770157_sub1 : (717897987691852588770157 - 1 : ℕ) = 2 ^ 2 * 3 * 7 ^ 2 * 1220914945054171069337 := by norm_num
private lemma prime_717897987691852588770157_pow : (2 : ZMod 717897987691852588770157) ^ (717897987691852588770157 - 1) = 1 := by
  reduce_mod_char
private lemma prime_717897987691852588770157_div_2 : (2 : ZMod 717897987691852588770157) ^ ((717897987691852588770157 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_717897987691852588770157_div_3 : (2 : ZMod 717897987691852588770157) ^ ((717897987691852588770157 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_717897987691852588770157_div_7 : (2 : ZMod 717897987691852588770157) ^ ((717897987691852588770157 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_717897987691852588770157_div_1220914945054171069337 : (2 : ZMod 717897987691852588770157) ^ ((717897987691852588770157 - 1) / 1220914945054171069337) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_717897987691852588770157 : Nat.Prime 717897987691852588770157 := by
  refine lucas_primality 717897987691852588770157 (2 : ZMod 717897987691852588770157) prime_717897987691852588770157_pow ?_
  intro q hq hqd
  rw [prime_717897987691852588770157_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 7 ^ 2, 1220914945054171069337].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_717897987691852588770157_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_717897987691852588770157_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_717897987691852588770157_div_7
  · have : q = 1220914945054171069337 := (Nat.prime_dvd_prime_iff_eq hq prime_1220914945054171069337).mp hdf
    subst this; exact prime_717897987691852588770157_div_1220914945054171069337
private lemma prime_B_51_sub1 : (4849687664788584363858216105990640631809 - 1 : ℕ) = 2 ^ 51 * 3 * 717897987691852588770157 := by norm_num
private lemma prime_B_51_pow : (13 : ZMod 4849687664788584363858216105990640631809) ^ (4849687664788584363858216105990640631809 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_51_div_2 : (13 : ZMod 4849687664788584363858216105990640631809) ^ ((4849687664788584363858216105990640631809 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_51_div_3 : (13 : ZMod 4849687664788584363858216105990640631809) ^ ((4849687664788584363858216105990640631809 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_51_div_717897987691852588770157 : (13 : ZMod 4849687664788584363858216105990640631809) ^ ((4849687664788584363858216105990640631809 - 1) / 717897987691852588770157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_51 : Nat.Prime 4849687664788584363858216105990640631809 := by
  refine lucas_primality 4849687664788584363858216105990640631809 (13 : ZMod 4849687664788584363858216105990640631809) prime_B_51_pow ?_
  intro q hq hqd
  rw [prime_B_51_sub1] at hqd
  have : q ∣ [2 ^ 51, 3, 717897987691852588770157].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_51_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_51_div_3
  · have : q = 717897987691852588770157 := (Nat.prime_dvd_prime_iff_eq hq prime_717897987691852588770157).mp hdf
    subst this; exact prime_B_51_div_717897987691852588770157
private lemma pair_51 :
    Nat.Prime ((3 ^ 51 - 276) * (2 ^ 51) - 1) ∧
    Nat.Prime ((3 ^ 51 - 276) * (2 ^ 51) + 1) := by
  constructor
  · convert prime_A_51
  · convert prime_B_51

/- Pair for n = 52 -/
private lemma prime_131 : Nat.Prime 131 := by norm_num
private lemma prime_25457 : Nat.Prime 25457 := by norm_num
private lemma prime_280128829_sub1 : (280128829 - 1 : ℕ) = 2 ^ 2 * 3 * 7 * 131 * 25457 := by norm_num
private lemma prime_280128829_pow : (2 : ZMod 280128829) ^ (280128829 - 1) = 1 := by
  reduce_mod_char
private lemma prime_280128829_div_2 : (2 : ZMod 280128829) ^ ((280128829 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_280128829_div_3 : (2 : ZMod 280128829) ^ ((280128829 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_280128829_div_7 : (2 : ZMod 280128829) ^ ((280128829 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_280128829_div_131 : (2 : ZMod 280128829) ^ ((280128829 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_280128829_div_25457 : (2 : ZMod 280128829) ^ ((280128829 - 1) / 25457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_280128829 : Nat.Prime 280128829 := by
  refine lucas_primality 280128829 (2 : ZMod 280128829) prime_280128829_pow ?_
  intro q hq hqd
  rw [prime_280128829_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 7, 131, 25457].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_280128829_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_280128829_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_280128829_div_7
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_280128829_div_131
  · have : q = 25457 := (Nat.prime_dvd_prime_iff_eq hq prime_25457).mp hdf
    subst this; exact prime_280128829_div_25457
private lemma prime_487 : Nat.Prime 487 := by norm_num
private lemma prime_186508339_sub1 : (186508339 - 1 : ℕ) = 2 * 3 * 29 * 31 * 71 * 487 := by norm_num
private lemma prime_186508339_pow : (3 : ZMod 186508339) ^ (186508339 - 1) = 1 := by
  reduce_mod_char
private lemma prime_186508339_div_2 : (3 : ZMod 186508339) ^ ((186508339 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_186508339_div_3 : (3 : ZMod 186508339) ^ ((186508339 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_186508339_div_29 : (3 : ZMod 186508339) ^ ((186508339 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_186508339_div_31 : (3 : ZMod 186508339) ^ ((186508339 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_186508339_div_71 : (3 : ZMod 186508339) ^ ((186508339 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_186508339_div_487 : (3 : ZMod 186508339) ^ ((186508339 - 1) / 487) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_186508339 : Nat.Prime 186508339 := by
  refine lucas_primality 186508339 (3 : ZMod 186508339) prime_186508339_pow ?_
  intro q hq hqd
  rw [prime_186508339_sub1] at hqd
  have : q ∣ [2, 3, 29, 31, 71, 487].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_186508339_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_186508339_div_3
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_186508339_div_29
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_186508339_div_31
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_186508339_div_71
  · have : q = 487 := (Nat.prime_dvd_prime_iff_eq hq prime_487).mp hdf
    subst this; exact prime_186508339_div_487
private lemma prime_2238100069_sub1 : (2238100069 - 1 : ℕ) = 2 ^ 2 * 3 * 186508339 := by norm_num
private lemma prime_2238100069_pow : (2 : ZMod 2238100069) ^ (2238100069 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2238100069_div_2 : (2 : ZMod 2238100069) ^ ((2238100069 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2238100069_div_3 : (2 : ZMod 2238100069) ^ ((2238100069 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2238100069_div_186508339 : (2 : ZMod 2238100069) ^ ((2238100069 - 1) / 186508339) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2238100069 : Nat.Prime 2238100069 := by
  refine lucas_primality 2238100069 (2 : ZMod 2238100069) prime_2238100069_pow ?_
  intro q hq hqd
  rw [prime_2238100069_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 186508339].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2238100069_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_2238100069_div_3
  · have : q = 186508339 := (Nat.prime_dvd_prime_iff_eq hq prime_186508339).mp hdf
    subst this; exact prime_2238100069_div_186508339
private lemma prime_10861 : Nat.Prime 10861 := by norm_num
private lemma prime_109 : Nat.Prime 109 := by norm_num
private lemma prime_271 : Nat.Prime 271 := by norm_num
private lemma prime_3433 : Nat.Prime 3433 := by norm_num
private lemma prime_42101 : Nat.Prime 42101 := by norm_num
private lemma prime_4414510381689959_sub1 : (4414510381689959 - 1 : ℕ) = 2 * 11 * 47 * 109 * 271 * 3433 * 42101 := by norm_num
private lemma prime_4414510381689959_pow : (11 : ZMod 4414510381689959) ^ (4414510381689959 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4414510381689959_div_2 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959_div_11 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959_div_47 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959_div_109 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959_div_271 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 271) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959_div_3433 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 3433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959_div_42101 : (11 : ZMod 4414510381689959) ^ ((4414510381689959 - 1) / 42101) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4414510381689959 : Nat.Prime 4414510381689959 := by
  refine lucas_primality 4414510381689959 (11 : ZMod 4414510381689959) prime_4414510381689959_pow ?_
  intro q hq hqd
  rw [prime_4414510381689959_sub1] at hqd
  have : q ∣ [2, 11, 47, 109, 271, 3433, 42101].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4414510381689959_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_4414510381689959_div_11
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_4414510381689959_div_47
  · have : q = 109 := (Nat.prime_dvd_prime_iff_eq hq prime_109).mp hdf
    subst this; exact prime_4414510381689959_div_109
  · have : q = 271 := (Nat.prime_dvd_prime_iff_eq hq prime_271).mp hdf
    subst this; exact prime_4414510381689959_div_271
  · have : q = 3433 := (Nat.prime_dvd_prime_iff_eq hq prime_3433).mp hdf
    subst this; exact prime_4414510381689959_div_3433
  · have : q = 42101 := (Nat.prime_dvd_prime_iff_eq hq prime_42101).mp hdf
    subst this; exact prime_4414510381689959_div_42101
private lemma prime_11602931335839384017159_sub1 : (11602931335839384017159 - 1 : ℕ) = 2 * 11 ^ 2 * 10861 * 4414510381689959 := by norm_num
private lemma prime_11602931335839384017159_pow : (7 : ZMod 11602931335839384017159) ^ (11602931335839384017159 - 1) = 1 := by
  reduce_mod_char
private lemma prime_11602931335839384017159_div_2 : (7 : ZMod 11602931335839384017159) ^ ((11602931335839384017159 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11602931335839384017159_div_11 : (7 : ZMod 11602931335839384017159) ^ ((11602931335839384017159 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11602931335839384017159_div_10861 : (7 : ZMod 11602931335839384017159) ^ ((11602931335839384017159 - 1) / 10861) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11602931335839384017159_div_4414510381689959 : (7 : ZMod 11602931335839384017159) ^ ((11602931335839384017159 - 1) / 4414510381689959) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11602931335839384017159 : Nat.Prime 11602931335839384017159 := by
  refine lucas_primality 11602931335839384017159 (7 : ZMod 11602931335839384017159) prime_11602931335839384017159_pow ?_
  intro q hq hqd
  rw [prime_11602931335839384017159_sub1] at hqd
  have : q ∣ [2, 11 ^ 2, 10861, 4414510381689959].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_11602931335839384017159_div_2
  · have : q = 11 := prime_eq_of_dvd_prime_pow hq prime_11 hdf
    subst this; exact prime_11602931335839384017159_div_11
  · have : q = 10861 := (Nat.prime_dvd_prime_iff_eq hq prime_10861).mp hdf
    subst this; exact prime_11602931335839384017159_div_10861
  · have : q = 4414510381689959 := (Nat.prime_dvd_prime_iff_eq hq prime_4414510381689959).mp hdf
    subst this; exact prime_11602931335839384017159_div_4414510381689959
private lemma prime_23205862671678768034319_sub1 : (23205862671678768034319 - 1 : ℕ) = 2 * 11602931335839384017159 := by norm_num
private lemma prime_23205862671678768034319_pow : (7 : ZMod 23205862671678768034319) ^ (23205862671678768034319 - 1) = 1 := by
  reduce_mod_char
private lemma prime_23205862671678768034319_div_2 : (7 : ZMod 23205862671678768034319) ^ ((23205862671678768034319 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23205862671678768034319_div_11602931335839384017159 : (7 : ZMod 23205862671678768034319) ^ ((23205862671678768034319 - 1) / 11602931335839384017159) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23205862671678768034319 : Nat.Prime 23205862671678768034319 := by
  refine lucas_primality 23205862671678768034319 (7 : ZMod 23205862671678768034319) prime_23205862671678768034319_pow ?_
  intro q hq hqd
  rw [prime_23205862671678768034319_sub1] at hqd
  have : q ∣ [2, 11602931335839384017159].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_23205862671678768034319_div_2
  · have : q = 11602931335839384017159 := (Nat.prime_dvd_prime_iff_eq hq prime_11602931335839384017159).mp hdf
    subst this; exact prime_23205862671678768034319_div_11602931335839384017159
private lemma prime_A_52_sub1 : (29098125988731506183139285133972199178239 - 1 : ℕ) = 2 * 280128829 * 2238100069 * 23205862671678768034319 := by norm_num
private lemma prime_A_52_pow : (7 : ZMod 29098125988731506183139285133972199178239) ^ (29098125988731506183139285133972199178239 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_52_div_2 : (7 : ZMod 29098125988731506183139285133972199178239) ^ ((29098125988731506183139285133972199178239 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_52_div_280128829 : (7 : ZMod 29098125988731506183139285133972199178239) ^ ((29098125988731506183139285133972199178239 - 1) / 280128829) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_52_div_2238100069 : (7 : ZMod 29098125988731506183139285133972199178239) ^ ((29098125988731506183139285133972199178239 - 1) / 2238100069) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_52_div_23205862671678768034319 : (7 : ZMod 29098125988731506183139285133972199178239) ^ ((29098125988731506183139285133972199178239 - 1) / 23205862671678768034319) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_52 : Nat.Prime 29098125988731506183139285133972199178239 := by
  refine lucas_primality 29098125988731506183139285133972199178239 (7 : ZMod 29098125988731506183139285133972199178239) prime_A_52_pow ?_
  intro q hq hqd
  rw [prime_A_52_sub1] at hqd
  have : q ∣ [2, 280128829, 2238100069, 23205862671678768034319].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_52_div_2
  · have : q = 280128829 := (Nat.prime_dvd_prime_iff_eq hq prime_280128829).mp hdf
    subst this; exact prime_A_52_div_280128829
  · have : q = 2238100069 := (Nat.prime_dvd_prime_iff_eq hq prime_2238100069).mp hdf
    subst this; exact prime_A_52_div_2238100069
  · have : q = 23205862671678768034319 := (Nat.prime_dvd_prime_iff_eq hq prime_23205862671678768034319).mp hdf
    subst this; exact prime_A_52_div_23205862671678768034319
private lemma prime_89 : Nat.Prime 89 := by norm_num
private lemma prime_3947 : Nat.Prime 3947 := by norm_num
private lemma prime_111253 : Nat.Prime 111253 := by norm_num
private lemma prime_386549 : Nat.Prime 386549 := by norm_num
private lemma prime_1584047 : Nat.Prime 1584047 := by norm_num
private lemma prime_B_52_sub1 : (29098125988731506183139285133972199178241 - 1 : ℕ) = 2 ^ 53 * 3 ^ 3 * 5 * 89 * 3947 * 111253 * 386549 * 1584047 := by norm_num
private lemma prime_B_52_pow : (11 : ZMod 29098125988731506183139285133972199178241) ^ (29098125988731506183139285133972199178241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_52_div_2 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_3 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_5 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_89 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_3947 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 3947) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_111253 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 111253) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_386549 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 386549) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52_div_1584047 : (11 : ZMod 29098125988731506183139285133972199178241) ^ ((29098125988731506183139285133972199178241 - 1) / 1584047) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_52 : Nat.Prime 29098125988731506183139285133972199178241 := by
  refine lucas_primality 29098125988731506183139285133972199178241 (11 : ZMod 29098125988731506183139285133972199178241) prime_B_52_pow ?_
  intro q hq hqd
  rw [prime_B_52_sub1] at hqd
  have : q ∣ [2 ^ 53, 3 ^ 3, 5, 89, 3947, 111253, 386549, 1584047].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_52_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_52_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_52_div_5
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_B_52_div_89
  · have : q = 3947 := (Nat.prime_dvd_prime_iff_eq hq prime_3947).mp hdf
    subst this; exact prime_B_52_div_3947
  · have : q = 111253 := (Nat.prime_dvd_prime_iff_eq hq prime_111253).mp hdf
    subst this; exact prime_B_52_div_111253
  · have : q = 386549 := (Nat.prime_dvd_prime_iff_eq hq prime_386549).mp hdf
    subst this; exact prime_B_52_div_386549
  · have : q = 1584047 := (Nat.prime_dvd_prime_iff_eq hq prime_1584047).mp hdf
    subst this; exact prime_B_52_div_1584047
private lemma pair_52 :
    Nat.Prime ((3 ^ 52 - 3051) * (2 ^ 52) - 1) ∧
    Nat.Prime ((3 ^ 52 - 3051) * (2 ^ 52) + 1) := by
  constructor
  · convert prime_A_52
  · convert prime_B_52

/- Pair for n = 53 -/
private lemma prime_36767 : Nat.Prime 36767 := by norm_num
private lemma prime_62143 : Nat.Prime 62143 := by norm_num
private lemma prime_27020233 : Nat.Prime 27020233 := by norm_num
private lemma prime_324242797_sub1 : (324242797 - 1 : ℕ) = 2 ^ 2 * 3 * 27020233 := by norm_num
private lemma prime_324242797_pow : (5 : ZMod 324242797) ^ (324242797 - 1) = 1 := by
  reduce_mod_char
private lemma prime_324242797_div_2 : (5 : ZMod 324242797) ^ ((324242797 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_324242797_div_3 : (5 : ZMod 324242797) ^ ((324242797 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_324242797_div_27020233 : (5 : ZMod 324242797) ^ ((324242797 - 1) / 27020233) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_324242797 : Nat.Prime 324242797 := by
  refine lucas_primality 324242797 (5 : ZMod 324242797) prime_324242797_pow ?_
  intro q hq hqd
  rw [prime_324242797_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 27020233].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_324242797_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_324242797_div_3
  · have : q = 27020233 := (Nat.prime_dvd_prime_iff_eq hq prime_27020233).mp hdf
    subst this; exact prime_324242797_div_27020233
private lemma prime_60309160243_sub1 : (60309160243 - 1 : ℕ) = 2 * 3 * 31 * 324242797 := by norm_num
private lemma prime_60309160243_pow : (2 : ZMod 60309160243) ^ (60309160243 - 1) = 1 := by
  reduce_mod_char
private lemma prime_60309160243_div_2 : (2 : ZMod 60309160243) ^ ((60309160243 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_60309160243_div_3 : (2 : ZMod 60309160243) ^ ((60309160243 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_60309160243_div_31 : (2 : ZMod 60309160243) ^ ((60309160243 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_60309160243_div_324242797 : (2 : ZMod 60309160243) ^ ((60309160243 - 1) / 324242797) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_60309160243 : Nat.Prime 60309160243 := by
  refine lucas_primality 60309160243 (2 : ZMod 60309160243) prime_60309160243_pow ?_
  intro q hq hqd
  rw [prime_60309160243_sub1] at hqd
  have : q ∣ [2, 3, 31, 324242797].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_60309160243_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_60309160243_div_3
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_60309160243_div_31
  · have : q = 324242797 := (Nat.prime_dvd_prime_iff_eq hq prime_324242797).mp hdf
    subst this; exact prime_60309160243_div_324242797
private lemma prime_3980404576039_sub1 : (3980404576039 - 1 : ℕ) = 2 * 3 * 11 * 60309160243 := by norm_num
private lemma prime_3980404576039_pow : (3 : ZMod 3980404576039) ^ (3980404576039 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3980404576039_div_2 : (3 : ZMod 3980404576039) ^ ((3980404576039 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3980404576039_div_3 : (3 : ZMod 3980404576039) ^ ((3980404576039 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3980404576039_div_11 : (3 : ZMod 3980404576039) ^ ((3980404576039 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3980404576039_div_60309160243 : (3 : ZMod 3980404576039) ^ ((3980404576039 - 1) / 60309160243) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3980404576039 : Nat.Prime 3980404576039 := by
  refine lucas_primality 3980404576039 (3 : ZMod 3980404576039) prime_3980404576039_pow ?_
  intro q hq hqd
  rw [prime_3980404576039_sub1] at hqd
  have : q ∣ [2, 3, 11, 60309160243].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3980404576039_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_3980404576039_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_3980404576039_div_11
  · have : q = 60309160243 := (Nat.prime_dvd_prime_iff_eq hq prime_60309160243).mp hdf
    subst this; exact prime_3980404576039_div_60309160243
private lemma prime_14779 : Nat.Prime 14779 := by norm_num
private lemma prime_4289 : Nat.Prime 4289 := by norm_num
private lemma prime_112349 : Nat.Prime 112349 := by norm_num
private lemma prime_46259026657_sub1 : (46259026657 - 1 : ℕ) = 2 ^ 5 * 3 * 4289 * 112349 := by norm_num
private lemma prime_46259026657_pow : (10 : ZMod 46259026657) ^ (46259026657 - 1) = 1 := by
  reduce_mod_char
private lemma prime_46259026657_div_2 : (10 : ZMod 46259026657) ^ ((46259026657 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_46259026657_div_3 : (10 : ZMod 46259026657) ^ ((46259026657 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_46259026657_div_4289 : (10 : ZMod 46259026657) ^ ((46259026657 - 1) / 4289) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_46259026657_div_112349 : (10 : ZMod 46259026657) ^ ((46259026657 - 1) / 112349) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_46259026657 : Nat.Prime 46259026657 := by
  refine lucas_primality 46259026657 (10 : ZMod 46259026657) prime_46259026657_pow ?_
  intro q hq hqd
  rw [prime_46259026657_sub1] at hqd
  have : q ∣ [2 ^ 5, 3, 4289, 112349].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_46259026657_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_46259026657_div_3
  · have : q = 4289 := (Nat.prime_dvd_prime_iff_eq hq prime_4289).mp hdf
    subst this; exact prime_46259026657_div_4289
  · have : q = 112349 := (Nat.prime_dvd_prime_iff_eq hq prime_112349).mp hdf
    subst this; exact prime_46259026657_div_112349
private lemma prime_4163312399131_sub1 : (4163312399131 - 1 : ℕ) = 2 * 3 ^ 2 * 5 * 46259026657 := by norm_num
private lemma prime_4163312399131_pow : (3 : ZMod 4163312399131) ^ (4163312399131 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4163312399131_div_2 : (3 : ZMod 4163312399131) ^ ((4163312399131 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4163312399131_div_3 : (3 : ZMod 4163312399131) ^ ((4163312399131 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4163312399131_div_5 : (3 : ZMod 4163312399131) ^ ((4163312399131 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4163312399131_div_46259026657 : (3 : ZMod 4163312399131) ^ ((4163312399131 - 1) / 46259026657) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4163312399131 : Nat.Prime 4163312399131 := by
  refine lucas_primality 4163312399131 (3 : ZMod 4163312399131) prime_4163312399131_pow ?_
  intro q hq hqd
  rw [prime_4163312399131_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 5, 46259026657].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4163312399131_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_4163312399131_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_4163312399131_div_5
  · have : q = 46259026657 := (Nat.prime_dvd_prime_iff_eq hq prime_46259026657).mp hdf
    subst this; exact prime_4163312399131_div_46259026657
private lemma prime_738355127361084589_sub1 : (738355127361084589 - 1 : ℕ) = 2 ^ 2 * 3 * 14779 * 4163312399131 := by norm_num
private lemma prime_738355127361084589_pow : (2 : ZMod 738355127361084589) ^ (738355127361084589 - 1) = 1 := by
  reduce_mod_char
private lemma prime_738355127361084589_div_2 : (2 : ZMod 738355127361084589) ^ ((738355127361084589 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_738355127361084589_div_3 : (2 : ZMod 738355127361084589) ^ ((738355127361084589 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_738355127361084589_div_14779 : (2 : ZMod 738355127361084589) ^ ((738355127361084589 - 1) / 14779) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_738355127361084589_div_4163312399131 : (2 : ZMod 738355127361084589) ^ ((738355127361084589 - 1) / 4163312399131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_738355127361084589 : Nat.Prime 738355127361084589 := by
  refine lucas_primality 738355127361084589 (2 : ZMod 738355127361084589) prime_738355127361084589_pow ?_
  intro q hq hqd
  rw [prime_738355127361084589_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 14779, 4163312399131].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_738355127361084589_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_738355127361084589_div_3
  · have : q = 14779 := (Nat.prime_dvd_prime_iff_eq hq prime_14779).mp hdf
    subst this; exact prime_738355127361084589_div_14779
  · have : q = 4163312399131 := (Nat.prime_dvd_prime_iff_eq hq prime_4163312399131).mp hdf
    subst this; exact prime_738355127361084589_div_4163312399131
private lemma prime_A_53_sub1 : (174588755932389037098917802417840904470527 - 1 : ℕ) = 2 * 13 * 36767 * 62143 * 3980404576039 * 738355127361084589 := by norm_num
private lemma prime_A_53_pow : (5 : ZMod 174588755932389037098917802417840904470527) ^ (174588755932389037098917802417840904470527 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_53_div_2 : (5 : ZMod 174588755932389037098917802417840904470527) ^ ((174588755932389037098917802417840904470527 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_53_div_13 : (5 : ZMod 174588755932389037098917802417840904470527) ^ ((174588755932389037098917802417840904470527 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_53_div_36767 : (5 : ZMod 174588755932389037098917802417840904470527) ^ ((174588755932389037098917802417840904470527 - 1) / 36767) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_53_div_62143 : (5 : ZMod 174588755932389037098917802417840904470527) ^ ((174588755932389037098917802417840904470527 - 1) / 62143) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_53_div_3980404576039 : (5 : ZMod 174588755932389037098917802417840904470527) ^ ((174588755932389037098917802417840904470527 - 1) / 3980404576039) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_53_div_738355127361084589 : (5 : ZMod 174588755932389037098917802417840904470527) ^ ((174588755932389037098917802417840904470527 - 1) / 738355127361084589) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_53 : Nat.Prime 174588755932389037098917802417840904470527 := by
  refine lucas_primality 174588755932389037098917802417840904470527 (5 : ZMod 174588755932389037098917802417840904470527) prime_A_53_pow ?_
  intro q hq hqd
  rw [prime_A_53_sub1] at hqd
  have : q ∣ [2, 13, 36767, 62143, 3980404576039, 738355127361084589].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_53_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_A_53_div_13
  · have : q = 36767 := (Nat.prime_dvd_prime_iff_eq hq prime_36767).mp hdf
    subst this; exact prime_A_53_div_36767
  · have : q = 62143 := (Nat.prime_dvd_prime_iff_eq hq prime_62143).mp hdf
    subst this; exact prime_A_53_div_62143
  · have : q = 3980404576039 := (Nat.prime_dvd_prime_iff_eq hq prime_3980404576039).mp hdf
    subst this; exact prime_A_53_div_3980404576039
  · have : q = 738355127361084589 := (Nat.prime_dvd_prime_iff_eq hq prime_738355127361084589).mp hdf
    subst this; exact prime_A_53_div_738355127361084589
private lemma prime_358571 : Nat.Prime 358571 := by norm_num
private lemma prime_322713901_sub1 : (322713901 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 ^ 2 * 358571 := by norm_num
private lemma prime_322713901_pow : (7 : ZMod 322713901) ^ (322713901 - 1) = 1 := by
  reduce_mod_char
private lemma prime_322713901_div_2 : (7 : ZMod 322713901) ^ ((322713901 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_322713901_div_3 : (7 : ZMod 322713901) ^ ((322713901 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_322713901_div_5 : (7 : ZMod 322713901) ^ ((322713901 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_322713901_div_358571 : (7 : ZMod 322713901) ^ ((322713901 - 1) / 358571) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_322713901 : Nat.Prime 322713901 := by
  refine lucas_primality 322713901 (7 : ZMod 322713901) prime_322713901_pow ?_
  intro q hq hqd
  rw [prime_322713901_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 5 ^ 2, 358571].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_322713901_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_322713901_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_322713901_div_5
  · have : q = 358571 := (Nat.prime_dvd_prime_iff_eq hq prime_358571).mp hdf
    subst this; exact prime_322713901_div_358571
private lemma prime_97 : Nat.Prime 97 := by norm_num
private lemma prime_2615227 : Nat.Prime 2615227 := by norm_num
private lemma prime_13191204989_sub1 : (13191204989 - 1 : ℕ) = 2 ^ 2 * 13 * 97 * 2615227 := by norm_num
private lemma prime_13191204989_pow : (2 : ZMod 13191204989) ^ (13191204989 - 1) = 1 := by
  reduce_mod_char
private lemma prime_13191204989_div_2 : (2 : ZMod 13191204989) ^ ((13191204989 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13191204989_div_13 : (2 : ZMod 13191204989) ^ ((13191204989 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13191204989_div_97 : (2 : ZMod 13191204989) ^ ((13191204989 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13191204989_div_2615227 : (2 : ZMod 13191204989) ^ ((13191204989 - 1) / 2615227) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13191204989 : Nat.Prime 13191204989 := by
  refine lucas_primality 13191204989 (2 : ZMod 13191204989) prime_13191204989_pow ?_
  intro q hq hqd
  rw [prime_13191204989_sub1] at hqd
  have : q ∣ [2 ^ 2, 13, 97, 2615227].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_13191204989_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_13191204989_div_13
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_13191204989_div_97
  · have : q = 2615227 := (Nat.prime_dvd_prime_iff_eq hq prime_2615227).mp hdf
    subst this; exact prime_13191204989_div_2615227
private lemma prime_26382409979_sub1 : (26382409979 - 1 : ℕ) = 2 * 13191204989 := by norm_num
private lemma prime_26382409979_pow : (2 : ZMod 26382409979) ^ (26382409979 - 1) = 1 := by
  reduce_mod_char
private lemma prime_26382409979_div_2 : (2 : ZMod 26382409979) ^ ((26382409979 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26382409979_div_13191204989 : (2 : ZMod 26382409979) ^ ((26382409979 - 1) / 13191204989) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26382409979 : Nat.Prime 26382409979 := by
  refine lucas_primality 26382409979 (2 : ZMod 26382409979) prime_26382409979_pow ?_
  intro q hq hqd
  rw [prime_26382409979_sub1] at hqd
  have : q ∣ [2, 13191204989].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_26382409979_div_2
  · have : q = 13191204989 := (Nat.prime_dvd_prime_iff_eq hq prime_13191204989).mp hdf
    subst this; exact prime_26382409979_div_13191204989
private lemma prime_52764819959_sub1 : (52764819959 - 1 : ℕ) = 2 * 26382409979 := by norm_num
private lemma prime_52764819959_pow : (11 : ZMod 52764819959) ^ (52764819959 - 1) = 1 := by
  reduce_mod_char
private lemma prime_52764819959_div_2 : (11 : ZMod 52764819959) ^ ((52764819959 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_52764819959_div_26382409979 : (11 : ZMod 52764819959) ^ ((52764819959 - 1) / 26382409979) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_52764819959 : Nat.Prime 52764819959 := by
  refine lucas_primality 52764819959 (11 : ZMod 52764819959) prime_52764819959_pow ?_
  intro q hq hqd
  rw [prime_52764819959_sub1] at hqd
  have : q ∣ [2, 26382409979].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_52764819959_div_2
  · have : q = 26382409979 := (Nat.prime_dvd_prime_iff_eq hq prime_26382409979).mp hdf
    subst this; exact prime_52764819959_div_26382409979
private lemma prime_294427695371221_sub1 : (294427695371221 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 * 31 * 52764819959 := by norm_num
private lemma prime_294427695371221_pow : (2 : ZMod 294427695371221) ^ (294427695371221 - 1) = 1 := by
  reduce_mod_char
private lemma prime_294427695371221_div_2 : (2 : ZMod 294427695371221) ^ ((294427695371221 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_294427695371221_div_3 : (2 : ZMod 294427695371221) ^ ((294427695371221 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_294427695371221_div_5 : (2 : ZMod 294427695371221) ^ ((294427695371221 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_294427695371221_div_31 : (2 : ZMod 294427695371221) ^ ((294427695371221 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_294427695371221_div_52764819959 : (2 : ZMod 294427695371221) ^ ((294427695371221 - 1) / 52764819959) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_294427695371221 : Nat.Prime 294427695371221 := by
  refine lucas_primality 294427695371221 (2 : ZMod 294427695371221) prime_294427695371221_pow ?_
  intro q hq hqd
  rw [prime_294427695371221_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 5, 31, 52764819959].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_294427695371221_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_294427695371221_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_294427695371221_div_5
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_294427695371221_div_31
  · have : q = 52764819959 := (Nat.prime_dvd_prime_iff_eq hq prime_52764819959).mp hdf
    subst this; exact prime_294427695371221_div_52764819959
private lemma prime_B_53_sub1 : (174588755932389037098917802417840904470529 - 1 : ℕ) = 2 ^ 55 * 3 * 17 * 322713901 * 294427695371221 := by norm_num
private lemma prime_B_53_pow : (14 : ZMod 174588755932389037098917802417840904470529) ^ (174588755932389037098917802417840904470529 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_53_div_2 : (14 : ZMod 174588755932389037098917802417840904470529) ^ ((174588755932389037098917802417840904470529 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_53_div_3 : (14 : ZMod 174588755932389037098917802417840904470529) ^ ((174588755932389037098917802417840904470529 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_53_div_17 : (14 : ZMod 174588755932389037098917802417840904470529) ^ ((174588755932389037098917802417840904470529 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_53_div_322713901 : (14 : ZMod 174588755932389037098917802417840904470529) ^ ((174588755932389037098917802417840904470529 - 1) / 322713901) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_53_div_294427695371221 : (14 : ZMod 174588755932389037098917802417840904470529) ^ ((174588755932389037098917802417840904470529 - 1) / 294427695371221) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_53 : Nat.Prime 174588755932389037098917802417840904470529 := by
  refine lucas_primality 174588755932389037098917802417840904470529 (14 : ZMod 174588755932389037098917802417840904470529) prime_B_53_pow ?_
  intro q hq hqd
  rw [prime_B_53_sub1] at hqd
  have : q ∣ [2 ^ 55, 3, 17, 322713901, 294427695371221].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_53_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_53_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_B_53_div_17
  · have : q = 322713901 := (Nat.prime_dvd_prime_iff_eq hq prime_322713901).mp hdf
    subst this; exact prime_B_53_div_322713901
  · have : q = 294427695371221 := (Nat.prime_dvd_prime_iff_eq hq prime_294427695371221).mp hdf
    subst this; exact prime_B_53_div_294427695371221
private lemma pair_53 :
    Nat.Prime ((3 ^ 53 - 39) * (2 ^ 53) - 1) ∧
    Nat.Prime ((3 ^ 53 - 39) * (2 ^ 53) + 1) := by
  constructor
  · convert prime_A_53
  · convert prime_B_53

/- Pair for n = 54 -/
private lemma prime_2111 : Nat.Prime 2111 := by norm_num
private lemma prime_1381 : Nat.Prime 1381 := by norm_num
private lemma prime_2677 : Nat.Prime 2677 := by norm_num
private lemma prime_36653 : Nat.Prime 36653 := by norm_num
private lemma prime_463 : Nat.Prime 463 := by norm_num
private lemma prime_9041 : Nat.Prime 9041 := by norm_num
private lemma prime_1490209949_sub1 : (1490209949 - 1 : ℕ) = 2 ^ 2 * 89 * 463 * 9041 := by norm_num
private lemma prime_1490209949_pow : (2 : ZMod 1490209949) ^ (1490209949 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1490209949_div_2 : (2 : ZMod 1490209949) ^ ((1490209949 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1490209949_div_89 : (2 : ZMod 1490209949) ^ ((1490209949 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1490209949_div_463 : (2 : ZMod 1490209949) ^ ((1490209949 - 1) / 463) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1490209949_div_9041 : (2 : ZMod 1490209949) ^ ((1490209949 - 1) / 9041) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1490209949 : Nat.Prime 1490209949 := by
  refine lucas_primality 1490209949 (2 : ZMod 1490209949) prime_1490209949_pow ?_
  intro q hq hqd
  rw [prime_1490209949_sub1] at hqd
  have : q ∣ [2 ^ 2, 89, 463, 9041].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1490209949_div_2
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_1490209949_div_89
  · have : q = 463 := (Nat.prime_dvd_prime_iff_eq hq prime_463).mp hdf
    subst this; exact prime_1490209949_div_463
  · have : q = 9041 := (Nat.prime_dvd_prime_iff_eq hq prime_9041).mp hdf
    subst this; exact prime_1490209949_div_9041
private lemma prime_12703 : Nat.Prime 12703 := by norm_num
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_943421 : Nat.Prime 943421 := by norm_num
private lemma prime_7851149563_sub1 : (7851149563 - 1 : ℕ) = 2 * 3 * 19 * 73 * 943421 := by norm_num
private lemma prime_7851149563_pow : (2 : ZMod 7851149563) ^ (7851149563 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7851149563_div_2 : (2 : ZMod 7851149563) ^ ((7851149563 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7851149563_div_3 : (2 : ZMod 7851149563) ^ ((7851149563 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7851149563_div_19 : (2 : ZMod 7851149563) ^ ((7851149563 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7851149563_div_73 : (2 : ZMod 7851149563) ^ ((7851149563 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7851149563_div_943421 : (2 : ZMod 7851149563) ^ ((7851149563 - 1) / 943421) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7851149563 : Nat.Prime 7851149563 := by
  refine lucas_primality 7851149563 (2 : ZMod 7851149563) prime_7851149563_pow ?_
  intro q hq hqd
  rw [prime_7851149563_sub1] at hqd
  have : q ∣ [2, 3, 19, 73, 943421].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_7851149563_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_7851149563_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_7851149563_div_19
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_7851149563_div_73
  · have : q = 943421 := (Nat.prime_dvd_prime_iff_eq hq prime_943421).mp hdf
    subst this; exact prime_7851149563_div_943421
private lemma prime_398932611595157_sub1 : (398932611595157 - 1 : ℕ) = 2 ^ 2 * 12703 * 7851149563 := by norm_num
private lemma prime_398932611595157_pow : (2 : ZMod 398932611595157) ^ (398932611595157 - 1) = 1 := by
  reduce_mod_char
private lemma prime_398932611595157_div_2 : (2 : ZMod 398932611595157) ^ ((398932611595157 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_398932611595157_div_12703 : (2 : ZMod 398932611595157) ^ ((398932611595157 - 1) / 12703) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_398932611595157_div_7851149563 : (2 : ZMod 398932611595157) ^ ((398932611595157 - 1) / 7851149563) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_398932611595157 : Nat.Prime 398932611595157 := by
  refine lucas_primality 398932611595157 (2 : ZMod 398932611595157) prime_398932611595157_pow ?_
  intro q hq hqd
  rw [prime_398932611595157_sub1] at hqd
  have : q ∣ [2 ^ 2, 12703, 7851149563].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_398932611595157_div_2
  · have : q = 12703 := (Nat.prime_dvd_prime_iff_eq hq prime_12703).mp hdf
    subst this; exact prime_398932611595157_div_12703
  · have : q = 7851149563 := (Nat.prime_dvd_prime_iff_eq hq prime_7851149563).mp hdf
    subst this; exact prime_398932611595157_div_7851149563
private lemma prime_116663470679961817114345608272867_sub1 : (116663470679961817114345608272867 - 1 : ℕ) = 2 * 2677 * 36653 * 1490209949 * 398932611595157 := by norm_num
private lemma prime_116663470679961817114345608272867_pow : (2 : ZMod 116663470679961817114345608272867) ^ (116663470679961817114345608272867 - 1) = 1 := by
  reduce_mod_char
private lemma prime_116663470679961817114345608272867_div_2 : (2 : ZMod 116663470679961817114345608272867) ^ ((116663470679961817114345608272867 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_116663470679961817114345608272867_div_2677 : (2 : ZMod 116663470679961817114345608272867) ^ ((116663470679961817114345608272867 - 1) / 2677) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_116663470679961817114345608272867_div_36653 : (2 : ZMod 116663470679961817114345608272867) ^ ((116663470679961817114345608272867 - 1) / 36653) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_116663470679961817114345608272867_div_1490209949 : (2 : ZMod 116663470679961817114345608272867) ^ ((116663470679961817114345608272867 - 1) / 1490209949) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_116663470679961817114345608272867_div_398932611595157 : (2 : ZMod 116663470679961817114345608272867) ^ ((116663470679961817114345608272867 - 1) / 398932611595157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_116663470679961817114345608272867 : Nat.Prime 116663470679961817114345608272867 := by
  refine lucas_primality 116663470679961817114345608272867 (2 : ZMod 116663470679961817114345608272867) prime_116663470679961817114345608272867_pow ?_
  intro q hq hqd
  rw [prime_116663470679961817114345608272867_sub1] at hqd
  have : q ∣ [2, 2677, 36653, 1490209949, 398932611595157].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_116663470679961817114345608272867_div_2
  · have : q = 2677 := (Nat.prime_dvd_prime_iff_eq hq prime_2677).mp hdf
    subst this; exact prime_116663470679961817114345608272867_div_2677
  · have : q = 36653 := (Nat.prime_dvd_prime_iff_eq hq prime_36653).mp hdf
    subst this; exact prime_116663470679961817114345608272867_div_36653
  · have : q = 1490209949 := (Nat.prime_dvd_prime_iff_eq hq prime_1490209949).mp hdf
    subst this; exact prime_116663470679961817114345608272867_div_1490209949
  · have : q = 398932611595157 := (Nat.prime_dvd_prime_iff_eq hq prime_398932611595157).mp hdf
    subst this; exact prime_116663470679961817114345608272867_div_398932611595157
private lemma prime_49622573926780398985952675787647432717_sub1 : (49622573926780398985952675787647432717 - 1 : ℕ) = 2 ^ 2 * 7 * 11 * 1381 * 116663470679961817114345608272867 := by norm_num
private lemma prime_49622573926780398985952675787647432717_pow : (2 : ZMod 49622573926780398985952675787647432717) ^ (49622573926780398985952675787647432717 - 1) = 1 := by
  reduce_mod_char
private lemma prime_49622573926780398985952675787647432717_div_2 : (2 : ZMod 49622573926780398985952675787647432717) ^ ((49622573926780398985952675787647432717 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49622573926780398985952675787647432717_div_7 : (2 : ZMod 49622573926780398985952675787647432717) ^ ((49622573926780398985952675787647432717 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49622573926780398985952675787647432717_div_11 : (2 : ZMod 49622573926780398985952675787647432717) ^ ((49622573926780398985952675787647432717 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49622573926780398985952675787647432717_div_1381 : (2 : ZMod 49622573926780398985952675787647432717) ^ ((49622573926780398985952675787647432717 - 1) / 1381) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49622573926780398985952675787647432717_div_116663470679961817114345608272867 : (2 : ZMod 49622573926780398985952675787647432717) ^ ((49622573926780398985952675787647432717 - 1) / 116663470679961817114345608272867) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49622573926780398985952675787647432717 : Nat.Prime 49622573926780398985952675787647432717 := by
  refine lucas_primality 49622573926780398985952675787647432717 (2 : ZMod 49622573926780398985952675787647432717) prime_49622573926780398985952675787647432717_pow ?_
  intro q hq hqd
  rw [prime_49622573926780398985952675787647432717_sub1] at hqd
  have : q ∣ [2 ^ 2, 7, 11, 1381, 116663470679961817114345608272867].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_49622573926780398985952675787647432717_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_49622573926780398985952675787647432717_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_49622573926780398985952675787647432717_div_11
  · have : q = 1381 := (Nat.prime_dvd_prime_iff_eq hq prime_1381).mp hdf
    subst this; exact prime_49622573926780398985952675787647432717_div_1381
  · have : q = 116663470679961817114345608272867 := (Nat.prime_dvd_prime_iff_eq hq prime_116663470679961817114345608272867).mp hdf
    subst this; exact prime_49622573926780398985952675787647432717_div_116663470679961817114345608272867
private lemma prime_A_54_sub1 : (1047532535594334222593460985877237304655871 - 1 : ℕ) = 2 * 5 * 2111 * 49622573926780398985952675787647432717 := by norm_num
private lemma prime_A_54_pow : (13 : ZMod 1047532535594334222593460985877237304655871) ^ (1047532535594334222593460985877237304655871 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_54_div_2 : (13 : ZMod 1047532535594334222593460985877237304655871) ^ ((1047532535594334222593460985877237304655871 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_54_div_5 : (13 : ZMod 1047532535594334222593460985877237304655871) ^ ((1047532535594334222593460985877237304655871 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_54_div_2111 : (13 : ZMod 1047532535594334222593460985877237304655871) ^ ((1047532535594334222593460985877237304655871 - 1) / 2111) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_54_div_49622573926780398985952675787647432717 : (13 : ZMod 1047532535594334222593460985877237304655871) ^ ((1047532535594334222593460985877237304655871 - 1) / 49622573926780398985952675787647432717) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_54 : Nat.Prime 1047532535594334222593460985877237304655871 := by
  refine lucas_primality 1047532535594334222593460985877237304655871 (13 : ZMod 1047532535594334222593460985877237304655871) prime_A_54_pow ?_
  intro q hq hqd
  rw [prime_A_54_sub1] at hqd
  have : q ∣ [2, 5, 2111, 49622573926780398985952675787647432717].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_54_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_54_div_5
  · have : q = 2111 := (Nat.prime_dvd_prime_iff_eq hq prime_2111).mp hdf
    subst this; exact prime_A_54_div_2111
  · have : q = 49622573926780398985952675787647432717 := (Nat.prime_dvd_prime_iff_eq hq prime_49622573926780398985952675787647432717).mp hdf
    subst this; exact prime_A_54_div_49622573926780398985952675787647432717
private lemma prime_91691 : Nat.Prime 91691 := by norm_num
private lemma prime_3157303 : Nat.Prime 3157303 := by norm_num
private lemma prime_118549 : Nat.Prime 118549 := by norm_num
private lemma prime_605074097_sub1 : (605074097 - 1 : ℕ) = 2 ^ 4 * 11 * 29 * 118549 := by norm_num
private lemma prime_605074097_pow : (3 : ZMod 605074097) ^ (605074097 - 1) = 1 := by
  reduce_mod_char
private lemma prime_605074097_div_2 : (3 : ZMod 605074097) ^ ((605074097 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_605074097_div_11 : (3 : ZMod 605074097) ^ ((605074097 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_605074097_div_29 : (3 : ZMod 605074097) ^ ((605074097 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_605074097_div_118549 : (3 : ZMod 605074097) ^ ((605074097 - 1) / 118549) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_605074097 : Nat.Prime 605074097 := by
  refine lucas_primality 605074097 (3 : ZMod 605074097) prime_605074097_pow ?_
  intro q hq hqd
  rw [prime_605074097_sub1] at hqd
  have : q ∣ [2 ^ 4, 11, 29, 118549].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_605074097_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_605074097_div_11
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_605074097_div_29
  · have : q = 118549 := (Nat.prime_dvd_prime_iff_eq hq prime_118549).mp hdf
    subst this; exact prime_605074097_div_118549
private lemma prime_15731926523_sub1 : (15731926523 - 1 : ℕ) = 2 * 13 * 605074097 := by norm_num
private lemma prime_15731926523_pow : (2 : ZMod 15731926523) ^ (15731926523 - 1) = 1 := by
  reduce_mod_char
private lemma prime_15731926523_div_2 : (2 : ZMod 15731926523) ^ ((15731926523 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_15731926523_div_13 : (2 : ZMod 15731926523) ^ ((15731926523 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_15731926523_div_605074097 : (2 : ZMod 15731926523) ^ ((15731926523 - 1) / 605074097) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_15731926523 : Nat.Prime 15731926523 := by
  refine lucas_primality 15731926523 (2 : ZMod 15731926523) prime_15731926523_pow ?_
  intro q hq hqd
  rw [prime_15731926523_sub1] at hqd
  have : q ∣ [2, 13, 605074097].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_15731926523_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_15731926523_div_13
  · have : q = 605074097 := (Nat.prime_dvd_prime_iff_eq hq prime_605074097).mp hdf
    subst this; exact prime_15731926523_div_605074097
private lemma prime_397363670454779753_sub1 : (397363670454779753 - 1 : ℕ) = 2 ^ 3 * 3157303 * 15731926523 := by norm_num
private lemma prime_397363670454779753_pow : (3 : ZMod 397363670454779753) ^ (397363670454779753 - 1) = 1 := by
  reduce_mod_char
private lemma prime_397363670454779753_div_2 : (3 : ZMod 397363670454779753) ^ ((397363670454779753 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_397363670454779753_div_3157303 : (3 : ZMod 397363670454779753) ^ ((397363670454779753 - 1) / 3157303) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_397363670454779753_div_15731926523 : (3 : ZMod 397363670454779753) ^ ((397363670454779753 - 1) / 15731926523) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_397363670454779753 : Nat.Prime 397363670454779753 := by
  refine lucas_primality 397363670454779753 (3 : ZMod 397363670454779753) prime_397363670454779753_pow ?_
  intro q hq hqd
  rw [prime_397363670454779753_sub1] at hqd
  have : q ∣ [2 ^ 3, 3157303, 15731926523].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_397363670454779753_div_2
  · have : q = 3157303 := (Nat.prime_dvd_prime_iff_eq hq prime_3157303).mp hdf
    subst this; exact prime_397363670454779753_div_3157303
  · have : q = 15731926523 := (Nat.prime_dvd_prime_iff_eq hq prime_15731926523).mp hdf
    subst this; exact prime_397363670454779753_div_15731926523
private lemma prime_B_54_sub1 : (1047532535594334222593460985877237304655873 - 1 : ℕ) = 2 ^ 56 * 3 * 7 * 19 * 91691 * 397363670454779753 := by norm_num
private lemma prime_B_54_pow : (5 : ZMod 1047532535594334222593460985877237304655873) ^ (1047532535594334222593460985877237304655873 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_54_div_2 : (5 : ZMod 1047532535594334222593460985877237304655873) ^ ((1047532535594334222593460985877237304655873 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_54_div_3 : (5 : ZMod 1047532535594334222593460985877237304655873) ^ ((1047532535594334222593460985877237304655873 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_54_div_7 : (5 : ZMod 1047532535594334222593460985877237304655873) ^ ((1047532535594334222593460985877237304655873 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_54_div_19 : (5 : ZMod 1047532535594334222593460985877237304655873) ^ ((1047532535594334222593460985877237304655873 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_54_div_91691 : (5 : ZMod 1047532535594334222593460985877237304655873) ^ ((1047532535594334222593460985877237304655873 - 1) / 91691) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_54_div_397363670454779753 : (5 : ZMod 1047532535594334222593460985877237304655873) ^ ((1047532535594334222593460985877237304655873 - 1) / 397363670454779753) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_54 : Nat.Prime 1047532535594334222593460985877237304655873 := by
  refine lucas_primality 1047532535594334222593460985877237304655873 (5 : ZMod 1047532535594334222593460985877237304655873) prime_B_54_pow ?_
  intro q hq hqd
  rw [prime_B_54_sub1] at hqd
  have : q ∣ [2 ^ 56, 3, 7, 19, 91691, 397363670454779753].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_54_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_54_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_54_div_7
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_54_div_19
  · have : q = 91691 := (Nat.prime_dvd_prime_iff_eq hq prime_91691).mp hdf
    subst this; exact prime_B_54_div_91691
  · have : q = 397363670454779753 := (Nat.prime_dvd_prime_iff_eq hq prime_397363670454779753).mp hdf
    subst this; exact prime_B_54_div_397363670454779753
private lemma pair_54 :
    Nat.Prime ((3 ^ 54 - 2661) * (2 ^ 54) - 1) ∧
    Nat.Prime ((3 ^ 54 - 2661) * (2 ^ 54) + 1) := by
  constructor
  · convert prime_A_54
  · convert prime_B_54

/- Pair for n = 55 -/
private lemma prime_13879 : Nat.Prime 13879 := by norm_num
private lemma prime_92064179 : Nat.Prime 92064179 := by norm_num
private lemma prime_79221041901143_sub1 : (79221041901143 - 1 : ℕ) = 2 * 31 * 13879 * 92064179 := by norm_num
private lemma prime_79221041901143_pow : (5 : ZMod 79221041901143) ^ (79221041901143 - 1) = 1 := by
  reduce_mod_char
private lemma prime_79221041901143_div_2 : (5 : ZMod 79221041901143) ^ ((79221041901143 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79221041901143_div_31 : (5 : ZMod 79221041901143) ^ ((79221041901143 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79221041901143_div_13879 : (5 : ZMod 79221041901143) ^ ((79221041901143 - 1) / 13879) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79221041901143_div_92064179 : (5 : ZMod 79221041901143) ^ ((79221041901143 - 1) / 92064179) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79221041901143 : Nat.Prime 79221041901143 := by
  refine lucas_primality 79221041901143 (5 : ZMod 79221041901143) prime_79221041901143_pow ?_
  intro q hq hqd
  rw [prime_79221041901143_sub1] at hqd
  have : q ∣ [2, 31, 13879, 92064179].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_79221041901143_div_2
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_79221041901143_div_31
  · have : q = 13879 := (Nat.prime_dvd_prime_iff_eq hq prime_13879).mp hdf
    subst this; exact prime_79221041901143_div_13879
  · have : q = 92064179 := (Nat.prime_dvd_prime_iff_eq hq prime_92064179).mp hdf
    subst this; exact prime_79221041901143_div_92064179
private lemma prime_8080546273916587_sub1 : (8080546273916587 - 1 : ℕ) = 2 * 3 * 17 * 79221041901143 := by norm_num
private lemma prime_8080546273916587_pow : (2 : ZMod 8080546273916587) ^ (8080546273916587 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8080546273916587_div_2 : (2 : ZMod 8080546273916587) ^ ((8080546273916587 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8080546273916587_div_3 : (2 : ZMod 8080546273916587) ^ ((8080546273916587 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8080546273916587_div_17 : (2 : ZMod 8080546273916587) ^ ((8080546273916587 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8080546273916587_div_79221041901143 : (2 : ZMod 8080546273916587) ^ ((8080546273916587 - 1) / 79221041901143) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8080546273916587 : Nat.Prime 8080546273916587 := by
  refine lucas_primality 8080546273916587 (2 : ZMod 8080546273916587) prime_8080546273916587_pow ?_
  intro q hq hqd
  rw [prime_8080546273916587_sub1] at hqd
  have : q ∣ [2, 3, 17, 79221041901143].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8080546273916587_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_8080546273916587_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_8080546273916587_div_17
  · have : q = 79221041901143 := (Nat.prime_dvd_prime_iff_eq hq prime_79221041901143).mp hdf
    subst this; exact prime_8080546273916587_div_79221041901143
private lemma prime_509 : Nat.Prime 509 := by norm_num
private lemma prime_119297 : Nat.Prime 119297 := by norm_num
private lemma prime_673 : Nat.Prime 673 := by norm_num
private lemma prime_215359 : Nat.Prime 215359 := by norm_num
private lemma prime_250677877_sub1 : (250677877 - 1 : ℕ) = 2 ^ 2 * 3 * 97 * 215359 := by norm_num
private lemma prime_250677877_pow : (2 : ZMod 250677877) ^ (250677877 - 1) = 1 := by
  reduce_mod_char
private lemma prime_250677877_div_2 : (2 : ZMod 250677877) ^ ((250677877 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_250677877_div_3 : (2 : ZMod 250677877) ^ ((250677877 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_250677877_div_97 : (2 : ZMod 250677877) ^ ((250677877 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_250677877_div_215359 : (2 : ZMod 250677877) ^ ((250677877 - 1) / 215359) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_250677877 : Nat.Prime 250677877 := by
  refine lucas_primality 250677877 (2 : ZMod 250677877) prime_250677877_pow ?_
  intro q hq hqd
  rw [prime_250677877_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 97, 215359].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_250677877_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_250677877_div_3
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_250677877_div_97
  · have : q = 215359 := (Nat.prime_dvd_prime_iff_eq hq prime_215359).mp hdf
    subst this; exact prime_250677877_div_215359
private lemma prime_3036711801979_sub1 : (3036711801979 - 1 : ℕ) = 2 * 3 ^ 2 * 673 * 250677877 := by norm_num
private lemma prime_3036711801979_pow : (2 : ZMod 3036711801979) ^ (3036711801979 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3036711801979_div_2 : (2 : ZMod 3036711801979) ^ ((3036711801979 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3036711801979_div_3 : (2 : ZMod 3036711801979) ^ ((3036711801979 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3036711801979_div_673 : (2 : ZMod 3036711801979) ^ ((3036711801979 - 1) / 673) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3036711801979_div_250677877 : (2 : ZMod 3036711801979) ^ ((3036711801979 - 1) / 250677877) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3036711801979 : Nat.Prime 3036711801979 := by
  refine lucas_primality 3036711801979 (2 : ZMod 3036711801979) prime_3036711801979_pow ?_
  intro q hq hqd
  rw [prime_3036711801979_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 673, 250677877].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3036711801979_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_3036711801979_div_3
  · have : q = 673 := (Nat.prime_dvd_prime_iff_eq hq prime_673).mp hdf
    subst this; exact prime_3036711801979_div_673
  · have : q = 250677877 := (Nat.prime_dvd_prime_iff_eq hq prime_250677877).mp hdf
    subst this; exact prime_3036711801979_div_250677877
private lemma prime_84822040119818866968821_sub1 : (84822040119818866968821 - 1 : ℕ) = 2 ^ 2 * 5 * 23 * 509 * 119297 * 3036711801979 := by norm_num
private lemma prime_84822040119818866968821_pow : (2 : ZMod 84822040119818866968821) ^ (84822040119818866968821 - 1) = 1 := by
  reduce_mod_char
private lemma prime_84822040119818866968821_div_2 : (2 : ZMod 84822040119818866968821) ^ ((84822040119818866968821 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_84822040119818866968821_div_5 : (2 : ZMod 84822040119818866968821) ^ ((84822040119818866968821 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_84822040119818866968821_div_23 : (2 : ZMod 84822040119818866968821) ^ ((84822040119818866968821 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_84822040119818866968821_div_509 : (2 : ZMod 84822040119818866968821) ^ ((84822040119818866968821 - 1) / 509) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_84822040119818866968821_div_119297 : (2 : ZMod 84822040119818866968821) ^ ((84822040119818866968821 - 1) / 119297) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_84822040119818866968821_div_3036711801979 : (2 : ZMod 84822040119818866968821) ^ ((84822040119818866968821 - 1) / 3036711801979) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_84822040119818866968821 : Nat.Prime 84822040119818866968821 := by
  refine lucas_primality 84822040119818866968821 (2 : ZMod 84822040119818866968821) prime_84822040119818866968821_pow ?_
  intro q hq hqd
  rw [prime_84822040119818866968821_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 23, 509, 119297, 3036711801979].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_84822040119818866968821_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_84822040119818866968821_div_5
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_84822040119818866968821_div_23
  · have : q = 509 := (Nat.prime_dvd_prime_iff_eq hq prime_509).mp hdf
    subst this; exact prime_84822040119818866968821_div_509
  · have : q = 119297 := (Nat.prime_dvd_prime_iff_eq hq prime_119297).mp hdf
    subst this; exact prime_84822040119818866968821_div_119297
  · have : q = 3036711801979 := (Nat.prime_dvd_prime_iff_eq hq prime_3036711801979).mp hdf
    subst this; exact prime_84822040119818866968821_div_3036711801979
private lemma prime_A_55_sub1 : (6285195213566005335560883729429675840110591 - 1 : ℕ) = 2 * 5 * 7 * 131 * 8080546273916587 * 84822040119818866968821 := by norm_num
private lemma prime_A_55_pow : (7 : ZMod 6285195213566005335560883729429675840110591) ^ (6285195213566005335560883729429675840110591 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_55_div_2 : (7 : ZMod 6285195213566005335560883729429675840110591) ^ ((6285195213566005335560883729429675840110591 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_55_div_5 : (7 : ZMod 6285195213566005335560883729429675840110591) ^ ((6285195213566005335560883729429675840110591 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_55_div_7 : (7 : ZMod 6285195213566005335560883729429675840110591) ^ ((6285195213566005335560883729429675840110591 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_55_div_131 : (7 : ZMod 6285195213566005335560883729429675840110591) ^ ((6285195213566005335560883729429675840110591 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_55_div_8080546273916587 : (7 : ZMod 6285195213566005335560883729429675840110591) ^ ((6285195213566005335560883729429675840110591 - 1) / 8080546273916587) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_55_div_84822040119818866968821 : (7 : ZMod 6285195213566005335560883729429675840110591) ^ ((6285195213566005335560883729429675840110591 - 1) / 84822040119818866968821) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_55 : Nat.Prime 6285195213566005335560883729429675840110591 := by
  refine lucas_primality 6285195213566005335560883729429675840110591 (7 : ZMod 6285195213566005335560883729429675840110591) prime_A_55_pow ?_
  intro q hq hqd
  rw [prime_A_55_sub1] at hqd
  have : q ∣ [2, 5, 7, 131, 8080546273916587, 84822040119818866968821].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_55_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_55_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_55_div_7
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_A_55_div_131
  · have : q = 8080546273916587 := (Nat.prime_dvd_prime_iff_eq hq prime_8080546273916587).mp hdf
    subst this; exact prime_A_55_div_8080546273916587
  · have : q = 84822040119818866968821 := (Nat.prime_dvd_prime_iff_eq hq prime_84822040119818866968821).mp hdf
    subst this; exact prime_A_55_div_84822040119818866968821
private lemma prime_400559 : Nat.Prime 400559 := by norm_num
private lemma prime_1103587 : Nat.Prime 1103587 := by norm_num
private lemma prime_107 : Nat.Prime 107 := by norm_num
private lemma prime_347 : Nat.Prime 347 := by norm_num
private lemma prime_3217 : Nat.Prime 3217 := by norm_num
private lemma prime_685130743849_sub1 : (685130743849 - 1 : ℕ) = 2 ^ 3 * 3 * 107 * 239 * 347 * 3217 := by norm_num
private lemma prime_685130743849_pow : (7 : ZMod 685130743849) ^ (685130743849 - 1) = 1 := by
  reduce_mod_char
private lemma prime_685130743849_div_2 : (7 : ZMod 685130743849) ^ ((685130743849 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_685130743849_div_3 : (7 : ZMod 685130743849) ^ ((685130743849 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_685130743849_div_107 : (7 : ZMod 685130743849) ^ ((685130743849 - 1) / 107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_685130743849_div_239 : (7 : ZMod 685130743849) ^ ((685130743849 - 1) / 239) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_685130743849_div_347 : (7 : ZMod 685130743849) ^ ((685130743849 - 1) / 347) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_685130743849_div_3217 : (7 : ZMod 685130743849) ^ ((685130743849 - 1) / 3217) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_685130743849 : Nat.Prime 685130743849 := by
  refine lucas_primality 685130743849 (7 : ZMod 685130743849) prime_685130743849_pow ?_
  intro q hq hqd
  rw [prime_685130743849_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 107, 239, 347, 3217].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_685130743849_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_685130743849_div_3
  · have : q = 107 := (Nat.prime_dvd_prime_iff_eq hq prime_107).mp hdf
    subst this; exact prime_685130743849_div_107
  · have : q = 239 := (Nat.prime_dvd_prime_iff_eq hq prime_239).mp hdf
    subst this; exact prime_685130743849_div_239
  · have : q = 347 := (Nat.prime_dvd_prime_iff_eq hq prime_347).mp hdf
    subst this; exact prime_685130743849_div_347
  · have : q = 3217 := (Nat.prime_dvd_prime_iff_eq hq prime_3217).mp hdf
    subst this; exact prime_685130743849_div_3217
private lemma prime_32886275704753_sub1 : (32886275704753 - 1 : ℕ) = 2 ^ 4 * 3 * 685130743849 := by norm_num
private lemma prime_32886275704753_pow : (5 : ZMod 32886275704753) ^ (32886275704753 - 1) = 1 := by
  reduce_mod_char
private lemma prime_32886275704753_div_2 : (5 : ZMod 32886275704753) ^ ((32886275704753 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_32886275704753_div_3 : (5 : ZMod 32886275704753) ^ ((32886275704753 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_32886275704753_div_685130743849 : (5 : ZMod 32886275704753) ^ ((32886275704753 - 1) / 685130743849) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_32886275704753 : Nat.Prime 32886275704753 := by
  refine lucas_primality 32886275704753 (5 : ZMod 32886275704753) prime_32886275704753_pow ?_
  intro q hq hqd
  rw [prime_32886275704753_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 685130743849].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_32886275704753_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_32886275704753_div_3
  · have : q = 685130743849 := (Nat.prime_dvd_prime_iff_eq hq prime_685130743849).mp hdf
    subst this; exact prime_32886275704753_div_685130743849
private lemma prime_29074868501520029845194299_sub1 : (29074868501520029845194299 - 1 : ℕ) = 2 * 400559 * 1103587 * 32886275704753 := by norm_num
private lemma prime_29074868501520029845194299_pow : (2 : ZMod 29074868501520029845194299) ^ (29074868501520029845194299 - 1) = 1 := by
  reduce_mod_char
private lemma prime_29074868501520029845194299_div_2 : (2 : ZMod 29074868501520029845194299) ^ ((29074868501520029845194299 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29074868501520029845194299_div_400559 : (2 : ZMod 29074868501520029845194299) ^ ((29074868501520029845194299 - 1) / 400559) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29074868501520029845194299_div_1103587 : (2 : ZMod 29074868501520029845194299) ^ ((29074868501520029845194299 - 1) / 1103587) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29074868501520029845194299_div_32886275704753 : (2 : ZMod 29074868501520029845194299) ^ ((29074868501520029845194299 - 1) / 32886275704753) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29074868501520029845194299 : Nat.Prime 29074868501520029845194299 := by
  refine lucas_primality 29074868501520029845194299 (2 : ZMod 29074868501520029845194299) prime_29074868501520029845194299_pow ?_
  intro q hq hqd
  rw [prime_29074868501520029845194299_sub1] at hqd
  have : q ∣ [2, 400559, 1103587, 32886275704753].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_29074868501520029845194299_div_2
  · have : q = 400559 := (Nat.prime_dvd_prime_iff_eq hq prime_400559).mp hdf
    subst this; exact prime_29074868501520029845194299_div_400559
  · have : q = 1103587 := (Nat.prime_dvd_prime_iff_eq hq prime_1103587).mp hdf
    subst this; exact prime_29074868501520029845194299_div_1103587
  · have : q = 32886275704753 := (Nat.prime_dvd_prime_iff_eq hq prime_32886275704753).mp hdf
    subst this; exact prime_29074868501520029845194299_div_32886275704753
private lemma prime_B_55_sub1 : (6285195213566005335560883729429675840110593 - 1 : ℕ) = 2 ^ 56 * 3 * 29074868501520029845194299 := by norm_num
private lemma prime_B_55_pow : (7 : ZMod 6285195213566005335560883729429675840110593) ^ (6285195213566005335560883729429675840110593 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_55_div_2 : (7 : ZMod 6285195213566005335560883729429675840110593) ^ ((6285195213566005335560883729429675840110593 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_55_div_3 : (7 : ZMod 6285195213566005335560883729429675840110593) ^ ((6285195213566005335560883729429675840110593 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_55_div_29074868501520029845194299 : (7 : ZMod 6285195213566005335560883729429675840110593) ^ ((6285195213566005335560883729429675840110593 - 1) / 29074868501520029845194299) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_55 : Nat.Prime 6285195213566005335560883729429675840110593 := by
  refine lucas_primality 6285195213566005335560883729429675840110593 (7 : ZMod 6285195213566005335560883729429675840110593) prime_B_55_pow ?_
  intro q hq hqd
  rw [prime_B_55_sub1] at hqd
  have : q ∣ [2 ^ 56, 3, 29074868501520029845194299].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_55_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_55_div_3
  · have : q = 29074868501520029845194299 := (Nat.prime_dvd_prime_iff_eq hq prime_29074868501520029845194299).mp hdf
    subst this; exact prime_B_55_div_29074868501520029845194299
private lemma pair_55 :
    Nat.Prime ((3 ^ 55 - 4713) * (2 ^ 55) - 1) ∧
    Nat.Prime ((3 ^ 55 - 4713) * (2 ^ 55) + 1) := by
  constructor
  · convert prime_A_55
  · convert prime_B_55

/- Pair for n = 56 -/
private lemma prime_24359 : Nat.Prime 24359 := by norm_num
private lemma prime_3866839 : Nat.Prime 3866839 := by norm_num
private lemma prime_565153987207_sub1 : (565153987207 - 1 : ℕ) = 2 * 3 * 24359 * 3866839 := by norm_num
private lemma prime_565153987207_pow : (5 : ZMod 565153987207) ^ (565153987207 - 1) = 1 := by
  reduce_mod_char
private lemma prime_565153987207_div_2 : (5 : ZMod 565153987207) ^ ((565153987207 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_565153987207_div_3 : (5 : ZMod 565153987207) ^ ((565153987207 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_565153987207_div_24359 : (5 : ZMod 565153987207) ^ ((565153987207 - 1) / 24359) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_565153987207_div_3866839 : (5 : ZMod 565153987207) ^ ((565153987207 - 1) / 3866839) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_565153987207 : Nat.Prime 565153987207 := by
  refine lucas_primality 565153987207 (5 : ZMod 565153987207) prime_565153987207_pow ?_
  intro q hq hqd
  rw [prime_565153987207_sub1] at hqd
  have : q ∣ [2, 3, 24359, 3866839].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_565153987207_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_565153987207_div_3
  · have : q = 24359 := (Nat.prime_dvd_prime_iff_eq hq prime_24359).mp hdf
    subst this; exact prime_565153987207_div_24359
  · have : q = 3866839 := (Nat.prime_dvd_prime_iff_eq hq prime_3866839).mp hdf
    subst this; exact prime_565153987207_div_3866839
private lemma prime_181 : Nat.Prime 181 := by norm_num
private lemma prime_22843283 : Nat.Prime 22843283 := by norm_num
private lemma prime_1141159045549_sub1 : (1141159045549 - 1 : ℕ) = 2 ^ 2 * 3 * 23 * 181 * 22843283 := by norm_num
private lemma prime_1141159045549_pow : (2 : ZMod 1141159045549) ^ (1141159045549 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1141159045549_div_2 : (2 : ZMod 1141159045549) ^ ((1141159045549 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1141159045549_div_3 : (2 : ZMod 1141159045549) ^ ((1141159045549 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1141159045549_div_23 : (2 : ZMod 1141159045549) ^ ((1141159045549 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1141159045549_div_181 : (2 : ZMod 1141159045549) ^ ((1141159045549 - 1) / 181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1141159045549_div_22843283 : (2 : ZMod 1141159045549) ^ ((1141159045549 - 1) / 22843283) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1141159045549 : Nat.Prime 1141159045549 := by
  refine lucas_primality 1141159045549 (2 : ZMod 1141159045549) prime_1141159045549_pow ?_
  intro q hq hqd
  rw [prime_1141159045549_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 23, 181, 22843283].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1141159045549_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1141159045549_div_3
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_1141159045549_div_23
  · have : q = 181 := (Nat.prime_dvd_prime_iff_eq hq prime_181).mp hdf
    subst this; exact prime_1141159045549_div_181
  · have : q = 22843283 := (Nat.prime_dvd_prime_iff_eq hq prime_22843283).mp hdf
    subst this; exact prime_1141159045549_div_22843283
private lemma prime_53 : Nat.Prime 53 := by norm_num
private lemma prime_31023263 : Nat.Prime 31023263 := by norm_num
private lemma prime_4376948083619_sub1 : (4376948083619 - 1 : ℕ) = 2 * 11 ^ 3 * 53 * 31023263 := by norm_num
private lemma prime_4376948083619_pow : (2 : ZMod 4376948083619) ^ (4376948083619 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4376948083619_div_2 : (2 : ZMod 4376948083619) ^ ((4376948083619 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4376948083619_div_11 : (2 : ZMod 4376948083619) ^ ((4376948083619 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4376948083619_div_53 : (2 : ZMod 4376948083619) ^ ((4376948083619 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4376948083619_div_31023263 : (2 : ZMod 4376948083619) ^ ((4376948083619 - 1) / 31023263) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4376948083619 : Nat.Prime 4376948083619 := by
  refine lucas_primality 4376948083619 (2 : ZMod 4376948083619) prime_4376948083619_pow ?_
  intro q hq hqd
  rw [prime_4376948083619_sub1] at hqd
  have : q ∣ [2, 11 ^ 3, 53, 31023263].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4376948083619_div_2
  · have : q = 11 := prime_eq_of_dvd_prime_pow hq prime_11 hdf
    subst this; exact prime_4376948083619_div_11
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_4376948083619_div_53
  · have : q = 31023263 := (Nat.prime_dvd_prime_iff_eq hq prime_31023263).mp hdf
    subst this; exact prime_4376948083619_div_31023263
private lemma prime_350155846689521_sub1 : (350155846689521 - 1 : ℕ) = 2 ^ 4 * 5 * 4376948083619 := by norm_num
private lemma prime_350155846689521_pow : (6 : ZMod 350155846689521) ^ (350155846689521 - 1) = 1 := by
  reduce_mod_char
private lemma prime_350155846689521_div_2 : (6 : ZMod 350155846689521) ^ ((350155846689521 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350155846689521_div_5 : (6 : ZMod 350155846689521) ^ ((350155846689521 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350155846689521_div_4376948083619 : (6 : ZMod 350155846689521) ^ ((350155846689521 - 1) / 4376948083619) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350155846689521 : Nat.Prime 350155846689521 := by
  refine lucas_primality 350155846689521 (6 : ZMod 350155846689521) prime_350155846689521_pow ?_
  intro q hq hqd
  rw [prime_350155846689521_sub1] at hqd
  have : q ∣ [2 ^ 4, 5, 4376948083619].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_350155846689521_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_350155846689521_div_5
  · have : q = 4376948083619 := (Nat.prime_dvd_prime_iff_eq hq prime_4376948083619).mp hdf
    subst this; exact prime_350155846689521_div_4376948083619
private lemma prime_265571628742225577558912248605262336251529_sub1 : (265571628742225577558912248605262336251529 - 1 : ℕ) = 2 ^ 3 * 3 * 7 ^ 2 * 565153987207 * 1141159045549 * 350155846689521 := by norm_num
private lemma prime_265571628742225577558912248605262336251529_pow : (13 : ZMod 265571628742225577558912248605262336251529) ^ (265571628742225577558912248605262336251529 - 1) = 1 := by
  reduce_mod_char
private lemma prime_265571628742225577558912248605262336251529_div_2 : (13 : ZMod 265571628742225577558912248605262336251529) ^ ((265571628742225577558912248605262336251529 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_265571628742225577558912248605262336251529_div_3 : (13 : ZMod 265571628742225577558912248605262336251529) ^ ((265571628742225577558912248605262336251529 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_265571628742225577558912248605262336251529_div_7 : (13 : ZMod 265571628742225577558912248605262336251529) ^ ((265571628742225577558912248605262336251529 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_265571628742225577558912248605262336251529_div_565153987207 : (13 : ZMod 265571628742225577558912248605262336251529) ^ ((265571628742225577558912248605262336251529 - 1) / 565153987207) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_265571628742225577558912248605262336251529_div_1141159045549 : (13 : ZMod 265571628742225577558912248605262336251529) ^ ((265571628742225577558912248605262336251529 - 1) / 1141159045549) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_265571628742225577558912248605262336251529_div_350155846689521 : (13 : ZMod 265571628742225577558912248605262336251529) ^ ((265571628742225577558912248605262336251529 - 1) / 350155846689521) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_265571628742225577558912248605262336251529 : Nat.Prime 265571628742225577558912248605262336251529 := by
  refine lucas_primality 265571628742225577558912248605262336251529 (13 : ZMod 265571628742225577558912248605262336251529) prime_265571628742225577558912248605262336251529_pow ?_
  intro q hq hqd
  rw [prime_265571628742225577558912248605262336251529_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 7 ^ 2, 565153987207, 1141159045549, 350155846689521].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_265571628742225577558912248605262336251529_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_265571628742225577558912248605262336251529_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_265571628742225577558912248605262336251529_div_7
  · have : q = 565153987207 := (Nat.prime_dvd_prime_iff_eq hq prime_565153987207).mp hdf
    subst this; exact prime_265571628742225577558912248605262336251529_div_565153987207
  · have : q = 1141159045549 := (Nat.prime_dvd_prime_iff_eq hq prime_1141159045549).mp hdf
    subst this; exact prime_265571628742225577558912248605262336251529_div_1141159045549
  · have : q = 350155846689521 := (Nat.prime_dvd_prime_iff_eq hq prime_350155846689521).mp hdf
    subst this; exact prime_265571628742225577558912248605262336251529_div_350155846689521
private lemma prime_A_56_sub1 : (37711171281396032013365539301947251747717119 - 1 : ℕ) = 2 * 71 * 265571628742225577558912248605262336251529 := by norm_num
private lemma prime_A_56_pow : (11 : ZMod 37711171281396032013365539301947251747717119) ^ (37711171281396032013365539301947251747717119 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_56_div_2 : (11 : ZMod 37711171281396032013365539301947251747717119) ^ ((37711171281396032013365539301947251747717119 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_56_div_71 : (11 : ZMod 37711171281396032013365539301947251747717119) ^ ((37711171281396032013365539301947251747717119 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_56_div_265571628742225577558912248605262336251529 : (11 : ZMod 37711171281396032013365539301947251747717119) ^ ((37711171281396032013365539301947251747717119 - 1) / 265571628742225577558912248605262336251529) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_56 : Nat.Prime 37711171281396032013365539301947251747717119 := by
  refine lucas_primality 37711171281396032013365539301947251747717119 (11 : ZMod 37711171281396032013365539301947251747717119) prime_A_56_pow ?_
  intro q hq hqd
  rw [prime_A_56_sub1] at hqd
  have : q ∣ [2, 71, 265571628742225577558912248605262336251529].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_56_div_2
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_A_56_div_71
  · have : q = 265571628742225577558912248605262336251529 := (Nat.prime_dvd_prime_iff_eq hq prime_265571628742225577558912248605262336251529).mp hdf
    subst this; exact prime_A_56_div_265571628742225577558912248605262336251529
private lemma prime_67 : Nat.Prime 67 := by norm_num
private lemma prime_379 : Nat.Prime 379 := by norm_num
private lemma prime_26107 : Nat.Prime 26107 := by norm_num
private lemma prime_853 : Nat.Prime 853 := by norm_num
private lemma prime_389 : Nat.Prime 389 := by norm_num
private lemma prime_3628506421_sub1 : (3628506421 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 * 7 * 11 * 389 * 673 := by norm_num
private lemma prime_3628506421_pow : (10 : ZMod 3628506421) ^ (3628506421 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3628506421_div_2 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421_div_3 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421_div_5 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421_div_7 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421_div_11 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421_div_389 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 389) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421_div_673 : (10 : ZMod 3628506421) ^ ((3628506421 - 1) / 673) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3628506421 : Nat.Prime 3628506421 := by
  refine lucas_primality 3628506421 (10 : ZMod 3628506421) prime_3628506421_pow ?_
  intro q hq hqd
  rw [prime_3628506421_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 5, 7, 11, 389, 673].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3628506421_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_3628506421_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_3628506421_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_3628506421_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_3628506421_div_11
  · have : q = 389 := (Nat.prime_dvd_prime_iff_eq hq prime_389).mp hdf
    subst this; exact prime_3628506421_div_389
  · have : q = 673 := (Nat.prime_dvd_prime_iff_eq hq prime_673).mp hdf
    subst this; exact prime_3628506421_div_673
private lemma prime_2024205849031903_sub1 : (2024205849031903 - 1 : ℕ) = 2 * 3 * 109 * 853 * 3628506421 := by norm_num
private lemma prime_2024205849031903_pow : (6 : ZMod 2024205849031903) ^ (2024205849031903 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2024205849031903_div_2 : (6 : ZMod 2024205849031903) ^ ((2024205849031903 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2024205849031903_div_3 : (6 : ZMod 2024205849031903) ^ ((2024205849031903 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2024205849031903_div_109 : (6 : ZMod 2024205849031903) ^ ((2024205849031903 - 1) / 109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2024205849031903_div_853 : (6 : ZMod 2024205849031903) ^ ((2024205849031903 - 1) / 853) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2024205849031903_div_3628506421 : (6 : ZMod 2024205849031903) ^ ((2024205849031903 - 1) / 3628506421) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2024205849031903 : Nat.Prime 2024205849031903 := by
  refine lucas_primality 2024205849031903 (6 : ZMod 2024205849031903) prime_2024205849031903_pow ?_
  intro q hq hqd
  rw [prime_2024205849031903_sub1] at hqd
  have : q ∣ [2, 3, 109, 853, 3628506421].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2024205849031903_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_2024205849031903_div_3
  · have : q = 109 := (Nat.prime_dvd_prime_iff_eq hq prime_109).mp hdf
    subst this; exact prime_2024205849031903_div_109
  · have : q = 853 := (Nat.prime_dvd_prime_iff_eq hq prime_853).mp hdf
    subst this; exact prime_2024205849031903_div_853
  · have : q = 3628506421 := (Nat.prime_dvd_prime_iff_eq hq prime_3628506421).mp hdf
    subst this; exact prime_2024205849031903_div_3628506421
private lemma prime_B_56_sub1 : (37711171281396032013365539301947251747717121 - 1 : ℕ) = 2 ^ 57 * 3 * 5 * 13 * 67 * 379 * 26107 * 2024205849031903 := by norm_num
private lemma prime_B_56_pow : (7 : ZMod 37711171281396032013365539301947251747717121) ^ (37711171281396032013365539301947251747717121 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_56_div_2 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_3 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_5 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_13 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_67 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 67) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_379 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 379) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_26107 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 26107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56_div_2024205849031903 : (7 : ZMod 37711171281396032013365539301947251747717121) ^ ((37711171281396032013365539301947251747717121 - 1) / 2024205849031903) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_56 : Nat.Prime 37711171281396032013365539301947251747717121 := by
  refine lucas_primality 37711171281396032013365539301947251747717121 (7 : ZMod 37711171281396032013365539301947251747717121) prime_B_56_pow ?_
  intro q hq hqd
  rw [prime_B_56_sub1] at hqd
  have : q ∣ [2 ^ 57, 3, 5, 13, 67, 379, 26107, 2024205849031903].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_56_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_56_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_56_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_56_div_13
  · have : q = 67 := (Nat.prime_dvd_prime_iff_eq hq prime_67).mp hdf
    subst this; exact prime_B_56_div_67
  · have : q = 379 := (Nat.prime_dvd_prime_iff_eq hq prime_379).mp hdf
    subst this; exact prime_B_56_div_379
  · have : q = 26107 := (Nat.prime_dvd_prime_iff_eq hq prime_26107).mp hdf
    subst this; exact prime_B_56_div_26107
  · have : q = 2024205849031903 := (Nat.prime_dvd_prime_iff_eq hq prime_2024205849031903).mp hdf
    subst this; exact prime_B_56_div_2024205849031903
private lemma pair_56 :
    Nat.Prime ((3 ^ 56 - 10851) * (2 ^ 56) - 1) ∧
    Nat.Prime ((3 ^ 56 - 10851) * (2 ^ 56) + 1) := by
  constructor
  · convert prime_A_56
  · convert prime_B_56

/- Pair for n = 57 -/
private lemma prime_996847 : Nat.Prime 996847 := by norm_num
private lemma prime_5405011 : Nat.Prime 5405011 := by norm_num
private lemma prime_7652191 : Nat.Prime 7652191 := by norm_num
private lemma prime_9310667 : Nat.Prime 9310667 := by norm_num
private lemma prime_27027589 : Nat.Prime 27027589 := by norm_num
private lemma prime_557 : Nat.Prime 557 := by norm_num
private lemma prime_1697 : Nat.Prime 1697 := by norm_num
private lemma prime_389434349_sub1 : (389434349 - 1 : ℕ) = 2 ^ 2 * 103 * 557 * 1697 := by norm_num
private lemma prime_389434349_pow : (2 : ZMod 389434349) ^ (389434349 - 1) = 1 := by
  reduce_mod_char
private lemma prime_389434349_div_2 : (2 : ZMod 389434349) ^ ((389434349 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_389434349_div_103 : (2 : ZMod 389434349) ^ ((389434349 - 1) / 103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_389434349_div_557 : (2 : ZMod 389434349) ^ ((389434349 - 1) / 557) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_389434349_div_1697 : (2 : ZMod 389434349) ^ ((389434349 - 1) / 1697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_389434349 : Nat.Prime 389434349 := by
  refine lucas_primality 389434349 (2 : ZMod 389434349) prime_389434349_pow ?_
  intro q hq hqd
  rw [prime_389434349_sub1] at hqd
  have : q ∣ [2 ^ 2, 103, 557, 1697].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_389434349_div_2
  · have : q = 103 := (Nat.prime_dvd_prime_iff_eq hq prime_103).mp hdf
    subst this; exact prime_389434349_div_103
  · have : q = 557 := (Nat.prime_dvd_prime_iff_eq hq prime_557).mp hdf
    subst this; exact prime_389434349_div_557
  · have : q = 1697 := (Nat.prime_dvd_prime_iff_eq hq prime_1697).mp hdf
    subst this; exact prime_389434349_div_1697
private lemma prime_2743976491430961967661237_sub1 : (2743976491430961967661237 - 1 : ℕ) = 2 ^ 2 * 7 * 9310667 * 27027589 * 389434349 := by norm_num
private lemma prime_2743976491430961967661237_pow : (2 : ZMod 2743976491430961967661237) ^ (2743976491430961967661237 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2743976491430961967661237_div_2 : (2 : ZMod 2743976491430961967661237) ^ ((2743976491430961967661237 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2743976491430961967661237_div_7 : (2 : ZMod 2743976491430961967661237) ^ ((2743976491430961967661237 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2743976491430961967661237_div_9310667 : (2 : ZMod 2743976491430961967661237) ^ ((2743976491430961967661237 - 1) / 9310667) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2743976491430961967661237_div_27027589 : (2 : ZMod 2743976491430961967661237) ^ ((2743976491430961967661237 - 1) / 27027589) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2743976491430961967661237_div_389434349 : (2 : ZMod 2743976491430961967661237) ^ ((2743976491430961967661237 - 1) / 389434349) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2743976491430961967661237 : Nat.Prime 2743976491430961967661237 := by
  refine lucas_primality 2743976491430961967661237 (2 : ZMod 2743976491430961967661237) prime_2743976491430961967661237_pow ?_
  intro q hq hqd
  rw [prime_2743976491430961967661237_sub1] at hqd
  have : q ∣ [2 ^ 2, 7, 9310667, 27027589, 389434349].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2743976491430961967661237_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_2743976491430961967661237_div_7
  · have : q = 9310667 := (Nat.prime_dvd_prime_iff_eq hq prime_9310667).mp hdf
    subst this; exact prime_2743976491430961967661237_div_9310667
  · have : q = 27027589 := (Nat.prime_dvd_prime_iff_eq hq prime_27027589).mp hdf
    subst this; exact prime_2743976491430961967661237_div_27027589
  · have : q = 389434349 := (Nat.prime_dvd_prime_iff_eq hq prime_389434349).mp hdf
    subst this; exact prime_2743976491430961967661237_div_389434349
private lemma prime_A_57_sub1 : (226267027688376192080196763751487607438049279 - 1 : ℕ) = 2 * 996847 * 5405011 * 7652191 * 2743976491430961967661237 := by norm_num
private lemma prime_A_57_pow : (11 : ZMod 226267027688376192080196763751487607438049279) ^ (226267027688376192080196763751487607438049279 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_57_div_2 : (11 : ZMod 226267027688376192080196763751487607438049279) ^ ((226267027688376192080196763751487607438049279 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_57_div_996847 : (11 : ZMod 226267027688376192080196763751487607438049279) ^ ((226267027688376192080196763751487607438049279 - 1) / 996847) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_57_div_5405011 : (11 : ZMod 226267027688376192080196763751487607438049279) ^ ((226267027688376192080196763751487607438049279 - 1) / 5405011) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_57_div_7652191 : (11 : ZMod 226267027688376192080196763751487607438049279) ^ ((226267027688376192080196763751487607438049279 - 1) / 7652191) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_57_div_2743976491430961967661237 : (11 : ZMod 226267027688376192080196763751487607438049279) ^ ((226267027688376192080196763751487607438049279 - 1) / 2743976491430961967661237) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_57 : Nat.Prime 226267027688376192080196763751487607438049279 := by
  refine lucas_primality 226267027688376192080196763751487607438049279 (11 : ZMod 226267027688376192080196763751487607438049279) prime_A_57_pow ?_
  intro q hq hqd
  rw [prime_A_57_sub1] at hqd
  have : q ∣ [2, 996847, 5405011, 7652191, 2743976491430961967661237].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_57_div_2
  · have : q = 996847 := (Nat.prime_dvd_prime_iff_eq hq prime_996847).mp hdf
    subst this; exact prime_A_57_div_996847
  · have : q = 5405011 := (Nat.prime_dvd_prime_iff_eq hq prime_5405011).mp hdf
    subst this; exact prime_A_57_div_5405011
  · have : q = 7652191 := (Nat.prime_dvd_prime_iff_eq hq prime_7652191).mp hdf
    subst this; exact prime_A_57_div_7652191
  · have : q = 2743976491430961967661237 := (Nat.prime_dvd_prime_iff_eq hq prime_2743976491430961967661237).mp hdf
    subst this; exact prime_A_57_div_2743976491430961967661237
private lemma prime_1429 : Nat.Prime 1429 := by norm_num
private lemma prime_2281 : Nat.Prime 2281 := by norm_num
private lemma prime_15187 : Nat.Prime 15187 := by norm_num
private lemma prime_2297 : Nat.Prime 2297 := by norm_num
private lemma prime_439253 : Nat.Prime 439253 := by norm_num
private lemma prime_133183266613_sub1 : (133183266613 - 1 : ℕ) = 2 ^ 2 * 3 * 11 * 2297 * 439253 := by norm_num
private lemma prime_133183266613_pow : (5 : ZMod 133183266613) ^ (133183266613 - 1) = 1 := by
  reduce_mod_char
private lemma prime_133183266613_div_2 : (5 : ZMod 133183266613) ^ ((133183266613 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_133183266613_div_3 : (5 : ZMod 133183266613) ^ ((133183266613 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_133183266613_div_11 : (5 : ZMod 133183266613) ^ ((133183266613 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_133183266613_div_2297 : (5 : ZMod 133183266613) ^ ((133183266613 - 1) / 2297) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_133183266613_div_439253 : (5 : ZMod 133183266613) ^ ((133183266613 - 1) / 439253) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_133183266613 : Nat.Prime 133183266613 := by
  refine lucas_primality 133183266613 (5 : ZMod 133183266613) prime_133183266613_pow ?_
  intro q hq hqd
  rw [prime_133183266613_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 11, 2297, 439253].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_133183266613_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_133183266613_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_133183266613_div_11
  · have : q = 2297 := (Nat.prime_dvd_prime_iff_eq hq prime_2297).mp hdf
    subst this; exact prime_133183266613_div_2297
  · have : q = 439253 := (Nat.prime_dvd_prime_iff_eq hq prime_439253).mp hdf
    subst this; exact prime_133183266613_div_439253
private lemma prime_4069260811969213414303_sub1 : (4069260811969213414303 - 1 : ℕ) = 2 * 3 ^ 2 * 7 ^ 2 * 2281 * 15187 * 133183266613 := by norm_num
private lemma prime_4069260811969213414303_pow : (3 : ZMod 4069260811969213414303) ^ (4069260811969213414303 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4069260811969213414303_div_2 : (3 : ZMod 4069260811969213414303) ^ ((4069260811969213414303 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4069260811969213414303_div_3 : (3 : ZMod 4069260811969213414303) ^ ((4069260811969213414303 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4069260811969213414303_div_7 : (3 : ZMod 4069260811969213414303) ^ ((4069260811969213414303 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4069260811969213414303_div_2281 : (3 : ZMod 4069260811969213414303) ^ ((4069260811969213414303 - 1) / 2281) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4069260811969213414303_div_15187 : (3 : ZMod 4069260811969213414303) ^ ((4069260811969213414303 - 1) / 15187) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4069260811969213414303_div_133183266613 : (3 : ZMod 4069260811969213414303) ^ ((4069260811969213414303 - 1) / 133183266613) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4069260811969213414303 : Nat.Prime 4069260811969213414303 := by
  refine lucas_primality 4069260811969213414303 (3 : ZMod 4069260811969213414303) prime_4069260811969213414303_pow ?_
  intro q hq hqd
  rw [prime_4069260811969213414303_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 7 ^ 2, 2281, 15187, 133183266613].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4069260811969213414303_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_4069260811969213414303_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_4069260811969213414303_div_7
  · have : q = 2281 := (Nat.prime_dvd_prime_iff_eq hq prime_2281).mp hdf
    subst this; exact prime_4069260811969213414303_div_2281
  · have : q = 15187 := (Nat.prime_dvd_prime_iff_eq hq prime_15187).mp hdf
    subst this; exact prime_4069260811969213414303_div_15187
  · have : q = 133183266613 := (Nat.prime_dvd_prime_iff_eq hq prime_133183266613).mp hdf
    subst this; exact prime_4069260811969213414303_div_133183266613
private lemma prime_B_57_sub1 : (226267027688376192080196763751487607438049281 - 1 : ℕ) = 2 ^ 58 * 3 ^ 3 * 5 * 1429 * 4069260811969213414303 := by norm_num
private lemma prime_B_57_pow : (13 : ZMod 226267027688376192080196763751487607438049281) ^ (226267027688376192080196763751487607438049281 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_57_div_2 : (13 : ZMod 226267027688376192080196763751487607438049281) ^ ((226267027688376192080196763751487607438049281 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_57_div_3 : (13 : ZMod 226267027688376192080196763751487607438049281) ^ ((226267027688376192080196763751487607438049281 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_57_div_5 : (13 : ZMod 226267027688376192080196763751487607438049281) ^ ((226267027688376192080196763751487607438049281 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_57_div_1429 : (13 : ZMod 226267027688376192080196763751487607438049281) ^ ((226267027688376192080196763751487607438049281 - 1) / 1429) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_57_div_4069260811969213414303 : (13 : ZMod 226267027688376192080196763751487607438049281) ^ ((226267027688376192080196763751487607438049281 - 1) / 4069260811969213414303) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_57 : Nat.Prime 226267027688376192080196763751487607438049281 := by
  refine lucas_primality 226267027688376192080196763751487607438049281 (13 : ZMod 226267027688376192080196763751487607438049281) prime_B_57_pow ?_
  intro q hq hqd
  rw [prime_B_57_sub1] at hqd
  have : q ∣ [2 ^ 58, 3 ^ 3, 5, 1429, 4069260811969213414303].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_57_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_57_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_57_div_5
  · have : q = 1429 := (Nat.prime_dvd_prime_iff_eq hq prime_1429).mp hdf
    subst this; exact prime_B_57_div_1429
  · have : q = 4069260811969213414303 := (Nat.prime_dvd_prime_iff_eq hq prime_4069260811969213414303).mp hdf
    subst this; exact prime_B_57_div_4069260811969213414303
private lemma pair_57 :
    Nat.Prime ((3 ^ 57 - 8073) * (2 ^ 57) - 1) ∧
    Nat.Prime ((3 ^ 57 - 8073) * (2 ^ 57) + 1) := by
  constructor
  · convert prime_A_57
  · convert prime_B_57

/- Pair for n = 58 -/
private lemma prime_269 : Nat.Prime 269 := by norm_num
private lemma prime_12758903 : Nat.Prime 12758903 := by norm_num
private lemma prime_21493229 : Nat.Prime 21493229 := by norm_num
private lemma prime_6581520575226889_sub1 : (6581520575226889 - 1 : ℕ) = 2 ^ 3 * 3 * 12758903 * 21493229 := by norm_num
private lemma prime_6581520575226889_pow : (11 : ZMod 6581520575226889) ^ (6581520575226889 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6581520575226889_div_2 : (11 : ZMod 6581520575226889) ^ ((6581520575226889 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6581520575226889_div_3 : (11 : ZMod 6581520575226889) ^ ((6581520575226889 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6581520575226889_div_12758903 : (11 : ZMod 6581520575226889) ^ ((6581520575226889 - 1) / 12758903) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6581520575226889_div_21493229 : (11 : ZMod 6581520575226889) ^ ((6581520575226889 - 1) / 21493229) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6581520575226889 : Nat.Prime 6581520575226889 := by
  refine lucas_primality 6581520575226889 (11 : ZMod 6581520575226889) prime_6581520575226889_pow ?_
  intro q hq hqd
  rw [prime_6581520575226889_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 12758903, 21493229].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_6581520575226889_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_6581520575226889_div_3
  · have : q = 12758903 := (Nat.prime_dvd_prime_iff_eq hq prime_12758903).mp hdf
    subst this; exact prime_6581520575226889_div_12758903
  · have : q = 21493229 := (Nat.prime_dvd_prime_iff_eq hq prime_21493229).mp hdf
    subst this; exact prime_6581520575226889_div_21493229
private lemma prime_21245148416832397693_sub1 : (21245148416832397693 - 1 : ℕ) = 2 ^ 2 * 3 * 269 * 6581520575226889 := by norm_num
private lemma prime_21245148416832397693_pow : (6 : ZMod 21245148416832397693) ^ (21245148416832397693 - 1) = 1 := by
  reduce_mod_char
private lemma prime_21245148416832397693_div_2 : (6 : ZMod 21245148416832397693) ^ ((21245148416832397693 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21245148416832397693_div_3 : (6 : ZMod 21245148416832397693) ^ ((21245148416832397693 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21245148416832397693_div_269 : (6 : ZMod 21245148416832397693) ^ ((21245148416832397693 - 1) / 269) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21245148416832397693_div_6581520575226889 : (6 : ZMod 21245148416832397693) ^ ((21245148416832397693 - 1) / 6581520575226889) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21245148416832397693 : Nat.Prime 21245148416832397693 := by
  refine lucas_primality 21245148416832397693 (6 : ZMod 21245148416832397693) prime_21245148416832397693_pow ?_
  intro q hq hqd
  rw [prime_21245148416832397693_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 269, 6581520575226889].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_21245148416832397693_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_21245148416832397693_div_3
  · have : q = 269 := (Nat.prime_dvd_prime_iff_eq hq prime_269).mp hdf
    subst this; exact prime_21245148416832397693_div_269
  · have : q = 6581520575226889 := (Nat.prime_dvd_prime_iff_eq hq prime_6581520575226889).mp hdf
    subst this; exact prime_21245148416832397693_div_6581520575226889
private lemma prime_4799 : Nat.Prime 4799 := by norm_num
private lemma prime_8293 : Nat.Prime 8293 := by norm_num
private lemma prime_10331197 : Nat.Prime 10331197 := by norm_num
private lemma prime_26270693 : Nat.Prime 26270693 := by norm_num
private lemma prime_1879463239841782197753979_sub1 : (1879463239841782197753979 - 1 : ℕ) = 2 * 3 * 29 * 4799 * 8293 * 10331197 * 26270693 := by norm_num
private lemma prime_1879463239841782197753979_pow : (2 : ZMod 1879463239841782197753979) ^ (1879463239841782197753979 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1879463239841782197753979_div_2 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979_div_3 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979_div_29 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979_div_4799 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 4799) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979_div_8293 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 8293) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979_div_10331197 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 10331197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979_div_26270693 : (2 : ZMod 1879463239841782197753979) ^ ((1879463239841782197753979 - 1) / 26270693) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1879463239841782197753979 : Nat.Prime 1879463239841782197753979 := by
  refine lucas_primality 1879463239841782197753979 (2 : ZMod 1879463239841782197753979) prime_1879463239841782197753979_pow ?_
  intro q hq hqd
  rw [prime_1879463239841782197753979_sub1] at hqd
  have : q ∣ [2, 3, 29, 4799, 8293, 10331197, 26270693].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1879463239841782197753979_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1879463239841782197753979_div_3
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_1879463239841782197753979_div_29
  · have : q = 4799 := (Nat.prime_dvd_prime_iff_eq hq prime_4799).mp hdf
    subst this; exact prime_1879463239841782197753979_div_4799
  · have : q = 8293 := (Nat.prime_dvd_prime_iff_eq hq prime_8293).mp hdf
    subst this; exact prime_1879463239841782197753979_div_8293
  · have : q = 10331197 := (Nat.prime_dvd_prime_iff_eq hq prime_10331197).mp hdf
    subst this; exact prime_1879463239841782197753979_div_10331197
  · have : q = 26270693 := (Nat.prime_dvd_prime_iff_eq hq prime_26270693).mp hdf
    subst this; exact prime_1879463239841782197753979_div_26270693
private lemma prime_A_58_sub1 : (1357602166130257152481186730462848960639795199 - 1 : ℕ) = 2 * 17 * 21245148416832397693 * 1879463239841782197753979 := by norm_num
private lemma prime_A_58_pow : (7 : ZMod 1357602166130257152481186730462848960639795199) ^ (1357602166130257152481186730462848960639795199 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_58_div_2 : (7 : ZMod 1357602166130257152481186730462848960639795199) ^ ((1357602166130257152481186730462848960639795199 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_58_div_17 : (7 : ZMod 1357602166130257152481186730462848960639795199) ^ ((1357602166130257152481186730462848960639795199 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_58_div_21245148416832397693 : (7 : ZMod 1357602166130257152481186730462848960639795199) ^ ((1357602166130257152481186730462848960639795199 - 1) / 21245148416832397693) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_58_div_1879463239841782197753979 : (7 : ZMod 1357602166130257152481186730462848960639795199) ^ ((1357602166130257152481186730462848960639795199 - 1) / 1879463239841782197753979) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_58 : Nat.Prime 1357602166130257152481186730462848960639795199 := by
  refine lucas_primality 1357602166130257152481186730462848960639795199 (7 : ZMod 1357602166130257152481186730462848960639795199) prime_A_58_pow ?_
  intro q hq hqd
  rw [prime_A_58_sub1] at hqd
  have : q ∣ [2, 17, 21245148416832397693, 1879463239841782197753979].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_58_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_A_58_div_17
  · have : q = 21245148416832397693 := (Nat.prime_dvd_prime_iff_eq hq prime_21245148416832397693).mp hdf
    subst this; exact prime_A_58_div_21245148416832397693
  · have : q = 1879463239841782197753979 := (Nat.prime_dvd_prime_iff_eq hq prime_1879463239841782197753979).mp hdf
    subst this; exact prime_A_58_div_1879463239841782197753979
private lemma prime_538001 : Nat.Prime 538001 := by norm_num
private lemma prime_52733 : Nat.Prime 52733 := by norm_num
private lemma prime_60923 : Nat.Prime 60923 := by norm_num
private lemma prime_31178311187211151_sub1 : (31178311187211151 - 1 : ℕ) = 2 * 3 * 5 ^ 2 * 23 * 29 * 97 * 52733 * 60923 := by norm_num
private lemma prime_31178311187211151_pow : (12 : ZMod 31178311187211151) ^ (31178311187211151 - 1) = 1 := by
  reduce_mod_char
private lemma prime_31178311187211151_div_2 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_3 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_5 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_23 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_29 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_97 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_52733 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 52733) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151_div_60923 : (12 : ZMod 31178311187211151) ^ ((31178311187211151 - 1) / 60923) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31178311187211151 : Nat.Prime 31178311187211151 := by
  refine lucas_primality 31178311187211151 (12 : ZMod 31178311187211151) prime_31178311187211151_pow ?_
  intro q hq hqd
  rw [prime_31178311187211151_sub1] at hqd
  have : q ∣ [2, 3, 5 ^ 2, 23, 29, 97, 52733, 60923].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_31178311187211151_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_31178311187211151_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_31178311187211151_div_5
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_31178311187211151_div_23
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_31178311187211151_div_29
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_31178311187211151_div_97
  · have : q = 52733 := (Nat.prime_dvd_prime_iff_eq hq prime_52733).mp hdf
    subst this; exact prime_31178311187211151_div_52733
  · have : q = 60923 := (Nat.prime_dvd_prime_iff_eq hq prime_60923).mp hdf
    subst this; exact prime_31178311187211151_div_60923
private lemma prime_B_58_sub1 : (1357602166130257152481186730462848960639795201 - 1 : ℕ) = 2 ^ 63 * 3 ^ 3 * 5 ^ 2 * 13 * 538001 * 31178311187211151 := by norm_num
private lemma prime_B_58_pow : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ (1357602166130257152481186730462848960639795201 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_58_div_2 : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ ((1357602166130257152481186730462848960639795201 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_58_div_3 : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ ((1357602166130257152481186730462848960639795201 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_58_div_5 : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ ((1357602166130257152481186730462848960639795201 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_58_div_13 : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ ((1357602166130257152481186730462848960639795201 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_58_div_538001 : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ ((1357602166130257152481186730462848960639795201 - 1) / 538001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_58_div_31178311187211151 : (7 : ZMod 1357602166130257152481186730462848960639795201) ^ ((1357602166130257152481186730462848960639795201 - 1) / 31178311187211151) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_58 : Nat.Prime 1357602166130257152481186730462848960639795201 := by
  refine lucas_primality 1357602166130257152481186730462848960639795201 (7 : ZMod 1357602166130257152481186730462848960639795201) prime_B_58_pow ?_
  intro q hq hqd
  rw [prime_B_58_sub1] at hqd
  have : q ∣ [2 ^ 63, 3 ^ 3, 5 ^ 2, 13, 538001, 31178311187211151].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_58_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_58_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_B_58_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_58_div_13
  · have : q = 538001 := (Nat.prime_dvd_prime_iff_eq hq prime_538001).mp hdf
    subst this; exact prime_B_58_div_538001
  · have : q = 31178311187211151 := (Nat.prime_dvd_prime_iff_eq hq prime_31178311187211151).mp hdf
    subst this; exact prime_B_58_div_31178311187211151
private lemma pair_58 :
    Nat.Prime ((3 ^ 58 - 2889) * (2 ^ 58) - 1) ∧
    Nat.Prime ((3 ^ 58 - 2889) * (2 ^ 58) + 1) := by
  constructor
  · convert prime_A_58
  · convert prime_B_58

/- Pair for n = 59 -/
private lemma prime_11057239 : Nat.Prime 11057239 := by norm_num
private lemma prime_1433 : Nat.Prime 1433 := by norm_num
private lemma prime_8537 : Nat.Prime 8537 := by norm_num
private lemma prime_122335211_sub1 : (122335211 - 1 : ℕ) = 2 * 5 * 1433 * 8537 := by norm_num
private lemma prime_122335211_pow : (2 : ZMod 122335211) ^ (122335211 - 1) = 1 := by
  reduce_mod_char
private lemma prime_122335211_div_2 : (2 : ZMod 122335211) ^ ((122335211 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_122335211_div_5 : (2 : ZMod 122335211) ^ ((122335211 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_122335211_div_1433 : (2 : ZMod 122335211) ^ ((122335211 - 1) / 1433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_122335211_div_8537 : (2 : ZMod 122335211) ^ ((122335211 - 1) / 8537) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_122335211 : Nat.Prime 122335211 := by
  refine lucas_primality 122335211 (2 : ZMod 122335211) prime_122335211_pow ?_
  intro q hq hqd
  rw [prime_122335211_sub1] at hqd
  have : q ∣ [2, 5, 1433, 8537].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_122335211_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_122335211_div_5
  · have : q = 1433 := (Nat.prime_dvd_prime_iff_eq hq prime_1433).mp hdf
    subst this; exact prime_122335211_div_1433
  · have : q = 8537 := (Nat.prime_dvd_prime_iff_eq hq prime_8537).mp hdf
    subst this; exact prime_122335211_div_8537
private lemma prime_2705379332284859_sub1 : (2705379332284859 - 1 : ℕ) = 2 * 11057239 * 122335211 := by norm_num
private lemma prime_2705379332284859_pow : (2 : ZMod 2705379332284859) ^ (2705379332284859 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2705379332284859_div_2 : (2 : ZMod 2705379332284859) ^ ((2705379332284859 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2705379332284859_div_11057239 : (2 : ZMod 2705379332284859) ^ ((2705379332284859 - 1) / 11057239) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2705379332284859_div_122335211 : (2 : ZMod 2705379332284859) ^ ((2705379332284859 - 1) / 122335211) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2705379332284859 : Nat.Prime 2705379332284859 := by
  refine lucas_primality 2705379332284859 (2 : ZMod 2705379332284859) prime_2705379332284859_pow ?_
  intro q hq hqd
  rw [prime_2705379332284859_sub1] at hqd
  have : q ∣ [2, 11057239, 122335211].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2705379332284859_div_2
  · have : q = 11057239 := (Nat.prime_dvd_prime_iff_eq hq prime_11057239).mp hdf
    subst this; exact prime_2705379332284859_div_11057239
  · have : q = 122335211 := (Nat.prime_dvd_prime_iff_eq hq prime_122335211).mp hdf
    subst this; exact prime_2705379332284859_div_122335211
private lemma prime_5410758664569719_sub1 : (5410758664569719 - 1 : ℕ) = 2 * 2705379332284859 := by norm_num
private lemma prime_5410758664569719_pow : (13 : ZMod 5410758664569719) ^ (5410758664569719 - 1) = 1 := by
  reduce_mod_char
private lemma prime_5410758664569719_div_2 : (13 : ZMod 5410758664569719) ^ ((5410758664569719 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5410758664569719_div_2705379332284859 : (13 : ZMod 5410758664569719) ^ ((5410758664569719 - 1) / 2705379332284859) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5410758664569719 : Nat.Prime 5410758664569719 := by
  refine lucas_primality 5410758664569719 (13 : ZMod 5410758664569719) prime_5410758664569719_pow ?_
  intro q hq hqd
  rw [prime_5410758664569719_sub1] at hqd
  have : q ∣ [2, 2705379332284859].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_5410758664569719_div_2
  · have : q = 2705379332284859 := (Nat.prime_dvd_prime_iff_eq hq prime_2705379332284859).mp hdf
    subst this; exact prime_5410758664569719_div_2705379332284859
private lemma prime_293 : Nat.Prime 293 := by norm_num
private lemma prime_547 : Nat.Prime 547 := by norm_num
private lemma prime_1367 : Nat.Prime 1367 := by norm_num
private lemma prime_167495777_sub1 : (167495777 - 1 : ℕ) = 2 ^ 5 * 7 * 547 * 1367 := by norm_num
private lemma prime_167495777_pow : (3 : ZMod 167495777) ^ (167495777 - 1) = 1 := by
  reduce_mod_char
private lemma prime_167495777_div_2 : (3 : ZMod 167495777) ^ ((167495777 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167495777_div_7 : (3 : ZMod 167495777) ^ ((167495777 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167495777_div_547 : (3 : ZMod 167495777) ^ ((167495777 - 1) / 547) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167495777_div_1367 : (3 : ZMod 167495777) ^ ((167495777 - 1) / 1367) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_167495777 : Nat.Prime 167495777 := by
  refine lucas_primality 167495777 (3 : ZMod 167495777) prime_167495777_pow ?_
  intro q hq hqd
  rw [prime_167495777_sub1] at hqd
  have : q ∣ [2 ^ 5, 7, 547, 1367].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_167495777_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_167495777_div_7
  · have : q = 547 := (Nat.prime_dvd_prime_iff_eq hq prime_547).mp hdf
    subst this; exact prime_167495777_div_547
  · have : q = 1367 := (Nat.prime_dvd_prime_iff_eq hq prime_1367).mp hdf
    subst this; exact prime_167495777_div_1367
private lemma prime_47623 : Nat.Prime 47623 := by norm_num
private lemma prime_288595381_sub1 : (288595381 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 101 * 47623 := by norm_num
private lemma prime_288595381_pow : (2 : ZMod 288595381) ^ (288595381 - 1) = 1 := by
  reduce_mod_char
private lemma prime_288595381_div_2 : (2 : ZMod 288595381) ^ ((288595381 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_288595381_div_3 : (2 : ZMod 288595381) ^ ((288595381 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_288595381_div_5 : (2 : ZMod 288595381) ^ ((288595381 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_288595381_div_101 : (2 : ZMod 288595381) ^ ((288595381 - 1) / 101) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_288595381_div_47623 : (2 : ZMod 288595381) ^ ((288595381 - 1) / 47623) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_288595381 : Nat.Prime 288595381 := by
  refine lucas_primality 288595381 (2 : ZMod 288595381) prime_288595381_pow ?_
  intro q hq hqd
  rw [prime_288595381_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 101, 47623].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_288595381_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_288595381_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_288595381_div_5
  · have : q = 101 := (Nat.prime_dvd_prime_iff_eq hq prime_101).mp hdf
    subst this; exact prime_288595381_div_101
  · have : q = 47623 := (Nat.prime_dvd_prime_iff_eq hq prime_47623).mp hdf
    subst this; exact prime_288595381_div_47623
private lemma prime_311590019855562114503_sub1 : (311590019855562114503 - 1 : ℕ) = 2 * 11 * 293 * 167495777 * 288595381 := by norm_num
private lemma prime_311590019855562114503_pow : (5 : ZMod 311590019855562114503) ^ (311590019855562114503 - 1) = 1 := by
  reduce_mod_char
private lemma prime_311590019855562114503_div_2 : (5 : ZMod 311590019855562114503) ^ ((311590019855562114503 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_311590019855562114503_div_11 : (5 : ZMod 311590019855562114503) ^ ((311590019855562114503 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_311590019855562114503_div_293 : (5 : ZMod 311590019855562114503) ^ ((311590019855562114503 - 1) / 293) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_311590019855562114503_div_167495777 : (5 : ZMod 311590019855562114503) ^ ((311590019855562114503 - 1) / 167495777) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_311590019855562114503_div_288595381 : (5 : ZMod 311590019855562114503) ^ ((311590019855562114503 - 1) / 288595381) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_311590019855562114503 : Nat.Prime 311590019855562114503 := by
  refine lucas_primality 311590019855562114503 (5 : ZMod 311590019855562114503) prime_311590019855562114503_pow ?_
  intro q hq hqd
  rw [prime_311590019855562114503_sub1] at hqd
  have : q ∣ [2, 11, 293, 167495777, 288595381].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_311590019855562114503_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_311590019855562114503_div_11
  · have : q = 293 := (Nat.prime_dvd_prime_iff_eq hq prime_293).mp hdf
    subst this; exact prime_311590019855562114503_div_293
  · have : q = 167495777 := (Nat.prime_dvd_prime_iff_eq hq prime_167495777).mp hdf
    subst this; exact prime_311590019855562114503_div_167495777
  · have : q = 288595381 := (Nat.prime_dvd_prime_iff_eq hq prime_288595381).mp hdf
    subst this; exact prime_311590019855562114503_div_288595381
private lemma prime_336517221444007083663241_sub1 : (336517221444007083663241 - 1 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 * 311590019855562114503 := by norm_num
private lemma prime_336517221444007083663241_pow : (13 : ZMod 336517221444007083663241) ^ (336517221444007083663241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_336517221444007083663241_div_2 : (13 : ZMod 336517221444007083663241) ^ ((336517221444007083663241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_336517221444007083663241_div_3 : (13 : ZMod 336517221444007083663241) ^ ((336517221444007083663241 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_336517221444007083663241_div_5 : (13 : ZMod 336517221444007083663241) ^ ((336517221444007083663241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_336517221444007083663241_div_311590019855562114503 : (13 : ZMod 336517221444007083663241) ^ ((336517221444007083663241 - 1) / 311590019855562114503) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_336517221444007083663241 : Nat.Prime 336517221444007083663241 := by
  refine lucas_primality 336517221444007083663241 (13 : ZMod 336517221444007083663241) prime_336517221444007083663241_pow ?_
  intro q hq hqd
  rw [prime_336517221444007083663241_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 3, 5, 311590019855562114503].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_336517221444007083663241_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_336517221444007083663241_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_336517221444007083663241_div_5
  · have : q = 311590019855562114503 := (Nat.prime_dvd_prime_iff_eq hq prime_311590019855562114503).mp hdf
    subst this; exact prime_336517221444007083663241_div_311590019855562114503
private lemma prime_4686773876168896959083497242355704586144147_sub1 : (4686773876168896959083497242355704586144147 - 1 : ℕ) = 2 * 3 ^ 2 * 11 * 13 * 5410758664569719 * 336517221444007083663241 := by norm_num
private lemma prime_4686773876168896959083497242355704586144147_pow : (2 : ZMod 4686773876168896959083497242355704586144147) ^ (4686773876168896959083497242355704586144147 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4686773876168896959083497242355704586144147_div_2 : (2 : ZMod 4686773876168896959083497242355704586144147) ^ ((4686773876168896959083497242355704586144147 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4686773876168896959083497242355704586144147_div_3 : (2 : ZMod 4686773876168896959083497242355704586144147) ^ ((4686773876168896959083497242355704586144147 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4686773876168896959083497242355704586144147_div_11 : (2 : ZMod 4686773876168896959083497242355704586144147) ^ ((4686773876168896959083497242355704586144147 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4686773876168896959083497242355704586144147_div_13 : (2 : ZMod 4686773876168896959083497242355704586144147) ^ ((4686773876168896959083497242355704586144147 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4686773876168896959083497242355704586144147_div_5410758664569719 : (2 : ZMod 4686773876168896959083497242355704586144147) ^ ((4686773876168896959083497242355704586144147 - 1) / 5410758664569719) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4686773876168896959083497242355704586144147_div_336517221444007083663241 : (2 : ZMod 4686773876168896959083497242355704586144147) ^ ((4686773876168896959083497242355704586144147 - 1) / 336517221444007083663241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4686773876168896959083497242355704586144147 : Nat.Prime 4686773876168896959083497242355704586144147 := by
  refine lucas_primality 4686773876168896959083497242355704586144147 (2 : ZMod 4686773876168896959083497242355704586144147) prime_4686773876168896959083497242355704586144147_pow ?_
  intro q hq hqd
  rw [prime_4686773876168896959083497242355704586144147_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 11, 13, 5410758664569719, 336517221444007083663241].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4686773876168896959083497242355704586144147_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_4686773876168896959083497242355704586144147_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_4686773876168896959083497242355704586144147_div_11
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_4686773876168896959083497242355704586144147_div_13
  · have : q = 5410758664569719 := (Nat.prime_dvd_prime_iff_eq hq prime_5410758664569719).mp hdf
    subst this; exact prime_4686773876168896959083497242355704586144147_div_5410758664569719
  · have : q = 336517221444007083663241 := (Nat.prime_dvd_prime_iff_eq hq prime_336517221444007083663241).mp hdf
    subst this; exact prime_4686773876168896959083497242355704586144147_div_336517221444007083663241
private lemma prime_A_59_sub1 : (8145612996781542914887118207214214570718527487 - 1 : ℕ) = 2 * 11 * 79 * 4686773876168896959083497242355704586144147 := by norm_num
private lemma prime_A_59_pow : (5 : ZMod 8145612996781542914887118207214214570718527487) ^ (8145612996781542914887118207214214570718527487 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_59_div_2 : (5 : ZMod 8145612996781542914887118207214214570718527487) ^ ((8145612996781542914887118207214214570718527487 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_59_div_11 : (5 : ZMod 8145612996781542914887118207214214570718527487) ^ ((8145612996781542914887118207214214570718527487 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_59_div_79 : (5 : ZMod 8145612996781542914887118207214214570718527487) ^ ((8145612996781542914887118207214214570718527487 - 1) / 79) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_59_div_4686773876168896959083497242355704586144147 : (5 : ZMod 8145612996781542914887118207214214570718527487) ^ ((8145612996781542914887118207214214570718527487 - 1) / 4686773876168896959083497242355704586144147) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_59 : Nat.Prime 8145612996781542914887118207214214570718527487 := by
  refine lucas_primality 8145612996781542914887118207214214570718527487 (5 : ZMod 8145612996781542914887118207214214570718527487) prime_A_59_pow ?_
  intro q hq hqd
  rw [prime_A_59_sub1] at hqd
  have : q ∣ [2, 11, 79, 4686773876168896959083497242355704586144147].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_59_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_59_div_11
  · have : q = 79 := (Nat.prime_dvd_prime_iff_eq hq prime_79).mp hdf
    subst this; exact prime_A_59_div_79
  · have : q = 4686773876168896959083497242355704586144147 := (Nat.prime_dvd_prime_iff_eq hq prime_4686773876168896959083497242355704586144147).mp hdf
    subst this; exact prime_A_59_div_4686773876168896959083497242355704586144147
private lemma prime_5407 : Nat.Prime 5407 := by norm_num
private lemma prime_767623 : Nat.Prime 767623 := by norm_num
private lemma prime_43 : Nat.Prime 43 := by norm_num
private lemma prime_6301 : Nat.Prime 6301 := by norm_num
private lemma prime_307874056850977_sub1 : (307874056850977 - 1 : ℕ) = 2 ^ 5 * 3 * 7 * 11 * 43 * 347 * 443 * 6301 := by norm_num
private lemma prime_307874056850977_pow : (5 : ZMod 307874056850977) ^ (307874056850977 - 1) = 1 := by
  reduce_mod_char
private lemma prime_307874056850977_div_2 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_3 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_7 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_11 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_43 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_347 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 347) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_443 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 443) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977_div_6301 : (5 : ZMod 307874056850977) ^ ((307874056850977 - 1) / 6301) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_307874056850977 : Nat.Prime 307874056850977 := by
  refine lucas_primality 307874056850977 (5 : ZMod 307874056850977) prime_307874056850977_pow ?_
  intro q hq hqd
  rw [prime_307874056850977_sub1] at hqd
  have : q ∣ [2 ^ 5, 3, 7, 11, 43, 347, 443, 6301].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_307874056850977_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_307874056850977_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_307874056850977_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_307874056850977_div_11
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_307874056850977_div_43
  · have : q = 347 := (Nat.prime_dvd_prime_iff_eq hq prime_347).mp hdf
    subst this; exact prime_307874056850977_div_347
  · have : q = 443 := (Nat.prime_dvd_prime_iff_eq hq prime_443).mp hdf
    subst this; exact prime_307874056850977_div_443
  · have : q = 6301 := (Nat.prime_dvd_prime_iff_eq hq prime_6301).mp hdf
    subst this; exact prime_307874056850977_div_6301
private lemma prime_B_59_sub1 : (8145612996781542914887118207214214570718527489 - 1 : ℕ) = 2 ^ 60 * 3 * 19 * 97 * 5407 * 767623 * 307874056850977 := by norm_num
private lemma prime_B_59_pow : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ (8145612996781542914887118207214214570718527489 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_59_div_2 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59_div_3 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59_div_19 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59_div_97 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59_div_5407 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 5407) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59_div_767623 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 767623) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59_div_307874056850977 : (7 : ZMod 8145612996781542914887118207214214570718527489) ^ ((8145612996781542914887118207214214570718527489 - 1) / 307874056850977) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_59 : Nat.Prime 8145612996781542914887118207214214570718527489 := by
  refine lucas_primality 8145612996781542914887118207214214570718527489 (7 : ZMod 8145612996781542914887118207214214570718527489) prime_B_59_pow ?_
  intro q hq hqd
  rw [prime_B_59_sub1] at hqd
  have : q ∣ [2 ^ 60, 3, 19, 97, 5407, 767623, 307874056850977].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_59_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_59_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_59_div_19
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_B_59_div_97
  · have : q = 5407 := (Nat.prime_dvd_prime_iff_eq hq prime_5407).mp hdf
    subst this; exact prime_B_59_div_5407
  · have : q = 767623 := (Nat.prime_dvd_prime_iff_eq hq prime_767623).mp hdf
    subst this; exact prime_B_59_div_767623
  · have : q = 307874056850977 := (Nat.prime_dvd_prime_iff_eq hq prime_307874056850977).mp hdf
    subst this; exact prime_B_59_div_307874056850977
private lemma pair_59 :
    Nat.Prime ((3 ^ 59 - 12441) * (2 ^ 59) - 1) ∧
    Nat.Prime ((3 ^ 59 - 12441) * (2 ^ 59) + 1) := by
  constructor
  · convert prime_A_59
  · convert prime_B_59

/- Pair for n = 60 -/
private lemma prime_691 : Nat.Prime 691 := by norm_num
private lemma prime_149 : Nat.Prime 149 := by norm_num
private lemma prime_1942321 : Nat.Prime 1942321 := by norm_num
private lemma prime_578811659_sub1 : (578811659 - 1 : ℕ) = 2 * 149 * 1942321 := by norm_num
private lemma prime_578811659_pow : (2 : ZMod 578811659) ^ (578811659 - 1) = 1 := by
  reduce_mod_char
private lemma prime_578811659_div_2 : (2 : ZMod 578811659) ^ ((578811659 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_578811659_div_149 : (2 : ZMod 578811659) ^ ((578811659 - 1) / 149) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_578811659_div_1942321 : (2 : ZMod 578811659) ^ ((578811659 - 1) / 1942321) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_578811659 : Nat.Prime 578811659 := by
  refine lucas_primality 578811659 (2 : ZMod 578811659) prime_578811659_pow ?_
  intro q hq hqd
  rw [prime_578811659_sub1] at hqd
  have : q ∣ [2, 149, 1942321].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_578811659_div_2
  · have : q = 149 := (Nat.prime_dvd_prime_iff_eq hq prime_149).mp hdf
    subst this; exact prime_578811659_div_149
  · have : q = 1942321 := (Nat.prime_dvd_prime_iff_eq hq prime_1942321).mp hdf
    subst this; exact prime_578811659_div_1942321
private lemma prime_1378253 : Nat.Prime 1378253 := by norm_num
private lemma prime_813169271_sub1 : (813169271 - 1 : ℕ) = 2 * 5 * 59 * 1378253 := by norm_num
private lemma prime_813169271_pow : (13 : ZMod 813169271) ^ (813169271 - 1) = 1 := by
  reduce_mod_char
private lemma prime_813169271_div_2 : (13 : ZMod 813169271) ^ ((813169271 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813169271_div_5 : (13 : ZMod 813169271) ^ ((813169271 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813169271_div_59 : (13 : ZMod 813169271) ^ ((813169271 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813169271_div_1378253 : (13 : ZMod 813169271) ^ ((813169271 - 1) / 1378253) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813169271 : Nat.Prime 813169271 := by
  refine lucas_primality 813169271 (13 : ZMod 813169271) prime_813169271_pow ?_
  intro q hq hqd
  rw [prime_813169271_sub1] at hqd
  have : q ∣ [2, 5, 59, 1378253].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_813169271_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_813169271_div_5
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_813169271_div_59
  · have : q = 1378253 := (Nat.prime_dvd_prime_iff_eq hq prime_1378253).mp hdf
    subst this; exact prime_813169271_div_1378253
private lemma prime_10640831 : Nat.Prime 10640831 := by norm_num
private lemma prime_915111467_sub1 : (915111467 - 1 : ℕ) = 2 * 43 * 10640831 := by norm_num
private lemma prime_915111467_pow : (2 : ZMod 915111467) ^ (915111467 - 1) = 1 := by
  reduce_mod_char
private lemma prime_915111467_div_2 : (2 : ZMod 915111467) ^ ((915111467 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_915111467_div_43 : (2 : ZMod 915111467) ^ ((915111467 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_915111467_div_10640831 : (2 : ZMod 915111467) ^ ((915111467 - 1) / 10640831) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_915111467 : Nat.Prime 915111467 := by
  refine lucas_primality 915111467 (2 : ZMod 915111467) prime_915111467_pow ?_
  intro q hq hqd
  rw [prime_915111467_sub1] at hqd
  have : q ∣ [2, 43, 10640831].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_915111467_div_2
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_915111467_div_43
  · have : q = 10640831 := (Nat.prime_dvd_prime_iff_eq hq prime_10640831).mp hdf
    subst this; exact prime_915111467_div_10640831
private lemma prime_2017 : Nat.Prime 2017 := by norm_num
private lemma prime_276977 : Nat.Prime 276977 := by norm_num
private lemma prime_318437687131_sub1 : (318437687131 - 1 : ℕ) = 2 * 3 * 5 * 19 * 2017 * 276977 := by norm_num
private lemma prime_318437687131_pow : (3 : ZMod 318437687131) ^ (318437687131 - 1) = 1 := by
  reduce_mod_char
private lemma prime_318437687131_div_2 : (3 : ZMod 318437687131) ^ ((318437687131 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318437687131_div_3 : (3 : ZMod 318437687131) ^ ((318437687131 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318437687131_div_5 : (3 : ZMod 318437687131) ^ ((318437687131 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318437687131_div_19 : (3 : ZMod 318437687131) ^ ((318437687131 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318437687131_div_2017 : (3 : ZMod 318437687131) ^ ((318437687131 - 1) / 2017) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318437687131_div_276977 : (3 : ZMod 318437687131) ^ ((318437687131 - 1) / 276977) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318437687131 : Nat.Prime 318437687131 := by
  refine lucas_primality 318437687131 (3 : ZMod 318437687131) prime_318437687131_pow ?_
  intro q hq hqd
  rw [prime_318437687131_sub1] at hqd
  have : q ∣ [2, 3, 5, 19, 2017, 276977].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_318437687131_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_318437687131_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_318437687131_div_5
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_318437687131_div_19
  · have : q = 2017 := (Nat.prime_dvd_prime_iff_eq hq prime_2017).mp hdf
    subst this; exact prime_318437687131_div_2017
  · have : q = 276977 := (Nat.prime_dvd_prime_iff_eq hq prime_276977).mp hdf
    subst this; exact prime_318437687131_div_276977
private lemma prime_7464179386350641_sub1 : (7464179386350641 - 1 : ℕ) = 2 ^ 4 * 5 * 293 * 318437687131 := by norm_num
private lemma prime_7464179386350641_pow : (3 : ZMod 7464179386350641) ^ (7464179386350641 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7464179386350641_div_2 : (3 : ZMod 7464179386350641) ^ ((7464179386350641 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7464179386350641_div_5 : (3 : ZMod 7464179386350641) ^ ((7464179386350641 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7464179386350641_div_293 : (3 : ZMod 7464179386350641) ^ ((7464179386350641 - 1) / 293) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7464179386350641_div_318437687131 : (3 : ZMod 7464179386350641) ^ ((7464179386350641 - 1) / 318437687131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7464179386350641 : Nat.Prime 7464179386350641 := by
  refine lucas_primality 7464179386350641 (3 : ZMod 7464179386350641) prime_7464179386350641_pow ?_
  intro q hq hqd
  rw [prime_7464179386350641_sub1] at hqd
  have : q ∣ [2 ^ 4, 5, 293, 318437687131].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_7464179386350641_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_7464179386350641_div_5
  · have : q = 293 := (Nat.prime_dvd_prime_iff_eq hq prime_293).mp hdf
    subst this; exact prime_7464179386350641_div_293
  · have : q = 318437687131 := (Nat.prime_dvd_prime_iff_eq hq prime_318437687131).mp hdf
    subst this; exact prime_7464179386350641_div_318437687131
private lemma prime_A_60_sub1 : (48873677980689257489322749814593034539256250367 - 1 : ℕ) = 2 * 11 * 691 * 578811659 * 813169271 * 915111467 * 7464179386350641 := by norm_num
private lemma prime_A_60_pow : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ (48873677980689257489322749814593034539256250367 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_60_div_2 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60_div_11 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60_div_691 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 691) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60_div_578811659 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 578811659) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60_div_813169271 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 813169271) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60_div_915111467 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 915111467) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60_div_7464179386350641 : (5 : ZMod 48873677980689257489322749814593034539256250367) ^ ((48873677980689257489322749814593034539256250367 - 1) / 7464179386350641) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_60 : Nat.Prime 48873677980689257489322749814593034539256250367 := by
  refine lucas_primality 48873677980689257489322749814593034539256250367 (5 : ZMod 48873677980689257489322749814593034539256250367) prime_A_60_pow ?_
  intro q hq hqd
  rw [prime_A_60_sub1] at hqd
  have : q ∣ [2, 11, 691, 578811659, 813169271, 915111467, 7464179386350641].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_60_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_60_div_11
  · have : q = 691 := (Nat.prime_dvd_prime_iff_eq hq prime_691).mp hdf
    subst this; exact prime_A_60_div_691
  · have : q = 578811659 := (Nat.prime_dvd_prime_iff_eq hq prime_578811659).mp hdf
    subst this; exact prime_A_60_div_578811659
  · have : q = 813169271 := (Nat.prime_dvd_prime_iff_eq hq prime_813169271).mp hdf
    subst this; exact prime_A_60_div_813169271
  · have : q = 915111467 := (Nat.prime_dvd_prime_iff_eq hq prime_915111467).mp hdf
    subst this; exact prime_A_60_div_915111467
  · have : q = 7464179386350641 := (Nat.prime_dvd_prime_iff_eq hq prime_7464179386350641).mp hdf
    subst this; exact prime_A_60_div_7464179386350641
private lemma prime_457 : Nat.Prime 457 := by norm_num
private lemma prime_4201 : Nat.Prime 4201 := by norm_num
private lemma prime_26540103169_sub1 : (26540103169 - 1 : ℕ) = 2 ^ 9 * 3 ^ 3 * 457 * 4201 := by norm_num
private lemma prime_26540103169_pow : (7 : ZMod 26540103169) ^ (26540103169 - 1) = 1 := by
  reduce_mod_char
private lemma prime_26540103169_div_2 : (7 : ZMod 26540103169) ^ ((26540103169 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26540103169_div_3 : (7 : ZMod 26540103169) ^ ((26540103169 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26540103169_div_457 : (7 : ZMod 26540103169) ^ ((26540103169 - 1) / 457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26540103169_div_4201 : (7 : ZMod 26540103169) ^ ((26540103169 - 1) / 4201) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26540103169 : Nat.Prime 26540103169 := by
  refine lucas_primality 26540103169 (7 : ZMod 26540103169) prime_26540103169_pow ?_
  intro q hq hqd
  rw [prime_26540103169_sub1] at hqd
  have : q ∣ [2 ^ 9, 3 ^ 3, 457, 4201].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_26540103169_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_26540103169_div_3
  · have : q = 457 := (Nat.prime_dvd_prime_iff_eq hq prime_457).mp hdf
    subst this; exact prime_26540103169_div_457
  · have : q = 4201 := (Nat.prime_dvd_prime_iff_eq hq prime_4201).mp hdf
    subst this; exact prime_26540103169_div_4201
private lemma prime_318481238029_sub1 : (318481238029 - 1 : ℕ) = 2 ^ 2 * 3 * 26540103169 := by norm_num
private lemma prime_318481238029_pow : (2 : ZMod 318481238029) ^ (318481238029 - 1) = 1 := by
  reduce_mod_char
private lemma prime_318481238029_div_2 : (2 : ZMod 318481238029) ^ ((318481238029 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318481238029_div_3 : (2 : ZMod 318481238029) ^ ((318481238029 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318481238029_div_26540103169 : (2 : ZMod 318481238029) ^ ((318481238029 - 1) / 26540103169) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_318481238029 : Nat.Prime 318481238029 := by
  refine lucas_primality 318481238029 (2 : ZMod 318481238029) prime_318481238029_pow ?_
  intro q hq hqd
  rw [prime_318481238029_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 26540103169].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_318481238029_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_318481238029_div_3
  · have : q = 26540103169 := (Nat.prime_dvd_prime_iff_eq hq prime_26540103169).mp hdf
    subst this; exact prime_318481238029_div_26540103169
private lemma prime_14723 : Nat.Prime 14723 := by norm_num
private lemma prime_18189667 : Nat.Prime 18189667 := by norm_num
private lemma prime_1606838803447_sub1 : (1606838803447 - 1 : ℕ) = 2 * 3 * 14723 * 18189667 := by norm_num
private lemma prime_1606838803447_pow : (3 : ZMod 1606838803447) ^ (1606838803447 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1606838803447_div_2 : (3 : ZMod 1606838803447) ^ ((1606838803447 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1606838803447_div_3 : (3 : ZMod 1606838803447) ^ ((1606838803447 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1606838803447_div_14723 : (3 : ZMod 1606838803447) ^ ((1606838803447 - 1) / 14723) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1606838803447_div_18189667 : (3 : ZMod 1606838803447) ^ ((1606838803447 - 1) / 18189667) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1606838803447 : Nat.Prime 1606838803447 := by
  refine lucas_primality 1606838803447 (3 : ZMod 1606838803447) prime_1606838803447_pow ?_
  intro q hq hqd
  rw [prime_1606838803447_sub1] at hqd
  have : q ∣ [2, 3, 14723, 18189667].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1606838803447_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1606838803447_div_3
  · have : q = 14723 := (Nat.prime_dvd_prime_iff_eq hq prime_14723).mp hdf
    subst this; exact prime_1606838803447_div_14723
  · have : q = 18189667 := (Nat.prime_dvd_prime_iff_eq hq prime_18189667).mp hdf
    subst this; exact prime_1606838803447_div_18189667
private lemma prime_B_60_sub1 : (48873677980689257489322749814593034539256250369 - 1 : ℕ) = 2 ^ 62 * 3 ^ 3 * 13 * 59 * 318481238029 * 1606838803447 := by norm_num
private lemma prime_B_60_pow : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ (48873677980689257489322749814593034539256250369 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_60_div_2 : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ ((48873677980689257489322749814593034539256250369 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_60_div_3 : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ ((48873677980689257489322749814593034539256250369 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_60_div_13 : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ ((48873677980689257489322749814593034539256250369 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_60_div_59 : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ ((48873677980689257489322749814593034539256250369 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_60_div_318481238029 : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ ((48873677980689257489322749814593034539256250369 - 1) / 318481238029) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_60_div_1606838803447 : (17 : ZMod 48873677980689257489322749814593034539256250369) ^ ((48873677980689257489322749814593034539256250369 - 1) / 1606838803447) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_60 : Nat.Prime 48873677980689257489322749814593034539256250369 := by
  refine lucas_primality 48873677980689257489322749814593034539256250369 (17 : ZMod 48873677980689257489322749814593034539256250369) prime_B_60_pow ?_
  intro q hq hqd
  rw [prime_B_60_sub1] at hqd
  have : q ∣ [2 ^ 62, 3 ^ 3, 13, 59, 318481238029, 1606838803447].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_60_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_60_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_60_div_13
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_B_60_div_59
  · have : q = 318481238029 := (Nat.prime_dvd_prime_iff_eq hq prime_318481238029).mp hdf
    subst this; exact prime_B_60_div_318481238029
  · have : q = 1606838803447 := (Nat.prime_dvd_prime_iff_eq hq prime_1606838803447).mp hdf
    subst this; exact prime_B_60_div_1606838803447
private lemma pair_60 :
    Nat.Prime ((3 ^ 60 - 2133) * (2 ^ 60) - 1) ∧
    Nat.Prime ((3 ^ 60 - 2133) * (2 ^ 60) + 1) := by
  constructor
  · convert prime_A_60
  · convert prime_B_60
