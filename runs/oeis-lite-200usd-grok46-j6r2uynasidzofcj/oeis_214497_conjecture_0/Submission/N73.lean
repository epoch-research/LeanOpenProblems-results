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
private lemma prime_113 : Nat.Prime 113 := by norm_num
private lemma prime_517499 : Nat.Prime 517499 := by norm_num
private lemma prime_999611 : Nat.Prime 999611 := by norm_num
private lemma prime_436283 : Nat.Prime 436283 := by norm_num
private lemma prime_141355693_sub1 : (141355693 - 1 : ℕ) = 2 ^ 2 * 3 ^ 4 * 436283 := by norm_num
private lemma prime_141355693_pow : (2 : ZMod 141355693) ^ (141355693 - 1) = 1 := by
  reduce_mod_char
private lemma prime_141355693_div_2 : (2 : ZMod 141355693) ^ ((141355693 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_141355693_div_3 : (2 : ZMod 141355693) ^ ((141355693 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_141355693_div_436283 : (2 : ZMod 141355693) ^ ((141355693 - 1) / 436283) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_141355693 : Nat.Prime 141355693 := by
  refine lucas_primality 141355693 (2 : ZMod 141355693) prime_141355693_pow ?_
  intro q hq hqd
  rw [prime_141355693_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 4, 436283].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_141355693_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_141355693_div_3
  · have : q = 436283 := (Nat.prime_dvd_prime_iff_eq hq prime_436283).mp hdf
    subst this; exact prime_141355693_div_436283
private lemma prime_5654227721_sub1 : (5654227721 - 1 : ℕ) = 2 ^ 3 * 5 * 141355693 := by norm_num
private lemma prime_5654227721_pow : (3 : ZMod 5654227721) ^ (5654227721 - 1) = 1 := by
  reduce_mod_char
private lemma prime_5654227721_div_2 : (3 : ZMod 5654227721) ^ ((5654227721 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5654227721_div_5 : (3 : ZMod 5654227721) ^ ((5654227721 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5654227721_div_141355693 : (3 : ZMod 5654227721) ^ ((5654227721 - 1) / 141355693) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5654227721 : Nat.Prime 5654227721 := by
  refine lucas_primality 5654227721 (3 : ZMod 5654227721) prime_5654227721_pow ?_
  intro q hq hqd
  rw [prime_5654227721_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 141355693].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_5654227721_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_5654227721_div_5
  · have : q = 141355693 := (Nat.prime_dvd_prime_iff_eq hq prime_141355693).mp hdf
    subst this; exact prime_5654227721_div_141355693
private lemma prime_41 : Nat.Prime 41 := by norm_num
private lemma prime_89 : Nat.Prime 89 := by norm_num
private lemma prime_28300007 : Nat.Prime 28300007 := by norm_num
private lemma prime_30360417309643_sub1 : (30360417309643 - 1 : ℕ) = 2 * 3 * 7 ^ 2 * 41 * 89 * 28300007 := by norm_num
private lemma prime_30360417309643_pow : (2 : ZMod 30360417309643) ^ (30360417309643 - 1) = 1 := by
  reduce_mod_char
private lemma prime_30360417309643_div_2 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_3 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_7 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_41 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_89 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_28300007 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 28300007) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643 : Nat.Prime 30360417309643 := by
  refine lucas_primality 30360417309643 (2 : ZMod 30360417309643) prime_30360417309643_pow ?_
  intro q hq hqd
  rw [prime_30360417309643_sub1] at hqd
  have : q ∣ [2, 3, 7 ^ 2, 41, 89, 28300007].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_30360417309643_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_30360417309643_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_30360417309643_div_7
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_30360417309643_div_41
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_30360417309643_div_89
  · have : q = 28300007 := (Nat.prime_dvd_prime_iff_eq hq prime_28300007).mp hdf
    subst this; exact prime_30360417309643_div_28300007
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_2677 : Nat.Prime 2677 := by norm_num
private lemma prime_12433 : Nat.Prime 12433 := by norm_num
private lemma prime_19990457 : Nat.Prime 19990457 := by norm_num
private lemma prime_31806161892299830349_sub1 : (31806161892299830349 - 1 : ℕ) = 2 ^ 2 * 17 * 19 * 37 * 2677 * 12433 * 19990457 := by norm_num
private lemma prime_31806161892299830349_pow : (2 : ZMod 31806161892299830349) ^ (31806161892299830349 - 1) = 1 := by
  reduce_mod_char
private lemma prime_31806161892299830349_div_2 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_17 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_19 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_37 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_2677 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 2677) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_12433 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 12433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_19990457 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 19990457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349 : Nat.Prime 31806161892299830349 := by
  refine lucas_primality 31806161892299830349 (2 : ZMod 31806161892299830349) prime_31806161892299830349_pow ?_
  intro q hq hqd
  rw [prime_31806161892299830349_sub1] at hqd
  have : q ∣ [2 ^ 2, 17, 19, 37, 2677, 12433, 19990457].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_31806161892299830349_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_31806161892299830349_div_17
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_31806161892299830349_div_19
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_31806161892299830349_div_37
  · have : q = 2677 := (Nat.prime_dvd_prime_iff_eq hq prime_2677).mp hdf
    subst this; exact prime_31806161892299830349_div_2677
  · have : q = 12433 := (Nat.prime_dvd_prime_iff_eq hq prime_12433).mp hdf
    subst this; exact prime_31806161892299830349_div_12433
  · have : q = 19990457 := (Nat.prime_dvd_prime_iff_eq hq prime_19990457).mp hdf
    subst this; exact prime_31806161892299830349_div_19990457
private lemma prime_A_73_sub1 : (638324153542299148846280854514488143130545802757862850559 - 1 : ℕ) = 2 * 113 * 517499 * 999611 * 5654227721 * 30360417309643 * 31806161892299830349 := by norm_num
private lemma prime_A_73_pow : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ (638324153542299148846280854514488143130545802757862850559 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_73_div_2 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_113 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_517499 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 517499) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_999611 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 999611) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_5654227721 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 5654227721) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_30360417309643 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 30360417309643) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_31806161892299830349 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 31806161892299830349) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73 : Nat.Prime 638324153542299148846280854514488143130545802757862850559 := by
  refine lucas_primality 638324153542299148846280854514488143130545802757862850559 (7 : ZMod 638324153542299148846280854514488143130545802757862850559) prime_A_73_pow ?_
  intro q hq hqd
  rw [prime_A_73_sub1] at hqd
  have : q ∣ [2, 113, 517499, 999611, 5654227721, 30360417309643, 31806161892299830349].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_73_div_2
  · have : q = 113 := (Nat.prime_dvd_prime_iff_eq hq prime_113).mp hdf
    subst this; exact prime_A_73_div_113
  · have : q = 517499 := (Nat.prime_dvd_prime_iff_eq hq prime_517499).mp hdf
    subst this; exact prime_A_73_div_517499
  · have : q = 999611 := (Nat.prime_dvd_prime_iff_eq hq prime_999611).mp hdf
    subst this; exact prime_A_73_div_999611
  · have : q = 5654227721 := (Nat.prime_dvd_prime_iff_eq hq prime_5654227721).mp hdf
    subst this; exact prime_A_73_div_5654227721
  · have : q = 30360417309643 := (Nat.prime_dvd_prime_iff_eq hq prime_30360417309643).mp hdf
    subst this; exact prime_A_73_div_30360417309643
  · have : q = 31806161892299830349 := (Nat.prime_dvd_prime_iff_eq hq prime_31806161892299830349).mp hdf
    subst this; exact prime_A_73_div_31806161892299830349
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_10867 : Nat.Prime 10867 := by norm_num
private lemma prime_7547 : Nat.Prime 7547 := by norm_num
private lemma prime_4126417 : Nat.Prime 4126417 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_271 : Nat.Prime 271 := by norm_num
private lemma prime_4463 : Nat.Prime 4463 := by norm_num
private lemma prime_7001 : Nat.Prime 7001 := by norm_num
private lemma prime_59991288961_sub1 : (59991288961 - 1 : ℕ) = 2 ^ 7 * 3 * 5 * 4463 * 7001 := by norm_num
private lemma prime_59991288961_pow : (11 : ZMod 59991288961) ^ (59991288961 - 1) = 1 := by
  reduce_mod_char
private lemma prime_59991288961_div_2 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_3 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_5 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_4463 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 4463) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_7001 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 7001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961 : Nat.Prime 59991288961 := by
  refine lucas_primality 59991288961 (11 : ZMod 59991288961) prime_59991288961_pow ?_
  intro q hq hqd
  rw [prime_59991288961_sub1] at hqd
  have : q ∣ [2 ^ 7, 3, 5, 4463, 7001].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_59991288961_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_59991288961_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_59991288961_div_5
  · have : q = 4463 := (Nat.prime_dvd_prime_iff_eq hq prime_4463).mp hdf
    subst this; exact prime_59991288961_div_4463
  · have : q = 7001 := (Nat.prime_dvd_prime_iff_eq hq prime_7001).mp hdf
    subst this; exact prime_59991288961_div_7001
private lemma prime_13753962854932627_sub1 : (13753962854932627 - 1 : ℕ) = 2 * 3 ^ 2 * 47 * 271 * 59991288961 := by norm_num
private lemma prime_13753962854932627_pow : (3 : ZMod 13753962854932627) ^ (13753962854932627 - 1) = 1 := by
  reduce_mod_char
private lemma prime_13753962854932627_div_2 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_3 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_47 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_271 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 271) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_59991288961 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 59991288961) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627 : Nat.Prime 13753962854932627 := by
  refine lucas_primality 13753962854932627 (3 : ZMod 13753962854932627) prime_13753962854932627_pow ?_
  intro q hq hqd
  rw [prime_13753962854932627_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 47, 271, 59991288961].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_13753962854932627_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_13753962854932627_div_3
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_13753962854932627_div_47
  · have : q = 271 := (Nat.prime_dvd_prime_iff_eq hq prime_271).mp hdf
    subst this; exact prime_13753962854932627_div_271
  · have : q = 59991288961 := (Nat.prime_dvd_prime_iff_eq hq prime_59991288961).mp hdf
    subst this; exact prime_13753962854932627_div_59991288961
private lemma prime_18846381910989212053038095213_sub1 : (18846381910989212053038095213 - 1 : ℕ) = 2 ^ 2 * 11 * 7547 * 4126417 * 13753962854932627 := by norm_num
private lemma prime_18846381910989212053038095213_pow : (2 : ZMod 18846381910989212053038095213) ^ (18846381910989212053038095213 - 1) = 1 := by
  reduce_mod_char
private lemma prime_18846381910989212053038095213_div_2 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_11 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_7547 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 7547) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_4126417 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 4126417) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_13753962854932627 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 13753962854932627) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213 : Nat.Prime 18846381910989212053038095213 := by
  refine lucas_primality 18846381910989212053038095213 (2 : ZMod 18846381910989212053038095213) prime_18846381910989212053038095213_pow ?_
  intro q hq hqd
  rw [prime_18846381910989212053038095213_sub1] at hqd
  have : q ∣ [2 ^ 2, 11, 7547, 4126417, 13753962854932627].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_18846381910989212053038095213_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_11
  · have : q = 7547 := (Nat.prime_dvd_prime_iff_eq hq prime_7547).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_7547
  · have : q = 4126417 := (Nat.prime_dvd_prime_iff_eq hq prime_4126417).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_4126417
  · have : q = 13753962854932627 := (Nat.prime_dvd_prime_iff_eq hq prime_13753962854932627).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_13753962854932627
private lemma prime_B_73_sub1 : (638324153542299148846280854514488143130545802757862850561 - 1 : ℕ) = 2 ^ 74 * 3 * 5 * 11 * 10867 * 18846381910989212053038095213 := by norm_num
private lemma prime_B_73_pow : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ (638324153542299148846280854514488143130545802757862850561 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_73_div_2 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_3 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_5 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_11 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_10867 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 10867) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_18846381910989212053038095213 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 18846381910989212053038095213) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73 : Nat.Prime 638324153542299148846280854514488143130545802757862850561 := by
  refine lucas_primality 638324153542299148846280854514488143130545802757862850561 (19 : ZMod 638324153542299148846280854514488143130545802757862850561) prime_B_73_pow ?_
  intro q hq hqd
  rw [prime_B_73_sub1] at hqd
  have : q ∣ [2 ^ 74, 3, 5, 11, 10867, 18846381910989212053038095213].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_73_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_73_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_73_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_73_div_11
  · have : q = 10867 := (Nat.prime_dvd_prime_iff_eq hq prime_10867).mp hdf
    subst this; exact prime_B_73_div_10867
  · have : q = 18846381910989212053038095213 := (Nat.prime_dvd_prime_iff_eq hq prime_18846381910989212053038095213).mp hdf
    subst this; exact prime_B_73_div_18846381910989212053038095213
private lemma pair_73 :
    Nat.Prime ((3 ^ 73 - 26493) * (2 ^ 73) - 1) ∧
    Nat.Prime ((3 ^ 73 - 26493) * (2 ^ 73) + 1) := by
  constructor
  · convert prime_A_73
  · convert prime_B_73
