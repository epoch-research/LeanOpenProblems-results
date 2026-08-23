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
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_613 : Nat.Prime 613 := by norm_num
private lemma prime_1181 : Nat.Prime 1181 := by norm_num
private lemma prime_1856083 : Nat.Prime 1856083 := by norm_num
private lemma prime_4384068047_sub1 : (4384068047 - 1 : ℕ) = 2 * 1181 * 1856083 := by norm_num
private lemma prime_4384068047_pow : (5 : ZMod 4384068047) ^ (4384068047 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4384068047_div_2 : (5 : ZMod 4384068047) ^ ((4384068047 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4384068047_div_1181 : (5 : ZMod 4384068047) ^ ((4384068047 - 1) / 1181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4384068047_div_1856083 : (5 : ZMod 4384068047) ^ ((4384068047 - 1) / 1856083) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4384068047 : Nat.Prime 4384068047 := by
  refine lucas_primality 4384068047 (5 : ZMod 4384068047) prime_4384068047_pow ?_
  intro q hq hqd
  rw [prime_4384068047_sub1] at hqd
  have : q ∣ [2, 1181, 1856083].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4384068047_div_2
  · have : q = 1181 := (Nat.prime_dvd_prime_iff_eq hq prime_1181).mp hdf
    subst this; exact prime_4384068047_div_1181
  · have : q = 1856083 := (Nat.prime_dvd_prime_iff_eq hq prime_1856083).mp hdf
    subst this; exact prime_4384068047_div_1856083
private lemma prime_673 : Nat.Prime 673 := by norm_num
private lemma prime_1697 : Nat.Prime 1697 := by norm_num
private lemma prime_12203 : Nat.Prime 12203 := by norm_num
private lemma prime_27253 : Nat.Prime 27253 := by norm_num
private lemma prime_1334833 : Nat.Prime 1334833 := by norm_num
private lemma prime_859 : Nat.Prime 859 := by norm_num
private lemma prime_25561 : Nat.Prime 25561 := by norm_num
private lemma prime_395224183_sub1 : (395224183 - 1 : ℕ) = 2 * 3 ^ 2 * 859 * 25561 := by norm_num
private lemma prime_395224183_pow : (3 : ZMod 395224183) ^ (395224183 - 1) = 1 := by
  reduce_mod_char
private lemma prime_395224183_div_2 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183_div_3 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183_div_859 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 859) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183_div_25561 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 25561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183 : Nat.Prime 395224183 := by
  refine lucas_primality 395224183 (3 : ZMod 395224183) prime_395224183_pow ?_
  intro q hq hqd
  rw [prime_395224183_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 859, 25561].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_395224183_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_395224183_div_3
  · have : q = 859 := (Nat.prime_dvd_prime_iff_eq hq prime_859).mp hdf
    subst this; exact prime_395224183_div_859
  · have : q = 25561 := (Nat.prime_dvd_prime_iff_eq hq prime_25561).mp hdf
    subst this; exact prime_395224183_div_25561
private lemma prime_41 : Nat.Prime 41 := by norm_num
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_1109 : Nat.Prime 1109 := by norm_num
private lemma prime_6834172577_sub1 : (6834172577 - 1 : ℕ) = 2 ^ 5 * 7 * 11 * 41 * 61 * 1109 := by norm_num
private lemma prime_6834172577_pow : (3 : ZMod 6834172577) ^ (6834172577 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6834172577_div_2 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_7 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_11 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_41 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_61 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_1109 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 1109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577 : Nat.Prime 6834172577 := by
  refine lucas_primality 6834172577 (3 : ZMod 6834172577) prime_6834172577_pow ?_
  intro q hq hqd
  rw [prime_6834172577_sub1] at hqd
  have : q ∣ [2 ^ 5, 7, 11, 41, 61, 1109].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_6834172577_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_6834172577_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_6834172577_div_11
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_6834172577_div_41
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_6834172577_div_61
  · have : q = 1109 := (Nat.prime_dvd_prime_iff_eq hq prime_1109).mp hdf
    subst this; exact prime_6834172577_div_1109
private lemma prime_8216473729924211106919060089235839395623_sub1 : (8216473729924211106919060089235839395623 - 1 : ℕ) = 2 * 3 * 673 * 1697 * 12203 * 27253 * 1334833 * 395224183 * 6834172577 := by norm_num
private lemma prime_8216473729924211106919060089235839395623_pow : (7 : ZMod 8216473729924211106919060089235839395623) ^ (8216473729924211106919060089235839395623 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8216473729924211106919060089235839395623_div_2 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_3 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_673 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 673) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_1697 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 1697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_12203 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 12203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_27253 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 27253) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_1334833 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 1334833) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_395224183 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 395224183) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_6834172577 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 6834172577) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623 : Nat.Prime 8216473729924211106919060089235839395623 := by
  refine lucas_primality 8216473729924211106919060089235839395623 (7 : ZMod 8216473729924211106919060089235839395623) prime_8216473729924211106919060089235839395623_pow ?_
  intro q hq hqd
  rw [prime_8216473729924211106919060089235839395623_sub1] at hqd
  have : q ∣ [2, 3, 673, 1697, 12203, 27253, 1334833, 395224183, 6834172577].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_3
  · have : q = 673 := (Nat.prime_dvd_prime_iff_eq hq prime_673).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_673
  · have : q = 1697 := (Nat.prime_dvd_prime_iff_eq hq prime_1697).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_1697
  · have : q = 12203 := (Nat.prime_dvd_prime_iff_eq hq prime_12203).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_12203
  · have : q = 27253 := (Nat.prime_dvd_prime_iff_eq hq prime_27253).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_27253
  · have : q = 1334833 := (Nat.prime_dvd_prime_iff_eq hq prime_1334833).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_1334833
  · have : q = 395224183 := (Nat.prime_dvd_prime_iff_eq hq prime_395224183).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_395224183
  · have : q = 6834172577 := (Nat.prime_dvd_prime_iff_eq hq prime_6834172577).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_6834172577
private lemma prime_174088405511536131503531142140382058964518683881088578653_sub1 : (174088405511536131503531142140382058964518683881088578653 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 73 * 613 * 4384068047 * 8216473729924211106919060089235839395623 := by norm_num
private lemma prime_174088405511536131503531142140382058964518683881088578653_pow : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ (174088405511536131503531142140382058964518683881088578653 - 1) = 1 := by
  reduce_mod_char
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_2 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_3 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_73 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_613 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 613) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_4384068047 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 4384068047) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_8216473729924211106919060089235839395623 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 8216473729924211106919060089235839395623) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653 : Nat.Prime 174088405511536131503531142140382058964518683881088578653 := by
  refine lucas_primality 174088405511536131503531142140382058964518683881088578653 (5 : ZMod 174088405511536131503531142140382058964518683881088578653) prime_174088405511536131503531142140382058964518683881088578653_pow ?_
  intro q hq hqd
  rw [prime_174088405511536131503531142140382058964518683881088578653_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 73, 613, 4384068047, 8216473729924211106919060089235839395623].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_3
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_73
  · have : q = 613 := (Nat.prime_dvd_prime_iff_eq hq prime_613).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_613
  · have : q = 4384068047 := (Nat.prime_dvd_prime_iff_eq hq prime_4384068047).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_4384068047
  · have : q = 8216473729924211106919060089235839395623 := (Nat.prime_dvd_prime_iff_eq hq prime_8216473729924211106919060089235839395623).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_8216473729924211106919060089235839395623
private lemma prime_A_74_sub1 : (3829944921253794893077685127088405297219411045383948730367 - 1 : ℕ) = 2 * 11 * 174088405511536131503531142140382058964518683881088578653 := by norm_num
private lemma prime_A_74_pow : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ (3829944921253794893077685127088405297219411045383948730367 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_74_div_2 : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ ((3829944921253794893077685127088405297219411045383948730367 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_74_div_11 : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ ((3829944921253794893077685127088405297219411045383948730367 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_74_div_174088405511536131503531142140382058964518683881088578653 : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ ((3829944921253794893077685127088405297219411045383948730367 - 1) / 174088405511536131503531142140382058964518683881088578653) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_74 : Nat.Prime 3829944921253794893077685127088405297219411045383948730367 := by
  refine lucas_primality 3829944921253794893077685127088405297219411045383948730367 (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) prime_A_74_pow ?_
  intro q hq hqd
  rw [prime_A_74_sub1] at hqd
  have : q ∣ [2, 11, 174088405511536131503531142140382058964518683881088578653].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_74_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_74_div_11
  · have : q = 174088405511536131503531142140382058964518683881088578653 := (Nat.prime_dvd_prime_iff_eq hq prime_174088405511536131503531142140382058964518683881088578653).mp hdf
    subst this; exact prime_A_74_div_174088405511536131503531142140382058964518683881088578653
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_107 : Nat.Prime 107 := by norm_num
private lemma prime_211 : Nat.Prime 211 := by norm_num
private lemma prime_431 : Nat.Prime 431 := by norm_num
private lemma prime_5557 : Nat.Prime 5557 := by norm_num
private lemma prime_15753371 : Nat.Prime 15753371 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_157 : Nat.Prime 157 := by norm_num
private lemma prime_9103 : Nat.Prime 9103 := by norm_num
private lemma prime_797477419_sub1 : (797477419 - 1 : ℕ) = 2 * 3 ^ 2 * 31 * 157 * 9103 := by norm_num
private lemma prime_797477419_pow : (2 : ZMod 797477419) ^ (797477419 - 1) = 1 := by
  reduce_mod_char
private lemma prime_797477419_div_2 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_3 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_31 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_157 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_9103 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 9103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419 : Nat.Prime 797477419 := by
  refine lucas_primality 797477419 (2 : ZMod 797477419) prime_797477419_pow ?_
  intro q hq hqd
  rw [prime_797477419_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 31, 157, 9103].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_797477419_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_797477419_div_3
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_797477419_div_31
  · have : q = 157 := (Nat.prime_dvd_prime_iff_eq hq prime_157).mp hdf
    subst this; exact prime_797477419_div_157
  · have : q = 9103 := (Nat.prime_dvd_prime_iff_eq hq prime_9103).mp hdf
    subst this; exact prime_797477419_div_9103
private lemma prime_50729133577429_sub1 : (50729133577429 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 19 * 31 * 797477419 := by norm_num
private lemma prime_50729133577429_pow : (2 : ZMod 50729133577429) ^ (50729133577429 - 1) = 1 := by
  reduce_mod_char
private lemma prime_50729133577429_div_2 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_3 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_19 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_31 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_797477419 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 797477419) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429 : Nat.Prime 50729133577429 := by
  refine lucas_primality 50729133577429 (2 : ZMod 50729133577429) prime_50729133577429_pow ?_
  intro q hq hqd
  rw [prime_50729133577429_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 19, 31, 797477419].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_50729133577429_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_50729133577429_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_50729133577429_div_19
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_50729133577429_div_31
  · have : q = 797477419 := (Nat.prime_dvd_prime_iff_eq hq prime_797477419).mp hdf
    subst this; exact prime_50729133577429_div_797477419
private lemma prime_B_74_sub1 : (3829944921253794893077685127088405297219411045383948730369 - 1 : ℕ) = 2 ^ 76 * 3 * 17 * 23 * 107 * 211 * 431 * 5557 * 15753371 * 50729133577429 := by norm_num
private lemma prime_B_74_pow : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ (3829944921253794893077685127088405297219411045383948730369 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_74_div_2 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_3 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_17 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_23 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_107 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_211 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 211) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_431 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 431) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_5557 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 5557) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_15753371 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 15753371) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_50729133577429 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 50729133577429) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74 : Nat.Prime 3829944921253794893077685127088405297219411045383948730369 := by
  refine lucas_primality 3829944921253794893077685127088405297219411045383948730369 (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) prime_B_74_pow ?_
  intro q hq hqd
  rw [prime_B_74_sub1] at hqd
  have : q ∣ [2 ^ 76, 3, 17, 23, 107, 211, 431, 5557, 15753371, 50729133577429].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_74_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_74_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_B_74_div_17
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_B_74_div_23
  · have : q = 107 := (Nat.prime_dvd_prime_iff_eq hq prime_107).mp hdf
    subst this; exact prime_B_74_div_107
  · have : q = 211 := (Nat.prime_dvd_prime_iff_eq hq prime_211).mp hdf
    subst this; exact prime_B_74_div_211
  · have : q = 431 := (Nat.prime_dvd_prime_iff_eq hq prime_431).mp hdf
    subst this; exact prime_B_74_div_431
  · have : q = 5557 := (Nat.prime_dvd_prime_iff_eq hq prime_5557).mp hdf
    subst this; exact prime_B_74_div_5557
  · have : q = 15753371 := (Nat.prime_dvd_prime_iff_eq hq prime_15753371).mp hdf
    subst this; exact prime_B_74_div_15753371
  · have : q = 50729133577429 := (Nat.prime_dvd_prime_iff_eq hq prime_50729133577429).mp hdf
    subst this; exact prime_B_74_div_50729133577429
private lemma pair_74 :
    Nat.Prime ((3 ^ 74 - 1317) * (2 ^ 74) - 1) ∧
    Nat.Prime ((3 ^ 74 - 1317) * (2 ^ 74) + 1) := by
  constructor
  · convert prime_A_74
  · convert prime_B_74
