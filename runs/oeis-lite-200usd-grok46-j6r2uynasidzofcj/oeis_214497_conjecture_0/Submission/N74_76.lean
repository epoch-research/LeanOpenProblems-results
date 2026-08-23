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

/- n=74 -/
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

/- n=75 -/
private lemma prime_127 : Nat.Prime 127 := by norm_num
private lemma prime_4001 : Nat.Prime 4001 := by norm_num
private lemma prime_9199 : Nat.Prime 9199 := by norm_num
private lemma prime_736103981_sub1 : (736103981 - 1 : ℕ) = 2 ^ 2 * 5 * 4001 * 9199 := by norm_num
private lemma prime_736103981_pow : (2 : ZMod 736103981) ^ (736103981 - 1) = 1 := by
  reduce_mod_char
private lemma prime_736103981_div_2 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981_div_5 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981_div_4001 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 4001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981_div_9199 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 9199) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981 : Nat.Prime 736103981 := by
  refine lucas_primality 736103981 (2 : ZMod 736103981) prime_736103981_pow ?_
  intro q hq hqd
  rw [prime_736103981_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 4001, 9199].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_736103981_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_736103981_div_5
  · have : q = 4001 := (Nat.prime_dvd_prime_iff_eq hq prime_4001).mp hdf
    subst this; exact prime_736103981_div_4001
  · have : q = 9199 := (Nat.prime_dvd_prime_iff_eq hq prime_9199).mp hdf
    subst this; exact prime_736103981_div_9199
private lemma prime_1472207963_sub1 : (1472207963 - 1 : ℕ) = 2 * 736103981 := by norm_num
private lemma prime_1472207963_pow : (2 : ZMod 1472207963) ^ (1472207963 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1472207963_div_2 : (2 : ZMod 1472207963) ^ ((1472207963 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1472207963_div_736103981 : (2 : ZMod 1472207963) ^ ((1472207963 - 1) / 736103981) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1472207963 : Nat.Prime 1472207963 := by
  refine lucas_primality 1472207963 (2 : ZMod 1472207963) prime_1472207963_pow ?_
  intro q hq hqd
  rw [prime_1472207963_sub1] at hqd
  have : q ∣ [2, 736103981].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1472207963_div_2
  · have : q = 736103981 := (Nat.prime_dvd_prime_iff_eq hq prime_736103981).mp hdf
    subst this; exact prime_1472207963_div_736103981
private lemma prime_1543 : Nat.Prime 1543 := by norm_num
private lemma prime_92849 : Nat.Prime 92849 := by norm_num
private lemma prime_2865320141_sub1 : (2865320141 - 1 : ℕ) = 2 ^ 2 * 5 * 1543 * 92849 := by norm_num
private lemma prime_2865320141_pow : (3 : ZMod 2865320141) ^ (2865320141 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2865320141_div_2 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141_div_5 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141_div_1543 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 1543) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141_div_92849 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 92849) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141 : Nat.Prime 2865320141 := by
  refine lucas_primality 2865320141 (3 : ZMod 2865320141) prime_2865320141_pow ?_
  intro q hq hqd
  rw [prime_2865320141_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 1543, 92849].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2865320141_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_2865320141_div_5
  · have : q = 1543 := (Nat.prime_dvd_prime_iff_eq hq prime_1543).mp hdf
    subst this; exact prime_2865320141_div_1543
  · have : q = 92849 := (Nat.prime_dvd_prime_iff_eq hq prime_92849).mp hdf
    subst this; exact prime_2865320141_div_92849
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_80849 : Nat.Prime 80849 := by norm_num
private lemma prime_54969269 : Nat.Prime 54969269 := by norm_num
private lemma prime_19403422734677447_sub1 : (19403422734677447 - 1 : ℕ) = 2 * 37 * 59 * 80849 * 54969269 := by norm_num
private lemma prime_19403422734677447_pow : (5 : ZMod 19403422734677447) ^ (19403422734677447 - 1) = 1 := by
  reduce_mod_char
private lemma prime_19403422734677447_div_2 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_37 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_59 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_80849 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 80849) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_54969269 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 54969269) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447 : Nat.Prime 19403422734677447 := by
  refine lucas_primality 19403422734677447 (5 : ZMod 19403422734677447) prime_19403422734677447_pow ?_
  intro q hq hqd
  rw [prime_19403422734677447_sub1] at hqd
  have : q ∣ [2, 37, 59, 80849, 54969269].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_19403422734677447_div_2
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_19403422734677447_div_37
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_19403422734677447_div_59
  · have : q = 80849 := (Nat.prime_dvd_prime_iff_eq hq prime_80849).mp hdf
    subst this; exact prime_19403422734677447_div_80849
  · have : q = 54969269 := (Nat.prime_dvd_prime_iff_eq hq prime_54969269).mp hdf
    subst this; exact prime_19403422734677447_div_54969269
private lemma prime_811 : Nat.Prime 811 := by norm_num
private lemma prime_2801 : Nat.Prime 2801 := by norm_num
private lemma prime_22111 : Nat.Prime 22111 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_3203 : Nat.Prime 3203 := by norm_num
private lemma prime_305643073_sub1 : (305643073 - 1 : ℕ) = 2 ^ 6 * 3 * 7 * 71 * 3203 := by norm_num
private lemma prime_305643073_pow : (10 : ZMod 305643073) ^ (305643073 - 1) = 1 := by
  reduce_mod_char
private lemma prime_305643073_div_2 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_3 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_7 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_71 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_3203 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 3203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073 : Nat.Prime 305643073 := by
  refine lucas_primality 305643073 (10 : ZMod 305643073) prime_305643073_pow ?_
  intro q hq hqd
  rw [prime_305643073_sub1] at hqd
  have : q ∣ [2 ^ 6, 3, 7, 71, 3203].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_305643073_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_305643073_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_305643073_div_7
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_305643073_div_71
  · have : q = 3203 := (Nat.prime_dvd_prime_iff_eq hq prime_3203).mp hdf
    subst this; exact prime_305643073_div_3203
private lemma prime_1105323494970026371177_sub1 : (1105323494970026371177 - 1 : ℕ) = 2 ^ 3 * 3 ^ 2 * 811 * 2801 * 22111 * 305643073 := by norm_num
private lemma prime_1105323494970026371177_pow : (5 : ZMod 1105323494970026371177) ^ (1105323494970026371177 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1105323494970026371177_div_2 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_3 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_811 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 811) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_2801 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 2801) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_22111 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 22111) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_305643073 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 305643073) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177 : Nat.Prime 1105323494970026371177 := by
  refine lucas_primality 1105323494970026371177 (5 : ZMod 1105323494970026371177) prime_1105323494970026371177_pow ?_
  intro q hq hqd
  rw [prime_1105323494970026371177_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 2, 811, 2801, 22111, 305643073].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1105323494970026371177_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1105323494970026371177_div_3
  · have : q = 811 := (Nat.prime_dvd_prime_iff_eq hq prime_811).mp hdf
    subst this; exact prime_1105323494970026371177_div_811
  · have : q = 2801 := (Nat.prime_dvd_prime_iff_eq hq prime_2801).mp hdf
    subst this; exact prime_1105323494970026371177_div_2801
  · have : q = 22111 := (Nat.prime_dvd_prime_iff_eq hq prime_22111).mp hdf
    subst this; exact prime_1105323494970026371177_div_22111
  · have : q = 305643073 := (Nat.prime_dvd_prime_iff_eq hq prime_305643073).mp hdf
    subst this; exact prime_1105323494970026371177_div_305643073
private lemma prime_A_75_sub1 : (22979669527522769358466110762530181082324623688578587688959 - 1 : ℕ) = 2 * 127 * 1472207963 * 2865320141 * 19403422734677447 * 1105323494970026371177 := by norm_num
private lemma prime_A_75_pow : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ (22979669527522769358466110762530181082324623688578587688959 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_75_div_2 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_127 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 127) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_1472207963 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 1472207963) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_2865320141 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 2865320141) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_19403422734677447 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 19403422734677447) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_1105323494970026371177 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 1105323494970026371177) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75 : Nat.Prime 22979669527522769358466110762530181082324623688578587688959 := by
  refine lucas_primality 22979669527522769358466110762530181082324623688578587688959 (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) prime_A_75_pow ?_
  intro q hq hqd
  rw [prime_A_75_sub1] at hqd
  have : q ∣ [2, 127, 1472207963, 2865320141, 19403422734677447, 1105323494970026371177].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_75_div_2
  · have : q = 127 := (Nat.prime_dvd_prime_iff_eq hq prime_127).mp hdf
    subst this; exact prime_A_75_div_127
  · have : q = 1472207963 := (Nat.prime_dvd_prime_iff_eq hq prime_1472207963).mp hdf
    subst this; exact prime_A_75_div_1472207963
  · have : q = 2865320141 := (Nat.prime_dvd_prime_iff_eq hq prime_2865320141).mp hdf
    subst this; exact prime_A_75_div_2865320141
  · have : q = 19403422734677447 := (Nat.prime_dvd_prime_iff_eq hq prime_19403422734677447).mp hdf
    subst this; exact prime_A_75_div_19403422734677447
  · have : q = 1105323494970026371177 := (Nat.prime_dvd_prime_iff_eq hq prime_1105323494970026371177).mp hdf
    subst this; exact prime_A_75_div_1105323494970026371177
private lemma prime_1289593 : Nat.Prime 1289593 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_97 : Nat.Prime 97 := by norm_num
private lemma prime_6221 : Nat.Prime 6221 := by norm_num
private lemma prime_699986921_sub1 : (699986921 - 1 : ℕ) = 2 ^ 3 * 5 * 29 * 97 * 6221 := by norm_num
private lemma prime_699986921_pow : (3 : ZMod 699986921) ^ (699986921 - 1) = 1 := by
  reduce_mod_char
private lemma prime_699986921_div_2 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_5 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_29 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_97 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_6221 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 6221) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921 : Nat.Prime 699986921 := by
  refine lucas_primality 699986921 (3 : ZMod 699986921) prime_699986921_pow ?_
  intro q hq hqd
  rw [prime_699986921_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 29, 97, 6221].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_699986921_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_699986921_div_5
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_699986921_div_29
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_699986921_div_97
  · have : q = 6221 := (Nat.prime_dvd_prime_iff_eq hq prime_6221).mp hdf
    subst this; exact prime_699986921_div_6221
private lemma prime_1399973843_sub1 : (1399973843 - 1 : ℕ) = 2 * 699986921 := by norm_num
private lemma prime_1399973843_pow : (2 : ZMod 1399973843) ^ (1399973843 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1399973843_div_2 : (2 : ZMod 1399973843) ^ ((1399973843 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1399973843_div_699986921 : (2 : ZMod 1399973843) ^ ((1399973843 - 1) / 699986921) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1399973843 : Nat.Prime 1399973843 := by
  refine lucas_primality 1399973843 (2 : ZMod 1399973843) prime_1399973843_pow ?_
  intro q hq hqd
  rw [prime_1399973843_sub1] at hqd
  have : q ∣ [2, 699986921].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1399973843_div_2
  · have : q = 699986921 := (Nat.prime_dvd_prime_iff_eq hq prime_699986921).mp hdf
    subst this; exact prime_1399973843_div_699986921
private lemma prime_3610792936231799_sub1 : (3610792936231799 - 1 : ℕ) = 2 * 1289593 * 1399973843 := by norm_num
private lemma prime_3610792936231799_pow : (13 : ZMod 3610792936231799) ^ (3610792936231799 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3610792936231799_div_2 : (13 : ZMod 3610792936231799) ^ ((3610792936231799 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3610792936231799_div_1289593 : (13 : ZMod 3610792936231799) ^ ((3610792936231799 - 1) / 1289593) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3610792936231799_div_1399973843 : (13 : ZMod 3610792936231799) ^ ((3610792936231799 - 1) / 1399973843) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3610792936231799 : Nat.Prime 3610792936231799 := by
  refine lucas_primality 3610792936231799 (13 : ZMod 3610792936231799) prime_3610792936231799_pow ?_
  intro q hq hqd
  rw [prime_3610792936231799_sub1] at hqd
  have : q ∣ [2, 1289593, 1399973843].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3610792936231799_div_2
  · have : q = 1289593 := (Nat.prime_dvd_prime_iff_eq hq prime_1289593).mp hdf
    subst this; exact prime_3610792936231799_div_1289593
  · have : q = 1399973843 := (Nat.prime_dvd_prime_iff_eq hq prime_1399973843).mp hdf
    subst this; exact prime_3610792936231799_div_1399973843
private lemma prime_13171813 : Nat.Prime 13171813 := by norm_num
private lemma prime_49341343 : Nat.Prime 49341343 := by norm_num
private lemma prime_350954069309023861_sub1 : (350954069309023861 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 5 * 13171813 * 49341343 := by norm_num
private lemma prime_350954069309023861_pow : (6 : ZMod 350954069309023861) ^ (350954069309023861 - 1) = 1 := by
  reduce_mod_char
private lemma prime_350954069309023861_div_2 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_3 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_5 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_13171813 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 13171813) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_49341343 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 49341343) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861 : Nat.Prime 350954069309023861 := by
  refine lucas_primality 350954069309023861 (6 : ZMod 350954069309023861) prime_350954069309023861_pow ?_
  intro q hq hqd
  rw [prime_350954069309023861_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 5, 13171813, 49341343].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_350954069309023861_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_350954069309023861_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_350954069309023861_div_5
  · have : q = 13171813 := (Nat.prime_dvd_prime_iff_eq hq prime_13171813).mp hdf
    subst this; exact prime_350954069309023861_div_13171813
  · have : q = 49341343 := (Nat.prime_dvd_prime_iff_eq hq prime_49341343).mp hdf
    subst this; exact prime_350954069309023861_div_49341343
private lemma prime_B_75_sub1 : (22979669527522769358466110762530181082324623688578587688961 - 1 : ℕ) = 2 ^ 80 * 3 * 5 * 3610792936231799 * 350954069309023861 := by norm_num
private lemma prime_B_75_pow : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ (22979669527522769358466110762530181082324623688578587688961 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_75_div_2 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_3 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_5 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_3610792936231799 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 3610792936231799) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_350954069309023861 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 350954069309023861) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75 : Nat.Prime 22979669527522769358466110762530181082324623688578587688961 := by
  refine lucas_primality 22979669527522769358466110762530181082324623688578587688961 (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) prime_B_75_pow ?_
  intro q hq hqd
  rw [prime_B_75_sub1] at hqd
  have : q ∣ [2 ^ 80, 3, 5, 3610792936231799, 350954069309023861].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_75_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_75_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_75_div_5
  · have : q = 3610792936231799 := (Nat.prime_dvd_prime_iff_eq hq prime_3610792936231799).mp hdf
    subst this; exact prime_B_75_div_3610792936231799
  · have : q = 350954069309023861 := (Nat.prime_dvd_prime_iff_eq hq prime_350954069309023861).mp hdf
    subst this; exact prime_B_75_div_350954069309023861
private lemma pair_75 :
    Nat.Prime ((3 ^ 75 - 10587) * (2 ^ 75) - 1) ∧
    Nat.Prime ((3 ^ 75 - 10587) * (2 ^ 75) + 1) := by
  constructor
  · convert prime_A_75
  · convert prime_B_75

/- n=76 -/
private lemma prime_53 : Nat.Prime 53 := by norm_num
private lemma prime_12197 : Nat.Prime 12197 := by norm_num
private lemma prime_1399 : Nat.Prime 1399 := by norm_num
private lemma prime_43261697 : Nat.Prime 43261697 := by norm_num
private lemma prime_363138684619_sub1 : (363138684619 - 1 : ℕ) = 2 * 3 * 1399 * 43261697 := by norm_num
private lemma prime_363138684619_pow : (2 : ZMod 363138684619) ^ (363138684619 - 1) = 1 := by
  reduce_mod_char
private lemma prime_363138684619_div_2 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619_div_3 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619_div_1399 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 1399) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619_div_43261697 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 43261697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619 : Nat.Prime 363138684619 := by
  refine lucas_primality 363138684619 (2 : ZMod 363138684619) prime_363138684619_pow ?_
  intro q hq hqd
  rw [prime_363138684619_sub1] at hqd
  have : q ∣ [2, 3, 1399, 43261697].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_363138684619_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_363138684619_div_3
  · have : q = 1399 := (Nat.prime_dvd_prime_iff_eq hq prime_1399).mp hdf
    subst this; exact prime_363138684619_div_1399
  · have : q = 43261697 := (Nat.prime_dvd_prime_iff_eq hq prime_43261697).mp hdf
    subst this; exact prime_363138684619_div_43261697
private lemma prime_8858405072595887_sub1 : (8858405072595887 - 1 : ℕ) = 2 * 12197 * 363138684619 := by norm_num
private lemma prime_8858405072595887_pow : (5 : ZMod 8858405072595887) ^ (8858405072595887 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8858405072595887_div_2 : (5 : ZMod 8858405072595887) ^ ((8858405072595887 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8858405072595887_div_12197 : (5 : ZMod 8858405072595887) ^ ((8858405072595887 - 1) / 12197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8858405072595887_div_363138684619 : (5 : ZMod 8858405072595887) ^ ((8858405072595887 - 1) / 363138684619) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8858405072595887 : Nat.Prime 8858405072595887 := by
  refine lucas_primality 8858405072595887 (5 : ZMod 8858405072595887) prime_8858405072595887_pow ?_
  intro q hq hqd
  rw [prime_8858405072595887_sub1] at hqd
  have : q ∣ [2, 12197, 363138684619].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8858405072595887_div_2
  · have : q = 12197 := (Nat.prime_dvd_prime_iff_eq hq prime_12197).mp hdf
    subst this; exact prime_8858405072595887_div_12197
  · have : q = 363138684619 := (Nat.prime_dvd_prime_iff_eq hq prime_363138684619).mp hdf
    subst this; exact prime_8858405072595887_div_363138684619
private lemma prime_90426598981058814497_sub1 : (90426598981058814497 - 1 : ℕ) = 2 ^ 5 * 11 * 29 * 8858405072595887 := by norm_num
private lemma prime_90426598981058814497_pow : (3 : ZMod 90426598981058814497) ^ (90426598981058814497 - 1) = 1 := by
  reduce_mod_char
private lemma prime_90426598981058814497_div_2 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497_div_11 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497_div_29 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497_div_8858405072595887 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 8858405072595887) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497 : Nat.Prime 90426598981058814497 := by
  refine lucas_primality 90426598981058814497 (3 : ZMod 90426598981058814497) prime_90426598981058814497_pow ?_
  intro q hq hqd
  rw [prime_90426598981058814497_sub1] at hqd
  have : q ∣ [2 ^ 5, 11, 29, 8858405072595887].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_90426598981058814497_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_90426598981058814497_div_11
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_90426598981058814497_div_29
  · have : q = 8858405072595887 := (Nat.prime_dvd_prime_iff_eq hq prime_8858405072595887).mp hdf
    subst this; exact prime_90426598981058814497_div_8858405072595887
private lemma prime_397 : Nat.Prime 397 := by norm_num
private lemma prime_739 : Nat.Prime 739 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_137 : Nat.Prime 137 := by norm_num
private lemma prime_8573 : Nat.Prime 8573 := by norm_num
private lemma prime_131 : Nat.Prime 131 := by norm_num
private lemma prime_8893 : Nat.Prime 8893 := by norm_num
private lemma prime_441146442577_sub1 : (441146442577 - 1 : ℕ) = 2 ^ 4 * 3 * 7 ^ 3 * 23 * 131 * 8893 := by norm_num
private lemma prime_441146442577_pow : (5 : ZMod 441146442577) ^ (441146442577 - 1) = 1 := by
  reduce_mod_char
private lemma prime_441146442577_div_2 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_3 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_7 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_23 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_131 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_8893 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 8893) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577 : Nat.Prime 441146442577 := by
  refine lucas_primality 441146442577 (5 : ZMod 441146442577) prime_441146442577_pow ?_
  intro q hq hqd
  rw [prime_441146442577_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 7 ^ 3, 23, 131, 8893].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_441146442577_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_441146442577_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_441146442577_div_7
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_441146442577_div_23
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_441146442577_div_131
  · have : q = 8893 := (Nat.prime_dvd_prime_iff_eq hq prime_8893).mp hdf
    subst this; exact prime_441146442577_div_8893
private lemma prime_45383381426551453_sub1 : (45383381426551453 - 1 : ℕ) = 2 ^ 2 * 3 * 8573 * 441146442577 := by norm_num
private lemma prime_45383381426551453_pow : (2 : ZMod 45383381426551453) ^ (45383381426551453 - 1) = 1 := by
  reduce_mod_char
private lemma prime_45383381426551453_div_2 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453_div_3 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453_div_8573 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 8573) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453_div_441146442577 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 441146442577) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453 : Nat.Prime 45383381426551453 := by
  refine lucas_primality 45383381426551453 (2 : ZMod 45383381426551453) prime_45383381426551453_pow ?_
  intro q hq hqd
  rw [prime_45383381426551453_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 8573, 441146442577].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_45383381426551453_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_45383381426551453_div_3
  · have : q = 8573 := (Nat.prime_dvd_prime_iff_eq hq prime_8573).mp hdf
    subst this; exact prime_45383381426551453_div_8573
  · have : q = 441146442577 := (Nat.prime_dvd_prime_iff_eq hq prime_441146442577).mp hdf
    subst this; exact prime_45383381426551453_div_441146442577
private lemma prime_29953031741523958981_sub1 : (29953031741523958981 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 11 * 45383381426551453 := by norm_num
private lemma prime_29953031741523958981_pow : (6 : ZMod 29953031741523958981) ^ (29953031741523958981 - 1) = 1 := by
  reduce_mod_char
private lemma prime_29953031741523958981_div_2 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_3 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_5 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_11 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_45383381426551453 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 45383381426551453) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981 : Nat.Prime 29953031741523958981 := by
  refine lucas_primality 29953031741523958981 (6 : ZMod 29953031741523958981) prime_29953031741523958981_pow ?_
  intro q hq hqd
  rw [prime_29953031741523958981_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 11, 45383381426551453].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_29953031741523958981_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_29953031741523958981_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_29953031741523958981_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_29953031741523958981_div_11
  · have : q = 45383381426551453 := (Nat.prime_dvd_prime_iff_eq hq prime_45383381426551453).mp hdf
    subst this; exact prime_29953031741523958981_div_45383381426551453
private lemma prime_110826217443638648229701_sub1 : (110826217443638648229701 - 1 : ℕ) = 2 ^ 2 * 5 ^ 2 * 37 * 29953031741523958981 := by norm_num
private lemma prime_110826217443638648229701_pow : (2 : ZMod 110826217443638648229701) ^ (110826217443638648229701 - 1) = 1 := by
  reduce_mod_char
private lemma prime_110826217443638648229701_div_2 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701_div_5 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701_div_37 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701_div_29953031741523958981 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 29953031741523958981) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701 : Nat.Prime 110826217443638648229701 := by
  refine lucas_primality 110826217443638648229701 (2 : ZMod 110826217443638648229701) prime_110826217443638648229701_pow ?_
  intro q hq hqd
  rw [prime_110826217443638648229701_sub1] at hqd
  have : q ∣ [2 ^ 2, 5 ^ 2, 37, 29953031741523958981].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_110826217443638648229701_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_110826217443638648229701_div_5
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_110826217443638648229701_div_37
  · have : q = 29953031741523958981 := (Nat.prime_dvd_prime_iff_eq hq prime_29953031741523958981).mp hdf
    subst this; exact prime_110826217443638648229701_div_29953031741523958981
private lemma prime_7895259730684817299883899241_sub1 : (7895259730684817299883899241 - 1 : ℕ) = 2 ^ 3 * 5 * 13 * 137 * 110826217443638648229701 := by norm_num
private lemma prime_7895259730684817299883899241_pow : (3 : ZMod 7895259730684817299883899241) ^ (7895259730684817299883899241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7895259730684817299883899241_div_2 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_5 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_13 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_137 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 137) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_110826217443638648229701 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 110826217443638648229701) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241 : Nat.Prime 7895259730684817299883899241 := by
  refine lucas_primality 7895259730684817299883899241 (3 : ZMod 7895259730684817299883899241) prime_7895259730684817299883899241_pow ?_
  intro q hq hqd
  rw [prime_7895259730684817299883899241_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 13, 137, 110826217443638648229701].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_7895259730684817299883899241_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_13
  · have : q = 137 := (Nat.prime_dvd_prime_iff_eq hq prime_137).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_137
  · have : q = 110826217443638648229701 := (Nat.prime_dvd_prime_iff_eq hq prime_110826217443638648229701).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_110826217443638648229701
private lemma prime_2876888052074839662333662809689700327_sub1 : (2876888052074839662333662809689700327 - 1 : ℕ) = 2 * 3 ^ 3 * 23 * 397 * 739 * 7895259730684817299883899241 := by norm_num
private lemma prime_2876888052074839662333662809689700327_pow : (3 : ZMod 2876888052074839662333662809689700327) ^ (2876888052074839662333662809689700327 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2876888052074839662333662809689700327_div_2 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_3 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_23 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_397 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 397) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_739 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 739) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_7895259730684817299883899241 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 7895259730684817299883899241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327 : Nat.Prime 2876888052074839662333662809689700327 := by
  refine lucas_primality 2876888052074839662333662809689700327 (3 : ZMod 2876888052074839662333662809689700327) prime_2876888052074839662333662809689700327_pow ?_
  intro q hq hqd
  rw [prime_2876888052074839662333662809689700327_sub1] at hqd
  have : q ∣ [2, 3 ^ 3, 23, 397, 739, 7895259730684817299883899241].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_3
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_23
  · have : q = 397 := (Nat.prime_dvd_prime_iff_eq hq prime_397).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_397
  · have : q = 739 := (Nat.prime_dvd_prime_iff_eq hq prime_739).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_739
  · have : q = 7895259730684817299883899241 := (Nat.prime_dvd_prime_iff_eq hq prime_7895259730684817299883899241).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_7895259730684817299883899241
private lemma prime_A_76_sub1 : (137878017165136616150796664575183430072206928816041017475071 - 1 : ℕ) = 2 * 5 * 53 * 90426598981058814497 * 2876888052074839662333662809689700327 := by norm_num
private lemma prime_A_76_pow : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ (137878017165136616150796664575183430072206928816041017475071 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_76_div_2 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_5 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_53 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_90426598981058814497 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 90426598981058814497) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_2876888052074839662333662809689700327 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 2876888052074839662333662809689700327) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76 : Nat.Prime 137878017165136616150796664575183430072206928816041017475071 := by
  refine lucas_primality 137878017165136616150796664575183430072206928816041017475071 (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) prime_A_76_pow ?_
  intro q hq hqd
  rw [prime_A_76_sub1] at hqd
  have : q ∣ [2, 5, 53, 90426598981058814497, 2876888052074839662333662809689700327].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_76_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_76_div_5
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_A_76_div_53
  · have : q = 90426598981058814497 := (Nat.prime_dvd_prime_iff_eq hq prime_90426598981058814497).mp hdf
    subst this; exact prime_A_76_div_90426598981058814497
  · have : q = 2876888052074839662333662809689700327 := (Nat.prime_dvd_prime_iff_eq hq prime_2876888052074839662333662809689700327).mp hdf
    subst this; exact prime_A_76_div_2876888052074839662333662809689700327
private lemma prime_2097097 : Nat.Prime 2097097 := by norm_num
private lemma prime_2350207 : Nat.Prime 2350207 := by norm_num
private lemma prime_394834777_sub1 : (394834777 - 1 : ℕ) = 2 ^ 3 * 3 * 7 * 2350207 := by norm_num
private lemma prime_394834777_pow : (10 : ZMod 394834777) ^ (394834777 - 1) = 1 := by
  reduce_mod_char
private lemma prime_394834777_div_2 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777_div_3 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777_div_7 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777_div_2350207 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 2350207) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777 : Nat.Prime 394834777 := by
  refine lucas_primality 394834777 (10 : ZMod 394834777) prime_394834777_pow ?_
  intro q hq hqd
  rw [prime_394834777_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 7, 2350207].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_394834777_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_394834777_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_394834777_div_7
  · have : q = 2350207 := (Nat.prime_dvd_prime_iff_eq hq prime_2350207).mp hdf
    subst this; exact prime_394834777_div_2350207
private lemma prime_401 : Nat.Prime 401 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_231943 : Nat.Prime 231943 := by norm_num
private lemma prime_218026421_sub1 : (218026421 - 1 : ℕ) = 2 ^ 2 * 5 * 47 * 231943 := by norm_num
private lemma prime_218026421_pow : (2 : ZMod 218026421) ^ (218026421 - 1) = 1 := by
  reduce_mod_char
private lemma prime_218026421_div_2 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421_div_5 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421_div_47 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421_div_231943 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 231943) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421 : Nat.Prime 218026421 := by
  refine lucas_primality 218026421 (2 : ZMod 218026421) prime_218026421_pow ?_
  intro q hq hqd
  rw [prime_218026421_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 47, 231943].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_218026421_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_218026421_div_5
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_218026421_div_47
  · have : q = 231943 := (Nat.prime_dvd_prime_iff_eq hq prime_231943).mp hdf
    subst this; exact prime_218026421_div_231943
private lemma prime_436052843_sub1 : (436052843 - 1 : ℕ) = 2 * 218026421 := by norm_num
private lemma prime_436052843_pow : (2 : ZMod 436052843) ^ (436052843 - 1) = 1 := by
  reduce_mod_char
private lemma prime_436052843_div_2 : (2 : ZMod 436052843) ^ ((436052843 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_436052843_div_218026421 : (2 : ZMod 436052843) ^ ((436052843 - 1) / 218026421) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_436052843 : Nat.Prime 436052843 := by
  refine lucas_primality 436052843 (2 : ZMod 436052843) prime_436052843_pow ?_
  intro q hq hqd
  rw [prime_436052843_sub1] at hqd
  have : q ∣ [2, 218026421].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_436052843_div_2
  · have : q = 218026421 := (Nat.prime_dvd_prime_iff_eq hq prime_218026421).mp hdf
    subst this; exact prime_436052843_div_218026421
private lemma prime_872105687_sub1 : (872105687 - 1 : ℕ) = 2 * 436052843 := by norm_num
private lemma prime_872105687_pow : (5 : ZMod 872105687) ^ (872105687 - 1) = 1 := by
  reduce_mod_char
private lemma prime_872105687_div_2 : (5 : ZMod 872105687) ^ ((872105687 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_872105687_div_436052843 : (5 : ZMod 872105687) ^ ((872105687 - 1) / 436052843) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_872105687 : Nat.Prime 872105687 := by
  refine lucas_primality 872105687 (5 : ZMod 872105687) prime_872105687_pow ?_
  intro q hq hqd
  rw [prime_872105687_sub1] at hqd
  have : q ∣ [2, 436052843].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_872105687_div_2
  · have : q = 436052843 := (Nat.prime_dvd_prime_iff_eq hq prime_436052843).mp hdf
    subst this; exact prime_872105687_div_436052843
private lemma prime_16786290263377_sub1 : (16786290263377 - 1 : ℕ) = 2 ^ 4 * 3 * 401 * 872105687 := by norm_num
private lemma prime_16786290263377_pow : (7 : ZMod 16786290263377) ^ (16786290263377 - 1) = 1 := by
  reduce_mod_char
private lemma prime_16786290263377_div_2 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377_div_3 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377_div_401 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 401) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377_div_872105687 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 872105687) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377 : Nat.Prime 16786290263377 := by
  refine lucas_primality 16786290263377 (7 : ZMod 16786290263377) prime_16786290263377_pow ?_
  intro q hq hqd
  rw [prime_16786290263377_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 401, 872105687].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_16786290263377_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_16786290263377_div_3
  · have : q = 401 := (Nat.prime_dvd_prime_iff_eq hq prime_401).mp hdf
    subst this; exact prime_16786290263377_div_401
  · have : q = 872105687 := (Nat.prime_dvd_prime_iff_eq hq prime_872105687).mp hdf
    subst this; exact prime_16786290263377_div_872105687
private lemma prime_79533734073572748743149_sub1 : (79533734073572748743149 - 1 : ℕ) = 2 ^ 2 * 3 * 394834777 * 16786290263377 := by norm_num
private lemma prime_79533734073572748743149_pow : (2 : ZMod 79533734073572748743149) ^ (79533734073572748743149 - 1) = 1 := by
  reduce_mod_char
private lemma prime_79533734073572748743149_div_2 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149_div_3 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149_div_394834777 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 394834777) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149_div_16786290263377 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 16786290263377) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149 : Nat.Prime 79533734073572748743149 := by
  refine lucas_primality 79533734073572748743149 (2 : ZMod 79533734073572748743149) prime_79533734073572748743149_pow ?_
  intro q hq hqd
  rw [prime_79533734073572748743149_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 394834777, 16786290263377].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_79533734073572748743149_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_79533734073572748743149_div_3
  · have : q = 394834777 := (Nat.prime_dvd_prime_iff_eq hq prime_394834777).mp hdf
    subst this; exact prime_79533734073572748743149_div_394834777
  · have : q = 16786290263377 := (Nat.prime_dvd_prime_iff_eq hq prime_16786290263377).mp hdf
    subst this; exact prime_79533734073572748743149_div_16786290263377
private lemma prime_B_76_sub1 : (137878017165136616150796664575183430072206928816041017475073 - 1 : ℕ) = 2 ^ 76 * 3 * 13 * 23 * 12197 * 2097097 * 79533734073572748743149 := by norm_num
private lemma prime_B_76_pow : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ (137878017165136616150796664575183430072206928816041017475073 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_76_div_2 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_3 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_13 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_23 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_12197 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 12197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_2097097 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 2097097) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_79533734073572748743149 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 79533734073572748743149) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76 : Nat.Prime 137878017165136616150796664575183430072206928816041017475073 := by
  refine lucas_primality 137878017165136616150796664575183430072206928816041017475073 (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) prime_B_76_pow ?_
  intro q hq hqd
  rw [prime_B_76_sub1] at hqd
  have : q ∣ [2 ^ 76, 3, 13, 23, 12197, 2097097, 79533734073572748743149].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_76_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_76_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_76_div_13
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_B_76_div_23
  · have : q = 12197 := (Nat.prime_dvd_prime_iff_eq hq prime_12197).mp hdf
    subst this; exact prime_B_76_div_12197
  · have : q = 2097097 := (Nat.prime_dvd_prime_iff_eq hq prime_2097097).mp hdf
    subst this; exact prime_B_76_div_2097097
  · have : q = 79533734073572748743149 := (Nat.prime_dvd_prime_iff_eq hq prime_79533734073572748743149).mp hdf
    subst this; exact prime_B_76_div_79533734073572748743149
private lemma pair_76 :
    Nat.Prime ((3 ^ 76 - 744) * (2 ^ 76) - 1) ∧
    Nat.Prime ((3 ^ 76 - 744) * (2 ^ 76) + 1) := by
  constructor
  · convert prime_A_76
  · convert prime_B_76
