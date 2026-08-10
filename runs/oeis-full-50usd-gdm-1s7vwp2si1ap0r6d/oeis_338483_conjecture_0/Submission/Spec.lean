import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000
open Finset Nat Set

def trialDivStep (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | d + 2 =>
    if n % (d + 2) = 0 then false
    else trialDivStep n (d + 1)

lemma trialDivStep_iff (n : ℕ) (d : ℕ) : trialDivStep n d = true ↔ ∀ m, 2 ≤ m → m ≤ d → ¬ m ∣ n := by
  induction d with
  | zero =>
    simp [trialDivStep]
    intro m h2 h0
    omega
  | succ d ih =>
    cases d with
    | zero =>
      simp [trialDivStep]
      intro m h2 h1
      omega
    | succ d =>
      rw [trialDivStep]
      split_ifs with h_mod
      · constructor
        · intro h; contradiction
        · intro h
          have h_div : d + 2 ∣ n := dvd_of_mod_eq_zero h_mod
          have := h (d + 2) (by omega) (by omega)
          contradiction
      · rw [ih]
        constructor
        · rintro h m h2 h_le
          rcases eq_or_lt_of_le h_le with rfl | h_lt
          · intro hd
            have h_mod' : n % (d + 2) = 0 := mod_eq_zero_of_dvd hd
            exact h_mod h_mod'
          · exact h m h2 (by omega)
        · rintro h m h2 h_le
          exact h m h2 (by omega)

def fastIsPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else trialDivStep n (n - 1)

lemma fastIsPrime_iff (n : ℕ) : fastIsPrime n = true ↔ Nat.Prime n := by
  unfold fastIsPrime
  split_ifs with h1 h2
  · constructor
    · intro h; contradiction
    · intro hp
      have := hp.two_le
      omega
  · subst h2
    simp [Nat.prime_two]
  · rw [trialDivStep_iff]
    rw [Nat.prime_def_lt']
    have this : 2 ≤ n := by omega
    rw [and_iff_right this]
    constructor
    · intro h m h2 h_lt
      exact h m h2 (by omega)
    · intro h m h2 h_le
      exact h m h2 (by omega)

@[instance 10000]
def fastDecidePrime (n : ℕ) : Decidable (Nat.Prime n) :=
  decidable_of_iff (fastIsPrime n = true) (fastIsPrime_iff n)

lemma nth_le_of_mem {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite) {n : ℕ} {x : ℕ} (hpx : p x) (hx : nth p n < x) : nth p (n + 1) ≤ x := by
  have hm : nth p (count p x) = x := nth_count hpx
  have h_lt : nth p n < nth p (count p x) := by rwa [hm]
  rw [nth_lt_nth hp] at h_lt
  have h_le : n + 1 ≤ count p x := h_lt
  have h_nth_le := (nth_monotone hp) h_le
  rwa [hm] at h_nth_le

lemma nth_prime_next {n p q : ℕ} (hp : nth Nat.Prime n = p) (hq_prime : Nat.Prime q) (hpq : p < q) (h_no_prime : ∀ x ∈ Finset.Ioo p q, ¬ Nat.Prime x) : nth Nat.Prime (n + 1) = q := by
  have h_le : nth Nat.Prime (n + 1) ≤ q := by
    apply nth_le_of_mem infinite_setOf_prime hq_prime
    rwa [hp]
  have h_gt : nth Nat.Prime (n + 1) ≥ q := by
    by_contra h_lt_q
    have h_lt_q' : nth Nat.Prime (n + 1) < q := by omega
    have h_gt_p : nth Nat.Prime (n + 1) > p := by
      rw [← hp]
      apply (nth_strictMono infinite_setOf_prime) (lt_add_one n)
    have h_mem : nth Nat.Prime (n + 1) ∈ Finset.Ioo p q := by
      rw [Finset.mem_Ioo]
      exact ⟨h_gt_p, h_lt_q'⟩
    have h_prime : Nat.Prime (nth Nat.Prime (n + 1)) := nth_mem_of_infinite infinite_setOf_prime (n + 1)
    exact h_no_prime (nth Nat.Prime (n + 1)) h_mem h_prime
  omega

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

lemma tau_of_prime {p : ℕ} (hp : Nat.Prime p) : tau p = 2 := by
  unfold tau
  rw [Nat.Prime.divisors hp]
  have hp1 : 1 ≠ p := hp.ne_one.symm
  exact card_pair hp1

lemma tau_eq_two_iff_prime (n : ℕ) : tau n = 2 ↔ Nat.Prime n := by
  constructor
  · intro h
    have hn0 : n ≠ 0 := by
      rintro rfl
      unfold tau at h
      simp at h
    have hn_prop : properDivisors n = {1} := by
      have h1 : #n.divisors = 2 := h
      have h_card : #n.divisors = #n.properDivisors + 1 := by
        rw [← cons_self_properDivisors hn0, card_cons]
      have h_prop_card : #n.properDivisors = 1 := by
        omega
      have hn1 : 1 < n := by
        by_contra h_le
        interval_cases n
        · contradiction
        · unfold tau at h
          simp at h
      obtain ⟨a, ha⟩ := card_eq_one.mp h_prop_card
      have ha1 : a = 1 := by
        have h1_mem : 1 ∈ n.properDivisors := one_mem_properDivisors_iff_one_lt.mpr hn1
        rw [ha] at h1_mem
        exact (mem_singleton.mp h1_mem).symm
      rw [ha, ha1]
    rwa [← properDivisors_eq_singleton_one_iff_prime]
  · exact tau_of_prime

noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))

lemma filter_prime_Ico_eq_range (m : ℕ) :
  (Finset.Ico 1 m).filter (fun k => Nat.Prime k) = (Finset.range m).filter (fun k => Nat.Prime k) := by
  ext k
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨h2, hp⟩
  · rintro ⟨h2, hp⟩
    refine ⟨⟨?_, h2⟩, hp⟩
    exact hp.one_lt.le

lemma A047983_count_prime {m : ℕ} (hm : Nat.Prime m) :
  A047983_count m = count Nat.Prime m := by
  unfold A047983_count
  have htau : tau m = 2 := tau_of_prime hm
  rw [htau]
  dsimp only
  have h_eq : (Finset.Ico 1 m).filter (fun k : ℕ => tau k = 2) = (Finset.Ico 1 m).filter (fun k : ℕ => Nat.Prime k) := by
    ext k
    simp [tau_eq_two_iff_prime]
  rw [h_eq, filter_prime_Ico_eq_range, count_eq_card_filter_range]

lemma A047983_count_nth_prime (n : ℕ) : A047983_count (nth Nat.Prime n) = n := by
  have hp : Nat.Prime (nth Nat.Prime n) := nth_mem_of_infinite infinite_setOf_prime n
  rw [A047983_count_prime hp, count_nth_of_infinite infinite_setOf_prime]

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | A047983_count m = n}

lemma a_eq_nth_prime_of_prime {n : ℕ} (hp : Nat.Prime (a n)) : a n = nth Nat.Prime n := by
  have h_nonempty : {m : ℕ | A047983_count m = n}.Nonempty := ⟨nth Nat.Prime n, A047983_count_nth_prime n⟩
  have ha_mem : A047983_count (a n) = n := Nat.sInf_mem h_nonempty
  have ha_count : count Nat.Prime (a n) = n := by
    rw [← A047983_count_prime hp]
    exact ha_mem
  have h_nth := nth_count hp
  rw [ha_count] at h_nth
  exact h_nth.symm

lemma nth_prime_ten : nth Nat.Prime 10 = 31 := by
  have h_count : count Nat.Prime 31 = 10 := by decide
  have h_prime : Nat.Prime 31 := by decide
  have h_nth := nth_count h_prime
  rw [h_count] at h_nth
  exact h_nth

lemma n_gt_ten_of_nth_prime_gt_31 {n : ℕ} (h : nth Nat.Prime n > 31) : n > 10 := by
  by_contra h_le
  have h_le_10 : n ≤ 10 := by omega
  have h_mono : nth Nat.Prime n ≤ nth Nat.Prime 10 := (nth_monotone infinite_setOf_prime) h_le_10
  rw [nth_prime_ten] at h_mono
  omega

lemma A047983_count_lt (m : ℕ) (hm : m > 0) : A047983_count m < m := by
  unfold A047983_count
  dsimp only
  have h1 : #((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau m)) ≤ #(Finset.Ico 1 m) := card_filter_le _ _
  have h2 : #(Finset.Ico 1 m) = m - 1 := Nat.card_Ico 1 m
  omega

lemma a_mono (n : ℕ) : a n < a (n + 1) := by
  have h_nonempty : {m : ℕ | A047983_count m = n + 1}.Nonempty := ⟨nth Nat.Prime (n + 1), A047983_count_nth_prime (n + 1)⟩
  have hM : A047983_count (a (n + 1)) = n + 1 := Nat.sInf_mem h_nonempty
  unfold A047983_count at hM
  dsimp only at hM
  let S := (Finset.Ico 1 (a (n + 1))).filter (fun k => tau k = tau (a (n + 1)))
  have hS_card : #S = n + 1 := hM
  have hS_nonempty : S.Nonempty := by
    rw [← Finset.card_pos, hS_card]
    omega
  let k0 := S.max' hS_nonempty
  have hk0_mem : k0 ∈ S := Finset.max'_mem S hS_nonempty
  have hk0_lt : k0 < a (n + 1) := by
    have : k0 ∈ Finset.Ico 1 (a (n + 1)) := by
      exact Finset.mem_of_mem_filter _ hk0_mem
    rw [Finset.mem_Ico] at this
    exact this.2
  have hk0_tau : tau k0 = tau (a (n + 1)) := by
    have : k0 ∈ S := hk0_mem
    rw [Finset.mem_filter] at this
    exact this.2
  have hk0_count : A047983_count k0 = n := by
    unfold A047983_count
    dsimp only
    rw [hk0_tau]
    let S' := (Finset.Ico 1 k0).filter (fun k => tau k = tau (a (n + 1)))
    have h_eq : S' = S.erase k0 := by
      ext x
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hx_tau⟩
        refine ⟨by omega, ⟨hx1, ?_⟩, hx_tau⟩
        exact hx2.trans hk0_lt
      · rintro ⟨hx_ne, ⟨hx1, hx2⟩, hx_tau⟩
        refine ⟨⟨hx1, ?_⟩, hx_tau⟩
        have hx_mem_S : x ∈ S := by
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨hx1, hx2⟩, hx_tau⟩
        have hle := Finset.le_max' S x hx_mem_S
        exact lt_of_le_of_ne hle hx_ne
    have h_card : #S' = n := by
      rw [h_eq]
      rw [Finset.card_erase_of_mem hk0_mem]
      omega
    exact h_card
  have hk0_in : k0 ∈ {m : ℕ | A047983_count m = n} := hk0_count
  have ha_le : a n ≤ k0 := Nat.sInf_le hk0_in
  exact ha_le.trans_lt hk0_lt

lemma ge_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (x y : ℕ) (h : x ≤ y) : f y ≥ f x + (y - x) := by
  induction y, h using Nat.le_induction with
  | base => omega
  | succ y hxy ih =>
    have h1 : f (y + 1) ≥ f y + 1 := hf (lt_add_one y)
    omega

lemma sInf_eq {S : Set ℕ} {V : ℕ} (h1 : V ∈ S) (h2 : ∀ m < V, m ∉ S) : sInf S = V := by
  have h_nonempty : S.Nonempty := ⟨V, h1⟩
  have h_le : sInf S ≤ V := Nat.sInf_le h1
  have h_ge : sInf S ≥ V := by
    by_contra h_lt
    have h_lt' : sInf S < V := by omega
    have h_mem : sInf S ∈ S := Nat.sInf_mem h_nonempty
    exact h2 (sInf S) h_lt' h_mem
  omega

lemma a_31_eq_95 : a 31 = 95 := by
  unfold a
  apply sInf_eq
  · simp only [Set.mem_setOf_eq]
    decide
  · intro m hm
    have h_dec : ∀ x < 95, A047983_count x ≠ 31 := by decide
    exact h_dec m hm

lemma a_le_31_of_le_10 {n : ℕ} (hn : n > 0) (hn10 : n ≤ 10) : a n ≤ 31 := by
  interval_cases n
  · have h : A047983_count 3 = 1 := by decide
    have h_le : a 1 ≤ 3 := Nat.sInf_le h
    omega
  · have h : A047983_count 5 = 2 := by decide
    have h_le : a 2 ≤ 5 := Nat.sInf_le h
    omega
  · have h : A047983_count 7 = 3 := by decide
    have h_le : a 3 ≤ 7 := Nat.sInf_le h
    omega
  · have h : A047983_count 11 = 4 := by decide
    have h_le : a 4 ≤ 11 := Nat.sInf_le h
    omega
  · have h : A047983_count 13 = 5 := by decide
    have h_le : a 5 ≤ 13 := Nat.sInf_le h
    omega
  · have h : A047983_count 17 = 6 := by decide
    have h_le : a 6 ≤ 17 := Nat.sInf_le h
    omega
  · have h : A047983_count 19 = 7 := by decide
    have h_le : a 7 ≤ 19 := Nat.sInf_le h
    omega
  · have h : A047983_count 23 = 8 := by decide
    have h_le : a 8 ≤ 23 := Nat.sInf_le h
    omega
  · have h : A047983_count 29 = 9 := by decide
    have h_le : a 9 ≤ 29 := Nat.sInf_le h
    omega
  · have h : A047983_count 31 = 10 := by decide
    have h_le : a 10 ≤ 31 := Nat.sInf_le h
    omega

lemma a_11_eq_35 : a 11 = 35 := by
  unfold a
  apply sInf_eq
  · simp only [Set.mem_setOf_eq]
    decide
  · intro m hm
    have h_dec : ∀ x < 35, A047983_count x ≠ 11 := by decide
    exact h_dec m hm

lemma prime_ge_add_two {p q : ℕ} (hp : Nat.Prime p) (hp2 : p > 2) (hq : Nat.Prime q) (hpq : p < q) : q ≥ p + 2 := by
  by_contra h
  have h1 : q = p + 1 := by omega
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with hp_eq_two | hp_odd
    · subst hp_eq_two
      omega
    · exact hp_odd
  have hq_even : q % 2 = 0 := by
    rw [h1]
    omega
  have hq2 : q > 2 := by omega
  have hq_prime : ¬ Nat.Prime q := by
    intro hq_pr
    have h2_div_q : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq_even
    rcases (Nat.dvd_prime hq_pr).mp h2_div_q with h_eq_one | h_eq_two
    · contradiction
    · subst h_eq_two
      omega
  contradiction

lemma nth_prime_ge_two_mul_add_eleven (n : ℕ) (hn : n ≥ 10) : nth Nat.Prime n ≥ 2 * n + 11 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h_nth : nth Nat.Prime 10 = 31 := nth_prime_ten
    rw [h_nth]
  | succ n hn ih =>
    have hpn : Nat.Prime (nth Nat.Prime n) := nth_mem_of_infinite infinite_setOf_prime n
    have hpn2 : nth Nat.Prime n > 2 := by
      have h10 : nth Nat.Prime n ≥ nth Nat.Prime 10 := (nth_monotone infinite_setOf_prime) hn
      rw [nth_prime_ten] at h10
      omega
    have hpn_succ : Nat.Prime (nth Nat.Prime (n + 1)) := nth_mem_of_infinite infinite_setOf_prime (n + 1)
    have h_lt : nth Nat.Prime n < nth Nat.Prime (n + 1) := by
      rw [nth_lt_nth infinite_setOf_prime]
      omega
    have h_ge := prime_ge_add_two hpn hpn2 hpn_succ h_lt
    omega

def M_val (n : ℕ) : ℕ :=
  if n = 11 then 35
  else if n = 12 then 38
  else if n = 13 then 39
  else if n = 14 then 46
  else if n = 15 then 51
  else if n = 16 then 55
  else if n = 17 then 57
  else if n = 18 then 58
  else if n = 19 then 62
  else if n = 20 then 65
  else if n = 21 then 69
  else if n = 22 then 74
  else if n = 23 then 77
  else if n = 24 then 82
  else if n = 25 then 85
  else if n = 26 then 86
  else if n = 27 then 87
  else if n = 28 then 91
  else if n = 29 then 93
  else if n = 30 then 94
  else if n = 31 then 95
  else 0

lemma M_val_count {n : ℕ} (hn : n ≥ 11) (hn31 : n ≤ 31) : A047983_count (M_val n) = n := by
  interval_cases n <;> decide

lemma nth_prime_eq {n p : ℕ} (hp : Nat.Prime p) (hc : count Nat.Prime p = n) : nth Nat.Prime n = p := by
  have h := nth_count hp
  rw [hc] at h
  exact h

lemma count_prime_31 : count Nat.Prime 31 = 10 := by decide

lemma count_prime_37 : count Nat.Prime 37 = 11 := by
  have h := count_add Nat.Prime 31 6
  rw [h, count_prime_31]
  decide

lemma count_prime_41 : count Nat.Prime 41 = 12 := by
  have h := count_add Nat.Prime 37 4
  rw [h, count_prime_37]
  decide

lemma count_prime_43 : count Nat.Prime 43 = 13 := by
  have h := count_add Nat.Prime 41 2
  rw [h, count_prime_41]
  decide

lemma count_prime_47 : count Nat.Prime 47 = 14 := by
  have h := count_add Nat.Prime 43 4
  rw [h, count_prime_43]
  decide

lemma count_prime_53 : count Nat.Prime 53 = 15 := by
  have h := count_add Nat.Prime 47 6
  rw [h, count_prime_47]
  decide

lemma count_prime_59 : count Nat.Prime 59 = 16 := by
  have h := count_add Nat.Prime 53 6
  rw [h, count_prime_53]
  decide

lemma count_prime_61 : count Nat.Prime 61 = 17 := by
  have h := count_add Nat.Prime 59 2
  rw [h, count_prime_59]
  decide

lemma count_prime_67 : count Nat.Prime 67 = 18 := by
  have h := count_add Nat.Prime 61 6
  rw [h, count_prime_61]
  decide

lemma count_prime_71 : count Nat.Prime 71 = 19 := by
  have h := count_add Nat.Prime 67 4
  rw [h, count_prime_67]
  decide

lemma count_prime_73 : count Nat.Prime 73 = 20 := by
  have h := count_add Nat.Prime 71 2
  rw [h, count_prime_71]
  decide

lemma count_prime_79 : count Nat.Prime 79 = 21 := by
  have h := count_add Nat.Prime 73 6
  rw [h, count_prime_73]
  decide

lemma count_prime_83 : count Nat.Prime 83 = 22 := by
  have h := count_add Nat.Prime 79 4
  rw [h, count_prime_79]
  decide

lemma count_prime_89 : count Nat.Prime 89 = 23 := by
  have h := count_add Nat.Prime 83 6
  rw [h, count_prime_83]
  decide

lemma count_prime_97 : count Nat.Prime 97 = 24 := by
  have h := count_add Nat.Prime 89 8
  rw [h, count_prime_89]
  decide

lemma count_prime_101 : count Nat.Prime 101 = 25 := by
  have h := count_add Nat.Prime 97 4
  rw [h, count_prime_97]
  decide

lemma count_prime_103 : count Nat.Prime 103 = 26 := by
  have h := count_add Nat.Prime 101 2
  rw [h, count_prime_101]
  decide

lemma count_prime_107 : count Nat.Prime 107 = 27 := by
  have h := count_add Nat.Prime 103 4
  rw [h, count_prime_103]
  decide

lemma count_prime_109 : count Nat.Prime 109 = 28 := by
  have h := count_add Nat.Prime 107 2
  rw [h, count_prime_107]
  decide

lemma count_prime_113 : count Nat.Prime 113 = 29 := by
  have h := count_add Nat.Prime 109 4
  rw [h, count_prime_109]
  decide

lemma count_prime_127 : count Nat.Prime 127 = 30 := by
  have h := count_add Nat.Prime 113 14
  rw [h, count_prime_113]
  decide

lemma count_prime_131 : count Nat.Prime 131 = 31 := by
  have h := count_add Nat.Prime 127 4
  rw [h, count_prime_127]
  decide

lemma count_prime_137 : count Nat.Prime 137 = 32 := by
  have h := count_add Nat.Prime 131 6
  rw [h, count_prime_131]
  decide

lemma count_prime_149 : count Nat.Prime 149 = 34 := by
  have h := count_add Nat.Prime 137 12
  rw [h, count_prime_137]
  decide

lemma count_prime_173 : count Nat.Prime 173 = 39 := by
  have h := count_add Nat.Prime 149 24
  rw [h, count_prime_149]
  decide

lemma count_prime_197 : count Nat.Prime 197 = 44 := by
  have h := count_add Nat.Prime 173 24
  rw [h, count_prime_173]
  decide

lemma count_prime_229 : count Nat.Prime 229 = 49 := by
  have h := count_add Nat.Prime 197 32
  rw [h, count_prime_197]
  decide

lemma count_prime_269 : count Nat.Prime 269 = 56 := by
  have h := count_add Nat.Prime 229 40
  rw [h, count_prime_229]
  decide

lemma count_prime_281 : count Nat.Prime 281 = 59 := by
  have h := count_add Nat.Prime 269 12
  rw [h, count_prime_269]
  decide

lemma count_prime_321 : count Nat.Prime 321 = 66 := by
  have h := count_add Nat.Prime 281 40
  rw [h, count_prime_281]
  decide

lemma count_prime_347 : count Nat.Prime 347 = 68 := by
  have h := count_add Nat.Prime 321 26
  rw [h, count_prime_321]
  decide

lemma count_prime_359 : count Nat.Prime 359 = 71 := by
  have h := count_add Nat.Prime 347 12
  rw [h, count_prime_347]
  decide

lemma count_prime_387 : count Nat.Prime 387 = 76 := by
  have h := count_add Nat.Prime 347 40
  rw [h, count_prime_347]
  decide

lemma count_prime_397 : count Nat.Prime 397 = 77 := by
  have h := count_add Nat.Prime 387 10
  rw [h, count_prime_387]
  decide

lemma count_prime_431 : count Nat.Prime 431 = 82 := by
  have h := count_add Nat.Prime 387 44
  rw [h, count_prime_387]
  decide

lemma count_prime_471 : count Nat.Prime 471 = 91 := by
  have h := count_add Nat.Prime 431 40
  rw [h, count_prime_431]
  decide

lemma count_prime_511 : count Nat.Prime 511 = 97 := by
  have h := count_add Nat.Prime 471 40
  rw [h, count_prime_471]
  decide

lemma count_prime_523 : count Nat.Prime 523 = 98 := by
  have h := count_add Nat.Prime 511 12
  rw [h, count_prime_511]
  decide

lemma count_prime_563 : count Nat.Prime 563 = 102 := by
  have h := count_add Nat.Prime 523 40
  rw [h, count_prime_523]
  decide

lemma count_prime_603 : count Nat.Prime 603 = 110 := by
  have h := count_add Nat.Prime 563 40
  rw [h, count_prime_563]
  decide

lemma count_prime_643 : count Nat.Prime 643 = 116 := by
  have h := count_add Nat.Prime 603 40
  rw [h, count_prime_603]
  decide

lemma nth_prime_11 : nth Nat.Prime 11 = 37 := nth_prime_eq (by decide) count_prime_37
lemma nth_prime_12 : nth Nat.Prime 12 = 41 := nth_prime_eq (by decide) count_prime_41
lemma nth_prime_13 : nth Nat.Prime 13 = 43 := nth_prime_eq (by decide) count_prime_43
lemma nth_prime_14 : nth Nat.Prime 14 = 47 := nth_prime_eq (by decide) count_prime_47
lemma nth_prime_15 : nth Nat.Prime 15 = 53 := nth_prime_eq (by decide) count_prime_53
lemma nth_prime_16 : nth Nat.Prime 16 = 59 := nth_prime_eq (by decide) count_prime_59
lemma nth_prime_17 : nth Nat.Prime 17 = 61 := nth_prime_eq (by decide) count_prime_61
lemma nth_prime_18 : nth Nat.Prime 18 = 67 := nth_prime_eq (by decide) count_prime_67
lemma nth_prime_19 : nth Nat.Prime 19 = 71 := nth_prime_eq (by decide) count_prime_71
lemma nth_prime_20 : nth Nat.Prime 20 = 73 := nth_prime_eq (by decide) count_prime_73
lemma nth_prime_21 : nth Nat.Prime 21 = 79 := nth_prime_eq (by decide) count_prime_79
lemma nth_prime_22 : nth Nat.Prime 22 = 83 := nth_prime_eq (by decide) count_prime_83
lemma nth_prime_23 : nth Nat.Prime 23 = 89 := nth_prime_eq (by decide) count_prime_89
lemma nth_prime_24 : nth Nat.Prime 24 = 97 := nth_prime_eq (by decide) count_prime_97
lemma nth_prime_25 : nth Nat.Prime 25 = 101 := nth_prime_eq (by decide) count_prime_101
lemma nth_prime_26 : nth Nat.Prime 26 = 103 := nth_prime_eq (by decide) count_prime_103
lemma nth_prime_27 : nth Nat.Prime 27 = 107 := nth_prime_eq (by decide) count_prime_107
lemma nth_prime_28 : nth Nat.Prime 28 = 109 := nth_prime_eq (by decide) count_prime_109
lemma nth_prime_29 : nth Nat.Prime 29 = 113 := nth_prime_eq (by decide) count_prime_113
lemma nth_prime_30 : nth Nat.Prime 30 = 127 := nth_prime_eq (by decide) count_prime_127
lemma nth_prime_31 : nth Nat.Prime 31 = 131 := nth_prime_eq (by decide) count_prime_131
lemma nth_prime_32 : nth Nat.Prime 32 = 137 := nth_prime_eq (by decide) count_prime_137
lemma nth_prime_34 : nth Nat.Prime 34 = 149 := nth_prime_eq (by decide) count_prime_149
lemma nth_prime_39 : nth Nat.Prime 39 = 173 := nth_prime_eq (by decide) count_prime_173
lemma nth_prime_44 : nth Nat.Prime 44 = 197 := nth_prime_eq (by decide) count_prime_197
lemma nth_prime_46 : nth Nat.Prime 46 = 211 := nth_prime_eq (by decide) (by
  have h := count_add Nat.Prime 197 14
  rw [h, count_prime_197]
  decide)
lemma nth_prime_49 : nth Nat.Prime 49 = 229 := nth_prime_eq (by decide) count_prime_229
lemma nth_prime_59 : nth Nat.Prime 59 = 281 := nth_prime_eq (by decide) count_prime_281
lemma nth_prime_68 : nth Nat.Prime 68 = 347 := nth_prime_eq (by decide) count_prime_347
lemma nth_prime_71 : nth Nat.Prime 71 = 359 := nth_prime_eq (by decide) count_prime_359
lemma nth_prime_77 : nth Nat.Prime 77 = 397 := nth_prime_eq (by decide) count_prime_397
lemma nth_prime_82 : nth Nat.Prime 82 = 431 := nth_prime_eq (by decide) count_prime_431
lemma nth_prime_98 : nth Nat.Prime 98 = 523 := nth_prime_eq (by decide) count_prime_523
lemma nth_prime_116 : nth Nat.Prime 116 = 643 := nth_prime_eq (by decide) count_prime_643

lemma nth_prime_120 : nth Nat.Prime 120 = 661 := by
  have h117 : nth Nat.Prime 117 = 647 := nth_prime_next nth_prime_116 (by decide) (by decide) (by decide)
  have h118 : nth Nat.Prime 118 = 653 := nth_prime_next h117 (by decide) (by decide) (by decide)
  have h119 : nth Nat.Prime 119 = 659 := nth_prime_next h118 (by decide) (by decide) (by decide)
  exact nth_prime_next h119 (by decide) (by decide) (by decide)

lemma nth_prime_124 : nth Nat.Prime 124 = 691 := by
  have h121 : nth Nat.Prime 121 = 673 := nth_prime_next nth_prime_120 (by decide) (by decide) (by decide)
  have h122 : nth Nat.Prime 122 = 677 := nth_prime_next h121 (by decide) (by decide) (by decide)
  have h123 : nth Nat.Prime 123 = 683 := nth_prime_next h122 (by decide) (by decide) (by decide)
  exact nth_prime_next h123 (by decide) (by decide) (by decide)

lemma nth_prime_128 : nth Nat.Prime 128 = 727 := by
  have h125 : nth Nat.Prime 125 = 701 := nth_prime_next nth_prime_124 (by decide) (by decide) (by decide)
  have h126 : nth Nat.Prime 126 = 709 := nth_prime_next h125 (by decide) (by decide) (by decide)
  have h127 : nth Nat.Prime 127 = 719 := nth_prime_next h126 (by decide) (by decide) (by decide)
  exact nth_prime_next h127 (by decide) (by decide) (by decide)

lemma nth_prime_132 : nth Nat.Prime 132 = 751 := by
  have h129 : nth Nat.Prime 129 = 733 := nth_prime_next nth_prime_128 (by decide) (by decide) (by decide)
  have h130 : nth Nat.Prime 130 = 739 := nth_prime_next h129 (by decide) (by decide) (by decide)
  have h131 : nth Nat.Prime 131 = 743 := nth_prime_next h130 (by decide) (by decide) (by decide)
  exact nth_prime_next h131 (by decide) (by decide) (by decide)

lemma nth_prime_136 : nth Nat.Prime 136 = 773 := by
  have h133 : nth Nat.Prime 133 = 757 := nth_prime_next nth_prime_132 (by decide) (by decide) (by decide)
  have h134 : nth Nat.Prime 134 = 761 := nth_prime_next h133 (by decide) (by decide) (by decide)
  have h135 : nth Nat.Prime 135 = 769 := nth_prime_next h134 (by decide) (by decide) (by decide)
  exact nth_prime_next h135 (by decide) (by decide) (by decide)

lemma nth_prime_138 : nth Nat.Prime 138 = 797 := by
  have h137 : nth Nat.Prime 137 = 787 := nth_prime_next nth_prime_136 (by decide) (by decide) (by decide)
  exact nth_prime_next h137 (by decide) (by decide) (by decide)

lemma nth_prime_141 : nth Nat.Prime 141 = 821 := by
  have h139 : nth Nat.Prime 139 = 809 := nth_prime_next nth_prime_138 (by decide) (by decide) (by decide)
  have h140 : nth Nat.Prime 140 = 811 := nth_prime_next h139 (by decide) (by decide) (by decide)
  exact nth_prime_next h140 (by decide) (by decide) (by decide)

lemma nth_prime_142 : nth Nat.Prime 142 = 823 :=
  nth_prime_next nth_prime_141 (by decide) (by decide) (by decide)

lemma nth_prime_146 : nth Nat.Prime 146 = 853 := by
  have h143 : nth Nat.Prime 143 = 827 := nth_prime_next nth_prime_142 (by decide) (by decide) (by decide)
  have h144 : nth Nat.Prime 144 = 829 := nth_prime_next h143 (by decide) (by decide) (by decide)
  have h145 : nth Nat.Prime 145 = 839 := nth_prime_next h144 (by decide) (by decide) (by decide)
  exact nth_prime_next h145 (by decide) (by decide) (by decide)

lemma nth_prime_150 : nth Nat.Prime 150 = 877 := by
  have h147 : nth Nat.Prime 147 = 857 := nth_prime_next nth_prime_146 (by decide) (by decide) (by decide)
  have h148 : nth Nat.Prime 148 = 859 := nth_prime_next h147 (by decide) (by decide) (by decide)
  have h149 : nth Nat.Prime 149 = 863 := nth_prime_next h148 (by decide) (by decide) (by decide)
  exact nth_prime_next h149 (by decide) (by decide) (by decide)

lemma nth_prime_151 : nth Nat.Prime 151 = 881 :=
  nth_prime_next nth_prime_150 (by decide) (by decide) (by decide)

lemma nth_prime_154 : nth Nat.Prime 154 = 907 := by
  have h152 : nth Nat.Prime 152 = 883 := nth_prime_next nth_prime_151 (by decide) (by decide) (by decide)
  have h153 : nth Nat.Prime 153 = 887 := nth_prime_next h152 (by decide) (by decide) (by decide)
  exact nth_prime_next h153 (by decide) (by decide) (by decide)

lemma nth_prime_158 : nth Nat.Prime 158 = 937 := by
  have h155 : nth Nat.Prime 155 = 911 := nth_prime_next nth_prime_154 (by decide) (by decide) (by decide)
  have h156 : nth Nat.Prime 156 = 919 := nth_prime_next h155 (by decide) (by decide) (by decide)
  have h157 : nth Nat.Prime 157 = 929 := nth_prime_next h156 (by decide) (by decide) (by decide)
  exact nth_prime_next h157 (by decide) (by decide) (by decide)

lemma nth_prime_162 : nth Nat.Prime 162 = 967 := by
  have h159 : nth Nat.Prime 159 = 941 := nth_prime_next nth_prime_158 (by decide) (by decide) (by decide)
  have h160 : nth Nat.Prime 160 = 947 := nth_prime_next h159 (by decide) (by decide) (by decide)
  have h161 : nth Nat.Prime 161 = 953 := nth_prime_next h160 (by decide) (by decide) (by decide)
  exact nth_prime_next h161 (by decide) (by decide) (by decide)

lemma nth_prime_165 : nth Nat.Prime 165 = 983 := by
  have h163 : nth Nat.Prime 163 = 971 := nth_prime_next nth_prime_162 (by decide) (by decide) (by decide)
  have h164 : nth Nat.Prime 164 = 977 := nth_prime_next h163 (by decide) (by decide) (by decide)
  exact nth_prime_next h164 (by decide) (by decide) (by decide)

lemma nth_prime_169 : nth Nat.Prime 169 = 1013 := by
  have h166 : nth Nat.Prime 166 = 991 := nth_prime_next nth_prime_165 (by decide) (by decide) (by decide)
  have h167 : nth Nat.Prime 167 = 997 := nth_prime_next h166 (by decide) (by decide) (by decide)
  have h168 : nth Nat.Prime 168 = 1009 := nth_prime_next h167 (by decide) (by decide) (by decide)
  exact nth_prime_next h168 (by decide) (by decide) (by decide)

lemma nth_prime_173 : nth Nat.Prime 173 = 1033 := by
  have h170 : nth Nat.Prime 170 = 1019 := nth_prime_next nth_prime_169 (by decide) (by decide) (by decide)
  have h171 : nth Nat.Prime 171 = 1021 := nth_prime_next h170 (by decide) (by decide) (by decide)
  have h172 : nth Nat.Prime 172 = 1031 := nth_prime_next h171 (by decide) (by decide) (by decide)
  exact nth_prime_next h172 (by decide) (by decide) (by decide)

lemma nth_prime_177 : nth Nat.Prime 177 = 1061 := by
  have h174 : nth Nat.Prime 174 = 1039 := nth_prime_next nth_prime_173 (by decide) (by decide) (by decide)
  have h175 : nth Nat.Prime 175 = 1049 := nth_prime_next h174 (by decide) (by decide) (by decide)
  have h176 : nth Nat.Prime 176 = 1051 := nth_prime_next h175 (by decide) (by decide) (by decide)
  exact nth_prime_next h176 (by decide) (by decide) (by decide)

lemma nth_prime_181 : nth Nat.Prime 181 = 1091 := by
  have h178 : nth Nat.Prime 178 = 1063 := nth_prime_next nth_prime_177 (by decide) (by decide) (by decide)
  have h179 : nth Nat.Prime 179 = 1069 := nth_prime_next h178 (by decide) (by decide) (by decide)
  have h180 : nth Nat.Prime 180 = 1087 := nth_prime_next h179 (by decide) (by decide) (by decide)
  exact nth_prime_next h180 (by decide) (by decide) (by decide)

lemma nth_prime_185 : nth Nat.Prime 185 = 1109 := by
  have h182 : nth Nat.Prime 182 = 1093 := nth_prime_next nth_prime_181 (by decide) (by decide) (by decide)
  have h183 : nth Nat.Prime 183 = 1097 := nth_prime_next h182 (by decide) (by decide) (by decide)
  have h184 : nth Nat.Prime 184 = 1103 := nth_prime_next h183 (by decide) (by decide) (by decide)
  exact nth_prime_next h184 (by decide) (by decide) (by decide)

lemma nth_prime_189 : nth Nat.Prime 189 = 1151 := by
  have h186 : nth Nat.Prime 186 = 1117 := nth_prime_next nth_prime_185 (by decide) (by decide) (by decide)
  have h187 : nth Nat.Prime 187 = 1123 := nth_prime_next h186 (by decide) (by decide) (by decide)
  have h188 : nth Nat.Prime 188 = 1129 := nth_prime_next h187 (by decide) (by decide) (by decide)
  exact nth_prime_next h188 (by decide) (by decide) (by decide)

lemma nth_prime_193 : nth Nat.Prime 193 = 1181 := by
  have h190 : nth Nat.Prime 190 = 1153 := nth_prime_next nth_prime_189 (by decide) (by decide) (by decide)
  have h191 : nth Nat.Prime 191 = 1163 := nth_prime_next h190 (by decide) (by decide) (by decide)
  have h192 : nth Nat.Prime 192 = 1171 := nth_prime_next h191 (by decide) (by decide) (by decide)
  exact nth_prime_next h192 (by decide) (by decide) (by decide)

lemma nth_prime_197 : nth Nat.Prime 197 = 1213 := by
  have h194 : nth Nat.Prime 194 = 1187 := nth_prime_next nth_prime_193 (by decide) (by decide) (by decide)
  have h195 : nth Nat.Prime 195 = 1193 := nth_prime_next h194 (by decide) (by decide) (by decide)
  have h196 : nth Nat.Prime 196 = 1201 := nth_prime_next h195 (by decide) (by decide) (by decide)
  exact nth_prime_next h196 (by decide) (by decide) (by decide)

lemma M_val_lt_nth_prime {n : ℕ} (hn : n ≥ 11) (hn31 : n ≤ 31) : M_val n < nth Nat.Prime n := by
  interval_cases n
  · rw [nth_prime_11]; decide
  · rw [nth_prime_12]; decide
  · rw [nth_prime_13]; decide
  · rw [nth_prime_14]; decide
  · rw [nth_prime_15]; decide
  · rw [nth_prime_16]; decide
  · rw [nth_prime_17]; decide
  · rw [nth_prime_18]; decide
  · rw [nth_prime_19]; decide
  · rw [nth_prime_20]; decide
  · rw [nth_prime_21]; decide
  · rw [nth_prime_22]; decide
  · rw [nth_prime_23]; decide
  · rw [nth_prime_24]; decide
  · rw [nth_prime_25]; decide
  · rw [nth_prime_26]; decide
  · rw [nth_prime_27]; decide
  · rw [nth_prime_28]; decide
  · rw [nth_prime_29]; decide
  · rw [nth_prime_30]; decide
  · rw [nth_prime_31]; decide

lemma a_lt_nth_prime_of_le_31 {n : ℕ} (hn : n ≥ 11) (hn31 : n ≤ 31) : a n < nth Nat.Prime n := by
  have h_mem : A047983_count (M_val n) = n := M_val_count hn hn31
  have h_le : a n ≤ M_val n := Nat.sInf_le h_mem
  have h_lt : M_val n < nth Nat.Prime n := M_val_lt_nth_prime hn hn31
  omega

set_option maxHeartbeats 0

lemma Ico_succ_top_eq (X : ℕ) (hX : X ≥ 1) : Finset.Ico 1 (X + 1) = insert X (Finset.Ico 1 X) := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_insert]
  omega

noncomputable def C4 (X : ℕ) : ℕ := ((Finset.Ico 1 X).filter (fun k => tau k = 4)).card

lemma C4_succ (X : ℕ) : C4 (X + 1) = C4 X + if tau X = 4 then 1 else 0 := by
  by_cases hX : X ≥ 1
  · unfold C4
    rw [Ico_succ_top_eq X hX, filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem]
      · simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
    · omega
  · have hX0 : X = 0 := by omega
    subst hX0
    unfold C4
    rfl

lemma exists_of_C4_ge (n : ℕ) (X : ℕ) (hC : C4 X ≥ n + 1) : ∃ M < X, tau M = 4 ∧ C4 M = n := by
  induction X with
  | zero =>
    unfold C4 at hC
    simp at hC
  | succ X ih =>
    rw [C4_succ] at hC
    by_cases hX : C4 X ≥ n + 1
    · obtain ⟨M, hM1, hM2, hM3⟩ := ih hX
      exact ⟨M, hM1.trans (lt_add_one X), hM2, hM3⟩
    · split_ifs at hC with h_tau
      · have hCX : C4 X = n := by omega
        exact ⟨X, lt_add_one X, h_tau, hCX⟩
      · omega

lemma A047983_count_eq_C4 {M : ℕ} (hM : tau M = 4) : A047983_count M = C4 M := by
  unfold A047983_count
  rw [hM]
  rfl

lemma C4_monotone {X Y : ℕ} (h : X ≤ Y) : C4 X ≤ C4 Y := by
  unfold C4
  apply Finset.card_le_card
  apply filter_subset_filter
  intro x hx
  rw [Finset.mem_Ico] at hx ⊢
  omega

lemma tau_mul {m n : ℕ} (h : Nat.Coprime m n) : tau (m * n) = tau m * tau n := by
  unfold tau
  exact Nat.Coprime.card_divisors_mul h

lemma tau_two_mul_prime {p : ℕ} (hp : Nat.Prime p) (hp2 : p > 2) : tau (2 * p) = 4 := by
  have h_coprime : Nat.Coprime p 2 := by
    rw [hp.coprime_iff_not_dvd]
    intro h_dvd
    have : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have h_coprime2 := h_coprime.symm
  rw [tau_mul h_coprime2]
  have h_tau2 : tau 2 = 2 := tau_of_prime prime_two
  have h_taup : tau p = 2 := tau_of_prime hp
  rw [h_tau2, h_taup]

lemma tau_three_mul_prime {p : ℕ} (hp : Nat.Prime p) (hp3 : p > 3) : tau (3 * p) = 4 := by
  have h_coprime : Nat.Coprime p 3 := by
    rw [hp.coprime_iff_not_dvd]
    intro h_dvd
    have : p ≤ 3 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have h_coprime2 := h_coprime.symm
  rw [tau_mul h_coprime2]
  have h_tau3 : tau 3 = 2 := tau_of_prime prime_three
  have h_taup : tau p = 2 := tau_of_prime hp
  rw [h_tau3, h_taup]

lemma tau_five_mul_prime {p : ℕ} (hp : Nat.Prime p) (hp5 : p > 5) : tau (5 * p) = 4 := by
  have h_coprime : Nat.Coprime p 5 := by
    rw [hp.coprime_iff_not_dvd]
    intro h_dvd
    have : p ≤ 5 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have h_coprime2 := h_coprime.symm
  rw [tau_mul h_coprime2]
  have h_tau5 : tau 5 = 2 := tau_of_prime prime_five
  have h_taup : tau p = 2 := tau_of_prime hp
  rw [h_tau5, h_taup]

lemma nth_prime_succ_le_two_mul (k : ℕ) : nth Nat.Prime (k + 1) ≤ 2 * nth Nat.Prime k := by
  have hpk : nth Nat.Prime k ≠ 0 := by
    have := nth_mem_of_infinite infinite_setOf_prime k
    exact Nat.Prime.ne_zero this
  obtain ⟨p, hp_prime, hp_lt, hp_le⟩ := exists_prime_lt_and_le_two_mul (nth Nat.Prime k) hpk
  have h_count_gt : k < count Nat.Prime p := by
    by_contra h_le
    have h_le' : count Nat.Prime p ≤ k := by omega
    have h_le_nth : p ≤ nth Nat.Prime k := by
      rwa [count_le_iff_le_nth infinite_setOf_prime] at h_le'
    omega
  have h_count_ge : count Nat.Prime p ≥ k + 1 := by omega
  have h_nth_mono := (nth_monotone infinite_setOf_prime) h_count_ge
  have h_nth_count : nth Nat.Prime (count Nat.Prime p) = p := nth_count hp_prime
  rw [h_nth_count] at h_nth_mono
  exact h_nth_mono.trans hp_le

lemma prime_odd_of_ge_3 {p : ℕ} (hp : Nat.Prime p) (hp3 : p ≥ 3) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with rfl | hp_odd
  · omega
  · exact hp_odd

abbrev S2 (X : ℕ) : Finset ℕ := ((Finset.Ico 1 (X/2)).filter (fun p => Nat.Prime p ∧ p ≥ 3)).image (fun p => 2 * p)
abbrev S3 (X : ℕ) : Finset ℕ := ((Finset.Ico 1 (X/3)).filter (fun p => Nat.Prime p ∧ p ≥ 5)).image (fun p => 3 * p)
abbrev S5 (X : ℕ) : Finset ℕ := ((Finset.Ico 1 (X/5)).filter (fun p => Nat.Prime p ∧ p ≥ 7)).image (fun p => 5 * p)

lemma disjoint_S2_S3 (X : ℕ) : Disjoint (S2 X) (S3 X) := by
  rw [disjoint_iff_ne]
  rintro x hx y hy rfl
  rw [Finset.mem_image] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, h_eq⟩ := hy
  rw [Finset.mem_filter] at hp hq
  have hp_prime : Nat.Prime p := hp.2.1
  have hp3 : p ≥ 3 := hp.2.2
  have hq_prime : Nat.Prime q := hq.2.1
  have hq5 : q ≥ 5 := hq.2.2
  have hp_odd := prime_odd_of_ge_3 hp_prime hp3
  have hq_odd := prime_odd_of_ge_3 hq_prime (by omega)
  have h_odd : (3 * q) % 2 = 1 := by
    have : 3 % 2 = 1 := by decide
    omega
  have h_even : (2 * p) % 2 = 0 := by omega
  omega

lemma disjoint_S2_S5 (X : ℕ) : Disjoint (S2 X) (S5 X) := by
  rw [disjoint_iff_ne]
  rintro x hx y hy rfl
  rw [Finset.mem_image] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, h_eq⟩ := hy
  rw [Finset.mem_filter] at hp hq
  have hp_prime : Nat.Prime p := hp.2.1
  have hp3 : p ≥ 3 := hp.2.2
  have hq_prime : Nat.Prime q := hq.2.1
  have hq7 : q ≥ 7 := hq.2.2
  have hp_odd := prime_odd_of_ge_3 hp_prime hp3
  have hq_odd := prime_odd_of_ge_3 hq_prime (by omega)
  have h_odd : (5 * q) % 2 = 1 := by omega
  have h_even : (2 * p) % 2 = 0 := by omega
  omega

lemma disjoint_S3_S5 (X : ℕ) : Disjoint (S3 X) (S5 X) := by
  rw [disjoint_iff_ne]
  rintro x hx y hy rfl
  rw [Finset.mem_image] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, h_eq⟩ := hy
  rw [Finset.mem_filter] at hp hq
  have hp_prime : Nat.Prime p := hp.2.1
  have hp5 : p ≥ 5 := hp.2.2
  have hq_prime : Nat.Prime q := hq.2.1
  have hq7 : q ≥ 7 := hq.2.2
  have h_dvd : 5 ∣ 3 * p := by
    use q
    omega
  have h_prime5 : Nat.Prime 5 := prime_five
  rcases (Nat.Prime.dvd_mul h_prime5).mp h_dvd with h_dvd_3 | h_dvd_p
  · have : ¬ 5 ∣ 3 := by decide
    contradiction
  · have hp5_eq : p = 5 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp_prime 5 h_dvd_p) with hp1 | hp5_self
      · contradiction
      · exact hp5_self.symm
    subst hp5_eq
    have hq3 : q = 3 := by omega
    omega

lemma tau_eq_four_of_mem_S2 {X : ℕ} {x : ℕ} (hx : x ∈ S2 X) : tau x = 4 ∧ x < X ∧ 1 ≤ x := by
  rw [Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_Ico] at hp
  have hp_prime : Nat.Prime p := hp.2.1
  have hp3 : p ≥ 3 := hp.2.2
  have hp_lt : p < X / 2 := hp.1.2
  refine ⟨?_, ?_, ?_⟩
  · exact tau_two_mul_prime hp_prime (by omega)
  · have : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
    omega
  · omega

lemma tau_eq_four_of_mem_S3 {X : ℕ} {x : ℕ} (hx : x ∈ S3 X) : tau x = 4 ∧ x < X ∧ 1 ≤ x := by
  rw [Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_Ico] at hp
  have hp_prime : Nat.Prime p := hp.2.1
  have hp5 : p ≥ 5 := hp.2.2
  have hp_lt : p < X / 3 := hp.1.2
  refine ⟨?_, ?_, ?_⟩
  · exact tau_three_mul_prime hp_prime (by omega)
  · have : 3 * (X / 3) ≤ X := Nat.mul_div_le X 3
    omega
  · omega

lemma tau_eq_four_of_mem_S5 {X : ℕ} {x : ℕ} (hx : x ∈ S5 X) : tau x = 4 ∧ x < X ∧ 1 ≤ x := by
  rw [Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_Ico] at hp
  have hp_prime : Nat.Prime p := hp.2.1
  have hp7 : p ≥ 7 := hp.2.2
  have hp_lt : p < X / 5 := hp.1.2
  refine ⟨?_, ?_, ?_⟩
  · exact tau_five_mul_prime hp_prime (by omega)
  · have : 5 * (X / 5) ≤ X := Nat.mul_div_le X 5
    omega
  · omega

lemma union_subset_C4 (X : ℕ) : S2 X ∪ S3 X ∪ S5 X ⊆ (Finset.Ico 1 X).filter (fun k => tau k = 4) := by
  intro x hx
  rw [Finset.mem_filter, Finset.mem_Ico]
  simp only [Finset.mem_union] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨ht, hlt, h1⟩ := tau_eq_four_of_mem_S2 hx
    refine ⟨⟨h1, hlt⟩, ht⟩
  · obtain ⟨ht, hlt, h1⟩ := tau_eq_four_of_mem_S3 hx
    refine ⟨⟨h1, hlt⟩, ht⟩
  · obtain ⟨ht, hlt, h1⟩ := tau_eq_four_of_mem_S5 hx
    refine ⟨⟨h1, hlt⟩, ht⟩

lemma union_card (X : ℕ) : #(S2 X ∪ S3 X ∪ S5 X) = #(S2 X) + #(S3 X) + #(S5 X) := by
  have h1 : Disjoint (S3 X) (S5 X) := disjoint_S3_S5 X
  have h2 : Disjoint (S2 X) (S3 X ∪ S5 X) := by
    apply Finset.disjoint_union_right.mpr
    constructor
    · exact disjoint_S2_S3 X
    · exact disjoint_S2_S5 X
  rw [Finset.union_assoc]
  rw [Finset.card_union_of_disjoint h2]
  rw [Finset.card_union_of_disjoint h1]
  omega

lemma C4_ge_union (X : ℕ) : C4 X ≥ #(S2 X) + #(S3 X) + #(S5 X) := by
  have h1 : #(S2 X ∪ S3 X ∪ S5 X) ≤ C4 X := by
    unfold C4
    exact Finset.card_le_card (union_subset_C4 X)
  rw [union_card X] at h1
  exact h1

lemma card_S2 (X : ℕ) : #(S2 X) = ((Finset.Ico 1 (X/2)).filter (fun p => Nat.Prime p ∧ p ≥ 3)).card := by
  unfold S2
  apply Finset.card_image_of_injective
  intro a b hab
  dsimp at hab
  omega

lemma card_S3 (X : ℕ) : #(S3 X) = ((Finset.Ico 1 (X/3)).filter (fun p => Nat.Prime p ∧ p ≥ 5)).card := by
  unfold S3
  apply Finset.card_image_of_injective
  intro a b hab
  dsimp at hab
  omega

lemma card_S5 (X : ℕ) : #(S5 X) = ((Finset.Ico 1 (X/5)).filter (fun p => Nat.Prime p ∧ p ≥ 7)).card := by
  unfold S5
  apply Finset.card_image_of_injective
  intro a b hab
  dsimp at hab
  omega

lemma filter_prime_Ico_eq_range_filter_ge (Y : ℕ) (p0 : ℕ) :
  ((Finset.Ico 1 Y).filter (fun p => Nat.Prime p ∧ p ≥ p0)) = ((Finset.range Y).filter (fun p => Nat.Prime p ∧ p ≥ p0)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp, hp0⟩
    exact ⟨h2, hp, hp0⟩
  · rintro ⟨h2, hp, hp0⟩
    refine ⟨⟨?_, h2⟩, hp, hp0⟩
    exact hp.one_lt.le

def prime_count_ge (Y : ℕ) (p0 : ℕ) : ℕ :=
  ((Finset.range Y).filter (fun p => Nat.Prime p ∧ p ≥ p0)).card

lemma card_S2_eq (X : ℕ) : #(S2 X) = prime_count_ge (X/2) 3 := by
  rw [card_S2, filter_prime_Ico_eq_range_filter_ge]
  rfl

lemma card_S3_eq (X : ℕ) : #(S3 X) = prime_count_ge (X/3) 5 := by
  rw [card_S3, filter_prime_Ico_eq_range_filter_ge]
  rfl

lemma card_S5_eq (X : ℕ) : #(S5 X) = prime_count_ge (X/5) 7 := by
  rw [card_S5, filter_prime_Ico_eq_range_filter_ge]
  rfl

def C4_lower (X : ℕ) : ℕ :=
  prime_count_ge (X / 2) 3 + prime_count_ge (X / 3) 5 + prime_count_ge (X / 5) 7

lemma C4_ge_lower (X : ℕ) : C4 X ≥ C4_lower X := by
  have := C4_ge_union X
  rw [card_S2_eq, card_S3_eq, card_S5_eq] at this
  exact this

lemma prime_count_ge_monotone (p0 : ℕ) : Monotone (fun Y => prime_count_ge Y p0) := by
  intro Y1 Y2 hY
  unfold prime_count_ge
  apply Finset.card_le_card
  apply filter_subset_filter
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

lemma C4_lower_monotone : Monotone C4_lower := by
  intro X1 X2 hX
  unfold C4_lower
  have h1 : X1 / 2 ≤ X2 / 2 := Nat.div_le_div_right hX
  have h2 : X1 / 3 ≤ X2 / 3 := Nat.div_le_div_right hX
  have h3 : X1 / 5 ≤ X2 / 5 := Nat.div_le_div_right hX
  have hm2 := prime_count_ge_monotone 3 h1
  have hm3 := prime_count_ge_monotone 5 h2
  have hm5 := prime_count_ge_monotone 7 h3
  dsimp only at hm2 hm3 hm5
  omega

lemma C4_lower_nth_prime_monotone : Monotone (fun n => C4_lower (nth Nat.Prime n)) := by
  intro n1 n2 hn
  apply C4_lower_monotone
  exact nth_monotone infinite_setOf_prime hn

lemma C4_lower_nth_prime_ge_of_le_137 {n : ℕ} (hn : n ≥ 31) (hn137 : n ≤ 137) : C4_lower (nth Nat.Prime n) ≥ n + 1 := by
  have h_mono := C4_lower_nth_prime_monotone
  rcases le_or_gt n 33 with h_33 | h_33
  · have h_le : 31 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 31) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 31) = 34 := by
      rw [nth_prime_31]
      rfl
    omega
  rcases le_or_gt n 38 with h_38 | h_38
  · have h_le : 34 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 34) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 34) = 39 := by
      rw [nth_prime_34]
      rfl
    omega
  rcases le_or_gt n 43 with h_43 | h_43
  · have h_le : 39 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 39) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 39) = 44 := by
      rw [nth_prime_39]
      rfl
    omega
  rcases le_or_gt n 48 with h_48 | h_48
  · have h_le : 44 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 44) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 44) = 49 := by
      rw [nth_prime_44]
      rfl
    omega
  rcases le_or_gt n 58 with h_58 | h_58
  · have h_le : 49 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 49) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 49) = 59 := by
      rw [nth_prime_49]
      rfl
    omega
  rcases le_or_gt n 67 with h_67 | h_67
  · have h_le : 59 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 59) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 59) = 68 := by
      rw [nth_prime_59]
      rfl
    omega
  rcases le_or_gt n 81 with h_81 | h_81
  · have h_le : 68 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 68) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 68) = 82 := by
      rw [nth_prime_68]
      rfl
    omega
  rcases le_or_gt n 97 with h_97 | h_97
  · have h_le : 82 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 82) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 82) = 98 := by
      rw [nth_prime_82]
      rfl
    omega
  rcases le_or_gt n 115 with h_115 | h_115
  · have h_le : 98 ≤ n := by omega
    have h_ge : C4_lower (nth Nat.Prime 98) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
    have h_val : C4_lower (nth Nat.Prime 98) = 116 := by
      rw [nth_prime_98]
      rfl
    omega
  have h_le : 116 ≤ n := by omega
  have h_ge : C4_lower (nth Nat.Prime 116) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
  have h_val : C4_lower (nth Nat.Prime 116) = 138 := by
    rw [nth_prime_116]
    rfl
  omega

lemma prime_step2 (k : ℕ) (hk : k ≥ 2) : nth Nat.Prime (k + 2) ≥ nth Nat.Prime k + 6 := by
  have hpk : Nat.Prime (nth Nat.Prime k) := nth_mem_of_infinite infinite_setOf_prime k
  have hpk1 : Nat.Prime (nth Nat.Prime (k + 1)) := nth_mem_of_infinite infinite_setOf_prime (k + 1)
  have hpk2 : Nat.Prime (nth Nat.Prime (k + 2)) := nth_mem_of_infinite infinite_setOf_prime (k + 2)
  have h1 : nth Nat.Prime k < nth Nat.Prime (k + 1) := (nth_lt_nth infinite_setOf_prime).mpr (by omega)
  have h2 : nth Nat.Prime (k + 1) < nth Nat.Prime (k + 2) := (nth_lt_nth infinite_setOf_prime).mpr (by omega)
  have hpk_ge_5 : nth Nat.Prime k ≥ 5 := by
    have : nth Nat.Prime k ≥ nth Nat.Prime 2 := (nth_monotone infinite_setOf_prime) hk
    have : nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
    omega
  have hpk3 : nth Nat.Prime k > 2 := by omega
  have h_ge1 : nth Nat.Prime (k + 1) ≥ nth Nat.Prime k + 2 := prime_ge_add_two hpk hpk3 hpk1 h1
  have hpk1_3 : nth Nat.Prime (k + 1) > 2 := by omega
  have h_ge2 : nth Nat.Prime (k + 2) ≥ nth Nat.Prime (k + 1) + 2 := prime_ge_add_two hpk1 hpk1_3 hpk2 h2
  have h_odd0 : nth Nat.Prime k % 2 = 1 := prime_odd_of_ge_3 hpk (by omega)
  have h_odd1 : nth Nat.Prime (k + 1) % 2 = 1 := prime_odd_of_ge_3 hpk1 (by omega)
  have h_odd2 : nth Nat.Prime (k + 2) % 2 = 1 := prime_odd_of_ge_3 hpk2 (by omega)
  by_contra h_lt
  have h_eq1 : nth Nat.Prime (k + 1) = nth Nat.Prime k + 2 := by omega
  have h_eq2 : nth Nat.Prime (k + 2) = nth Nat.Prime k + 4 := by omega
  let p := nth Nat.Prime k
  have h_mod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h_mod with hp3 | hp3 | hp3
  · have h_dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3
    have : p = 3 := by
      rcases hpk.eq_one_or_self_of_dvd 3 h_dvd with hp1 | hp3_self
      · omega
      · exact hp3_self.symm
    omega
  · have h_dvd : 3 ∣ p + 2 := by
      use p / 3 + 1
      omega
    have hp1_prime : Nat.Prime (p + 2) := by rwa [← h_eq1]
    have : p + 2 = 3 := by
      rcases hp1_prime.eq_one_or_self_of_dvd 3 h_dvd with hp1' | hp3_self'
      · omega
      · exact hp3_self'.symm
    omega
  · have h_dvd : 3 ∣ p + 4 := by
      use p / 3 + 2
      omega
    have hp2_prime : Nat.Prime (p + 4) := by rwa [← h_eq2]
    have : p + 4 = 3 := by
      rcases hp2_prime.eq_one_or_self_of_dvd 3 h_dvd with hp1'' | hp3_self''
      · omega
      · exact hp3_self''.symm
    omega

lemma nth_prime_ge_three_mul_add_38 (n : ℕ) (hn : n ≥ 31) : nth Nat.Prime n ≥ 3 * n + 38 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hn_eq : n = 31
  · subst hn_eq
    have : nth Nat.Prime 31 = 131 := by
      rw [nth_prime_31]
    omega
  by_cases hn_eq2 : n = 32
  · subst hn_eq2
    have : nth Nat.Prime 32 = 137 := by
      rw [nth_prime_32]
    omega
  have h_sub : n - 2 < n := by omega
  have h_ge : n - 2 ≥ 31 := by omega
  have ih1 := ih (n - 2) h_sub h_ge
  have h_step : nth Nat.Prime n ≥ nth Nat.Prime (n - 2) + 6 := by
    have h_eq : n = (n - 2) + 2 := by omega
    rw [h_eq]
    exact prime_step2 (n - 2) (by omega)
  omega

lemma prime_count_ge_le_sub (Y : ℕ) (p0 : ℕ) (hY : p0 ≤ Y) : prime_count_ge Y p0 ≥ count Nat.Prime Y - count Nat.Prime p0 := by
  unfold prime_count_ge
  rw [count_eq_card_filter_range, count_eq_card_filter_range]
  have h_sub : (range Y).filter (fun p => Nat.Prime p) ⊆ (range p0).filter (fun p => Nat.Prime p) ∪ (range Y).filter (fun p => Nat.Prime p ∧ p ≥ p0) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hx ⊢
    rcases hx with ⟨hx1, hx2⟩
    by_cases hxp0 : x < p0
    · left
      exact ⟨hxp0, hx2⟩
    · right
      exact ⟨hx1, hx2, by omega⟩
  have h_card := Finset.card_le_card h_sub
  have h_union : ((range p0).filter (fun p => Nat.Prime p) ∪ (range Y).filter (fun p => Nat.Prime p ∧ p ≥ p0)).card ≤ ((range p0).filter (fun p => Nat.Prime p)).card + ((range Y).filter (fun p => Nat.Prime p ∧ p ≥ p0)).card := Finset.card_union_le _ _
  omega

lemma C4_lower_ge_count_primes (X : ℕ) (hX2 : 3 ≤ X / 2) (hX3 : 5 ≤ X / 3) (hX5 : 7 ≤ X / 5) :
    C4_lower X ≥ count Nat.Prime (X/2) - 1 + (count Nat.Prime (X/3) - 2) + (count Nat.Prime (X/5) - 3) := by
  unfold C4_lower
  have h1 := prime_count_ge_le_sub (X / 2) 3 hX2
  have h2 := prime_count_ge_le_sub (X / 3) 5 hX3
  have h3 := prime_count_ge_le_sub (X / 5) 7 hX5
  have hc3 : count Nat.Prime 3 = 1 := by decide
  have hc5 : count Nat.Prime 5 = 2 := by decide
  have hc7 : count Nat.Prime 7 = 3 := by decide
  rw [hc3] at h1
  rw [hc5] at h2
  rw [hc7] at h3
  omega

lemma count_ge_helper (n A d q m : ℕ) (hn : n ≥ A) (hq : q < nth Nat.Prime A / d) (hq_idx : nth Nat.Prime m = q) :
  count Nat.Prime (nth Nat.Prime n / d) ≥ m + 1 := by
  have h1 : nth Nat.Prime A ≤ nth Nat.Prime n := nth_monotone infinite_setOf_prime hn
  have h2 : nth Nat.Prime A / d ≤ nth Nat.Prime n / d := Nat.div_le_div_right h1
  have h3 : q < nth Nat.Prime n / d := hq.trans_le h2
  have h4 : q + 1 ≤ nth Nat.Prime n / d := h3
  have h5 : count Nat.Prime (q + 1) ≤ count Nat.Prime (nth Nat.Prime n / d) := count_monotone _ h4
  have h6 : count Nat.Prime (q + 1) = m + 1 := by
    rw [count_succ, ← hq_idx, count_nth_of_infinite infinite_setOf_prime]
    have hp : Nat.Prime (nth Nat.Prime m) := nth_mem_of_infinite infinite_setOf_prime m
    rw [if_pos hp]
  omega

lemma C4_lower_nth_prime_ge_of_ge_138 {n : ℕ} (hn : n ≥ 138) : C4_lower (nth Nat.Prime n) ≥ n + 1 := by
  rcases le_or_gt n 210 with hn210 | hn210
  · have h_mono := C4_lower_nth_prime_monotone
    rcases le_or_gt n 164 with h_164 | h_164
    · have h_le : 138 ≤ n := by omega
      have h_ge : C4_lower (nth Nat.Prime 138) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
      have h_val : C4_lower (nth Nat.Prime 138) = 165 := by
        rw [nth_prime_138]
        rfl
      omega
    rcases le_or_gt n 196 with h_196 | h_196
    · have h_le : 165 ≤ n := by omega
      have h_ge : C4_lower (nth Nat.Prime 165) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
      have h_val : C4_lower (nth Nat.Prime 165) = 197 := by
        rw [nth_prime_165]
        rfl
      omega
    · have h_le : 197 ≤ n := by omega
      have h_ge : C4_lower (nth Nat.Prime 197) ≤ C4_lower (nth Nat.Prime n) := h_mono h_le
      have h_val : C4_lower (nth Nat.Prime 197) = 236 := by
        rw [nth_prime_197]
        rfl
      omega
  · sorry

theorem oeis_338483_conjecture_0.disproof :
  ¬ ∃ n : ℕ, n > 0 ∧ Nat.Prime (a n) ∧ a n > 31 := by
  rintro ⟨n, hn, hp, h_gt⟩
  have ha_eq := a_eq_nth_prime_of_prime hp
  rw [ha_eq] at h_gt
  have hn10 : n > 10 := n_gt_ten_of_nth_prime_gt_31 h_gt
  have ha_lt : a n < nth Nat.Prime n := by
    rcases le_or_gt n 31 with hn31 | hn31
    · exact a_lt_nth_prime_of_le_31 (by omega) hn31
    · have h_C4 : C4 (nth Nat.Prime n) ≥ n + 1 := by
        have h_ge := C4_ge_lower (nth Nat.Prime n)
        have h_lower : C4_lower (nth Nat.Prime n) ≥ n + 1 := by
          rcases le_or_gt n 137 with hn137 | hn137
          · exact C4_lower_nth_prime_ge_of_le_137 (by omega) hn137
          · exact C4_lower_nth_prime_ge_of_ge_138 (by omega)
        omega
      obtain ⟨M, hM1, hM2, hM3⟩ := exists_of_C4_ge n (nth Nat.Prime n) h_C4
      have hM4 : A047983_count M = n := by
        rw [A047983_count_eq_C4 hM2]
        exact hM3
      have ha_le : a n ≤ M := Nat.sInf_le hM4
      omega
  omega
