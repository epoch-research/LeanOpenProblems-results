import FormalConjectures.Util.ProblemImports
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

open Nat BigOperators Finset
lemma chain_le_of_mem {α : Type*} [Preorder α] {x y : α} {l : List α} (h : List.IsChain (· ≤ ·) (x :: y :: l)) (a : α) (ha : a ∈ l) : y ≤ a := by
  induction l generalizing x y with
  | nil => cases ha
  | cons b l ih =>
    cases ha with
    | head =>
      rw [List.isChain_cons_cons] at h
      have h2 := h.2
      rw [List.isChain_cons_cons] at h2
      exact h2.1
    | tail _ h_mem =>
      rw [List.isChain_cons_cons] at h
      have h2 := h.2
      rw [List.isChain_cons_cons] at h2
      have hyb : y ≤ b := h2.1
      have hba : b ≤ a := ih h.2 h_mem
      exact le_trans hyb hba


def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

lemma prime_gcd_eq_one_of_lt {p m : ℕ} (hp : Nat.Prime p) (hm0 : m ≠ 0) (hmp : m < p) : Nat.gcd m p = 1 := by
  rw [Nat.gcd_comm]
  have h_min : minFac p = p := Nat.Prime.minFac_eq hp
  have h_lt : m < minFac p := by rwa [h_min]
  exact gcd_eq_one_of_lt_minFac hm0 h_lt

lemma prime_sum_gcd {p : ℕ} (hp : Nat.Prime p) :
    (Finset.Ico 1 p).sum (fun k => Nat.gcd k p) = p - 1 := by
  have h_congr : (Finset.Ico 1 p).sum (fun k => Nat.gcd k p) = (Finset.Ico 1 p).sum (fun k => 1) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk0 : k ≠ 0 := by omega
    exact prime_gcd_eq_one_of_lt hp hk0 hk.2
  rw [h_congr]
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Nat.card_Ico]

lemma prime_A018804 {p : ℕ} (hp : Nat.Prime p) :
    (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p) = 2 * p - 1 := by
  have hp_le : 1 ≤ p := by
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    omega
  rw [Ico_succ_right_eq_insert_Ico hp_le]
  have hp_not_mem : p ∉ Finset.Ico 1 p := by
    rw [Finset.mem_Ico]
    omega
  rw [Finset.sum_insert hp_not_mem]
  rw [Nat.gcd_self]
  rw [prime_sum_gcd hp]
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  omega

lemma prime_a_eq_1 {p : ℕ} (hp : Nat.Prime p) : a p = 1 := by
  change p / Nat.gcd p (1 + (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p)) = 1
  rw [prime_A018804 hp]
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have h_add : 1 + (2 * p - 1) = 2 * p := by omega
  rw [h_add]
  have h_gcd : Nat.gcd p (2 * p) = p := Nat.gcd_eq_left (dvd_mul_left p 2)
  rw [h_gcd]
  exact Nat.div_self (by omega)

lemma gcd_sum_eq_divisors_sum (n : ℕ) (hn : n ≠ 0) :
    (Finset.range n).sum (fun k => Nat.gcd k n) = n.divisors.sum (fun d => d * (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).card) := by
  have h_maps : ∀ k ∈ Finset.range n, Nat.gcd k n ∈ n.divisors := by
    intro k _
    rw [mem_divisors]
    exact ⟨Nat.gcd_dvd_right k n, hn⟩
  rw [← Finset.sum_fiberwise_of_maps_to h_maps]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have h_congr : (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).sum (fun k => Nat.gcd k n) =
                 (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).sum (fun _ => d) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_filter] at hk
    exact hk.2
  rw [h_congr]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma gcd_sum_eq_divisors_totient (n : ℕ) (hn : n ≠ 0) :
    (Finset.range n).sum (fun k => Nat.gcd k n) = n.divisors.sum (fun d => d * φ (n / d)) := by
  rw [gcd_sum_eq_divisors_sum n hn]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have h_dvd : d ∣ n := dvd_of_mem_divisors hd
  have h_totient := totient_div_of_dvd h_dvd
  have h_card : (Finset.filter (fun k => Nat.gcd k n = d) (Finset.range n)).card = (Finset.filter (fun k => Nat.gcd n k = d) (Finset.range n)).card := by
    simp_rw [Nat.gcd_comm]
  rw [h_card]
  rw [← h_totient]

lemma A018804_eq_range_sum (n : ℕ) : (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = (Finset.range n).sum (fun k => Nat.gcd k n) := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn1 : 1 ≤ n := hn
  rw [Ico_succ_right_eq_insert_Ico hn1]
  have hn_not_mem : n ∉ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  rw [Finset.sum_insert hn_not_mem]
  have h_range : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [h_range]
  have h0_not_mem : 0 ∉ Finset.Ico 1 n := by
    rw [Finset.mem_Ico]
    omega
  rw [Finset.sum_insert h0_not_mem]
  simp only [Nat.gcd_self, Nat.gcd_zero_left]

lemma prime_sq_dvd_A {n p : ℕ} (hp : Nat.Prime p) (hn0 : n ≠ 0) (h_sq : p ^ 2 ∣ n) : p ∣ (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) := by
  rw [A018804_eq_range_sum n]
  rw [gcd_sum_eq_divisors_totient n hn0]
  refine Finset.dvd_sum ?_
  intro d hd
  have hd_dvd : d ∣ n := dvd_of_mem_divisors hd
  by_cases hpd : p ∣ d
  · exact dvd_mul_of_dvd_left hpd _
  · have h_cop : Nat.Coprime (p ^ 2) d := by
      have h1 : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
      exact h1.pow_left 2
    have h_mul : p ^ 2 ∣ (n / d) * d := by
      rw [Nat.div_mul_cancel hd_dvd]
      exact h_sq
    have h_nd : p ^ 2 ∣ n / d := h_cop.dvd_of_dvd_mul_right h_mul
    have h_p_nd : p ∣ n / d := by
      have h_p_sq : p ∣ p ^ 2 := by
        use p
        ring
      exact dvd_trans h_p_sq h_nd
    have h_tot : p ∣ φ (n / d) := by
      have h_div_cancel : n / d = p * (n / d / p) := by
        exact (Nat.mul_div_cancel' h_p_nd).symm
      rw [h_div_cancel]
      rw [totient_mul_of_prime_of_dvd hp]
      · exact dvd_mul_right p (φ (n / d / p))
      · have h_z : p ^ 2 ∣ n / d := h_nd
        rcases h_z with ⟨z, hz⟩
        have h_eq : n / d / p = p * z := by
          rw [hz]
          have hp2_eq : p ^ 2 = p * p := by ring
          rw [hp2_eq, mul_assoc]
          exact Nat.mul_div_cancel_left (p * z) hp.pos
        rw [h_eq]
        exact dvd_mul_right p z
    exact dvd_mul_of_dvd_right h_tot d

lemma sq_free_of_a_eq_1 {n : ℕ} (h_a : a n = 1) : Squarefree n := by
  by_cases h_sf : Squarefree n
  · exact h_sf
  · rw [squarefree_iff_prime_squarefree] at h_sf
    push_neg at h_sf
    rcases h_sf with ⟨p, hp, h_sq⟩
    have h_sq_pow : p ^ 2 ∣ n := by
      have h_p2 : p ^ 2 = p * p := by ring
      rwa [h_p2]
    have hn0 : n ≠ 0 := by
      rintro rfl
      change 0 / Nat.gcd 0 (1 + (Finset.Ico 1 1).sum (fun k => Nat.gcd k 0)) = 1 at h_a
      simp at h_a
    have h_p_dvd : p ∣ (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) := prime_sq_dvd_A hp hn0 h_sq_pow
    have h_a1 : n / Nat.gcd n (1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) = 1 := h_a
    have h_gcd : Nat.gcd n (1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) = n := by
      have h_div_canc := Nat.mul_div_cancel' (Nat.gcd_dvd_left n (1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)))
      rw [h_a1] at h_div_canc
      rw [mul_one] at h_div_canc
      exact h_div_canc
    have h_dvd : n ∣ (1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) := by
      nth_rw 1 [← h_gcd]
      exact Nat.gcd_dvd_right n (1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n))
    have h_p_n : p ∣ n := by
      have h_p_sq_p : p ∣ p ^ 2 := by
        use p
        ring
      exact dvd_trans h_p_sq_p h_sq_pow
    have h_p_one_add : p ∣ (1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) := dvd_trans h_p_n h_dvd
    have h_p_one : p ∣ 1 := by
      have h_comm : 1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) + 1 := by ring
      rw [h_comm] at h_p_one_add
      exact (Nat.dvd_add_right h_p_dvd).mp h_p_one_add
    have h_p_1 : p = 1 := Nat.eq_one_of_dvd_one h_p_one
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    omega


lemma divisors_mul_prime {p m : ℕ} (hp : Nat.Prime p) (_h_cop : Nat.Coprime p m) (hm0 : m ≠ 0) :
    (p * m).divisors = m.divisors ∪ m.divisors.map ⟨fun d => p * d, fun _ _ h => Nat.mul_left_cancel hp.pos h⟩ := by
  ext x
  constructor
  · intro hx
    rw [mem_divisors] at hx
    have hx_dvd := hx.1
    by_cases h_dvd : p ∣ x
    · rcases h_dvd with ⟨d', rfl⟩
      rw [mem_union]
      right
      rw [mem_map]
      use d'
      have h_div : d' ∣ m := Nat.dvd_of_mul_dvd_mul_left hp.pos hx_dvd
      rw [mem_divisors]
      exact ⟨⟨h_div, hm0⟩, rfl⟩
    · rw [mem_union]
      left
      rw [mem_divisors]
      have h_cop_px : Nat.Coprime p x := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_dvd
      have h_cop_xp : Nat.Coprime x p := h_cop_px.symm
      have h_dvd' : x ∣ m := h_cop_xp.dvd_of_dvd_mul_left hx_dvd
      exact ⟨h_dvd', hm0⟩
  · intro hx
    rw [mem_union] at hx
    rw [mem_divisors]
    have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
    refine ⟨?_, hpm0⟩
    rcases hx with (h1 | h2)
    · rw [mem_divisors] at h1
      exact dvd_mul_of_dvd_right h1.1 p
    · rw [mem_map] at h2
      rcases h2 with ⟨d', hd', rfl⟩
      rw [mem_divisors] at hd'
      exact Nat.mul_dvd_mul_left p hd'.1

lemma sum_divisors_mul_prime {p m : ℕ} (hp : Nat.Prime p) (h_cop : Nat.Coprime p m) (hm0 : m ≠ 0) :
    (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m)) = (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := by
  rw [A018804_eq_range_sum (p * m)]
  rw [A018804_eq_range_sum m]
  have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
  rw [gcd_sum_eq_divisors_totient (p * m) hpm0]
  rw [gcd_sum_eq_divisors_totient m hm0]
  rw [divisors_mul_prime hp h_cop hm0]
  have h_disj : Disjoint m.divisors (m.divisors.map ⟨fun d => p * d, fun _ _ h => Nat.mul_left_cancel hp.pos h⟩) := by
    rw [Finset.disjoint_iff_ne]
    intro d1 hd1 d2 hd2
    rw [mem_divisors] at hd1
    rw [mem_map] at hd2
    rcases hd2 with ⟨d2', hd2', rfl⟩
    rw [mem_divisors] at hd2'
    intro h_eq
    have hp_dvd_m : p ∣ m := by
      rw [h_eq] at hd1
      have h_mul_dvd : p * d2' ∣ m := hd1.1
      exact dvd_of_mul_right_dvd h_mul_dvd
    have h_gcd : Nat.gcd p m = p := Nat.gcd_eq_left hp_dvd_m
    rw [h_cop] at h_gcd
    exact hp.ne_one h_gcd.symm
  rw [Finset.sum_union h_disj]
  have h_term1 : ∑ d ∈ m.divisors, d * φ (p * m / d) = ∑ d ∈ m.divisors, (p - 1) * (d * φ (m / d)) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [mem_divisors] at hd
    have hd_dvd : d ∣ m := hd.1
    have h_div : p * m / d = p * (m / d) := Nat.mul_div_assoc p hd_dvd
    rw [h_div]
    have h_cop_div : Nat.Coprime p (m / d) := h_cop.coprime_div_right hd_dvd
    have h_not_dvd : ¬ p ∣ m / d := by
      intro hp_dvd
      have h_gcd : Nat.gcd p (m / d) = p := Nat.gcd_eq_left hp_dvd
      rw [h_cop_div] at h_gcd
      exact hp.ne_one h_gcd.symm
    rw [totient_mul_of_prime_of_not_dvd hp h_not_dvd]
    ring
  have h_term2 : ∑ x ∈ m.divisors.map ⟨fun d => p * d, fun _ _ h => Nat.mul_left_cancel hp.pos h⟩, x * φ (p * m / x) =
                 ∑ d ∈ m.divisors, p * (d * φ (m / d)) := by
    rw [Finset.sum_map]
    dsimp only [Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [mem_divisors] at hd
    have hd_dvd : d ∣ m := hd.1
    have hd0 : d ≠ 0 := by
      rintro rfl
      have hm0_zero := zero_dvd_iff.mp hd_dvd
      exact hm0 hm0_zero
    have h_div2 : p * m / (p * d) = m / d := Nat.mul_div_mul_left m d hp.pos
    rw [h_div2]
    ring
  rw [h_term1, h_term2]
  rw [← Finset.sum_add_distrib]
  have h_combine : ∀ d ∈ m.divisors, (p - 1) * (d * φ (m / d)) + p * (d * φ (m / d)) = (2 * p - 1) * (d * φ (m / d)) := by
    intro d hd
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    have h_sub1 : (p - 1) * (d * φ (m / d)) = p * (d * φ (m / d)) - d * φ (m / d) := by
      rw [Nat.sub_mul, one_mul]
    have h_sub2 : (2 * p - 1) * (d * φ (m / d)) = 2 * (p * (d * φ (m / d))) - d * φ (m / d) := by
      rw [Nat.sub_mul, one_mul]
      congr 1
      ring
    have h_le : d * φ (m / d) ≤ p * (d * φ (m / d)) := by
      have h_mul_le : 1 * (d * φ (m / d)) ≤ p * (d * φ (m / d)) := Nat.mul_le_mul_right (d * φ (m / d)) (by omega)
      rwa [one_mul] at h_mul_le
    rw [h_sub1, h_sub2]
    omega
  rw [Finset.sum_congr rfl h_combine]
  rw [← Finset.mul_sum]

lemma dvd_of_dvd_sub_left {a b c : ℕ} (h1 : a ∣ b) (h2 : a ∣ b - c) (hle : c ≤ b) : a ∣ c := by
  rcases h1 with ⟨k1, rfl⟩
  rcases h2 with ⟨k2, hk2⟩
  use k1 - k2
  rw [Nat.mul_sub_left_distrib]
  omega

lemma dvd_of_dvd_add_left {a b c : ℕ} (h1 : a ∣ b + c) (h2 : a ∣ b) : a ∣ c := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, rfl⟩
  use k1 - k2
  rw [Nat.mul_sub_left_distrib]
  omega

lemma dvd_of_dvd_one_add {a b : ℕ} (h1 : a ∣ 1 + b) (h2 : a ∣ b) : a ∣ 1 := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, rfl⟩
  use k1 - k2
  rw [Nat.mul_sub_left_distrib]
  omega

lemma coprime_two_of_odd {x : ℕ} (hx : Odd x) : Nat.Coprime 2 x := by
  have h_gcd := Nat.gcd_dvd_left 2 x
  have h_gcd_x := Nat.gcd_dvd_right 2 x
  have h_le : Nat.gcd 2 x ≤ 2 := Nat.le_of_dvd (by omega) h_gcd
  have h_pos : Nat.gcd 2 x ≥ 1 := Nat.gcd_pos_of_pos_left x (by omega)
  rcases (by omega : Nat.gcd 2 x = 1 ∨ Nat.gcd 2 x = 2) with h1 | h2
  · exact h1
  · rcases h_gcd_x with ⟨k, hk⟩
    have h_even : Even x := by
      use k
      rw [hk, h2]
      ring
    rcases hx with ⟨m, rfl⟩
    rcases h_even with ⟨n, hn⟩
    omega



lemma prime_factors_length_ge_two {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hp : ¬ Nat.Prime n) : 2 ≤ (Nat.primeFactorsList n).length := by
  have h_len : (Nat.primeFactorsList n).length ≠ 0 := by
    intro hc
    have h_nil : Nat.primeFactorsList n = [] := by
      cases h_list : Nat.primeFactorsList n
      · rfl
      · simp [h_list] at hc
    rw [Nat.primeFactorsList_eq_nil] at h_nil
    rcases h_nil with rfl | rfl
    · exact hn0 rfl
    · exact hn1 rfl
  have h_len1 : (Nat.primeFactorsList n).length ≠ 1 := by
    intro hc
    match h_list : Nat.primeFactorsList n with
    | [] =>
      simp [h_list] at hc
    | p :: tail =>
      have h_tail_nil : tail = [] := by
        have : (p :: tail).length = 1 := by rwa [← h_list]
        simp at this
        exact this
      subst h_tail_nil
      have hp_in : p ∈ Nat.primeFactorsList n := by
        rw [h_list]
        exact List.mem_cons_self
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp_in
      have h_prod : (Nat.primeFactorsList n).prod = p := by
        rw [h_list]
        simp
      rw [Nat.prod_primeFactorsList hn0] at h_prod
      subst h_prod
      exact hp hp_prime
  omega

lemma exists_two_prime_factors_of_squarefree_composite {n : ℕ}
    (h_sf : Squarefree n) (hn1 : n ≠ 1) (hp : ¬ Nat.Prime n) (hn0 : n ≠ 0) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p * q ∣ n := by
  have h_len := prime_factors_length_ge_two hn0 hn1 hp
  match h_list : Nat.primeFactorsList n with
  | [] =>
    simp [h_list] at h_len
  | [p] =>
    simp [h_list] at h_len
  | p :: q :: tail =>
    have h_chain : List.IsChain (· ≤ ·) (Nat.primeFactorsList n) := Nat.isChain_primeFactorsList n
    rw [h_list] at h_chain
    have hpq_le : p ≤ q := List.IsChain.rel_head h_chain
    have hp_mem : p ∈ Nat.primeFactorsList n := by
      rw [h_list]
      simp
    have hq_mem : q ∈ Nat.primeFactorsList n := by
      rw [h_list]
      simp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp_mem
    have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hq_mem
    have hpq_ne : p ≠ q := by
      intro hc
      subst hc
      have h_p2_dvd : p * p ∣ n := by
        have h_prod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn0
        rw [h_list] at h_prod
        have h_prod_eq : (p :: p :: tail).prod = (p * p) * tail.prod := by
          simp [List.prod_cons]
          ring
        rw [h_prod_eq] at h_prod
        rw [← h_prod]
        exact dvd_mul_right (p * p) tail.prod
      rw [squarefree_iff_prime_squarefree] at h_sf
      exact h_sf p hp_prime h_p2_dvd
    have hpq_lt : p < q := Nat.lt_of_le_of_ne hpq_le hpq_ne
    have hpq_dvd : p * q ∣ n := by
      have h_prod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn0
      rw [h_list] at h_prod
      have h_prod_eq : (p :: q :: tail).prod = (p * q) * tail.prod := by
        simp [List.prod_cons]
        ring
      rw [h_prod_eq] at h_prod
      rw [← h_prod]
      exact dvd_mul_right (p * q) tail.prod
    exact ⟨p, q, hp_prime, hq_prime, hpq_lt, hpq_dvd⟩


lemma coprime_of_dvd {m A S : ℕ} (h_dvd : m ∣ 1 + A * S) : Nat.Coprime m S := by
  have h_gcd : Nat.gcd m S ∣ 1 := by
    have h1 : Nat.gcd m S ∣ m := Nat.gcd_dvd_left m S
    have h2 : Nat.gcd m S ∣ S := Nat.gcd_dvd_right m S
    have h3 : Nat.gcd m S ∣ 1 + A * S := dvd_trans h1 h_dvd
    have h4 : Nat.gcd m S ∣ A * S := dvd_mul_of_dvd_right h2 A
    exact dvd_of_dvd_one_add h3 h4
  exact Nat.eq_one_of_dvd_one h_gcd



lemma minFac_proper_divisor {n : ℕ} (hn1 : n ≠ 1) (hp : ¬ Nat.Prime n) (hn0 : n ≠ 0) :
    minFac n ∣ n ∧ 1 < minFac n ∧ minFac n < n := by
  have hdvd := Nat.minFac_dvd n
  have h1 : 1 < minFac n := by
    have hp_min := Nat.minFac_prime hn1
    have h_le := Nat.Prime.two_le hp_min
    omega
  have hlt : minFac n < n := by
    by_contra hc
    push_neg at hc
    have h_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have h_le := Nat.le_of_dvd h_pos hdvd
    have heq : minFac n = n := by omega
    have h_n1 : 1 < n := by omega
    have h_prime : Nat.Prime n := Nat.prime_def_minFac.mpr ⟨h_n1, heq⟩
    exact hp h_prime
  exact ⟨hdvd, h1, hlt⟩


lemma sum_gcd_ge_two_mul_of_composite {n : ℕ} (hn1 : n ≠ 1) (hp : ¬ Nat.Prime n) (hn0 : n ≠ 0) :
    (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) ≥ 2 * n := by
  rcases minFac_proper_divisor hn1 hp hn0 with ⟨hdvd, h1, hlt⟩
  have h_n1 : 1 < n := by
    have : minFac n < n := hlt
    omega
  have hn_mem : n ∈ Ico 1 (n + 1) := by
    rw [Finset.mem_Ico]
    omega
  have hm_mem : minFac n ∈ Ico 1 (n + 1) := by
    rw [Finset.mem_Ico]
    omega
  have hne : minFac n ≠ n := by omega
  have h_split : Ico 1 (n + 1) = insert n (insert (minFac n) (Ico 1 (n + 1) \ {n, minFac n})) := by
    ext x
    simp only [mem_Ico, mem_insert, mem_sdiff, mem_singleton]
    omega
  rw [h_split]
  have h_disj1 : n ∉ insert (minFac n) (Ico 1 (n + 1) \ {n, minFac n}) := by
    simp [hne, hne.symm]
  have h_disj2 : minFac n ∉ Ico 1 (n + 1) \ {n, minFac n} := by
    simp [hne, hne.symm]
  rw [Finset.sum_insert h_disj1]
  rw [Finset.sum_insert h_disj2]
  have h_gcd_n : Nat.gcd n n = n := Nat.gcd_self n
  have h_gcd_m : Nat.gcd (minFac n) n = minFac n := Nat.gcd_eq_left hdvd
  rw [h_gcd_n, h_gcd_m]
  have h_sum_le : (∑ k ∈ Ico 1 (n + 1) \ {n, minFac n}, Nat.gcd k n) ≥ ∑ k ∈ Ico 1 (n + 1) \ {n, minFac n}, 1 := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have h_gcd_pos : Nat.gcd k n > 0 := Nat.gcd_pos_of_pos_right k (Nat.pos_of_ne_zero hn0)
    exact Nat.succ_le_of_lt h_gcd_pos
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h_sum_le
  have h_card : (Ico 1 (n + 1) \ {n, minFac n}).card = n - 2 := by
    have h_card_S : (Ico 1 (n + 1)).card = n := by
      rw [Nat.card_Ico]
      omega
    have h_sub : ({n, minFac n} : Finset ℕ) ⊆ Ico 1 (n + 1) := by
      rw [Finset.subset_iff]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hn_mem
      · exact hm_mem
    rw [Finset.card_sdiff_of_subset h_sub]
    have h_card_doubleton : ({n, minFac n} : Finset ℕ).card = 2 := by
      rw [Finset.card_pair hne.symm]
    omega
  rw [h_card] at h_sum_le
  omega

lemma sum_gcd_ge_two_mul_sub_one (n : ℕ) (hn0 : n ≠ 0) :
    (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) ≥ 2 * n - 1 := by
  by_cases hn1 : n = 1
  · subst hn1; simp
  · by_cases hp : Nat.Prime n
    · rw [prime_A018804 hp]
    · have h_ge := sum_gcd_ge_two_mul_of_composite hn1 hp hn0
      omega

lemma dvd_of_dvd_mul_add {p X : ℕ} (h_dvd : p ∣ (2 * p - 1) * X + 1) (hX : X ≥ 1) : p ∣ X - 1 := by
  have h_eq : 2 * p * X = ((2 * p - 1) * X + 1) + (X - 1) := by
    have h_sub : (2 * p - 1) * X + X = 2 * p * X := by
      rcases p with _ | p
      · have h_zero : (2 * 0 - 1) * X + 1 = 0 := zero_dvd_iff.mp h_dvd
        omega
      · simp [Nat.succ_mul]
        ring
    omega
  have h_dvd_mul : p ∣ 2 * p * X := by use 2 * X; ring
  rw [h_eq] at h_dvd_mul
  exact (Nat.dvd_add_right h_dvd).mp h_dvd_mul





lemma dvd_S_sub_one {p m : ℕ} (hp : Nat.Prime p) (h_sf : Squarefree (p * m)) (h_a : a (p * m) = 1) :
    p ∣ (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) - 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [a] at h_a
  have h_cop : Nat.Coprime p m := by
    have h_p2 : ¬ p * p ∣ p * m := by
      intro hc
      rw [squarefree_iff_prime_squarefree] at h_sf
      exact h_sf p hp hc
    have h_dvd : p ∣ m → p * p ∣ p * m := by
      rintro ⟨k, rfl⟩
      use k
      ring
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => h_p2 (h_dvd h))
  have h_S : (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m)) = (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := by
    exact sum_divisors_mul_prime hp h_cop hm0
  have h_div : (p * m) ∣ 1 + (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m)) := by
    have h_a1 : a (p * m) = 1 := h_a
    change (p * m) / Nat.gcd (p * m) (1 + (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m))) = 1 at h_a1
    have h_gcd : Nat.gcd (p * m) (1 + (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m))) = p * m := by
      have h_div_canc := Nat.mul_div_cancel' (Nat.gcd_dvd_left (p * m) (1 + (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m))))
      rw [h_a1] at h_div_canc
      rw [mul_one] at h_div_canc
      exact h_div_canc
    nth_rw 1 [← h_gcd]
    exact Nat.gcd_dvd_right (p * m) (1 + (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m)))
  rw [h_S] at h_div
  have h_div_p : p ∣ (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) + 1 := by
    have h_comm : 1 + (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) = (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) + 1 := by ring
    rw [h_comm] at h_div
    exact dvd_trans (dvd_mul_right p m) h_div
  have h_ge1 : (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) ≥ 1 := by
    have hm_pos : m ≥ 1 := by omega
    have h_mem : 1 ∈ Finset.Ico 1 (m + 1) := by
      rw [Finset.mem_Ico]
      omega
    have h_le : Nat.gcd 1 m ≤ (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.gcd x m)) h_mem
    rw [Nat.gcd_one_left] at h_le
    exact h_le
  exact dvd_of_dvd_mul_add h_div_p h_ge1


lemma pq_divisibility {p q m : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (h_sf : Squarefree (p * q * m)) (h_a : a (p * q * m) = 1) :
    p ∣ (2 * q - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) - 1 ∧
    q ∣ (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) - 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [a] at h_a
  have h_pq_m : p * q * m = p * (q * m) := by ring
  have h_sf_p : Squarefree (p * (q * m)) := by rwa [← h_pq_m]
  have h_a_p : a (p * (q * m)) = 1 := by rwa [← h_pq_m]
  have h_dvd_p := dvd_S_sub_one hp h_sf_p h_a_p
  have h_cop_q : Nat.Coprime q m := by
    have h_q2 : ¬ q * q ∣ p * q * m := by
      intro hc
      rw [squarefree_iff_prime_squarefree] at h_sf
      exact h_sf q hq hc
    have h_dvd : q ∣ m → q * q ∣ p * q * m := by
      rintro ⟨k, rfl⟩
      use p * k
      ring
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => h_q2 (h_dvd h))
  have h_S_qm : (Finset.Ico 1 (q * m + 1)).sum (fun k => Nat.gcd k (q * m)) = (2 * q - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := by
    exact sum_divisors_mul_prime hq h_cop_q hm0
  rw [h_S_qm] at h_dvd_p
  
  have h_qp_m : p * q * m = q * (p * m) := by ring
  have h_sf_q : Squarefree (q * (p * m)) := by rwa [← h_qp_m]
  have h_a_q : a (q * (p * m)) = 1 := by rwa [← h_qp_m]
  have h_dvd_q := dvd_S_sub_one hq h_sf_q h_a_q
  have h_cop_p : Nat.Coprime p m := by
    have h_p2 : ¬ p * p ∣ p * q * m := by
      intro hc
      rw [squarefree_iff_prime_squarefree] at h_sf
      exact h_sf p hp hc
    have h_dvd : p ∣ m → p * p ∣ p * q * m := by
      rintro ⟨k, rfl⟩
      use q * k
      ring
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => h_p2 (h_dvd h))
  have h_S_pm : (Finset.Ico 1 (p * m + 1)).sum (fun k => Nat.gcd k (p * m)) = (2 * p - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := by
    exact sum_divisors_mul_prime hp h_cop_p hm0
  rw [h_S_pm] at h_dvd_q
  exact ⟨h_dvd_p, h_dvd_q⟩


lemma pqX_contradiction_p2 {q X : ℕ} (hq : Nat.Prime q) (hq_gt : 2 < q) (hX : X = 1) (h_p : 2 ∣ (2 * q - 1) * X - 1) (h_q : q ∣ 3 * X - 1) : False := by
  subst hX
  have : q ∣ 2 := h_q
  have : q ≤ 2 := Nat.le_of_dvd (by omega) this
  omega


lemma no_solution_X1 {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (h_p : p ∣ 2 * q - 2) (h_q : q ∣ 2 * p - 2) : False := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have hq2 : q ≥ 2 := Nat.Prime.two_le hq
  have h_dvd : q ∣ 2 * (p - 1) := by
    have : 2 * p - 2 = 2 * (p - 1) := by omega
    rwa [this] at h_q
  rcases (Nat.Prime.dvd_mul hq).mp h_dvd with hq_dvd_2 | hq_dvd_p1
  · have : q ≤ 2 := Nat.le_of_dvd (by omega) hq_dvd_2
    omega
  · have hp1_pos : p - 1 > 0 := by omega
    have : q ≤ p - 1 := Nat.le_of_dvd hp1_pos hq_dvd_p1
    omega



lemma gcd_odd_of_odd {k n : ℕ} (hn : Odd n) : Odd (Nat.gcd k n) := by
  have hdvd := Nat.gcd_dvd_right k n
  rcases hdvd with ⟨c, hc⟩
  have h_mul : Odd (Nat.gcd k n * c) := by rwa [← hc]
  exact (Nat.odd_mul.mp h_mul).1

lemma sum_mod_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (hf : ∀ x ∈ s, f x % 2 = 1) :
    s.sum f % 2 = s.card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h_odd : f a % 2 = 1 := hf a (Finset.mem_insert_self a s)
    have h_ih : s.sum f % 2 = s.card % 2 := by
      refine ih ?_
      intro x hx
      exact hf x (Finset.mem_insert_of_mem hx)
    rw [Nat.add_mod, Nat.add_mod, h_odd, h_ih, add_comm]
    omega


lemma odd_S_of_odd {n : ℕ} (hn : Odd n) : Odd ((Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) := by
  have h_odd : ∀ k ∈ Finset.Ico 1 (n + 1), (Nat.gcd k n) % 2 = 1 := by
    intro k _
    have hg_odd := @gcd_odd_of_odd k n hn
    exact Nat.odd_iff.mp hg_odd
  have h_sum := sum_mod_two (Finset.Ico 1 (n + 1)) (fun k => Nat.gcd k n) h_odd
  have h_card_eq : (Finset.Ico 1 (n + 1)).card = n := by rw [Nat.card_Ico]; omega
  rw [h_card_eq] at h_sum
  have hn_odd_mod : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [hn_odd_mod] at h_sum
  exact Nat.odd_iff.mpr h_sum

lemma test_ineq1 (p q r : ℕ) (hp : p ≥ 3) (hq : q ≥ 7) (hr : r ≥ 11) :
    4 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
  have hp' : 3 ≤ (p : ℤ) := by exact_mod_cast hp
  have hq' : 7 ≤ (q : ℤ) := by exact_mod_cast hq
  have hr' : 11 ≤ (r : ℤ) := by exact_mod_cast hr
  have h_ge1 : 2 * p ≥ 1 := by omega
  have h_ge2 : 2 * q ≥ 1 := by omega
  have h_ge3 : 2 * r ≥ 1 := by omega
  -- Move everything to Z
  zify [h_ge1, h_ge2, h_ge3]
  let p_z := (p : ℤ)
  let q_z := (q : ℤ)
  let r_z := (r : ℤ)
  have h_eq : (2 * p_z - 1) * (2 * q_z - 1) * (2 * r_z - 1) + 1 - 4 * p_z * q_z * r_z =
               4 * (p_z - 3) * (q_z - 7) * (r_z - 11) + 40 * (p_z - 3) * (q_z - 7) + 24 * (p_z - 3) * (r_z - 11) + 8 * (q_z - 7) * (r_z - 11) + 238 * (p_z - 3) + 78 * (q_z - 7) + 46 * (r_z - 11) + 442 := by ring
  have u1 : p_z - 3 ≥ 0 := by omega
  have u2 : q_z - 7 ≥ 0 := by omega
  have u3 : r_z - 11 ≥ 0 := by omega
  have h_pos : 4 * (p_z - 3) * (q_z - 7) * (r_z - 11) + 40 * (p_z - 3) * (q_z - 7) + 24 * (p_z - 3) * (r_z - 11) + 8 * (q_z - 7) * (r_z - 11) + 238 * (p_z - 3) + 78 * (q_z - 7) + 46 * (r_z - 11) + 442 > 0 := by
    have t1 : (p_z - 3) * (q_z - 7) ≥ 0 := mul_nonneg u1 u2
    have t2 : (p_z - 3) * (q_z - 7) * (r_z - 11) ≥ 0 := mul_nonneg t1 u3
    have t3 : (p_z - 3) * (r_z - 11) ≥ 0 := mul_nonneg u1 u3
    have t4 : (q_z - 7) * (r_z - 11) ≥ 0 := mul_nonneg u2 u3
    linarith
  linarith

lemma test_ineq2 (p q r : ℕ) (hp : p ≥ 3) (hq : q ≥ 11) (hr : r ≥ 13) :
    6 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
  have hp' : 3 ≤ (p : ℤ) := by exact_mod_cast hp
  have hq' : 11 ≤ (q : ℤ) := by exact_mod_cast hq
  have hr' : 13 ≤ (r : ℤ) := by exact_mod_cast hr
  have h_ge1 : 2 * p ≥ 1 := by omega
  have h_ge2 : 2 * q ≥ 1 := by omega
  have h_ge3 : 2 * r ≥ 1 := by omega
  -- Move everything to Z
  zify [h_ge1, h_ge2, h_ge3]
  let p_z := (p : ℤ)
  let q_z := (q : ℤ)
  let r_z := (r : ℤ)
  have h_eq : (2 * p_z - 1) * (2 * q_z - 1) * (2 * r_z - 1) + 1 - 6 * p_z * q_z * r_z =
               2 * (p_z - 3) * (q_z - 11) * (r_z - 13) + 22 * (p_z - 3) * (q_z - 11) + 18 * (p_z - 3) * (r_z - 13) + 2 * (q_z - 11) * (r_z - 13) + 192 * (p_z - 3) + 16 * (q_z - 11) + 12 * (r_z - 13) + 52 := by ring
  have u1 : p_z - 3 ≥ 0 := by omega
  have u2 : q_z - 11 ≥ 0 := by omega
  have u3 : r_z - 13 ≥ 0 := by omega
  have h_pos : 2 * (p_z - 3) * (q_z - 11) * (r_z - 13) + 22 * (p_z - 3) * (q_z - 11) + 18 * (p_z - 3) * (r_z - 13) + 2 * (q_z - 11) * (r_z - 13) + 192 * (p_z - 3) + 16 * (q_z - 11) + 12 * (r_z - 13) + 52 > 0 := by
    have t1 : (p_z - 3) * (q_z - 11) ≥ 0 := mul_nonneg u1 u2
    have t2 : (p_z - 3) * (q_z - 11) * (r_z - 13) ≥ 0 := mul_nonneg t1 u3
    have t3 : (p_z - 3) * (r_z - 13) ≥ 0 := mul_nonneg u1 u3
    have t4 : (q_z - 11) * (r_z - 13) ≥ 0 := mul_nonneg u2 u3
    linarith
  linarith


lemma a_eq_1_impl_prime_or_1 (n : ℕ) (h : a n = 1) : n = 1 ∨ Nat.Prime n := by
  by_cases hn1 : n = 1
  · left; exact hn1
  · right
    by_cases hn0 : n = 0
    · subst hn0; change 0 / _ = 1 at h; simp at h
    · by_cases hp : Nat.Prime n
      · exact hp
      · have h_sf : Squarefree n := sq_free_of_a_eq_1 h
        have h_len := prime_factors_length_ge_two hn0 hn1 hp
        match h_list : Nat.primeFactorsList n with
        | [] => simp [h_list] at h_len
        | [p] => simp [h_list] at h_len
        | p :: q :: tail =>
          have h_chain : List.IsChain (· ≤ ·) (p :: q :: tail) := by
            have h_c := Nat.isChain_primeFactorsList n
            rwa [h_list] at h_c
          have hpq_le : p ≤ q := List.IsChain.rel_head h_chain
          have hp_mem : p ∈ Nat.primeFactorsList n := by rw [h_list]; simp
          have hq_mem : q ∈ Nat.primeFactorsList n := by rw [h_list]; simp
          have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp_mem
          have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hq_mem
          have hpq_ne : p ≠ q := by
            intro hc; subst hc
            have h_p2_dvd : p * p ∣ n := by
              have h_prod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn0
              rw [h_list] at h_prod
              have h_prod_eq : (p :: p :: tail).prod = (p * p) * tail.prod := by
                simp [List.prod_cons]
                ring
              rw [h_prod_eq] at h_prod
              rw [← h_prod]
              exact dvd_mul_right (p * p) tail.prod
            rw [squarefree_iff_prime_squarefree] at h_sf
            exact h_sf p hp_prime h_p2_dvd
          have hpq_lt : p < q := Nat.lt_of_le_of_ne hpq_le hpq_ne
          let m := tail.prod
          have h_prod_n : n = p * q * m := by
            have h_prod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn0
            rw [h_list] at h_prod
            rw [← h_prod]
            simp [m, List.prod_cons]
            ring
          have h_sf_pqm : Squarefree (p * q * m) := by rwa [← h_prod_n]
          have h_a_pqm : a (p * q * m) = 1 := by rwa [← h_prod_n]
          have h_divs := pq_divisibility hp_prime hq_prime hpq_lt h_sf_pqm h_a_pqm
          have hp_dvd := h_divs.1
          have hq_dvd := h_divs.2
          let Y := (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m)
          rcases hp_prime.eq_two_or_odd with hp2 | hp_odd
          · subst hp2
            have hq_ge3 : q ≥ 3 := by omega
            have hm_odd : Odd m := by
              by_contra hc
              have h_even : m % 2 = 0 := by
                have : ¬ (m % 2 = 1) := by
                  intro h_odd
                  exact hc (Nat.odd_iff.mpr h_odd)
                omega
              have h2_dvd_m : 2 ∣ m := Nat.dvd_of_mod_eq_zero h_even
              rcases h2_dvd_m with ⟨k, hk⟩
              have h4_dvd : 2 * 2 ∣ n := by
                rw [h_prod_n, hk]
                use q * k
                ring
              rw [squarefree_iff_prime_squarefree] at h_sf
              exact h_sf 2 Nat.prime_two h4_dvd
            have hY_odd : Odd Y := odd_S_of_odd hm_odd
            have hq_dvd_3Y : q ∣ 3 * Y - 1 := hq_dvd
            cases tail with
            | nil =>
              have hm1 : m = 1 := rfl
              have hY1 : Y = 1 := by
                change (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) = 1
                rw [hm1]
                rfl
              rw [hY1] at hq_dvd_3Y
              have : q ∣ 2 := hq_dvd_3Y
              have : q ≤ 2 := Nat.le_of_dvd (by omega) this
              omega
            | cons r tail' =>
              have hr_mem : r ∈ Nat.primeFactorsList n := by rw [h_list]; simp
              have hr_prime : Nat.Prime r := Nat.prime_of_mem_primeFactorsList hr_mem
              have hqr_le : q ≤ r := by
                have h_chain_sub : List.IsChain (· ≤ ·) (q :: r :: tail') := List.IsChain.tail h_chain
                exact List.IsChain.rel_head h_chain_sub
              have hqr_ne : q ≠ r := by
                intro hc; subst hc
                have hq2_dvd : q * q ∣ n := by
                  have h_prod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn0
                  rw [h_list] at h_prod
                  rw [← h_prod]
                  simp [List.prod_cons]
                  use 2 * tail'.prod
                  ring
                rw [squarefree_iff_prime_squarefree] at h_sf
                exact h_sf q hq_prime hq2_dvd
              have hqr_lt : q < r := Nat.lt_of_le_of_ne hqr_le hqr_ne
              have hr_ge5 : r ≥ 5 := by
                rcases hr_prime.eq_two_or_odd with hr2 | hr_odd
                · omega
                · have : r ≠ 3 := by omega
                  omega
              have hq_ge5 : q ≥ 5 := by
                rcases hq_prime.eq_two_or_odd with hq2 | hq_odd
                · omega
                · have hq_ne3 : q ≠ 3 := by
                    intro hc; subst hc
                    rcases hY_odd with ⟨ky, hky⟩
                    have hY_ge1 : Y ≥ 1 := by omega
                    have h_dvd31 : 3 ∣ 1 := dvd_of_dvd_sub_left (dvd_mul_right 3 Y) hq_dvd_3Y (by omega)
                    have h_not_3 : ¬ 3 ∣ 1 := by rintro ⟨k, hk⟩; omega
                    exact h_not_3 h_dvd31
                  omega
              have hr_ge7 : r ≥ 7 := by
                rcases hr_prime.eq_two_or_odd with hr2 | hr_odd
                · omega
                · have h_ne3 : r ≠ 3 := by omega
                  have h_ne5 : r ≠ 5 := by
                    intro hc; subst hc
                    have : q < 5 := hqr_lt
                    omega
                  omega
              let m' := tail'.prod
              have hm_eq : m = r * m' := rfl
              have hm0 : m' ≠ 0 := by
                intro hc
                have : m = 0 := by rw [hm_eq, hc, mul_zero]
                have : n = 0 := by rw [h_prod_n, this, mul_zero]
                exact hn0 this
              have h_cop_r : Nat.Coprime r m' := by
                have hr2_not_dvd : ¬ r * r ∣ n := by
                  rw [squarefree_iff_prime_squarefree] at h_sf
                  exact h_sf r hr_prime
                have hr_dvd_m' : r ∣ m' → r * r ∣ n := by
                  rintro ⟨k, hk⟩
                  use 2 * q * k
                  rw [h_prod_n, hm_eq, hk]
                  ring
                exact (Nat.Prime.coprime_iff_not_dvd hr_prime).mpr (fun h => hr2_not_dvd (hr_dvd_m' h))
              have h_Y_eq : Y = (2 * r - 1) * (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m') := by
                exact sum_divisors_mul_prime hr_prime h_cop_r hm0
              let Y' := (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m')
              have hY_val : Y = (2 * r - 1) * Y' := h_Y_eq
              have hq_dvd' : q ∣ 3 * (2 * r - 1) * Y' - 1 := by
                have h_eq : 3 * Y - 1 = 3 * (2 * r - 1) * Y' - 1 := by rw [hY_val, mul_assoc]
                rwa [h_eq] at hq_dvd_3Y
              have h_sf_2rm' : Squarefree (2 * r * (q * m')) := by
                have h_eq : 2 * r * (q * m') = n := by
                  rw [h_prod_n, hm_eq]
                  ring
                rwa [h_eq]
              have h_a_2rm' : a (2 * r * (q * m')) = 1 := by
                have h_eq : 2 * r * (q * m') = n := by
                  rw [h_prod_n, hm_eq]
                  ring
                rwa [h_eq]
              have h_div_r_temp := (pq_divisibility Nat.prime_two hr_prime (by omega) h_sf_2rm' h_a_2rm').2
              have h_cop_q : Nat.Coprime q m' := by
                have hq2_not_dvd : ¬ q * q ∣ n := by
                  rw [squarefree_iff_prime_squarefree] at h_sf
                  exact h_sf q hq_prime
                have hq_dvd_m' : q ∣ m' → q * q ∣ n := by
                  rintro ⟨k, hk⟩
                  use 2 * r * k
                  rw [h_prod_n, hm_eq, hk]
                  ring
                exact (Nat.Prime.coprime_iff_not_dvd hq_prime).mpr (fun h => hq2_not_dvd (hq_dvd_m' h))
              have h_S_qm' : (Finset.Ico 1 (q * m' + 1)).sum (fun k => Nat.gcd k (q * m')) = (2 * q - 1) * Y' := by
                exact sum_divisors_mul_prime hq_prime h_cop_q hm0
              have h_div_r : r ∣ 3 * (2 * q - 1) * Y' - 1 := by
                have h_temp : (2 * 2 - 1) * (Finset.Ico 1 (q * m' + 1)).sum (fun k => Nat.gcd k (q * m')) - 1 = 3 * (2 * q - 1) * Y' - 1 := by
                  rw [h_S_qm']
                  ring
                rwa [h_temp] at h_div_r_temp
              let A' := 3 * (2 * q - 1) * (2 * r - 1) * Y' + 1
              have hY'_pos : Y' ≥ 1 := by
                have h_mem : 1 ∈ Finset.Ico 1 (m' + 1) := by rw [Finset.mem_Ico]; omega
                have h_le : Nat.gcd 1 m' ≤ Y' := Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.gcd x m')) h_mem
                rw [Nat.gcd_one_left] at h_le
                exact h_le
              have hq_div_A' : q ∣ A' := by
                have h_sum : (3 * (2 * r - 1) * Y' - 1) + A' = 2 * q * (3 * (2 * r - 1) * Y') := by
                  have h_3r_ge : 3 * (2 * r - 1) * Y' ≥ 1 := by
                    have h1 : 3 * (2 * r - 1) > 0 := by
                      apply Nat.mul_pos (by decide) (by omega)
                    have h2 : 3 * (2 * r - 1) * Y' > 0 := by
                      apply Nat.mul_pos h1 hY'_pos
                    omega
                  have h_eq : (3 * (2 * r - 1) * Y' - 1) + (3 * (2 * q - 1) * (2 * r - 1) * Y' + 1) =
                              ((3 * (2 * r - 1) * Y' - 1) + 1) + 3 * (2 * q - 1) * (2 * r - 1) * Y' := by omega
                  rw [h_eq]
                  rw [Nat.sub_add_cancel h_3r_ge]
                  have h_comm : 3 * (2 * r - 1) * Y' + 3 * (2 * q - 1) * (2 * r - 1) * Y' = 3 * (2 * r - 1) * Y' * (1 + (2 * q - 1)) := by ring
                  rw [h_comm]
                  have h_q_eq : 1 + (2 * q - 1) = 2 * q := by omega
                  rw [h_q_eq]
                  ring
                have h_div_sum : q ∣ (3 * (2 * r - 1) * Y' - 1) + A' := by
                  rw [h_sum]
                  use 2 * (3 * (2 * r - 1) * Y')
                  ring
                exact dvd_of_dvd_add_left h_div_sum hq_dvd'
              have hr_div_A' : r ∣ A' := by
                have h_sum : (3 * (2 * q - 1) * Y' - 1) + A' = 2 * r * (3 * (2 * q - 1) * Y') := by
                  have h_3q_ge : 3 * (2 * q - 1) * Y' ≥ 1 := by
                    have h1 : 3 * (2 * q - 1) > 0 := by
                      apply Nat.mul_pos (by decide) (by omega)
                    have h2 : 3 * (2 * q - 1) * Y' > 0 := by
                      apply Nat.mul_pos h1 hY'_pos
                    omega
                  have h_eq : (3 * (2 * q - 1) * Y' - 1) + (3 * (2 * q - 1) * (2 * r - 1) * Y' + 1) =
                              ((3 * (2 * q - 1) * Y' - 1) + 1) + 3 * (2 * q - 1) * (2 * r - 1) * Y' := by omega
                  rw [h_eq]
                  rw [Nat.sub_add_cancel h_3q_ge]
                  have h_comm : 3 * (2 * q - 1) * Y' + 3 * (2 * q - 1) * (2 * r - 1) * Y' = 3 * (2 * q - 1) * Y' * (1 + (2 * r - 1)) := by ring
                  rw [h_comm]
                  have h_r_eq : 1 + (2 * r - 1) = 2 * r := by omega
                  rw [h_r_eq]
                  ring
                have h_div_sum : r ∣ (3 * (2 * q - 1) * Y' - 1) + A' := by
                  rw [h_sum]
                  use 2 * (3 * (2 * q - 1) * Y')
                  ring
                exact dvd_of_dvd_add_left h_div_sum h_div_r
              have h_cop_qr : Nat.Coprime q r := by
                rw [hq_prime.coprime_iff_not_dvd]
                intro hq_dvd_r
                have h_eq : r = q := (Nat.Prime.dvd_iff_eq hr_prime hq_prime.ne_one).mp hq_dvd_r
                exact hqr_ne h_eq.symm
              have h_qr_div_A' : q * r ∣ A' := Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop_qr hq_div_A' hr_div_A'
              have h_qr_div_C' : q * r ∣ 6 * (q + r) * Y' - 3 * Y' - 1 := by
                have h_sum_A_C : A' + (6 * (q + r) * Y' - 3 * Y' - 1) = 12 * q * r * Y' := by
                  have h_sub_eq : 6 * (q + r) * Y' - 3 * Y' - 1 = 6 * (q + r) * Y' - (3 * Y' + 1) := by omega
                  rw [h_sub_eq]
                  have h_sub_ge : 3 * Y' + 1 ≤ 6 * (q + r) * Y' := by
                    have h1 : 6 * (q + r) * Y' = (6 * q + 6 * r) * Y' := by ring
                    have h_coef_ge : 6 * q + 6 * r ≥ 72 := by omega
                    have h2 : (6 * q + 6 * r) * Y' ≥ 72 * Y' := Nat.mul_le_mul_right Y' h_coef_ge
                    have h3 : 72 * Y' ≥ 3 * Y' + 1 := by omega
                    have h4 : 3 * Y' + 1 ≤ (6 * q + 6 * r) * Y' := Nat.le_trans h3 h2
                    rw [h1]
                    exact h4
                  rw [← Nat.add_sub_assoc h_sub_ge]
                  have h_ring : A' + 6 * (q + r) * Y' = 12 * q * r * Y' + 3 * Y' + 1 := by
                    have h_trans : A' + 6 * (q + r) * Y' = (3 * (2 * q - 1) * (2 * r - 1) + 6 * (q + r)) * Y' + 1 := by
                      change (3 * (2 * q - 1) * (2 * r - 1) * Y' + 1) + 6 * (q + r) * Y' = (3 * (2 * q - 1) * (2 * r - 1) + 6 * (q + r)) * Y' + 1
                      ring
                    rw [h_trans]
                    have h_coef : 3 * (2 * q - 1) * (2 * r - 1) + 6 * (q + r) = 12 * q * r + 3 := by
                      have h_q_ge : 2 * q ≥ 1 := by omega
                      have h_r_ge : 2 * r ≥ 1 := by omega
                      have h_cast : ((3 * (2 * q - 1) * (2 * r - 1) + 6 * (q + r) : ℕ) : ℤ) = ((12 * q * r + 3 : ℕ) : ℤ) := by
                        zify [h_q_ge, h_r_ge]
                        ring
                      exact_mod_cast h_cast
                    rw [h_coef]
                    ring
                  rw [h_ring]
                  exact Nat.add_sub_cancel (12 * q * r * Y') (3 * Y' + 1)
                have h_qr_div_sum : q * r ∣ A' + (6 * (q + r) * Y' - 3 * Y' - 1) := by
                  rw [h_sum_A_C]
                  use 12 * Y'
                  ring
                exact dvd_of_dvd_add_left h_qr_div_sum h_qr_div_A'
              have h_C_pos : 6 * (q + r) * Y' - 3 * Y' - 1 > 0 := by
                have h_qr : q + r ≥ 12 := by omega
                have h_mul : 72 * Y' ≤ 6 * (q + r) * Y' := by
                  have h_le : 72 ≤ 6 * (q + r) := by omega
                  exact Nat.mul_le_mul_right Y' h_le
                omega
              have h_le_C' : q * r ≤ 6 * (q + r) * Y' - 3 * Y' - 1 := Nat.le_of_dvd h_C_pos h_qr_div_C'
              cases tail' with
              | nil =>
                have hm'_eq : m' = 1 := rfl
                have hY'1 : Y' = 1 := by
                  change (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m') = 1
                  rw [hm'_eq]
                  rfl
                rw [hY'1] at h_le_C'
                rcases hq_prime.eq_two_or_odd with hq2_eq | hq_odd
                · omega
                · rcases hr_prime.eq_two_or_odd with hr2_eq | hr_odd
                  · omega
                  · by_cases hq5 : q = 5
                    · subst hq5
                      have hr13 : r = 13 := by
                        have h_dvd : r ∣ 26 := by
                          have h_dvd : r ∣ 3 * (2 * 5 - 1) * Y' - 1 := h_div_r
                          rw [hY'1] at h_dvd
                          have h_calc : 3 * (2 * 5 - 1) * 1 - 1 = 26 := by decide
                          rwa [h_calc] at h_dvd
                        have hr_le : r ≤ 26 := Nat.le_of_dvd (by decide) h_dvd
                        have h_mod : 26 % r = 0 := Nat.mod_eq_zero_of_dvd h_dvd
                        have hr_ge6 : r ≥ 6 := by omega
                        interval_cases r <;> (try rfl) <;> (first | (exfalso; revert hr_prime; decide) | (exfalso; revert h_mod; decide))
                      subst hr13
                      have h_dvd5 : 5 ∣ 74 := by
                        have h_dvd : 5 ∣ 3 * (2 * 13 - 1) * Y' - 1 := hq_dvd'
                        rw [hY'1] at h_dvd
                        have h_calc : 3 * (2 * 13 - 1) * 1 - 1 = 74 := by decide
                        rwa [h_calc] at h_dvd
                      have : ¬ 5 ∣ 74 := by decide
                      contradiction
                    · by_cases hq7 : q = 7
                      · subst hq7
                        have hr19 : r = 19 := by
                          have h_dvd : r ∣ 38 := by
                            have h_dvd : r ∣ 3 * (2 * 7 - 1) * Y' - 1 := h_div_r
                            rw [hY'1] at h_dvd
                            have h_calc : 3 * (2 * 7 - 1) * 1 - 1 = 38 := by decide
                            rwa [h_calc] at h_dvd
                          have hr_le : r ≤ 38 := Nat.le_of_dvd (by decide) h_dvd
                          have h_mod : 38 % r = 0 := Nat.mod_eq_zero_of_dvd h_dvd
                          have hr_ge8 : r ≥ 8 := by omega
                          interval_cases r <;> (try rfl) <;> (first | (exfalso; revert hr_prime; decide) | (exfalso; revert h_mod; decide))
                        subst hr19
                        have h_dvd7 : 7 ∣ 110 := by
                          have h_dvd : 7 ∣ 3 * (2 * 19 - 1) * Y' - 1 := hq_dvd'
                          rw [hY'1] at h_dvd
                          have h_calc : 3 * (2 * 19 - 1) * 1 - 1 = 110 := by decide
                          rwa [h_calc] at h_dvd
                        have : ¬ 7 ∣ 110 := by decide
                        contradiction
                      · have hq_ge11 : q ≥ 11 := by
                          have : q ≠ 5 := hq5
                          have : q ≠ 7 := hq7
                          have : q ≠ 9 := by
                            rintro rfl
                            have : ¬ Nat.Prime 9 := by decide
                            contradiction
                          omega
                        have hr_ge13 : r ≥ 13 := by omega
                        nlinarith
              | cons s tail'' =>
                have hs_mem : s ∈ Nat.primeFactorsList n := by rw [h_list]; simp
                have hs_prime : Nat.Prime s := Nat.prime_of_mem_primeFactorsList hs_mem
                have hrs_le : r ≤ s := by
                  have h_chain_sub : List.IsChain (· ≤ ·) (r :: s :: tail'') := by
                    rw [h_list] at h_chain
                    exact List.IsChain.tail (List.IsChain.tail h_chain)
                  exact List.IsChain.rel_head h_chain_sub
                have hrs_ne : r ≠ s := by
                  intro hc; subst hc
                  have hr2_dvd : r * r ∣ n := by
                    have h_prod : (Nat.primeFactorsList n).prod = n := Nat.prod_primeFactorsList hn0
                    rw [h_list] at h_prod
                    rw [← h_prod]
                    simp [List.prod_cons]
                    use 2 * q * tail''.prod
                    ring
                  rw [squarefree_iff_prime_squarefree] at h_sf
                  exact h_sf r hr_prime hr2_dvd
                have hrs_lt : r < s := Nat.lt_of_le_of_ne hrs_le hrs_ne
                have hs_ge7 : s ≥ 7 := by
                  rcases hs_prime.eq_two_or_odd with hs2 | hs_odd
                  · omega
                  · have : s ≠ 3 := by omega
                    have : s ≠ 5 := by omega
                    omega
                let m'' := tail''.prod
                have hm''_eq : m' = s * m'' := rfl
                have hm''0 : m'' ≠ 0 := by
                  intro hc
                  have : m' = 0 := by rw [hm''_eq, hc, mul_zero]
                  exact hm0 this
                have h_cop_s : Nat.Coprime s m'' := by
                  have hs2_not_dvd : ¬ s * s ∣ n := by
                    rw [squarefree_iff_prime_squarefree] at h_sf
                    exact h_sf s hs_prime
                  have hs_dvd_m'' : s ∣ m'' → s * s ∣ n := by
                    rintro ⟨k, hk⟩
                    use 2 * q * r * k
                    rw [h_prod_n, hm_eq, hm''_eq, hk]
                    ring
                  exact (Nat.Prime.coprime_iff_not_dvd hs_prime).mpr (fun h => hs2_not_dvd (hs_dvd_m'' h))
                have h_Y'_eq : Y' = (2 * s - 1) * (Finset.Ico 1 (m'' + 1)).sum (fun k => Nat.gcd k m'') := by
                  exact sum_divisors_mul_prime hs_prime h_cop_s hm''0
                let Y'' := (Finset.Ico 1 (m'' + 1)).sum (fun k => Nat.gcd k m'')
                have hY'_val : Y' = (2 * s - 1) * Y'' := h_Y'_eq
                have hY''_pos : Y'' ≥ 1 := by
                  have h_mem : 1 ∈ Finset.Ico 1 (m'' + 1) := by rw [Finset.mem_Ico]; omega
                  have h_le : Nat.gcd 1 m'' ≤ Y'' := Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.gcd x m'')) h_mem
                  rw [Nat.gcd_one_left] at h_le
                  exact h_le
                have hY'_ge13 : Y' ≥ 13 := by
                  have h_sub : 2 * s - 1 ≥ 13 := by omega
                  have h_mul : (2 * s - 1) * Y'' ≥ 13 * 1 := Nat.mul_le_mul h_sub hY''_pos
                  rwa [← hY'_val] at h_mul
                have hq_ge5 : q ≥ 5 := by
                  rcases hq_prime.eq_two_or_odd with hq2 | hq_odd
                  · omega
                  · have hq_ne3 : q ≠ 3 := by
                      intro hc; subst hc
                      rcases hY_odd with ⟨ky, hky⟩
                      have hY_ge1 : Y ≥ 1 := by omega
                      have h_dvd31 : 3 ∣ 1 := dvd_of_dvd_sub_left (dvd_mul_right 3 Y) hq_dvd_3Y (by omega)
                      have h_not_3 : ¬ 3 ∣ 1 := by rintro ⟨k, hk⟩; omega
                      exact h_not_3 h_dvd31
                    omega
                have hr_ge7 : r ≥ 7 := by
                  rcases hr_prime.eq_two_or_odd with hr2 | hr_odd
                  · omega
                  · have h_ne3 : r ≠ 3 := by omega
                    have h_ne5 : r ≠ 5 := by
                      intro hc; subst hc
                      have : q < 5 := hqr_lt
                      omega
                    omega
                have hr_dvd_3q_Y' : r ∣ 3 * (2 * q - 1) * Y' - 1 := h_div_r
                rcases hr_dvd_3q_Y' with ⟨b, hb⟩
                have hq_dvd_3r_Y' : q ∣ 3 * (2 * r - 1) * Y' - 1 := hq_dvd'
                rcases hq_dvd_3r_Y' with ⟨a, ha⟩
                have h_eq : (a + 6 * Y') * q = (b + 6 * Y') * r := by
                  have h_cast : ((a + 6 * Y') * q : ℕ) = ((b + 6 * Y') * r : ℕ) := by
                    have hq_ge : 2 * q ≥ 1 := by omega
                    have hr_ge : 2 * r ≥ 1 := by omega
                    have h_sub : 3 * (2 * q - 1) * Y' ≥ 1 := by
                      have h1 : 3 * (2 * q - 1) > 0 := by apply Nat.mul_pos (by decide) (by omega)
                      have h2 : 3 * (2 * q - 1) * Y' > 0 := by apply Nat.mul_pos h1 (by omega)
                      omega
                    have h_sub2 : 3 * (2 * r - 1) * Y' ≥ 1 := by
                      have h1 : 3 * (2 * r - 1) > 0 := by apply Nat.mul_pos (by decide) (by omega)
                      have h2 : 3 * (2 * r - 1) * Y' > 0 := by apply Nat.mul_pos h1 (by omega)
                      omega
                    zify [hq_ge, hr_ge, h_sub, h_sub2]
                    rw [← ha, ← hb]
                    ring
                  exact_mod_cast h_cast
                have hq_dvd_b6Y' : q ∣ b + 6 * Y' := by
                  have h_dvd : q ∣ (b + 6 * Y') * r := by
                    rw [← h_eq]
                    exact dvd_mul_left q (a + 6 * Y')
                  exact h_cop_qr.dvd_of_dvd_mul_right h_dvd
                rcases hq_dvd_b6Y' with ⟨c, hc⟩
                have hc_eq : b + 6 * Y' = q * c := hc
                have hc_eq2 : a + 6 * Y' = r * c := by
                  have : (a + 6 * Y') * q = (q * c) * r := by rw [h_eq, hc_eq]
                  have : (a + 6 * Y') * q = (r * c) * q := by
                    rw [this]
                    ring
                  exact Nat.eq_of_mul_eq_mul_right hq_prime.pos this
                have hqrc_eq : q * r * c = (6 * q + 6 * r - 3) * Y' - 1 := by
                  rw [mul_assoc]
                  rw [hc_eq2]
                  have h_ring : r * (a + 6 * Y') = a * r + 6 * r * Y' := by ring
                  rw [h_ring]
                  have : a * r = 3 * (2 * r - 1) * Y' - 1 := by
                    rw [mul_comm]
                    exact ha
                  rw [this]
                  have h_coef : 3 * (2 * r - 1) * Y' + 6 * r * Y' = (6 * q + 6 * r - 3) * Y' := by
                    have hq_odd : q % 2 = 1 := by
                      rcases hq_prime.eq_two_or_odd with rfl | h_odd
                      · omega
                      · exact h_odd
                    have hr_odd : r % 2 = 1 := by
                      rcases hr_prime.eq_two_or_odd with rfl | h_odd
                      · omega
                      · exact h_odd
                    have h_coef : 3 * (2 * r - 1) + 6 * r = 6 * q + 6 * r - 3 := by omega
                    rw [← h_coef]
                    ring
                  rw [h_coef]
                have hc_lt2Y' : c < 2 * Y' := by
                  have h_mul : q * r * c < q * r * (2 * Y') := by
                    rw [hqrc_eq]
                    have h_cast : (((6 * q + 6 * r - 3) * Y' - 1 : ℕ) : ℤ) < (((2 * q * r * Y' : ℕ) : ℤ)) := by
                      have h_sub_y : (6 * q + 6 * r - 3) * Y' ≥ 1 := by
                        have h1 : 6 * q + 6 * r - 3 ≥ 69 := by omega
                        have h2 : Y' ≥ 13 := hY'_ge13
                        have : (6 * q + 6 * r - 3) * Y' ≥ 69 * 13 := Nat.mul_le_mul h1 h2
                        omega
                      zify [h_sub_y]
                      have : 2 * (q : ℤ) * r - 6 * q - 6 * r + 3 ≥ 17 := by
                        have u1 : (q : ℤ) - 3 ≥ 2 := by omega
                        have u2 : (r : ℤ) - 3 ≥ 4 := by omega
                        nlinarith
                      nlinarith
                    exact_mod_cast h_cast
                  have h_qr_pos : q * r > 0 := by omega
                  exact Nat.lt_of_mul_lt_mul_left h_mul
                have hc_le : c ≤ 2 * Y' - 1 := by omega
                have h_le : (6 * q + 6 * r - 3) * Y' - 1 ≤ 2 * q * r * Y' - q * r := by
                  calc
                    (6 * q + 6 * r - 3) * Y' - 1 = q * r * c := hqrc_eq.symm
                    _ ≤ q * r * (2 * Y' - 1) := Nat.mul_le_mul_left (q * r) hc_le
                    _ = 2 * q * r * Y' - q * r := by
                      have h_sub_y : 2 * Y' ≥ 1 := by omega
                      have h_cast : (((q * r * (2 * Y' - 1) : ℕ) : ℤ)) = (((2 * q * r * Y' - q * r : ℕ) : ℤ)) := by
                        have h_sub_ge : 2 * q * r * Y' ≥ q * r := by
                          have : 2 * Y' ≥ 1 := by omega
                          have : 2 * q * r * Y' = q * r * (2 * Y') := by ring
                          rw [this]
                          exact Nat.mul_le_mul_left (q * r) (by omega)
                        zify [h_sub_y, h_sub_ge]
                        ring
                      exact_mod_cast h_cast
                have h_contr : Y' * (2 * q * r - 6 * q - 6 * r + 3) ≤ q * r - 1 := by
                  have h_sub_y : (6 * q + 6 * r - 3) * Y' ≥ 1 := by
                    have h1 : 6 * q + 6 * r - 3 ≥ 69 := by omega
                    have h2 : Y' ≥ 13 := hY'_ge13
                    have : (6 * q + 6 * r - 3) * Y' ≥ 69 * 13 := Nat.mul_le_mul h1 h2
                    omega
                  have h_sub_y2 : 2 * q * r * Y' ≥ q * r := by
                    have : 2 * Y' ≥ 1 := by omega
                    have : 2 * q * r * Y' = q * r * (2 * Y') := by ring
                    rw [this]
                    exact Nat.mul_le_mul_left (q * r) (by omega)
                  have h_cast : (((6 * q + 6 * r - 3) * Y' - 1 : ℕ) : ℤ) ≤ (((2 * q * r * Y' - q * r : ℕ) : ℤ)) := by
                    zify [h_sub_y, h_sub_y2]
                    exact_mod_cast h_le
                  have h_res : (Y' * (2 * q * r - 6 * q - 6 * r + 3) : ℤ) ≤ ((q * r - 1 : ℕ) : ℤ) := by
                    have : q * r ≥ 1 := by omega
                    zify [this] at h_cast ⊢
                    linarith
                  exact_mod_cast h_res
                  exact_mod_cast h_res
                by_cases hqr_7_5 : q = 5 ∧ r = 7
                · rcases hqr_7_5 with ⟨rfl, rfl⟩
                  -- Y' * (2 * 5 * 7 - 30 - 42 + 3) <= 35 - 1 => Y' * 1 <= 34 => Y' <= 34.
                  have hY'_le34 : Y' ≤ 34 := by
                    have h_calc : 2 * 5 * 7 - 6 * 5 - 6 * 7 + 3 = 1 := by decide
                    rw [h_calc] at h_contr
                    have h_calc2 : 5 * 7 - 1 = 34 := by decide
                    rwa [h_calc2, mul_one] at h_contr
                  -- But wait, we have c <= 2 * Y' - 1 and q = 5, r = 7 => 35 * c = 69 * Y' - 1
                  -- We can show Y' >= 34
                  have hY'_ge34 : Y' ≥ 34 := by
                    have h_calc : 35 * c = 69 * Y' - 1 := by
                      have : 5 * 7 * c = (6 * 5 + 6 * 7 - 3) * Y' - 1 := by
                        rw [← hc_eq2]
                        ring
                      change 35 * c = (6 * 5 + 6 * 7 - 3) * Y' - 1 at this
                      rwa [show 6 * 5 + 6 * 7 - 3 = 69 by decide] at this
                    have h_ineq : 35 * (2 * Y' - 1) ≥ 69 * Y' - 1 := by
                      rw [← h_calc]
                      exact Nat.mul_le_mul_left 35 hc_le
                    have h_cast : (35 * (2 * Y' - 1) : ℤ) ≥ (69 * Y' - 1 : ℤ) := by
                      have : 2 * Y' ≥ 1 := by omega
                      have : 69 * Y' ≥ 1 := by omega
                      zify [this] at h_ineq ⊢
                      exact_mod_cast h_ineq
                    have : 2 * Y' ≥ 1 := by omega
                    zify [this] at h_cast ⊢
                    omega
                  have hY'_34 : Y' = 34 := by omega
                  -- Since Y' = (2 * s - 1) * Y'' = 34
                  -- Since s is prime, s >= 11 => 2 * s - 1 >= 21
                  -- And 2 * s - 1 divides 34.
                  -- But the divisors of 34 are 1, 2, 17, 34.
                  -- Since 2 * s - 1 >= 21, 2 * s - 1 must be 34.
                  -- But 2 * s - 1 is odd (since 2 * s - 1 = 2 * (s - 1) + 1), and 34 is even!
                  -- Contradiction!
                  have h_dvd : 2 * s - 1 ∣ 34 := by
                    rw [hY'_34] at hY'_val
                    use Y''
                    exact hY'_val
                  have h_ge21 : 2 * s - 1 ≥ 21 := by omega
                  have h_divs : 2 * s - 1 = 34 := by
                    have h_le : 2 * s - 1 ≤ 34 := Nat.le_of_dvd (by decide) h_dvd
                    have h_mod : 34 % (2 * s - 1) = 0 := Nat.mod_eq_zero_of_dvd h_dvd
                    omega
                  have h_odd : (2 * s - 1) % 2 = 1 := by
                    have : 2 * s ≥ 1 := by omega
                    omega
                  rw [h_divs] at h_odd
                  contradiction
                · -- If q >= 5 and r >= 7 and (q,r) != (5,7)
                  -- Then Y' * (2 * q * r - 6 * q - 6 * r + 3) <= q * r - 1
                  -- is impossible because 2 * q * r - 6 * q - 6 * r + 3 >= 5 (or similar)
                  -- and Y' >= 13 => 13 * 5 > q * r?
                  -- Wait, let's use nlinarith or omega!
                  have h_contr2 : (Y' * (2 * q * r - 6 * q - 6 * r + 3) : ℤ) ≥ (13 * (2 * q * r - 6 * q - 6 * r + 3) : ℤ) := by
                    have h1 : (Y' : ℤ) ≥ 13 := by exact_mod_cast hY'_ge13
                    have h2 : (2 * (q : ℤ) * r - 6 * q - 6 * r + 3) ≥ 1 := by
                      have : 2 * (q - 3) * (r - 3) ≥ 16 := by
                        have u1 : q - 3 ≥ 2 := by omega
                        have u2 : r - 3 ≥ 4 := by omega
                        have t1 : (q - 3) * (r - 3) ≥ 8 := Nat.mul_le_mul u1 u2
                        omega
                      omega
                    nlinarith
                  have h_contr3 : (q * (r : ℤ) - 1) < (13 * (2 * q * r - 6 * q - 6 * r + 3) : ℤ) := by
                    -- since q >= 5 and r >= 7 and (q,r) != (5,7)
                    -- If q = 5, r >= 11:
                    -- 13 * (4 * r - 27) = 52 * r - 351 > 5 * r - 1 is true for r >= 11
                    -- If q >= 7, r >= 11:
                    -- 13 * (2 * q * r - 6 * q - 6 * r + 3) > q * r - 1 is true
                    by_cases hq5_eq : q = 5
                    · subst hq5_eq
                      have hr11 : r ≥ 11 := by
                        have : q < r := hqr_lt
                        have : r ≠ 5 := by
                          intro hc; subst hc
                          exact hqr_ne rfl
                        have : r ≠ 2 := hr_prime.ne_one
                        have : r ≠ 3 := by omega
                        omega
                      nlinarith
                    · have hq7_ge : q ≥ 7 := by
                        have : q ≠ 5 := hq5_eq
                        have : q ≠ 2 := hq_prime.ne_one
                        have : q ≠ 3 := by omega
                        omega
                      have hr11 : r ≥ 11 := by
                        have : q < r := hqr_lt
                        have : r ≠ 2 := hr_prime.ne_one
                        have : r ≠ 3 := by omega
                        have : r ≠ 5 := by omega
                        omega
                      nlinarith
                  have h_contr_all : ((Y' * (2 * q * r - 6 * q - 6 * r + 3) : ℕ) : ℤ) < ((Y' * (2 * q * r - 6 * q - 6 * r + 3) : ℕ) : ℤ) := by
                    calc
                      ((Y' * (2 * q * r - 6 * q - 6 * r + 3) : ℕ) : ℤ) ≤ (q * r - 1 : ℤ) := by exact_mod_cast h_contr
                      _ < (13 * (2 * q * r - 6 * q - 6 * r + 3) : ℤ) := h_contr3
                      _ ≤ (Y' * (2 * q * r - 6 * q - 6 * r + 3) : ℤ) := h_contr2
          · have hp_odd' : Odd p := hp_odd
            have hn_odd : Odd n := by
              by_contra h_even
              have h2_dvd : 2 ∣ n := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h_even)
              have h2_mem : 2 ∈ Nat.primeFactorsList n := by
                rw [Nat.mem_primeFactorsList_iff_dvd hn0]
                exact ⟨Nat.prime_two, h2_dvd⟩
              have h_mem : 2 ∈ p :: q :: tail := by rwa [← h_list]
              rcases h_mem with rfl | h_mem
              · rcases hp_prime.eq_two_or_odd with rfl | hp_odd''
                · contradiction
                · omega
              · rcases h_mem with rfl | h_mem
                · omega
                · have hq2 : q ≤ 2 := chain_le_of_mem h_chain 2 h_mem
                  omega
            have hp3 : p ≥ 3 := by omega
            have hq5 : q ≥ 5 := by omega
            have h_pq_div := h_divs
                exact hr_prime.ne_one this
              have hr_ne_q : r ≠ q := by
                intro hrq
                have h_dvd : q ∣ m := by rwa [← hrq]
                have h_gcd_qm : Nat.gcd q m = q := Nat.gcd_eq_left h_dvd
                rw [h_cop_qm] at h_gcd_qm
                exact hq_p.ne_one h_gcd_qm.symm
              have hr_ne_p : r ≠ p := by
                intro hrp
                have h_dvd : p ∣ m := by rwa [← hrp]
                have h_gcd_pm : Nat.gcd p m = p := Nat.gcd_eq_left h_dvd
                rw [h_cop_pm] at h_gcd_pm
                exact hp_p.ne_one h_gcd_pm.symm
              have hr_dvd_n : r ∣ p * q * m := by
                rcases hr_dvd with ⟨k, hk⟩
                use p * q * k
                rw [hk]
                ring
              have hn0_re : p * q * m ≠ 0 := hn0
              have hr_in : r ∈ Nat.primeFactorsList (p * q * m) := by
                rw [Nat.mem_primeFactorsList hn0_re]
                exact ⟨hr_prime, hr_dvd_n⟩
              rw [h_list] at hr_in
              simp only [List.mem_cons] at hr_in
              have hr_mem : r ∈ tail := by
                rcases hr_in with hp | hq | h_tail
                · exact False.elim (hr_ne_p hp)
                · exact False.elim (hr_ne_q hq)
                · exact h_tail
              have hqr_le : q ≤ r := chain_le_of_mem h_chain r hr_mem
              have hqr : q < r := Nat.lt_of_le_of_ne hqr_le hr_ne_q.symm
              have hqr_ge2 : r ≥ q + 2 := by
                by_contra h_ge
                have : r = q + 1 := by omega
                have h_even : 2 ∣ r := by
                  use (q / 2 + 1)
                  have hq_odd_m : Odd q := by
                    have hn_odd_eq : Odd (p * q * m) := hn_odd
                    rw [Nat.odd_mul, Nat.odd_mul] at hn_odd_eq
                    exact hn_odd_eq.1.2
                  have : q % 2 = 1 := Nat.odd_iff.mp hq_odd_m
                  omega
                have h_eq_2 : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd hr_prime 2 h_even |>.resolve_left (by norm_num)).symm
                omega
              obtain ⟨m', hm'_eq⟩ := hr_dvd
              have h_cop_rm' : Nat.Coprime r m' := by
                have h_sf_rm' : Squarefree (r * m') := by
                  have h_sf_m : Squarefree m := by
                    have : p * q * m = (p * q) * m := by ring
                    rw [this] at h_sf
                    exact Squarefree.squarefree_of_dvd (dvd_mul_left m (p * q)) h_sf
                  rwa [← hm'_eq]
                have h_r2_not_dvd : ¬ r * r ∣ r * m' := by
                  intro hc_r2
                  have h_r2_n : r * r ∣ p * q * m := by
                    rcases hc_r2 with ⟨k, hk⟩
                    use p * q * k
                    calc
                      p * q * m = p * q * (r * m') := by rw [hm'_eq]
                      _ = r * r * (p * q * k) := by rw [hk]; ring
                  rw [squarefree_iff_prime_squarefree] at h_sf
                  exact h_sf r hr_prime h_r2_n
                exact (Nat.Prime.coprime_iff_not_dvd hr_prime).mpr (by
                  intro hr_dvd_m'
                  have : r * r ∣ r * m' := by
                    rcases hr_dvd_m' with ⟨k, hk⟩
                    use k
                    rw [hk]
                    ring
                  exact h_r2_not_dvd this)
              have hm'_pos : m' ≠ 0 := by
                rintro rfl
                simp at hm'_eq
                exact hm0 hm'_eq
              have h_S_m : X = (2 * r - 1) * (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m') := by
                dsimp only [X]
                rw [hm'_eq]
                exact sum_divisors_mul_prime hr_prime h_cop_rm' hm'_pos
              let Y := (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m')
              have h_S_m_Y : X = (2 * r - 1) * Y := h_S_m
              have hY_pos : Y ≥ 1 := by
                have h_mem : 1 ∈ Finset.Ico 1 (m' + 1) := by
                  rw [Finset.mem_Ico]
                  omega
                have h_le : Nat.gcd 1 m' ≤ Y := Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.gcd x m')) h_mem
                rw [Nat.gcd_one_left] at h_le
                exact h_le
              have h_ineq1 : 5 * (2 * r - 1) ≤ 2 * (L * q) + 1 := by
                calc
                  5 * (2 * r - 1) ≤ (2 * p - 1) * (2 * r - 1) := Nat.mul_le_mul_right (2 * r - 1) (by omega)
                  _ ≤ (2 * p - 1) * ((2 * r - 1) * Y) := by
                    have : 2 * r - 1 ≤ (2 * r - 1) * Y := by
                      calc
                        2 * r - 1 = (2 * r - 1) * 1 := by ring
                        _ ≤ (2 * r - 1) * Y := Nat.mul_le_mul_left (2 * r - 1) hY_pos
                    exact Nat.mul_le_mul_left (2 * p - 1) this
                  _ = (2 * p - 1) * X := by rw [← h_S_m_Y]
                  _ = 2 * L * q + 1 := hK_eq
                  _ = 2 * (L * q) + 1 := by ring
              have h_ineq2 : 5 * r ≤ L * q + 3 := by
                have h_alg : 5 * (2 * r - 1) = 10 * r - 5 := by omega
                have h_ineq_re := h_ineq1
                rw [h_alg] at h_ineq_re
                have h_10r : 10 * r ≤ 2 * (L * q) + 6 := by omega
                have h_mul_le : 2 * (5 * r) ≤ 2 * (L * q + 3) := by
                  calc
                    2 * (5 * r) = 10 * r := by ring
                    _ ≤ 2 * (L * q) + 6 := h_10r
                    _ = 2 * (L * q + 3) := by ring
                exact Nat.le_of_mul_le_mul_left h_mul_le (by decide)
              have h_L_cases : L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L ≥ 6 := by omega
              rcases h_L_cases with rfl | rfl | rfl | rfl | hL6
              · omega
              · omega
              · omega
              · omega
              · have h_q7 : q ≥ 7 := by
                  by_contra h_q_lt
                  have h_cases : q = 5 ∨ q = 6 := by omega
                  rcases h_cases with rfl | rfl
                  · have hp_cases : p = 3 ∨ p = 4 := by omega
                    rcases hp_cases with rfl | rfl
                    · have hK_eq_re : 5 * X = 2 * L * 5 + 1 := by omega
                      have h_div5 : 5 ∣ 2 * L * 5 + 1 := ⟨X, by omega⟩
                      have h_div_one : 5 ∣ 1 := by
                        rcases h_div5 with ⟨z, hz⟩
                        use (z - 2 * L)
                        omega
                      omega
                    · exfalso
                      have : ¬ Nat.Prime 4 := by norm_num
                      exact this hp_p
                  · exfalso
                    have : ¬ Nat.Prime 6 := by norm_num
                    exact this hq_p
                have h_div_r : r ∣ L * (2 * q - 1) + 1 := by
                  use c * p * m'
                  calc
                    L * (2 * q - 1) + 1 = c * p * (r * m') := by rwa [hm'_eq] at h_div2
                    _ = r * (c * p * m') := by ring
                rcases h_div_r with ⟨a, h_a_eq⟩
                have ha_pos : a ≥ 1 := by
                  by_contra ha0
                  have : a = 0 := by omega
                  subst this
                  omega
                have ha_lt : a ≤ 2 * L - 1 := by
                  by_contra h_a_ge
                  have : a ≥ 2 * L := by omega
                  have h_le_a : 2 * L * (q + 2) ≤ a * r := by
                    calc
                      2 * L * (q + 2) ≤ a * (q + 2) := Nat.mul_le_mul_right (q + 2) (by omega)
                      _ ≤ a * r := Nat.mul_le_mul_left a hqr_ge2
                  have h_eq_a : a * r = L * (2 * q - 1) + 1 := by
                    calc
                      a * r = r * a := mul_comm a r
                      _ = L * (2 * q - 1) + 1 := h_a_eq.symm
                  have h_alg_contr : 2 * L * (q + 2) ≤ L * (2 * q - 1) + 1 := by
                    calc
                      2 * L * (q + 2) ≤ a * r := h_le_a
                      _ = L * (2 * q - 1) + 1 := h_eq_a
                  have h_L_sub : 2 * q - 1 + 1 = 2 * q := by omega
                  have h_alg_L : L * (2 * q - 1) + L = 2 * L * q := by
                    calc
                      L * (2 * q - 1) + L = L * (2 * q - 1) + L * 1 := by ring
                      _ = L * (2 * q - 1 + 1) := by rw [← Nat.mul_add]
                      _ = L * (2 * q) := by rw [h_L_sub]
                      _ = 2 * L * q := by ring
                  have h_contr : 2 * L * q + 5 * L ≤ 2 * L * q + 1 := by
                    calc
                      2 * L * q + 5 * L = 2 * L * (q + 2) + L := by ring
                      _ ≤ L * (2 * q - 1) + 1 + L := Nat.add_le_add_right h_alg_contr L
                      _ = (L * (2 * q - 1) + L) + 1 := by ring
                      _ = 2 * L * q + 1 := by rw [h_alg_L]
                  have h_contr2 : 5 * L ≤ 1 := by omega
                  omega
                have h_sum_sub : L * (2 * q - 1) + L = 2 * L * q := by
                  have : 2 * q - 1 + 1 = 2 * q := by omega
                  calc
                    L * (2 * q - 1) + L = L * (2 * q - 1) + L * 1 := by ring
                    _ = L * (2 * q - 1 + 1) := by rw [← Nat.mul_add]
                    _ = L * (2 * q) := by rw [this]
                    _ = 2 * L * q := by ring
                have h_ineq3 : 10 * L * q - 5 * L + 5 ≤ a * L * q + 3 * a := by
                  have : 5 * a * r ≤ a * (L * q + 3) := by
                    calc
                      5 * a * r = a * (5 * r) := by ring
                      _ ≤ a * (L * q + 3) := Nat.mul_le_mul_left a h_ineq2
                  have h_re1 : 5 * a * r = 10 * L * q - 5 * L + 5 := by
                    have h_sum5 : 5 * (L * (2 * q - 1)) + 5 * L = 10 * L * q := by
                      calc
                        5 * (L * (2 * q - 1)) + 5 * L = 5 * (L * (2 * q - 1) + L) := by ring
                        _ = 5 * (2 * L * q) := by rw [h_sum_sub]
                        _ = 10 * L * q := by ring
                    have h_sum5_sub : 5 * (L * (2 * q - 1)) = 10 * L * q - 5 * L := by
                      omega
                    calc
                      5 * a * r = 5 * (r * a) := by ring
                      _ = 5 * (L * (2 * q - 1) + 1) := by rw [h_a_eq]
                      _ = 5 * (L * (2 * q - 1)) + 5 := by ring
                      _ = 10 * L * q - 5 * L + 5 := by rw [h_sum5_sub]
                  have h_re2 : a * (L * q + 3) = a * L * q + 3 * a := by ring
                  omega

                have ha_eq_cpm' : a = c * p * m' := by
                  have h_eq : r * a = r * (c * p * m') := by
                    calc
                      r * a = L * (2 * q - 1) + 1 := h_a_eq.symm
                      _ = c * p * m := h_div2
                      _ = c * p * (r * m') := by rw [hm'_eq]
                      _ = r * (c * p * m') := by ring
                  exact Nat.eq_of_mul_eq_mul_left hr_prime.pos h_eq

                have ha_ge6 : a ≥ 6 := by
                  rw [ha_eq_cpm']
                  have hcp : c * p ≥ 6 := by
                    calc
                      c * p ≥ 2 * 3 := Nat.mul_le_mul hc_pos hp3
                      _ = 6 := by decide
                  have hm'1 : m' ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm'_pos
                  calc
                    c * p * m' ≥ c * p * 1 := Nat.mul_le_mul_left (c * p) hm'1
                    _ = c * p := by ring
                    _ ≥ 6 := hcp

                have h_cases : a < 10 ∨ a ≥ 10 := by omega
                rcases h_cases with ha_lt10 | ha_ge10
                · have h_a_le9 : a ≤ 9 := by omega
                  have h_mul_le : a * L * q + 3 * a ≤ 9 * L * q + 27 := by
                    calc
                      a * L * q + 3 * a = a * (L * q + 3) := by ring
                      _ ≤ 9 * (L * q + 3) := Nat.mul_le_mul_right (L * q + 3) h_a_le9
                      _ = 9 * L * q + 27 := by ring
                  have h_Lq_le : 10 * L * q - 5 * L + 5 ≤ 9 * L * q + 27 := le_trans h_ineq3 h_mul_le
                  have h_Lq_le2 : L * q ≤ 5 * L + 22 := by
                    have h_Lq_le_rew : 10 * (L * q) - 5 * L + 5 ≤ 9 * (L * q) + 27 := by
                      have h_rew1 : 10 * (L * q) = 10 * L * q := by ring
                      have h_rew2 : 9 * (L * q) = 9 * L * q := by ring
                      rwa [h_rew1, h_rew2]
                    omega
                  have h_q_le : q * L ≤ 5 * L + 22 := by
                    rw [mul_comm] at h_Lq_le2
                    exact h_Lq_le2
                  have h_7L_le : 7 * L ≤ q * L := Nat.mul_le_mul_right L h_q7
                  have h_2L_le : 2 * L ≤ 22 := by omega
                  have h_L_le : L ≤ 11 := by omega
                  have h_q7_eq : q = 7 := by
                    have h_6q : 6 * q ≤ 5 * L + 22 := by
                      calc
                        6 * q ≤ L * q := Nat.mul_le_mul_right q (by omega)
                        _ ≤ 5 * L + 22 := h_Lq_le2
                    have h_q_lt11 : q < 11 := by
                      by_contra hc
                      have h_q_ge11 : q ≥ 11 := by omega
                      have h_11L : 11 * L ≤ q * L := Nat.mul_le_mul_right L h_q_ge11
                      have : 11 * L ≤ 5 * L + 22 := by omega
                      omega
                    have h_q_cases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 := by omega
                    rcases h_q_cases with rfl | rfl | rfl | rfl
                    · rfl
                    · exfalso; exact (by norm_num : ¬ Nat.Prime 8) hq_p
                    · exfalso; exact (by norm_num : ¬ Nat.Prime 9) hq_p
                    · exfalso; exact (by norm_num : ¬ Nat.Prime 10) hq_p
                  have h_prod_eq : r * (c * p * m') = 13 * L + 1 := by
                    calc
                      r * (c * p * m') = c * p * (r * m') := by ring
                      _ = c * p * m := by rw [← hm'_eq]
                      _ = L * (2 * q - 1) + 1 := h_div2.symm
                      _ = 13 * L + 1 := by rw [h_q7_eq]; ring
                  have h_L_cases2 : L = 6 ∨ L = 7 ∨ L = 8 ∨ L = 9 ∨ L = 10 ∨ L = 11 := by omega
                  rcases h_L_cases2 with rfl | rfl | rfl | rfl | rfl | rfl
                  · have h_prod : r * (c * p * m') = 79 := by
                      have := h_prod_eq
                      omega
                    have h_79_prime : Nat.Prime 79 := by norm_num
                    have : r ∣ 79 := ⟨c * p * m', h_prod.symm⟩
                    have : r = 1 ∨ r = 79 := (Nat.Prime.eq_one_or_self_of_dvd h_79_prime r this)
                    rcases this with hr1 | hr79
                    · exfalso; exact hr_prime.ne_one hr1
                    · have : c * p * m' = 1 := by
                        have : 79 * (c * p * m') = 79 * 1 := by
                          calc
                            79 * (c * p * m') = r * (c * p * m') := by rw [hr79]
                            _ = 79 := h_prod
                            _ = 79 * 1 := by ring
                        exact Nat.eq_of_mul_eq_mul_left (by decide) this
                      rw [← ha_eq_cpm'] at this
                      omega
                  · have h_prod : r * (c * p * m') = 92 := by
                      have := h_prod_eq
                      omega
                    have h_div_r : r ∣ 92 := ⟨c * p * m', h_prod.symm⟩
                    have h_prime_div : r = 2 ∨ r = 23 := by
                      have hd : r ∣ 2 * (2 * 23) := by
                        have : 92 = 2 * (2 * 23) := by decide
                        rwa [this] at h_div_r
                      rcases (Nat.Prime.dvd_mul hr_prime).mp hd with hr2 | hd2
                      · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                        left; exact this
                      · have hd3 : r ∣ 2 * 23 := hd2
                        rcases (Nat.Prime.dvd_mul hr_prime).mp hd3 with hr2 | hr23
                        · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                          left; exact this
                        · have : r = 23 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr23 |>.resolve_left hr_prime.ne_one)
                          right; exact this
                    rcases h_prime_div with hr2 | hr23
                    · exact False.elim (hr_ne_2 hr2)
                    · have : c * p * m' = 4 := by
                        have : 23 * (c * p * m') = 23 * 4 := by
                          calc
                            23 * (c * p * m') = r * (c * p * m') := by rw [hr23]
                            _ = 92 := h_prod
                            _ = 23 * 4 := by decide
                        exact Nat.eq_of_mul_eq_mul_left (by decide) this
                      rw [← ha_eq_cpm'] at this
                      omega
                  · have hK_113 : (2 * p - 1) * X = 113 := by
                      omega
                    have h_X1 : X = 1 := by
                      by_contra hX_ne1
                      have hX_ge2 : X ≥ 2 := by omega
                      have h_div_X : X ∣ 113 := by
                        use (2 * p - 1)
                        rw [mul_comm]
                        exact hK_113.symm
                      have h113_prime : Nat.Prime 113 := by decide
                      rcases Nat.Prime.eq_one_or_self_of_dvd h113_prime X h_div_X with hX1 | hX113
                      · omega
                      · rw [hX113] at hK_113
                        have : 2 * p - 1 = 1 := by omega
                        omega
                    have hp57 : p = 57 := by
                      rw [h_X1] at hK_113
                      omega
                    have hp_not_prime : ¬ Nat.Prime p := by
                      rw [hp57]
                      decide
                    exact False.elim (hp_not_prime hp_p)
                  · have h_prod : r * (c * p * m') = 118 := by
                      have := h_prod_eq
                      omega
                    have h_div_r : r ∣ 118 := ⟨c * p * m', h_prod.symm⟩
                    have h_prime_div : r = 2 ∨ r = 59 := by
                      have hd : r ∣ 2 * 59 := by
                        have : 118 = 2 * 59 := by decide
                        rwa [this] at h_div_r
                      rcases (Nat.Prime.dvd_mul hr_prime).mp hd with hr2 | hr59
                      · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr2 |>.resolve_left hr_prime.ne_one)
                        left; exact this
                      · have : r = 59 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr59 |>.resolve_left hr_prime.ne_one)
                        right; exact this
                    rcases h_prime_div with hr2 | hr59
                    · exact False.elim (hr_ne_2 hr2)
                    · have : c * p * m' = 2 := by
                        have : 59 * (c * p * m') = 59 * 2 := by
                          calc
                            59 * (c * p * m') = r * (c * p * m') := by rw [hr59]
                            _ = 118 := h_prod
                            _ = 59 * 2 := by decide
                        exact Nat.eq_of_mul_eq_mul_left (by decide) this
                      rw [← ha_eq_cpm'] at this
                      omega
                  · have h_prod : r * (c * p * m') = 131 := by
                      have := h_prod_eq
                      omega
                    have h_131_prime : Nat.Prime 131 := by norm_num
                    have : r ∣ 131 := ⟨c * p * m', h_prod.symm⟩
                    have : r = 1 ∨ r = 131 := (Nat.Prime.eq_one_or_self_of_dvd h_131_prime r this)
                    rcases this with hr1 | hr131
                    · exfalso; exact hr_prime.ne_one hr1
                    · have : c * p * m' = 1 := by
                        have : 131 * (c * p * m') = 131 * 1 := by
                          calc
                            131 * (c * p * m') = r * (c * p * m') := by rw [hr131]
                            _ = 131 := h_prod
                            _ = 131 * 1 := by ring
                        exact Nat.eq_of_mul_eq_mul_left (by decide) this
                      rw [← ha_eq_cpm'] at this
                      omega
                  · have h_prod : r * (c * p * m') = 144 := by
                      have := h_prod_eq
                      omega
                    have h_div_r : r ∣ 144 := ⟨c * p * m', h_prod.symm⟩
                    have h_prime_div : r = 2 ∨ r = 3 := by
                      have hd : r ∣ 16 * 9 := by
                        have : 144 = 16 * 9 := by decide
                        rwa [this] at h_div_r
                      have h_16_fac : 16 = 2 * (2 * (2 * 2)) := by decide
                      have h_9_fac : 9 = 3 * 3 := by decide
                      rcases (Nat.Prime.dvd_mul hr_prime).mp hd with hr16 | hr9
                      · rw [h_16_fac] at hr16
                        rcases (Nat.Prime.dvd_mul hr_prime).mp hr16 with hr2 | hr8
                        · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                          left; exact this
                        · rcases (Nat.Prime.dvd_mul hr_prime).mp hr8 with hr2 | hr4
                          · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                            left; exact this
                          · rcases (Nat.Prime.dvd_mul hr_prime).mp hr4 with hr2 | hr2'
                            · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                              left; exact this
                            · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2' |>.resolve_left hr_prime.ne_one)
                              left; exact this
                      · rw [h_9_fac] at hr9
                        rcases (Nat.Prime.dvd_mul hr_prime).mp hr9 with hr3 | hr3'
                        · have : r = 3 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr3 |>.resolve_left hr_prime.ne_one)
                          right; exact this
                        · have : r = 3 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr3' |>.resolve_left hr_prime.ne_one)
                          right; exact this
                    rcases h_prime_div with hr2 | hr3
                    · exact False.elim (hr_ne_2 hr2)
                    · have h_p_dvd : p ∣ 48 := ⟨c * m', by omega⟩
                      have h_48 : 48 = 16 * 3 := by decide
                      rw [h_48] at h_p_dvd
                      have hp_cases : p = 2 ∨ p = 3 := by
                        rcases (Nat.Prime.dvd_mul hp_p).mp h_p_dvd with hp16 | hp3
                        · have h_16 : 16 = 2 * (2 * (2 * 2)) := by decide
                          rw [h_16] at hp16
                          rcases (Nat.Prime.dvd_mul hp_p).mp hp16 with hp2 | hp8
                          · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2 |>.resolve_left hp_p.ne_one)
                          · rcases (Nat.Prime.dvd_mul hp_p).mp hp8 with hp2 | hp4
                            · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2 |>.resolve_left hp_p.ne_one)
                            · rcases (Nat.Prime.dvd_mul hp_p).mp hp4 with hp2 | hp2'
                              · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2 |>.resolve_left hp_p.ne_one)
                              · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2' |>.resolve_left hp_p.ne_one)
                        · right; exact (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) p hp3 |>.resolve_left hp_p.ne_one)
                      rcases hp_cases with hp2 | hp3
                      · exfalso
                        have h_odd2 : ¬ Odd 2 := by decide
                        have h_odd2_re : Odd p := hp_odd
                        rw [hp2] at h_odd2_re
                        exact h_odd2 h_odd2_re
                      · exact False.elim (hpr_ne (hp3.trans hr3.symm))
                · have h_eq_main : 2 * a * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := by
                    have h_eq1 : 2 * a * q * r = 2 * q * (r * a) := by ring
                    have h_eq2 : 2 * q * (r * a) = (2 * L * q) * (2 * q - 1) + 2 * q := by
                      rw [← h_a_eq]
                      ring
                    have h_eq3 : 2 * L * q = (2 * p - 1) * (2 * r - 1) * Y - 1 := by
                      have h_temp := hK_eq
                      rw [h_S_m_Y] at h_temp
                      have h_assoc : (2 * p - 1) * ((2 * r - 1) * Y) = (2 * p - 1) * (2 * r - 1) * Y := by ring
                      rw [h_assoc] at h_temp
                      omega
                    have h_sub : ((2 * p - 1) * (2 * r - 1) * Y - 1) * (2 * q - 1) = (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) - (2 * q - 1) := by
                      rw [Nat.sub_mul, one_mul]
                    rw [h_eq1, h_eq2, h_eq3, h_sub]
                    have h_le : 2 * q - 1 ≤ (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) := by
                      have hp_ge : 2 * p - 1 ≥ 1 := by omega
                      have hr_ge : 2 * r - 1 ≥ 1 := by omega
                      have hY_ge : Y ≥ 1 := hY_pos
                      have h_prod : (2 * p - 1) * (2 * r - 1) * Y ≥ 1 := by omega
                      have : 1 * (2 * q - 1) ≤ (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) := Nat.mul_le_mul_right (2 * q - 1) h_prod
                      omega
                    have h_comm : (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y := by ring
                    rw [h_comm]
                    omega
                  have h_eq_div : 2 * c * m' * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := by
                    calc
                      2 * c * m' * p * q * r = 2 * (c * p * m') * q * r := by ring
                      _ = 2 * a * q * r := by rw [ha_eq_cpm']
                      _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := h_eq_main
                  have h_lt_main : (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 < 8 * p * q * r * Y := by
                    have h_id : (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 < 8 * p * q * r := by
                      have h_prod_ge : (2 * q - 1) * (2 * r - 1) ≥ 2 := by
                        have h1 : 2 * q - 1 ≥ 1 := by omega
                        have h2 : 2 * r - 1 ≥ 2 := by omega
                        have : (2 * q - 1) * (2 * r - 1) ≥ 1 * 2 := Nat.mul_le_mul h1 h2
                        omega
                      have h_add_alg : (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + (2 * q - 1) * (2 * r - 1) = (2 * p) * (2 * q - 1) * (2 * r - 1) := by
                        have h_dist : (2 * p - 1) * ((2 * q - 1) * (2 * r - 1)) + 1 * ((2 * q - 1) * (2 * r - 1)) = ((2 * p - 1) + 1) * ((2 * q - 1) * (2 * r - 1)) := by rw [← Nat.add_mul]
                        have h_add_one : (2 * p - 1) + 1 = 2 * p := by omega
                        rw [one_mul] at h_dist
                        rw [h_add_one] at h_dist
                        rw [mul_assoc, mul_assoc]
                        exact h_dist
                      calc
                        (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1
                        _ < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + (2 * q - 1) * (2 * r - 1) := by omega
                        _ = (2 * p) * (2 * q - 1) * (2 * r - 1) := h_add_alg
                        _ < (2 * p) * (2 * q) * (2 * r - 1) := by
                          have h_lt1 : 2 * q - 1 < 2 * q := by omega
                          have h_lt2 : 2 * p * (2 * q - 1) < 2 * p * (2 * q) := Nat.mul_lt_mul_of_pos_left h_lt1 (by omega)
                          exact Nat.mul_lt_mul_of_pos_right h_lt2 (by omega)
                        _ < (2 * p) * (2 * q) * (2 * r) := by
                          have h_lt_inner : 2 * r - 1 < 2 * r := by omega
                          exact Nat.mul_lt_mul_of_pos_left h_lt_inner (Nat.mul_pos (by omega) (by omega))
                        _ = 8 * p * q * r := by ring
                    calc
                      (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1
                      _ ≤ (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + Y := by omega
                      _ = ((2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1) * Y := by ring
                      _ < (8 * p * q * r) * Y := Nat.mul_lt_mul_of_pos_right h_id hY_pos
                      _ = 8 * p * q * r * Y := by ring
                  have h_div_lt : 2 * (c * m') < 8 * Y := by
                    have h_mul1 : 2 * (c * m') * (p * q * r) = 2 * c * m' * p * q * r := by ring
                    have h_mul2 : 8 * Y * (p * q * r) = 8 * p * q * r * Y := by ring
                    have h_lt_temp : 2 * c * m' * p * q * r < 8 * p * q * r * Y := by
                      calc
                        2 * c * m' * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := h_eq_div
                        _ < 8 * p * q * r * Y := h_lt_main
                    rw [← h_mul1, ← h_mul2] at h_lt_temp
                    exact Nat.lt_of_mul_lt_mul_right h_lt_temp
                  have h_cm'_lt : c * m' < 4 * Y := by
                    omega
                  by_cases hm'1 : m' = 1
                  · have h_Y_eq : Y = 1 := by
                      dsimp [Y]
                      rw [hm'1]
                      simp
                    have h_c_lt4 : c < 4 := by
                      have h_temp := h_cm'_lt
                      rw [hm'1, h_Y_eq] at h_temp
                      omega
                    have hc_cases : c = 2 ∨ c = 3 := by omega
                    rcases hc_cases with rfl | rfl
                    · have h_eq_div_re : 4 * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                        have h_temp := h_eq_div
                        rw [hm'1, h_Y_eq] at h_temp
                        calc
                          4 * p * q * r = 2 * 2 * 1 * p * q * r := by ring
                          _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * 1 + 1 := h_temp
                          _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by ring
                      have hr_ge11_tmp : r ≥ 11 := by
                        have : r ≠ 9 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                        have : r ≠ 10 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                        omega
                      have h_ineq : 4 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                        exact test_ineq1 p q r hp3 h_q7 hr_ge11_tmp
                      exfalso
                      rw [h_eq_div_re] at h_ineq
                      exact lt_irrefl _ h_ineq
                    · have h_eq_div_re : 6 * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                        have h_temp := h_eq_div
                        rw [hm'1, h_Y_eq] at h_temp
                        calc
                          6 * p * q * r = 2 * 3 * 1 * p * q * r := by ring
                          _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * 1 + 1 := h_temp
                          _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by ring
                      by_cases hq11 : q ≥ 11
                      · have h_ineq : 6 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                          exact test_ineq2 p q r hp3 hq11 (by omega)
                        exfalso
                        rw [h_eq_div_re] at h_ineq
                        exact lt_irrefl _ h_ineq
                      · have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hq_mem
                        have hq7_eq : q = 7 := by
                          have : q < 11 := by omega
                          interval_cases q
                          · rfl
                          · exfalso; revert hq_prime; decide
                          · exfalso; revert hq_prime; decide
                          · exfalso; revert hq_prime; decide
                        have hp_cases : p = 3 ∨ p = 5 := by
                          have : p < 7 := by omega
                          interval_cases p
                          · left; rfl
                          · exfalso; revert hp_p; decide
                          · right; rfl
                          · exfalso; revert hp_p; decide
                        rcases hp_cases with rfl | rfl
                        · have hr16 : r = 16 := by omega
                          rw [hr16] at hr_prime
                          have : ¬ Nat.Prime 16 := by decide
                          exact (this hr_prime).elim
                        · have hr_ge11 : r ≥ 11 := by
                            have : r ≠ 9 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                            have : r ≠ 10 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                            omega
                          rw [hq7_eq] at h_eq_div_re
                          have h_eq_re : (6 * 5 * 7 * r : ℤ) = (((2 * 5 - 1) * (2 * 7 - 1) * (2 * r - 1) + 1 : ℕ) : ℤ) := by
                            exact_mod_cast h_eq_div_re
                          have hr_ge11_z : (r : ℤ) ≥ 11 := by exact_mod_cast hr_ge11
                          have h_ge_r : 2 * r ≥ 1 := by omega
                          zify [h_ge_r] at h_eq_re
                          exfalso
                          omega
                  · have hm'_ge2 : m' ≥ 2 := by omega
                    have h_cp : c * p ≥ 6 := by
                      calc
                        c * p ≥ 2 * 3 := Nat.mul_le_mul hc_pos hp3
                        _ = 6 := by decide
                    have h_cpm' : c * p * m' ≥ 12 := by
                      calc
                        c * p * m' ≥ 6 * 2 := Nat.mul_le_mul h_cp hm'_ge2
                        _ = 12 := by decide
                    rw [← ha_eq_cpm'] at h_cpm'
                    omega
theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
constructor
· exact a_eq_1_impl_prime_or_1 n
· rintro (rfl | hp)
  · rfl
  · exact prime_a_eq_1 hp

#print axioms oeis_340079_conjecture_0
            have hn_odd : Odd n := by
              by_contra h_even
              have h2_dvd : 2 ∣ n := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h_even)
              have h2_mem : 2 ∈ Nat.primeFactorsList n := by
                rw [Nat.mem_primeFactorsList_iff_dvd hn0]
                exact ⟨Nat.prime_two, h2_dvd⟩
              have h_mem : 2 ∈ p :: q :: tail := by rwa [← h_list]
              rcases h_mem with rfl | h_mem
              · rcases hp_prime.eq_two_or_odd with rfl | hp_odd''
                · contradiction
                · omega
              · rcases h_mem with rfl | h_mem
                · omega
                · have hq2 : q ≤ 2 := chain_le_of_mem h_chain 2 h_mem
                  omega
            have hp3 : p ≥ 3 := by omega
            have hq5 : q ≥ 5 := by omega
            have h_pq_div := h_divs
              by_cases hk1 : m = 1
              · have h_pq_div_rw := h_pq_div
                rw [hk1] at h_pq_div_rw
                have hpq_dvd_2p_2 : q ∣ 2 * p - 2 := by
                  have h_div_q := h_pq_div_rw.2
                  have h_sum_1 : (Finset.Ico 1 (1 + 1)).sum (fun x => Nat.gcd x 1) = 1 := by simp
                  rw [h_sum_1] at h_div_q
                  have h_arith : (2 * p - 1) * 1 - 1 = 2 * p - 2 := by omega
                  rw [h_arith] at h_div_q
                  exact h_div_q
                have hpq_dvd_2q_2 : p ∣ 2 * q - 2 := by
                  have h_div_p := h_pq_div_rw.1
                  have h_sum_1 : (Finset.Ico 1 (1 + 1)).sum (fun x => Nat.gcd x 1) = 1 := by simp
                  rw [h_sum_1] at h_div_p
                  have h_arith : (2 * q - 1) * 1 - 1 = 2 * q - 2 := by omega
                  rw [h_arith] at h_div_p
                  exact h_div_p
                have h_contr : False := no_solution_X1 hp_p hq_p hpq hpq_dvd_2q_2 hpq_dvd_2p_2
                exact False.elim h_contr
              · have hm0 : m ≠ 0 := by
                  intro hm_zero
                  rw [hm_zero] at h
                  simp [a] at h
                have hm2 : m ≥ 2 := by omega
                have h_S_m_ge : (Finset.Ico 1 (m + 1)).sum (fun x => Nat.gcd x m) ≥ 1 := by
                  have h_mem : 1 ∈ Finset.Ico 1 (m + 1) := by
                    rw [Finset.mem_Ico]
                    omega
                  have h_le : Nat.gcd 1 m ≤ (Finset.Ico 1 (m + 1)).sum (fun x => Nat.gcd x m) := Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.gcd x m)) h_mem
                  rw [Nat.gcd_one_left] at h_le
                  exact h_le
                -- S_m * (4pq - 2p - 2q + 1) + 1 = 2 * c * p * q * m with c >= 2
                have hS_odd := odd_S_of_odd hn_odd
                have h_add_even : Even (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))) := by
                  rcases hS_odd with ⟨k, hk⟩
                  use k + 1
                  omega
                have h_gcd : Nat.gcd (p * q * m) (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))) = p * q * m := by
                  have h_a1 : a (p * q * m) = 1 := h
                  change (p * q * m) / Nat.gcd (p * q * m) (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))) = 1 at h_a1
                  have h_div_canc := Nat.mul_div_cancel' (Nat.gcd_dvd_left (p * q * m) (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))))
                  rw [h_a1] at h_div_canc
                  rw [mul_one] at h_div_canc
                  exact h_div_canc
                have h_dvd : (p * q * m) ∣ (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))) := by
                  nth_rw 1 [← h_gcd]
                  exact Nat.gcd_dvd_right (p * q * m) (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m)))
                have h_cop : Nat.Coprime 2 (p * q * m) := coprime_two_of_odd hn_odd
                have h_2_dvd : 2 ∣ (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))) := by
                  rcases h_add_even with ⟨k, hk⟩
                  use k
                  omega
                have h_2n_dvd : (2 * (p * q * m)) ∣ (1 + (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m))) := by
                  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop h_2_dvd h_dvd
                have h_ge : (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m)) ≥ 2 * (p * q * m) := by
                  exact sum_gcd_ge_two_mul_of_composite hn1 hp hn0
                rcases h_2n_dvd with ⟨c, hc⟩
                have hc_pos : c ≥ 2 := by
                  by_contra hc_lt
                  push_neg at hc_lt
                  interval_cases c
                  · omega
                  · omega
                -- S_m * (2p-1)(2q-1) + 1 = 2 * c * p * q * m
                have h_cop_q : Nat.Coprime q m := by
                  have h_q2 : ¬ q * q ∣ p * q * m := by
                    intro hc
                    rw [squarefree_iff_prime_squarefree] at h_sf
                    exact h_sf q hq_p hc
                  have h_dvd : q ∣ m → q * q ∣ p * q * m := by
                    rintro ⟨k, hk⟩
                    rw [hk] at *
                    use p * k
                    ring
                  exact (Nat.Prime.coprime_iff_not_dvd hq_p).mpr (fun h => h_q2 (h_dvd h))
                have h_S_qm : (Finset.Ico 1 (q * m + 1)).sum (fun k => Nat.gcd k (q * m)) = (2 * q - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := by
                  exact sum_divisors_mul_prime hq_p h_cop_q hm0
                have h_cop_p : Nat.Coprime p (q * m) := by
                  have h_p2 : ¬ p * p ∣ p * q * m := by
                    intro hc
                    rw [squarefree_iff_prime_squarefree] at h_sf
                    exact h_sf p hp_p hc
                  have h_dvd_re : p ∣ q * m → p * p ∣ p * q * m := by
                    rintro ⟨k, hk⟩
                    use k
                    have h_target : p * q * m = p * (q * m) := by ring
                    rw [h_target, hk]
                    ring
                  exact (Nat.Prime.coprime_iff_not_dvd hp_p).mpr (fun h => h_p2 (h_dvd_re h))
                have h_S_pqm : (Finset.Ico 1 (p * (q * m) + 1)).sum (fun k => Nat.gcd k (p * (q * m))) = (2 * p - 1) * (Finset.Ico 1 (q * m + 1)).sum (fun k => Nat.gcd k (q * m)) := by
                  have hqm_ne_0 : q * m ≠ 0 := Nat.mul_ne_zero hq_p.ne_zero hm0
                  exact sum_divisors_mul_prime hp_p h_cop_p hqm_ne_0
                have h_S_pqm_re : (Finset.Ico 1 (p * q * m + 1)).sum (fun k => Nat.gcd k (p * q * m)) = (2 * p - 1) * (2 * q - 1) * (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m) := by
                  have h_re : p * q * m = p * (q * m) := by ring
                  rw [h_re, h_S_pqm, h_S_qm]
                  ring
                rw [h_S_pqm_re] at hc
                -- S_m * (2p-1)(2q-1) + 1 = 2 * c * p * q * m
                -- Let S_m = X
                let X := (Finset.Ico 1 (m + 1)).sum (fun k => Nat.gcd k m)
                have hc_new : (4 * p * q - 2 * p - 2 * q + 1) * X + 1 = 2 * c * p * q * m := by
                  obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le hp3
                  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le hq5
                  have hc_comm : 1 + (2 * (3 + p') - 1) * (2 * (5 + q') - 1) * X = 2 * ((3 + p') * (5 + q') * m) * c := hc
                  have h_sub1 : 2 * (3 + p') - 1 = 2 * p' + 5 := by omega
                  have h_sub2 : 2 * (5 + q') - 1 = 2 * q' + 9 := by omega
                  have h_sub3 : 4 * (3 + p') * (5 + q') - 2 * (3 + p') - 2 * (5 + q') + 1 = 4 * p' * q' + 18 * p' + 10 * q' + 45 := by
                    have h_mul : 4 * (3 + p') * (5 + q') = 4 * p' * q' + 20 * p' + 12 * q' + 60 := by ring
                    rw [h_mul]
                    omega
                  calc
                    (4 * (3 + p') * (5 + q') - 2 * (3 + p') - 2 * (5 + q') + 1) * X + 1 = 1 + (2 * (3 + p') - 1) * (2 * (5 + q') - 1) * X := by
                      rw [h_sub1, h_sub2, h_sub3]
                      ring
                    _ = 2 * ((3 + p') * (5 + q') * m) * c := hc_comm
                    _ = 2 * c * (3 + p') * (5 + q') * m := by ring
                have hc := hc_new
                -- X * (4pq - 2p - 2q + 1) + 1 = 2 * c * p * q * m
                have h_lt_alg : X * (2 * p * q) < X * (4 * p * q - 2 * p - 2 * q + 1) := by
                  obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le hp3
                  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le hq5
                  have h_ineq : 2 * (3 + p') * (5 + q') < 4 * (3 + p') * (5 + q') - 2 * (3 + p') - 2 * (5 + q') + 1 := by
                    have h_expand1 : 2 * (3 + p') * (5 + q') = 2 * (p' * q') + 10 * p' + 6 * q' + 30 := by ring
                    have h_expand2 : 4 * (3 + p') * (5 + q') - 2 * (3 + p') - 2 * (5 + q') + 1 = 4 * (p' * q') + 18 * p' + 10 * q' + 45 := by
                      have h_mul : 4 * (3 + p') * (5 + q') = 4 * (p' * q') + 20 * p' + 12 * q' + 60 := by ring
                      have h_sub1_eq : 2 * (3 + p') = 2 * p' + 6 := by ring
                      have h_sub2_eq : 2 * (5 + q') = 2 * q' + 10 := by ring
                      rw [h_mul, h_sub1_eq, h_sub2_eq]
                      omega
                    rw [h_expand1, h_expand2]
                    omega
                  exact Nat.mul_lt_mul_of_pos_left h_ineq h_S_m_ge
                have h_lt : X * (2 * p * q) < 2 * c * p * q * m := by
                  calc
                    X * (2 * p * q) < X * (4 * p * q - 2 * p - 2 * q + 1) := h_lt_alg
                    _ < X * (4 * p * q - 2 * p - 2 * q + 1) + 1 := by omega
                    _ = (4 * p * q - 2 * p - 2 * q + 1) * X + 1 := by ring
                    _ = 2 * c * p * q * m := hc
                have h_lt_X : 2 * c * p * q * m < 4 * p * q * X := by
                  have h_lt_X_step : (4 * p * q - 2 * p - 2 * q + 1) * X + 1 < 4 * p * q * X := by
                    have h_sub_eq : (4 * p * q - 2 * p - 2 * q + 1) + (2 * p + 2 * q - 1) = 4 * p * q := by
                      have hp2 : p ≥ 2 := Nat.Prime.two_le hp_p
                      have hq2 : q ≥ 2 := Nat.Prime.two_le hq_p
                      have h_le : 2 * p + 2 * q ≤ 4 * p * q := by
                        have hp_le : 2 * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
                        have hq_le : 2 * p ≤ p * q := by
                          have : 2 * p ≤ q * p := Nat.mul_le_mul_right p (by omega)
                          rwa [mul_comm q p] at this
                        calc
                          2 * p + 2 * q ≤ p * q + p * q := by omega
                          _ = 2 * (p * q) := by ring
                          _ ≤ 4 * (p * q) := Nat.mul_le_mul_right (p * q) (by omega)
                          _ = 4 * p * q := by ring
                      omega
                    have h_alg3 : 4 * p * q * X = (4 * p * q - 2 * p - 2 * q + 1) * X + X * (2 * p + 2 * q - 1) := by
                      calc
                        4 * p * q * X = ((4 * p * q - 2 * p - 2 * q + 1) + (2 * p + 2 * q - 1)) * X := by rw [h_sub_eq]
                        _ = (4 * p * q - 2 * p - 2 * q + 1) * X + (2 * p + 2 * q - 1) * X := by rw [add_mul]
                        _ = (4 * p * q - 2 * p - 2 * q + 1) * X + X * (2 * p + 2 * q - 1) := by rw [mul_comm X]
                    have h_ge15 : 2 * p + 2 * q - 1 ≥ 15 := by omega
                    have h_prod : 15 ≤ (2 * p + 2 * q - 1) * X := Nat.mul_le_mul h_ge15 h_S_m_ge
                    have h_prod2 : X * (2 * p + 2 * q - 1) ≥ 15 := by rwa [mul_comm] at h_prod
                    omega
                  rw [hc] at h_lt_X_step
                  exact h_lt_X_step
                have h_lt_X2 : c * m < 2 * X := by
                  have hpq_pos2 : 2 * p * q > 0 := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
                  have h_mul_lt : (c * m) * (2 * p * q) < (2 * X) * (2 * p * q) := by
                    calc
                      (c * m) * (2 * p * q) = 2 * c * p * q * m := by ring
                      _ < 4 * p * q * X := h_lt_X
                      _ = (2 * X) * (2 * p * q) := by ring
                  exact Nat.lt_of_mul_lt_mul_right h_mul_lt
                have h_div_q : q ∣ (2 * p - 1) * X - 1 := h_pq_div.2
                rcases h_div_q with ⟨K, hK⟩
                have h_X_pos : (2 * p - 1) * X ≥ 5 := by
                  have h1 : 2 * p - 1 ≥ 5 := by omega
                  have h2 : X ≥ 1 := h_S_m_ge
                  calc
                    (2 * p - 1) * X ≥ 5 * 1 := Nat.mul_le_mul h1 h2
                    _ = 5 := by rfl
                have hK_eq : (2 * p - 1) * X = K * q + 1 := by
                  have h_comm : q * K = K * q := mul_comm q K
                  rw [h_comm] at hK
                  omega
                have h_alg2 : (K * q + 1) * (2 * q - 1) + 1 = (K * (2 * q - 1) + 2) * q := by
                  obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le hp3
                  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le hq5
                  have h_sub : 2 * (5 + q') - 1 = 2 * q' + 9 := by omega
                  rw [h_sub]
                  ring
                have h_comm_X : X * (2 * p - 1) = (2 * p - 1) * X := mul_comm X (2 * p - 1)
                have h_hc_re2 : X * (2 * p - 1) * (2 * q - 1) + 1 = 2 * (p * q * m) * c := by
                  calc
                    X * (2 * p - 1) * (2 * q - 1) + 1 = (4 * p * q - 2 * p - 2 * q + 1) * X + 1 := by
                      obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le hp3
                      obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le hq5
                      have h_sub1 : 2 * (3 + p') - 1 = 2 * p' + 5 := by omega
                      have h_sub2 : 2 * (5 + q') - 1 = 2 * q' + 9 := by omega
                      have h_sub3 : 4 * (3 + p') * (5 + q') - 2 * (3 + p') - 2 * (5 + q') + 1 = 4 * p' * q' + 18 * p' + 10 * q' + 45 := by
                        have h_mul : 4 * (3 + p') * (5 + q') = 4 * p' * q' + 20 * p' + 12 * q' + 60 := by ring
                        rw [h_mul]
                        omega
                      rw [h_sub1, h_sub2, h_sub3]
                      ring
                    _ = 2 * c * p * q * m := hc
                    _ = 2 * (p * q * m) * c := by ring
                rw [h_comm_X, hK_eq, h_alg2] at h_hc_re2
                have h_rhs : 2 * (p * q * m) * c = (2 * c * p * m) * q := by ring
                rw [h_rhs] at h_hc_re2
                have hq_pos : q > 0 := by omega
                have h_div_q2 := Nat.eq_of_mul_eq_mul_right hq_pos h_hc_re2
                have h_even_lhs : 2 ∣ K * (2 * q - 1) := by
                  have h_c_ge : c * p * m ≥ 1 := by
                    have hc_pos : c ≥ 1 := by omega
                    have hp_pos : p ≥ 1 := by omega
                    have hm_pos : m ≥ 1 := by omega
                    have : c * p * m > 0 := Nat.mul_pos (Nat.mul_pos hc_pos hp_pos) hm_pos
                    omega
                  use (c * p * m - 1)
                  have h_div_q2_symm : K * (2 * q - 1) + 2 = 2 * (c * p * m) := by
                    calc
                      K * (2 * q - 1) + 2 = 2 * c * p * m := h_div_q2
                      _ = 2 * (c * p * m) := by ring
                  omega
                have h_odd : ¬ 2 ∣ (2 * q - 1) := by
                  intro hc_odd
                  rcases hc_odd with ⟨z, hz⟩
                  omega
                have h_cop : Nat.Coprime 2 (2 * q - 1) := by
                  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h_odd
                have h_even_K : 2 ∣ K := h_cop.dvd_of_dvd_mul_right h_even_lhs
                rcases h_even_K with ⟨L, rfl⟩
                have h_div_q2_re : 2 * (L * (2 * q - 1) + 1) = 2 * (c * p * m) := by
                  calc
                    2 * (L * (2 * q - 1) + 1) = 2 * L * (2 * q - 1) + 2 := by ring
                    _ = 2 * c * p * m := h_div_q2
                    _ = 2 * (c * p * m) := by ring
                have h_div2 : L * (2 * q - 1) + 1 = c * p * m := Nat.eq_of_mul_eq_mul_left (by omega) h_div_q2_re
                have hL_pos : L ≥ 1 := by
                  have h_L_eq : (2 * p - 1) * X = 2 * L * q + 1 := hK_eq
                  by_contra h_L0
                  have h_L0' : L = 0 := by omega
                  subst h_L0'
                  simp only [mul_zero, zero_mul, add_zero] at h_L_eq
                  have : (2 * p - 1) * X ≥ 5 := h_X_pos
                  omega
                have h_L_ne_1 : L ≠ 1 := by
                  intro hL1
                  subst hL1
                  have h_L1_eq : 1 * (2 * q - 1) + 1 = 2 * q := by
                    have : q ≥ 2 := hq_p.two_le
                    omega
                  rw [h_L1_eq] at h_div2
                  have h_div3 : c * p * m = 2 * q := h_div2.symm
                  have hp_dvd : p ∣ 2 * q := by
                    use c * m
                    rw [← h_div3]
                    ring
                  rcases (Nat.Prime.dvd_mul hp_p).mp hp_dvd with hp_dvd_2 | hp_dvd_q
                  · have : p ≤ 2 := Nat.le_of_dvd (by omega) hp_dvd_2
                    omega
                  · have hp_eq_q : p = q := by
                      rcases Nat.Prime.eq_one_or_self_of_dvd hq_p p hp_dvd_q with h1 | h2
                      · exfalso; exact hp_p.ne_one h1
                      · exact h2
                    omega
                have hL2 : L ≥ 2 := by omega
                let r := minFac m
                have hr_prime : Nat.Prime r := Nat.minFac_prime (by omega)
                have hr_dvd : r ∣ m := Nat.minFac_dvd m
                have hm_odd : Odd m := by
                  have h_odd_pqm := hn_odd
                  rw [Nat.odd_mul, Nat.odd_mul] at h_odd_pqm
                  exact h_odd_pqm.2
                have hr_ne_2 : r ≠ 2 := by
                  intro hr2
                  rw [hr2] at hr_dvd
                  have h_mod := Nat.mod_eq_zero_of_dvd hr_dvd
                  have h_odd_mod := Nat.odd_iff.mp hm_odd
                  omega
                have h_cop_qm : Nat.Coprime q m := h_cop_q
                have h_cop_pm : Nat.Coprime p m := by
                  have h_p2 : ¬ p * p ∣ p * m := by
                    intro hc
                    have h_p2_pqm : p * p ∣ p * q * m := by
                      rcases hc with ⟨k, hk⟩
                      use q * k
                      calc
                        p * q * m = q * (p * m) := by ring
                        _ = q * (p * p * k) := by rw [hk]
                        _ = p * p * (q * k) := by ring
                    rw [squarefree_iff_prime_squarefree] at h_sf
                    exact h_sf p hp_p h_p2_pqm
                  have h_dvd : p ∣ m → p * p ∣ p * m := by
                    rintro ⟨k, hk⟩
                    use k
                    calc
                      p * m = p * (p * k) := by rw [hk]
                      _ = p * p * k := by ring
                  exact (Nat.Prime.coprime_iff_not_dvd hp_p).mpr (fun h => h_p2 (h_dvd h))
                have hpr_ne : p ≠ r := by
                  intro h_eq
                  subst h_eq
                  have h_gcd : Nat.gcd r m = r := Nat.gcd_eq_left hr_dvd
                  rw [h_cop_pm] at h_gcd
                  have : r = 1 := h_gcd.symm
                  exact hr_prime.ne_one this
                have hr_ne_q : r ≠ q := by
                  intro hrq
                  have h_dvd : q ∣ m := by rwa [← hrq]
                  have h_gcd_qm : Nat.gcd q m = q := Nat.gcd_eq_left h_dvd
                  rw [h_cop_qm] at h_gcd_qm
                  exact hq_p.ne_one h_gcd_qm.symm
                have hr_ne_p : r ≠ p := by
                  intro hrp
                  have h_dvd : p ∣ m := by rwa [← hrp]
                  have h_gcd_pm : Nat.gcd p m = p := Nat.gcd_eq_left h_dvd
                  rw [h_cop_pm] at h_gcd_pm
                  exact hp_p.ne_one h_gcd_pm.symm
                have hr_dvd_n : r ∣ p * q * m := by
                  rcases hr_dvd with ⟨k, hk⟩
                  use p * q * k
                  rw [hk]
                  ring
                have hn0_re : p * q * m ≠ 0 := hn0
                have hr_in : r ∈ Nat.primeFactorsList (p * q * m) := by
                  rw [Nat.mem_primeFactorsList hn0_re]
                  exact ⟨hr_prime, hr_dvd_n⟩
                rw [h_list] at hr_in
                simp only [List.mem_cons] at hr_in
                have hr_mem : r ∈ tail := by
                  rcases hr_in with hp | hq | h_tail
                  · exact False.elim (hr_ne_p hp)
                  · exact False.elim (hr_ne_q hq)
                  · exact h_tail
                have hqr_le : q ≤ r := chain_le_of_mem h_chain r hr_mem
                have hqr : q < r := Nat.lt_of_le_of_ne hqr_le hr_ne_q.symm
                have hqr_ge2 : r ≥ q + 2 := by
                  by_contra h_ge
                  have : r = q + 1 := by omega
                  have h_even : 2 ∣ r := by
                    use (q / 2 + 1)
                    have hq_odd_m : Odd q := by
                      have hn_odd_eq : Odd (p * q * m) := hn_odd
                      rw [Nat.odd_mul, Nat.odd_mul] at hn_odd_eq
                      exact hn_odd_eq.1.2
                    have : q % 2 = 1 := Nat.odd_iff.mp hq_odd_m
                    omega
                  have h_eq_2 : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd hr_prime 2 h_even |>.resolve_left (by norm_num)).symm
                  omega
                obtain ⟨m', hm'_eq⟩ := hr_dvd
                have h_cop_rm' : Nat.Coprime r m' := by
                  have h_sf_rm' : Squarefree (r * m') := by
                    have h_sf_m : Squarefree m := by
                      have : p * q * m = (p * q) * m := by ring
                      rw [this] at h_sf
                      exact Squarefree.squarefree_of_dvd (dvd_mul_left m (p * q)) h_sf
                    rwa [← hm'_eq]
                  have h_r2_not_dvd : ¬ r * r ∣ r * m' := by
                    intro hc_r2
                    have h_r2_n : r * r ∣ p * q * m := by
                      rcases hc_r2 with ⟨k, hk⟩
                      use p * q * k
                      calc
                        p * q * m = p * q * (r * m') := by rw [hm'_eq]
                        _ = r * r * (p * q * k) := by rw [hk]; ring
                    rw [squarefree_iff_prime_squarefree] at h_sf
                    exact h_sf r hr_prime h_r2_n
                  exact (Nat.Prime.coprime_iff_not_dvd hr_prime).mpr (by
                    intro hr_dvd_m'
                    have : r * r ∣ r * m' := by
                      rcases hr_dvd_m' with ⟨k, hk⟩
                      use k
                      rw [hk]
                      ring
                    exact h_r2_not_dvd this)
                have hm'_pos : m' ≠ 0 := by
                  rintro rfl
                  simp at hm'_eq
                  exact hm0 hm'_eq
                have h_S_m : X = (2 * r - 1) * (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m') := by
                  dsimp only [X]
                  rw [hm'_eq]
                  exact sum_divisors_mul_prime hr_prime h_cop_rm' hm'_pos
                let Y := (Finset.Ico 1 (m' + 1)).sum (fun k => Nat.gcd k m')
                have h_S_m_Y : X = (2 * r - 1) * Y := h_S_m
                have hY_pos : Y ≥ 1 := by
                  have h_mem : 1 ∈ Finset.Ico 1 (m' + 1) := by
                    rw [Finset.mem_Ico]
                    omega
                  have h_le : Nat.gcd 1 m' ≤ Y := Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.gcd x m')) h_mem
                  rw [Nat.gcd_one_left] at h_le
                  exact h_le
                have h_ineq1 : 5 * (2 * r - 1) ≤ 2 * (L * q) + 1 := by
                  calc
                    5 * (2 * r - 1) ≤ (2 * p - 1) * (2 * r - 1) := Nat.mul_le_mul_right (2 * r - 1) (by omega)
                    _ ≤ (2 * p - 1) * ((2 * r - 1) * Y) := by
                      have : 2 * r - 1 ≤ (2 * r - 1) * Y := by
                        calc
                          2 * r - 1 = (2 * r - 1) * 1 := by ring
                          _ ≤ (2 * r - 1) * Y := Nat.mul_le_mul_left (2 * r - 1) hY_pos
                      exact Nat.mul_le_mul_left (2 * p - 1) this
                    _ = (2 * p - 1) * X := by rw [← h_S_m_Y]
                    _ = 2 * L * q + 1 := hK_eq
                    _ = 2 * (L * q) + 1 := by ring
                have h_ineq2 : 5 * r ≤ L * q + 3 := by
                  have h_alg : 5 * (2 * r - 1) = 10 * r - 5 := by omega
                  have h_ineq_re := h_ineq1
                  rw [h_alg] at h_ineq_re
                  have h_10r : 10 * r ≤ 2 * (L * q) + 6 := by omega
                  have h_mul_le : 2 * (5 * r) ≤ 2 * (L * q + 3) := by
                    calc
                      2 * (5 * r) = 10 * r := by ring
                      _ ≤ 2 * (L * q) + 6 := h_10r
                      _ = 2 * (L * q + 3) := by ring
                  exact Nat.le_of_mul_le_mul_left h_mul_le (by decide)
                have h_L_cases : L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L ≥ 6 := by omega
                rcases h_L_cases with rfl | rfl | rfl | rfl | hL6
                · omega
                · omega
                · omega
                · omega
                · have h_q7 : q ≥ 7 := by
                    by_contra h_q_lt
                    have h_cases : q = 5 ∨ q = 6 := by omega
                    rcases h_cases with rfl | rfl
                    · have hp_cases : p = 3 ∨ p = 4 := by omega
                      rcases hp_cases with rfl | rfl
                      · have hK_eq_re : 5 * X = 2 * L * 5 + 1 := by omega
                        have h_div5 : 5 ∣ 2 * L * 5 + 1 := ⟨X, by omega⟩
                        have h_div_one : 5 ∣ 1 := by
                          rcases h_div5 with ⟨z, hz⟩
                          use (z - 2 * L)
                          omega
                        omega
                      · exfalso
                        have : ¬ Nat.Prime 4 := by norm_num
                        exact this hp_p
                    · exfalso
                      have : ¬ Nat.Prime 6 := by norm_num
                      exact this hq_p
                  have h_div_r : r ∣ L * (2 * q - 1) + 1 := by
                    use c * p * m'
                    calc
                      L * (2 * q - 1) + 1 = c * p * (r * m') := by rwa [hm'_eq] at h_div2
                      _ = r * (c * p * m') := by ring
                  rcases h_div_r with ⟨a, h_a_eq⟩
                  have ha_pos : a ≥ 1 := by
                    by_contra ha0
                    have : a = 0 := by omega
                    subst this
                    omega
                  have ha_lt : a ≤ 2 * L - 1 := by
                    by_contra h_a_ge
                    have : a ≥ 2 * L := by omega
                    have h_le_a : 2 * L * (q + 2) ≤ a * r := by
                      calc
                        2 * L * (q + 2) ≤ a * (q + 2) := Nat.mul_le_mul_right (q + 2) (by omega)
                        _ ≤ a * r := Nat.mul_le_mul_left a hqr_ge2
                    have h_eq_a : a * r = L * (2 * q - 1) + 1 := by
                      calc
                        a * r = r * a := mul_comm a r
                        _ = L * (2 * q - 1) + 1 := h_a_eq.symm
                    have h_alg_contr : 2 * L * (q + 2) ≤ L * (2 * q - 1) + 1 := by
                      calc
                        2 * L * (q + 2) ≤ a * r := h_le_a
                        _ = L * (2 * q - 1) + 1 := h_eq_a
                    have h_L_sub : 2 * q - 1 + 1 = 2 * q := by omega
                    have h_alg_L : L * (2 * q - 1) + L = 2 * L * q := by
                      calc
                        L * (2 * q - 1) + L = L * (2 * q - 1) + L * 1 := by ring
                        _ = L * (2 * q - 1 + 1) := by rw [← Nat.mul_add]
                        _ = L * (2 * q) := by rw [h_L_sub]
                        _ = 2 * L * q := by ring
                    have h_contr : 2 * L * q + 5 * L ≤ 2 * L * q + 1 := by
                      calc
                        2 * L * q + 5 * L = 2 * L * (q + 2) + L := by ring
                        _ ≤ L * (2 * q - 1) + 1 + L := Nat.add_le_add_right h_alg_contr L
                        _ = (L * (2 * q - 1) + L) + 1 := by ring
                        _ = 2 * L * q + 1 := by rw [h_alg_L]
                    have h_contr2 : 5 * L ≤ 1 := by omega
                    omega
                  have h_sum_sub : L * (2 * q - 1) + L = 2 * L * q := by
                    have : 2 * q - 1 + 1 = 2 * q := by omega
                    calc
                      L * (2 * q - 1) + L = L * (2 * q - 1) + L * 1 := by ring
                      _ = L * (2 * q - 1 + 1) := by rw [← Nat.mul_add]
                      _ = L * (2 * q) := by rw [this]
                      _ = 2 * L * q := by ring
                  have h_ineq3 : 10 * L * q - 5 * L + 5 ≤ a * L * q + 3 * a := by
                    have : 5 * a * r ≤ a * (L * q + 3) := by
                      calc
                        5 * a * r = a * (5 * r) := by ring
                        _ ≤ a * (L * q + 3) := Nat.mul_le_mul_left a h_ineq2
                    have h_re1 : 5 * a * r = 10 * L * q - 5 * L + 5 := by
                      have h_sum5 : 5 * (L * (2 * q - 1)) + 5 * L = 10 * L * q := by
                        calc
                          5 * (L * (2 * q - 1)) + 5 * L = 5 * (L * (2 * q - 1) + L) := by ring
                          _ = 5 * (2 * L * q) := by rw [h_sum_sub]
                          _ = 10 * L * q := by ring
                      have h_sum5_sub : 5 * (L * (2 * q - 1)) = 10 * L * q - 5 * L := by
                        omega
                      calc
                        5 * a * r = 5 * (r * a) := by ring
                        _ = 5 * (L * (2 * q - 1) + 1) := by rw [h_a_eq]
                        _ = 5 * (L * (2 * q - 1)) + 5 := by ring
                        _ = 10 * L * q - 5 * L + 5 := by rw [h_sum5_sub]
                    have h_re2 : a * (L * q + 3) = a * L * q + 3 * a := by ring
                    omega

                  have ha_eq_cpm' : a = c * p * m' := by
                    have h_eq : r * a = r * (c * p * m') := by
                      calc
                        r * a = L * (2 * q - 1) + 1 := h_a_eq.symm
                        _ = c * p * m := h_div2
                        _ = c * p * (r * m') := by rw [hm'_eq]
                        _ = r * (c * p * m') := by ring
                    exact Nat.eq_of_mul_eq_mul_left hr_prime.pos h_eq

                  have ha_ge6 : a ≥ 6 := by
                    rw [ha_eq_cpm']
                    have hcp : c * p ≥ 6 := by
                      calc
                        c * p ≥ 2 * 3 := Nat.mul_le_mul hc_pos hp3
                        _ = 6 := by decide
                    have hm'1 : m' ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm'_pos
                    calc
                      c * p * m' ≥ c * p * 1 := Nat.mul_le_mul_left (c * p) hm'1
                      _ = c * p := by ring
                      _ ≥ 6 := hcp

                  have h_cases : a < 10 ∨ a ≥ 10 := by omega
                  rcases h_cases with ha_lt10 | ha_ge10
                  · have h_a_le9 : a ≤ 9 := by omega
                    have h_mul_le : a * L * q + 3 * a ≤ 9 * L * q + 27 := by
                      calc
                        a * L * q + 3 * a = a * (L * q + 3) := by ring
                        _ ≤ 9 * (L * q + 3) := Nat.mul_le_mul_right (L * q + 3) h_a_le9
                        _ = 9 * L * q + 27 := by ring
                    have h_Lq_le : 10 * L * q - 5 * L + 5 ≤ 9 * L * q + 27 := le_trans h_ineq3 h_mul_le
                    have h_Lq_le2 : L * q ≤ 5 * L + 22 := by
                      have h_Lq_le_rew : 10 * (L * q) - 5 * L + 5 ≤ 9 * (L * q) + 27 := by
                        have h_rew1 : 10 * (L * q) = 10 * L * q := by ring
                        have h_rew2 : 9 * (L * q) = 9 * L * q := by ring
                        rwa [h_rew1, h_rew2]
                      omega
                    have h_q_le : q * L ≤ 5 * L + 22 := by
                      rw [mul_comm] at h_Lq_le2
                      exact h_Lq_le2
                    have h_7L_le : 7 * L ≤ q * L := Nat.mul_le_mul_right L h_q7
                    have h_2L_le : 2 * L ≤ 22 := by omega
                    have h_L_le : L ≤ 11 := by omega
                    have h_q7_eq : q = 7 := by
                      have h_6q : 6 * q ≤ 5 * L + 22 := by
                        calc
                          6 * q ≤ L * q := Nat.mul_le_mul_right q (by omega)
                          _ ≤ 5 * L + 22 := h_Lq_le2
                      have h_q_lt11 : q < 11 := by
                        by_contra hc
                        have h_q_ge11 : q ≥ 11 := by omega
                        have h_11L : 11 * L ≤ q * L := Nat.mul_le_mul_right L h_q_ge11
                        have : 11 * L ≤ 5 * L + 22 := by omega
                        omega
                      have h_q_cases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 := by omega
                      rcases h_q_cases with rfl | rfl | rfl | rfl
                      · rfl
                      · exfalso; exact (by norm_num : ¬ Nat.Prime 8) hq_p
                      · exfalso; exact (by norm_num : ¬ Nat.Prime 9) hq_p
                      · exfalso; exact (by norm_num : ¬ Nat.Prime 10) hq_p
                    have h_prod_eq : r * (c * p * m') = 13 * L + 1 := by
                      calc
                        r * (c * p * m') = c * p * (r * m') := by ring
                        _ = c * p * m := by rw [← hm'_eq]
                        _ = L * (2 * q - 1) + 1 := h_div2.symm
                        _ = 13 * L + 1 := by rw [h_q7_eq]; ring
                    have h_L_cases2 : L = 6 ∨ L = 7 ∨ L = 8 ∨ L = 9 ∨ L = 10 ∨ L = 11 := by omega
                    rcases h_L_cases2 with rfl | rfl | rfl | rfl | rfl | rfl
                    · have h_prod : r * (c * p * m') = 79 := by
                        have := h_prod_eq
                        omega
                      have h_79_prime : Nat.Prime 79 := by norm_num
                      have : r ∣ 79 := ⟨c * p * m', h_prod.symm⟩
                      have : r = 1 ∨ r = 79 := (Nat.Prime.eq_one_or_self_of_dvd h_79_prime r this)
                      rcases this with hr1 | hr79
                      · exfalso; exact hr_prime.ne_one hr1
                      · have : c * p * m' = 1 := by
                          have : 79 * (c * p * m') = 79 * 1 := by
                            calc
                              79 * (c * p * m') = r * (c * p * m') := by rw [hr79]
                              _ = 79 := h_prod
                              _ = 79 * 1 := by ring
                          exact Nat.eq_of_mul_eq_mul_left (by decide) this
                        rw [← ha_eq_cpm'] at this
                        omega
                    · have h_prod : r * (c * p * m') = 92 := by
                        have := h_prod_eq
                        omega
                      have h_div_r : r ∣ 92 := ⟨c * p * m', h_prod.symm⟩
                      have h_prime_div : r = 2 ∨ r = 23 := by
                        have hd : r ∣ 2 * (2 * 23) := by
                          have : 92 = 2 * (2 * 23) := by decide
                          rwa [this] at h_div_r
                        rcases (Nat.Prime.dvd_mul hr_prime).mp hd with hr2 | hd2
                        · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                          left; exact this
                        · have hd3 : r ∣ 2 * 23 := hd2
                          rcases (Nat.Prime.dvd_mul hr_prime).mp hd3 with hr2 | hr23
                          · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                            left; exact this
                          · have : r = 23 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr23 |>.resolve_left hr_prime.ne_one)
                            right; exact this
                      rcases h_prime_div with hr2 | hr23
                      · exact False.elim (hr_ne_2 hr2)
                      · have : c * p * m' = 4 := by
                          have : 23 * (c * p * m') = 23 * 4 := by
                            calc
                              23 * (c * p * m') = r * (c * p * m') := by rw [hr23]
                              _ = 92 := h_prod
                              _ = 23 * 4 := by decide
                          exact Nat.eq_of_mul_eq_mul_left (by decide) this
                        rw [← ha_eq_cpm'] at this
                        omega
                    · have hK_113 : (2 * p - 1) * X = 113 := by
                        omega
                      have h_X1 : X = 1 := by
                        by_contra hX_ne1
                        have hX_ge2 : X ≥ 2 := by omega
                        have h_div_X : X ∣ 113 := by
                          use (2 * p - 1)
                          rw [mul_comm]
                          exact hK_113.symm
                        have h113_prime : Nat.Prime 113 := by decide
                        rcases Nat.Prime.eq_one_or_self_of_dvd h113_prime X h_div_X with hX1 | hX113
                        · omega
                        · rw [hX113] at hK_113
                          have : 2 * p - 1 = 1 := by omega
                          omega
                      have hp57 : p = 57 := by
                        rw [h_X1] at hK_113
                        omega
                      have hp_not_prime : ¬ Nat.Prime p := by
                        rw [hp57]
                        decide
                      exact False.elim (hp_not_prime hp_p)
                    · have h_prod : r * (c * p * m') = 118 := by
                        have := h_prod_eq
                        omega
                      have h_div_r : r ∣ 118 := ⟨c * p * m', h_prod.symm⟩
                      have h_prime_div : r = 2 ∨ r = 59 := by
                        have hd : r ∣ 2 * 59 := by
                          have : 118 = 2 * 59 := by decide
                          rwa [this] at h_div_r
                        rcases (Nat.Prime.dvd_mul hr_prime).mp hd with hr2 | hr59
                        · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr2 |>.resolve_left hr_prime.ne_one)
                          left; exact this
                        · have : r = 59 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr59 |>.resolve_left hr_prime.ne_one)
                          right; exact this
                      rcases h_prime_div with hr2 | hr59
                      · exact False.elim (hr_ne_2 hr2)
                      · have : c * p * m' = 2 := by
                          have : 59 * (c * p * m') = 59 * 2 := by
                            calc
                              59 * (c * p * m') = r * (c * p * m') := by rw [hr59]
                              _ = 118 := h_prod
                              _ = 59 * 2 := by decide
                          exact Nat.eq_of_mul_eq_mul_left (by decide) this
                        rw [← ha_eq_cpm'] at this
                        omega
                    · have h_prod : r * (c * p * m') = 131 := by
                        have := h_prod_eq
                        omega
                      have h_131_prime : Nat.Prime 131 := by norm_num
                      have : r ∣ 131 := ⟨c * p * m', h_prod.symm⟩
                      have : r = 1 ∨ r = 131 := (Nat.Prime.eq_one_or_self_of_dvd h_131_prime r this)
                      rcases this with hr1 | hr131
                      · exfalso; exact hr_prime.ne_one hr1
                      · have : c * p * m' = 1 := by
                          have : 131 * (c * p * m') = 131 * 1 := by
                            calc
                              131 * (c * p * m') = r * (c * p * m') := by rw [hr131]
                              _ = 131 := h_prod
                              _ = 131 * 1 := by ring
                          exact Nat.eq_of_mul_eq_mul_left (by decide) this
                        rw [← ha_eq_cpm'] at this
                        omega
                    · have h_prod : r * (c * p * m') = 144 := by
                        have := h_prod_eq
                        omega
                      have h_div_r : r ∣ 144 := ⟨c * p * m', h_prod.symm⟩
                      have h_prime_div : r = 2 ∨ r = 3 := by
                        have hd : r ∣ 16 * 9 := by
                          have : 144 = 16 * 9 := by decide
                          rwa [this] at h_div_r
                        have h_16_fac : 16 = 2 * (2 * (2 * 2)) := by decide
                        have h_9_fac : 9 = 3 * 3 := by decide
                        rcases (Nat.Prime.dvd_mul hr_prime).mp hd with hr16 | hr9
                        · rw [h_16_fac] at hr16
                          rcases (Nat.Prime.dvd_mul hr_prime).mp hr16 with hr2 | hr8
                          · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                            left; exact this
                          · rcases (Nat.Prime.dvd_mul hr_prime).mp hr8 with hr2 | hr4
                            · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                              left; exact this
                            · rcases (Nat.Prime.dvd_mul hr_prime).mp hr4 with hr2 | hr2'
                              · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2 |>.resolve_left hr_prime.ne_one)
                                left; exact this
                              · have : r = 2 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two r hr2' |>.resolve_left hr_prime.ne_one)
                                left; exact this
                        · rw [h_9_fac] at hr9
                          rcases (Nat.Prime.dvd_mul hr_prime).mp hr9 with hr3 | hr3'
                          · have : r = 3 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr3 |>.resolve_left hr_prime.ne_one)
                            right; exact this
                          · have : r = 3 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) r hr3' |>.resolve_left hr_prime.ne_one)
                            right; exact this
                      rcases h_prime_div with hr2 | hr3
                      · exact False.elim (hr_ne_2 hr2)
                      · have h_p_dvd : p ∣ 48 := ⟨c * m', by omega⟩
                        have h_48 : 48 = 16 * 3 := by decide
                        rw [h_48] at h_p_dvd
                        have hp_cases : p = 2 ∨ p = 3 := by
                          rcases (Nat.Prime.dvd_mul hp_p).mp h_p_dvd with hp16 | hp3
                          · have h_16 : 16 = 2 * (2 * (2 * 2)) := by decide
                            rw [h_16] at hp16
                            rcases (Nat.Prime.dvd_mul hp_p).mp hp16 with hp2 | hp8
                            · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2 |>.resolve_left hp_p.ne_one)
                            · rcases (Nat.Prime.dvd_mul hp_p).mp hp8 with hp2 | hp4
                              · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2 |>.resolve_left hp_p.ne_one)
                              · rcases (Nat.Prime.dvd_mul hp_p).mp hp4 with hp2 | hp2'
                                · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2 |>.resolve_left hp_p.ne_one)
                                · left; exact (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp2' |>.resolve_left hp_p.ne_one)
                          · right; exact (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) p hp3 |>.resolve_left hp_p.ne_one)
                        rcases hp_cases with hp2 | hp3
                        · exfalso
                          have h_odd2 : ¬ Odd 2 := by decide
                          have h_odd2_re : Odd p := hp_odd
                          rw [hp2] at h_odd2_re
                          exact h_odd2 h_odd2_re
                        · exact False.elim (hpr_ne (hp3.trans hr3.symm))
                  · have h_eq_main : 2 * a * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := by
                      have h_eq1 : 2 * a * q * r = 2 * q * (r * a) := by ring
                      have h_eq2 : 2 * q * (r * a) = (2 * L * q) * (2 * q - 1) + 2 * q := by
                        rw [← h_a_eq]
                        ring
                      have h_eq3 : 2 * L * q = (2 * p - 1) * (2 * r - 1) * Y - 1 := by
                        have h_temp := hK_eq
                        rw [h_S_m_Y] at h_temp
                        have h_assoc : (2 * p - 1) * ((2 * r - 1) * Y) = (2 * p - 1) * (2 * r - 1) * Y := by ring
                        rw [h_assoc] at h_temp
                        omega
                      have h_sub : ((2 * p - 1) * (2 * r - 1) * Y - 1) * (2 * q - 1) = (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) - (2 * q - 1) := by
                        rw [Nat.sub_mul, one_mul]
                      rw [h_eq1, h_eq2, h_eq3, h_sub]
                      have h_le : 2 * q - 1 ≤ (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) := by
                        have hp_ge : 2 * p - 1 ≥ 1 := by omega
                        have hr_ge : 2 * r - 1 ≥ 1 := by omega
                        have hY_ge : Y ≥ 1 := hY_pos
                        have h_prod : (2 * p - 1) * (2 * r - 1) * Y ≥ 1 := by omega
                        have : 1 * (2 * q - 1) ≤ (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) := Nat.mul_le_mul_right (2 * q - 1) h_prod
                        omega
                      have h_comm : (2 * p - 1) * (2 * r - 1) * Y * (2 * q - 1) = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y := by ring
                      rw [h_comm]
                      omega
                    have h_eq_div : 2 * c * m' * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := by
                      calc
                        2 * c * m' * p * q * r = 2 * (c * p * m') * q * r := by ring
                        _ = 2 * a * q * r := by rw [ha_eq_cpm']
                        _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := h_eq_main
                    have h_lt_main : (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 < 8 * p * q * r * Y := by
                      have h_id : (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 < 8 * p * q * r := by
                        have h_prod_ge : (2 * q - 1) * (2 * r - 1) ≥ 2 := by
                          have h1 : 2 * q - 1 ≥ 1 := by omega
                          have h2 : 2 * r - 1 ≥ 2 := by omega
                          have : (2 * q - 1) * (2 * r - 1) ≥ 1 * 2 := Nat.mul_le_mul h1 h2
                          omega
                        have h_add_alg : (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + (2 * q - 1) * (2 * r - 1) = (2 * p) * (2 * q - 1) * (2 * r - 1) := by
                          have h_dist : (2 * p - 1) * ((2 * q - 1) * (2 * r - 1)) + 1 * ((2 * q - 1) * (2 * r - 1)) = ((2 * p - 1) + 1) * ((2 * q - 1) * (2 * r - 1)) := by rw [← Nat.add_mul]
                          have h_add_one : (2 * p - 1) + 1 = 2 * p := by omega
                          rw [one_mul] at h_dist
                          rw [h_add_one] at h_dist
                          rw [mul_assoc, mul_assoc]
                          exact h_dist
                        calc
                          (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1
                          _ < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + (2 * q - 1) * (2 * r - 1) := by omega
                          _ = (2 * p) * (2 * q - 1) * (2 * r - 1) := h_add_alg
                          _ < (2 * p) * (2 * q) * (2 * r - 1) := by
                            have h_lt1 : 2 * q - 1 < 2 * q := by omega
                            have h_lt2 : 2 * p * (2 * q - 1) < 2 * p * (2 * q) := Nat.mul_lt_mul_of_pos_left h_lt1 (by omega)
                            exact Nat.mul_lt_mul_of_pos_right h_lt2 (by omega)
                          _ < (2 * p) * (2 * q) * (2 * r) := by
                            have h_lt_inner : 2 * r - 1 < 2 * r := by omega
                            exact Nat.mul_lt_mul_of_pos_left h_lt_inner (Nat.mul_pos (by omega) (by omega))
                          _ = 8 * p * q * r := by ring
                      calc
                        (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1
                        _ ≤ (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + Y := by omega
                        _ = ((2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1) * Y := by ring
                        _ < (8 * p * q * r) * Y := Nat.mul_lt_mul_of_pos_right h_id hY_pos
                        _ = 8 * p * q * r * Y := by ring
                    have h_div_lt : 2 * (c * m') < 8 * Y := by
                      have h_mul1 : 2 * (c * m') * (p * q * r) = 2 * c * m' * p * q * r := by ring
                      have h_mul2 : 8 * Y * (p * q * r) = 8 * p * q * r * Y := by ring
                      have h_lt_temp : 2 * c * m' * p * q * r < 8 * p * q * r * Y := by
                        calc
                          2 * c * m' * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * Y + 1 := h_eq_div
                          _ < 8 * p * q * r * Y := h_lt_main
                      rw [← h_mul1, ← h_mul2] at h_lt_temp
                      exact Nat.lt_of_mul_lt_mul_right h_lt_temp
                    have h_cm'_lt : c * m' < 4 * Y := by
                      omega
                    by_cases hm'1 : m' = 1
                    · have h_Y_eq : Y = 1 := by
                        dsimp [Y]
                        rw [hm'1]
                        simp
                      have h_c_lt4 : c < 4 := by
                        have h_temp := h_cm'_lt
                        rw [hm'1, h_Y_eq] at h_temp
                        omega
                      have hc_cases : c = 2 ∨ c = 3 := by omega
                      rcases hc_cases with rfl | rfl
                      · have h_eq_div_re : 4 * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                          have h_temp := h_eq_div
                          rw [hm'1, h_Y_eq] at h_temp
                          calc
                            4 * p * q * r = 2 * 2 * 1 * p * q * r := by ring
                            _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * 1 + 1 := h_temp
                            _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by ring
                        have hr_ge11_tmp : r ≥ 11 := by
                          have : r ≠ 9 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                          have : r ≠ 10 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                          omega
                        have h_ineq : 4 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                          exact test_ineq1 p q r hp3 h_q7 hr_ge11_tmp
                        exfalso
                        rw [h_eq_div_re] at h_ineq
                        exact lt_irrefl _ h_ineq
                      · have h_eq_div_re : 6 * p * q * r = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                          have h_temp := h_eq_div
                          rw [hm'1, h_Y_eq] at h_temp
                          calc
                            6 * p * q * r = 2 * 3 * 1 * p * q * r := by ring
                            _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * 1 + 1 := h_temp
                            _ = (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by ring
                        by_cases hq11 : q ≥ 11
                        · have h_ineq : 6 * p * q * r < (2 * p - 1) * (2 * q - 1) * (2 * r - 1) + 1 := by
                            exact test_ineq2 p q r hp3 hq11 (by omega)
                          exfalso
                          rw [h_eq_div_re] at h_ineq
                          exact lt_irrefl _ h_ineq
                        · have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hq_mem
                          have hq7_eq : q = 7 := by
                            have : q < 11 := by omega
                            interval_cases q
                            · rfl
                            · exfalso; revert hq_prime; decide
                            · exfalso; revert hq_prime; decide
                            · exfalso; revert hq_prime; decide
                          have hp_cases : p = 3 ∨ p = 5 := by
                            have : p < 7 := by omega
                            interval_cases p
                            · left; rfl
                            · exfalso; revert hp_p; decide
                            · right; rfl
                            · exfalso; revert hp_p; decide
                          rcases hp_cases with rfl | rfl
                          · have hr16 : r = 16 := by omega
                            rw [hr16] at hr_prime
                            have : ¬ Nat.Prime 16 := by decide
                            exact (this hr_prime).elim
                          · have hr_ge11 : r ≥ 11 := by
                              have : r ≠ 9 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                              have : r ≠ 10 := by intro hc; rw [hc] at hr_prime; revert hr_prime; decide
                              omega
                            rw [hq7_eq] at h_eq_div_re
                            have h_eq_re : (6 * 5 * 7 * r : ℤ) = (((2 * 5 - 1) * (2 * 7 - 1) * (2 * r - 1) + 1 : ℕ) : ℤ) := by
                              exact_mod_cast h_eq_div_re
                            have hr_ge11_z : (r : ℤ) ≥ 11 := by exact_mod_cast hr_ge11
                            have h_ge_r : 2 * r ≥ 1 := by omega
                            zify [h_ge_r] at h_eq_re
                            exfalso
                            omega
                    · have hm'_ge2 : m' ≥ 2 := by omega
                      have h_cp : c * p ≥ 6 := by
                        calc
                          c * p ≥ 2 * 3 := Nat.mul_le_mul hc_pos hp3
                          _ = 6 := by decide
                      have h_cpm' : c * p * m' ≥ 12 := by
                        calc
                          c * p * m' ≥ 6 * 2 := Nat.mul_le_mul h_cp hm'_ge2
                          _ = 12 := by decide
                      rw [← ha_eq_cpm'] at h_cpm'
                      omega
theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  constructor
  · exact a_eq_1_impl_prime_or_1 n
  · rintro (rfl | hp)
    · rfl
    · exact prime_a_eq_1 hp

#print axioms oeis_340079_conjecture_0
