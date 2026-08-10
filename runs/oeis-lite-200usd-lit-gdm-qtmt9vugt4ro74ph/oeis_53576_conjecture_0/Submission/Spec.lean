import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000000000

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

theorem dvd_two_pow {d N : ℕ} (hd : d ∣ 2 ^ N) : ∃ v ≤ N, d = 2 ^ v := by
  have h_prime : Nat.Prime 2 := Nat.prime_two
  rcases (Nat.dvd_prime_pow h_prime).mp hd with ⟨v, hv, rfl⟩
  exact ⟨v, hv, rfl⟩

theorem odd_not_dvd_two_pow {q N : ℕ} (hq : Odd q) (hq1 : q > 1) : ¬ q ∣ 2 ^ N := by
  by_contra h_dvd
  rcases dvd_two_pow h_dvd with ⟨v, hv, rfl⟩
  by_cases hv0 : v = 0
  · subst hv0; simp at hq1
  · have hv1 : v ≥ 1 := by omega
    have h_even : Even (2 ^ v) := by
      rw [← Nat.succ_pred_eq_of_pos hv1]
      simp [pow_succ]
    have h_not_odd : ¬ Odd (2 ^ v) := Nat.not_odd_iff_even.mpr h_even
    exact h_not_odd hq

theorem totient_two_mul_le (k : ℕ) : totient (2 * k) ≤ k := by
  induction' k using Nat.strong_induction_on with k ih
  by_cases hk : k = 0
  · subst hk; simp
  · rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    -- case k is even: k = 2 * j
    · have hj_pos : j ≠ 0 := by omega
      have hj_lt : j < j + j := by omega
      have h1 : totient (2 * (2 * j)) = 2 * totient (2 * j) := by
        have h_even : 2 ∣ 2 * j := dvd_mul_right 2 j
        exact totient_mul_of_prime_of_dvd Nat.prime_two h_even
      have h_eq : j + j = 2 * j := by omega
      rw [h_eq]
      rw [h1]
      have h_ih := ih j hj_lt
      omega
    -- case k is odd: k = 2 * j + 1
    · have h_odd : ¬ 2 ∣ 2 * j + 1 := by omega
      have h1 : totient (2 * (2 * j + 1)) = totient (2 * j + 1) := by
        have := totient_mul_of_prime_of_not_dvd Nat.prime_two h_odd
        simp at this
        exact this
      rw [h1]
      exact totient_le (2 * j + 1)

theorem odd_of_mem_of_lt (m : ℕ) (N : ℕ) (hm : m > 0) (hdiv : 2 ^ N ∣ totient m) (hlt : m < 2 ^ (N + 1)) : Odd m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h_eq : k + k = 2 * k := by omega
    rw [h_eq] at hm hdiv
    have hk_pos : k > 0 := by omega
    have hlt_k : k < 2 ^ N := by
      have h_pow : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
      omega
    have h_tot_le : totient (2 * k) ≤ k := totient_two_mul_le k
    have h_tot_lt : totient (2 * k) < 2 ^ N := by omega
    have h_tot_pos : 0 < totient (2 * k) := totient_pos.mpr hm
    have h_tot_div : 2 ^ N ≤ totient (2 * k) := Nat.le_of_dvd h_tot_pos hdiv
    omega
  · exact ⟨k, rfl⟩

theorem totient_eq_two_pow (m : ℕ) (N : ℕ) (hN : N ≥ 1) (hm : m > 0) (hdiv : 2 ^ N ∣ totient m) (hlt : m < 2 ^ (N + 1)) : totient m = 2 ^ N := by
  have h_tot_pos : 0 < totient m := totient_pos.mpr hm
  have h_le : 2 ^ N ≤ totient m := Nat.le_of_dvd h_tot_pos hdiv
  by_cases h_meq : m = 1
  · subst h_meq
    simp at h_le
    have h_two_pow : 2 ^ N ≥ 2 := by
      calc
        2 ^ N ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hN
        _ = 2 := by rfl
    omega
  · have h_m_gt_1 : 1 < m := by omega
    have h_tot_lt : totient m < m := totient_lt m h_m_gt_1
    have h_tot_lt_pow : totient m < 2 ^ (N + 1) := by omega
    rcases hdiv with ⟨c, hc⟩
    have h_pow_eq : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
    have hc_pos : c > 0 := by
      by_contra hc0
      have : c = 0 := by omega
      subst this
      omega
    have hc_lt : c < 2 := by
      have h_mul_lt : 2 ^ N * c < 2 ^ N * 2 := by
        calc
          2 ^ N * c = totient m := hc.symm
          _ < 2 ^ (N + 1) := h_tot_lt_pow
          _ = 2 ^ N * 2 := by ring
      by_contra hc2
      have hc_ge : c ≥ 2 := by omega
      have h_le := Nat.mul_le_mul_left (2 ^ N) hc_ge
      omega
    have hc1 : c = 1 := by omega
    rw [hc, hc1]
    ring

theorem prime_of_fermat_in_set (N : ℕ) (hN : N ≥ 1) (hm : 2 ^ N + 1 ∈ {m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m}) : (2 ^ N + 1).Prime := by
  have h_two_pow : 2 ^ N ≥ 2 := by
    calc
      2 ^ N ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hN
      _ = 2 := by rfl
  have hm_pos : 2 ^ N + 1 > 0 := by omega
  have hdiv : 2 ^ N ∣ totient (2 ^ N + 1) := hm.2
  have h_tot_pos : 0 < totient (2 ^ N + 1) := totient_pos.mpr hm_pos
  have h_le : 2 ^ N ≤ totient (2 ^ N + 1) := Nat.le_of_dvd h_tot_pos hdiv
  by_contra h_not_prime
  have h_iff := totient_eq_iff_prime hm_pos
  have h_not_eq : totient (2 ^ N + 1) ≠ 2 ^ N + 1 - 1 := fun h ↦ h_not_prime (h_iff.mp h)
  have h_m_gt_1 : 1 < 2 ^ N + 1 := by omega
  have h_tot_lt : totient (2 ^ N + 1) < 2 ^ N + 1 := totient_lt (2 ^ N + 1) h_m_gt_1
  have h_tot_le : totient (2 ^ N + 1) ≤ 2 ^ N + 1 - 1 := Nat.le_sub_one_of_lt h_tot_lt
  have h_sub_eq : 2 ^ N + 1 - 1 = 2 ^ N := by omega
  omega

theorem lemma1 (m : ℕ) (N : ℕ) (hN : N ≥ 1) (hm : m > 0) (hdiv : 2 ^ N ∣ totient m) : m ≥ 2 ^ N + 1 := by
  have h_tot_pos : 0 < totient m := totient_pos.mpr hm
  have h_le : 2 ^ N ≤ totient m := Nat.le_of_dvd h_tot_pos hdiv
  by_cases h_meq : m = 1
  · subst h_meq
    simp at h_le
    have : 2 ^ N ≥ 2 := by
      calc
        2 ^ N ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hN
        _ = 2 := by rfl
    omega
  · have h_m_gt_1 : 1 < m := by omega
    have h_tot_lt : totient m < m := totient_lt m h_m_gt_1
    have h_tot_le : totient m ≤ m - 1 := Nat.le_sub_one_of_lt h_tot_lt
    omega

theorem sInf_eq_of_mem_of_le {s : Set ℕ} {x : ℕ} (hx : x ∈ s) (hle : ∀ y ∈ s, x ≤ y) : sInf s = x := by
  have h_nonempty : s.Nonempty := ⟨x, hx⟩
  have h_mem : sInf s ∈ s := Nat.sInf_mem h_nonempty
  have h1 : x ≤ sInf s := hle (sInf s) h_mem
  have h2 : sInf s ≤ x := Nat.sInf_le hx
  omega

theorem totient_mul_le_prime_right (p d : ℕ) (hp : p.Prime) : totient (p * d) ≤ (p - 1) * d := by
  induction' d using Nat.strong_induction_on with d ih
  by_cases hd0 : d = 0
  · subst hd0; simp
  · by_cases hpd : p ∣ d
    · have h1 : totient (p * d) = p * totient d := totient_mul_of_prime_of_dvd hp hpd
      rcases hpd with ⟨k, rfl⟩
      have hp2 : p ≥ 2 := hp.two_le
      have hk_pos : k > 0 := by
        by_contra hk0
        have : k = 0 := by omega
        subst this
        simp at hd0
      have hk_lt : k < p * k := by
        calc
          k < 2 * k := by omega
          _ ≤ p * k := Nat.mul_le_mul_right k hp2
      have h_ih := ih k hk_lt
      rw [h1]
      have h2 : p * totient (p * k) ≤ p * ((p - 1) * k) := by
        gcongr
      have h3 : (p - 1) * (p * k) = p * ((p - 1) * k) := by ring
      omega
    · have h1 : totient (p * d) = (p - 1) * totient d := totient_mul_of_prime_of_not_dvd hp hpd
      rw [h1]
      have : totient d ≤ d := totient_le d
      gcongr

theorem three_dvd_two_pow_add_one_of_odd {k : ℕ} (hk : Odd k) : 3 ∣ 2 ^ k + 1 := by
  rcases hk with ⟨j, rfl⟩
  induction' j with j ih
  · simp
  · have h_pow : 2 ^ (2 * (j + 1) + 1) = 2 ^ (2 * j + 1) * 4 := by
      have h_eq1 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [h_eq1, pow_add]
      ring
    have h_eq : 2 ^ (2 * (j + 1) + 1) + 1 = 4 * (2 ^ (2 * j + 1) + 1) - 3 := by
      omega
    rw [h_eq]
    have h1 : 3 ∣ 4 * (2 ^ (2 * j + 1) + 1) := dvd_mul_of_dvd_right ih 4
    have h2 : 3 ∣ 3 := dvd_refl 3
    exact Nat.dvd_sub h1 h2


theorem pow_two_add_pow_two_ne (c d : ℕ) (hcd : c < d) : 2 ^ c + 2 ^ d ≠ 2 ^ 33 := by
  intro h
  have h_eq : 2 ^ c + 2 ^ d = 2 ^ c * (1 + 2 ^ (d - c)) := by
    have h_sub : 2 ^ d = 2 ^ c * 2 ^ (d - c) := by
      have : d = c + (d - c) := by omega
      nth_rw 1 [this]
      rw [pow_add]
    rw [h_sub]
    ring
  have h_dvd : (1 + 2 ^ (d - c)) ∣ 2 ^ 33 := by
    rw [← h, h_eq]
    exact dvd_mul_left (1 + 2 ^ (d - c)) (2 ^ c)
  have h_odd : Odd (1 + 2 ^ (d - c)) := by
    have h_pos : d - c ≥ 1 := by omega
    use 2 ^ (d - c - 1)
    have h_eq2 : 2 ^ (d - c) = 2 * 2 ^ (d - c - 1) := by
      have : d - c = (d - c - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_succ, mul_comm]
    rw [h_eq2]
    omega
  have h_gt_1 : 1 < 1 + 2 ^ (d - c) := by
    have h_pos : d - c ≥ 1 := by omega
    have : 2 ^ (d - c) > 0 := Nat.pow_pos (by decide)
    omega
  have h_not_dvd := @odd_not_dvd_two_pow (1 + 2 ^ (d - c)) 33 h_odd h_gt_1
  exact h_not_dvd h_dvd

theorem coprime_prod_right_of_coprime_list {p : ℕ} (L : List ℕ) (h : ∀ x ∈ L, p.Coprime x) :
    p.Coprime L.prod := by
  induction' L with x t ih
  · simp
  · simp only [List.mem_cons, forall_eq_or_imp] at h
    have hx : p.Coprime x := h.1
    have ht : ∀ y ∈ t, p.Coprime y := h.2
    have h_prod : (x :: t).prod = x * t.prod := rfl
    rw [h_prod]
    exact Nat.Coprime.mul_right hx (ih ht)

theorem totient_eq_of_squarefree_list (L : List ℕ) (h_prime : ∀ p ∈ L, p.Prime) (h_nodup : L.Nodup) :
    totient L.prod = (L.map totient).prod := by
  induction' L with p t ih
  · simp
  · simp only [List.mem_cons, forall_eq_or_imp] at h_prime
    have hp_prime : p.Prime := h_prime.1
    have ht_prime : ∀ x ∈ t, x.Prime := h_prime.2
    simp only [List.nodup_cons] at h_nodup
    have hp_not_mem : p ∉ t := h_nodup.1
    have ht_nodup : t.Nodup := h_nodup.2
    have h_coprime : p.Coprime t.prod := by
      have h_cop_list : ∀ x ∈ t, p.Coprime x := by
        intro x hx
        have hx_prime : x.Prime := ht_prime x hx
        exact hp_prime.coprime_iff_not_dvd.mpr (by
          intro h_dvd
          rcases (dvd_prime hx_prime).mp h_dvd with hp1 | hpx
          · have : p > 1 := hp_prime.one_lt; omega
          · subst hpx; exact hp_not_mem hx)
      exact coprime_prod_right_of_coprime_list t h_cop_list
    have h_prod_eq : (p :: t).prod = p * t.prod := rfl
    rw [h_prod_eq, Nat.totient_mul h_coprime, ih ht_prime ht_nodup]
    rfl


theorem dvd_sum_of_dvd_mem {B : ℕ} (L : List ℕ) (h : ∀ x ∈ L, B ∣ x) : B ∣ L.sum := by
  induction' L with x t ih
  · simp
  · simp only [List.mem_cons, forall_eq_or_imp] at h
    have hx : B ∣ x := h.1
    have ht : ∀ y ∈ t, B ∣ y := h.2
    have h_sum : (x :: t).sum = x + t.sum := rfl
    rw [h_sum]
    exact dvd_add hx (ih ht)


theorem prod_pow_two_eq_pow_sum (E : List ℕ) :
    (E.map (fun y ↦ 2 ^ y)).prod = 2 ^ E.sum := by
  induction' E with x t ih
  · simp
  · have h_prod : ((x :: t).map (fun y ↦ 2 ^ y)).prod = 2 ^ x * (t.map (fun y ↦ 2 ^ y)).prod := rfl
    rw [h_prod, ih]
    have h_sum : (x :: t).sum = x + t.sum := rfl
    rw [h_sum, pow_add]


theorem list_min_achieved (L : List ℕ) (h : L ≠ []) : ∃ m ∈ L, ∀ x ∈ L, m ≤ x := by
  induction' L with a t ih
  · contradiction
  · by_cases ht : t = []
    · subst ht
      use a
      simp
    · rcases ih ht with ⟨m, hm_mem, hm_le⟩
      by_cases ham : a ≤ m
      · use a
        refine ⟨by simp, ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · have : m ≤ x := hm_le x hx
          omega
      · use m
        refine ⟨by simp [hm_mem], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact hm_le x hx



theorem fermat_pos (n : ℕ) : Nat.fermatNumber n > 0 := by
  dsimp [Nat.fermatNumber]
  positivity

theorem fermat_sub_one (n : ℕ) : Nat.fermatNumber n - 1 = 2 ^ (2 ^ n) := by
  dsimp [Nat.fermatNumber]

theorem fermat_eq (n : ℕ) : Nat.fermatNumber n = 2 ^ (2 ^ n) + 1 := rfl

-- Formalization of the conjecture

theorem oeis_53576_conjecture_helper (K : ℕ) (hK_ge_1 : K ≥ 1) :
    let N := 2 ^ K
    a N = if (2 ^ N + 1).Prime then 2 ^ N + 1 else 2 ^ (N + 1) := by
  intro N
  have hN_ge_1 : N ≥ 1 := by
    dsimp [N]
    calc
      2 ^ K ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hK_ge_1
      _ = 2 := rfl
      _ ≥ 1 := by omega
  let rhs := if (2 ^ N + 1).Prime then 2 ^ N + 1 else 2 ^ (N + 1)
  have h_rhs_mem : rhs ∈ { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } := by
    dsimp [rhs]
    rcases Classical.em (2 ^ N + 1).Prime with h_prime | h_prime
    · rw [if_pos h_prime]
      have h_f33_pos : 2 ^ N + 1 > 0 := by positivity
      refine ⟨h_f33_pos, ?_⟩
      have h_tot : totient (2 ^ N + 1) = 2 ^ N := (totient_eq_iff_prime h_f33_pos).mpr h_prime
      rw [h_tot]
    · rw [if_neg h_prime]
      have h_two_pow_pos : 2 ^ (N + 1) > 0 := Nat.pow_pos (by decide)
      refine ⟨h_two_pow_pos, ?_⟩
      have h_tot : totient (2 ^ (N + 1)) = 2 ^ N := by
        have h_prime_two : Nat.Prime 2 := Nat.prime_two
        have h_eq : totient (2 ^ (N + 1)) = 2 ^ N * (2 - 1) := totient_prime_pow_succ h_prime_two N
        have h_sub : 2 - 1 = 1 := rfl
        rw [h_eq, h_sub, mul_one]
      rw [h_tot]
  apply sInf_eq_of_mem_of_le h_rhs_mem
  intro m hm
  dsimp [rhs]
  rcases Classical.em (2 ^ N + 1).Prime with h_prime | h_prime
  · rw [if_pos h_prime]
    have h_lem1 : m ≥ 2 ^ N + 1 := lemma1 m N hN_ge_1 hm.1 hm.2
    exact h_lem1
  · rw [if_neg h_prime]
    have h_pow_eq : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ, mul_comm]
    rw [h_pow_eq]
    generalize hX : 2 ^ N = X
    by_contra h_lt_pow
    have h_lt : m < 2 * X := by omega
    have h_tot_eq : totient m = X := by
      have h_lt_pow2 : m < 2 ^ (N + 1) := by
        rw [h_pow_eq, hX]
        exact h_lt
      have : totient m = 2 ^ N := totient_eq_two_pow m N hN_ge_1 hm.1 hm.2 h_lt_pow2
      rw [this, hX]
    have h_odd : Odd m := odd_of_mem_of_lt m N hm.1 hm.2 (by rw [h_pow_eq, hX]; exact h_lt)
    have h_ge : m ≥ X + 1 := by
      have : m ≥ 2 ^ N + 1 := lemma1 m N hN_ge_1 hm.1 hm.2
      rw [hX] at this
      exact this
    have hX_ge_two : X ≥ 2 := by
      rw [← hX]
      calc
        2 ^ N ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hN_ge_1
        _ = 2 := rfl
    by_cases h_meq : m = X + 1
    · subst h_meq
      have hm_copy := hm
      rw [← hX] at hm_copy
      have : (2 ^ N + 1).Prime := prime_of_fermat_in_set N hN_ge_1 hm_copy
      exact h_prime this
    · have h_gt : m > X + 1 := by omega
      have hm_pos : m > 0 := by omega
      clear hm hN_ge_1
      by_cases h_mprime : m.Prime
      · have : totient m = m - 1 := (totient_eq_iff_prime hm_pos).mpr h_mprime
        rw [h_tot_eq] at this
        omega
      · have h_p1_prime : (minFac m).Prime := minFac_prime (by omega)
        have h_p1_dvd_m : minFac m ∣ m := minFac_dvd m
        have h_tot_p1_dvd : totient (minFac m) ∣ totient m := totient_dvd_of_dvd h_p1_dvd_m
        have h_p1_pos : minFac m > 0 := h_p1_prime.pos
        have h_tot_p1 : totient (minFac m) = minFac m - 1 := (totient_eq_iff_prime h_p1_pos).mpr h_p1_prime
        have h_p1_sub_dvd : minFac m - 1 ∣ X := by
          rw [← h_tot_eq]
          rw [h_tot_p1] at h_tot_p1_dvd
          exact h_tot_p1_dvd
        have h_p1_sub_dvd_2 : minFac m - 1 ∣ 2 ^ N := by
          rw [← hX] at h_p1_sub_dvd
          exact h_p1_sub_dvd
        rcases dvd_two_pow h_p1_sub_dvd_2 with ⟨v_1, hv1_le, hv1_eq⟩
        have hp1_eq : minFac m = 2 ^ v_1 + 1 := by omega
        have hp1_ne_two : minFac m ≠ 2 := by
          intro hp1_two
          have h_p1_dvd_m_copy := h_p1_dvd_m
          rw [hp1_two] at h_p1_dvd_m_copy
          have h_even : Even m := even_iff_two_dvd.mpr h_p1_dvd_m_copy
          have h_not_odd : ¬ Odd m := Nat.not_odd_iff_even.mpr h_even
          exact h_not_odd h_odd
        have hv1_ne_zero : v_1 ≠ 0 := by
          intro hv1_zero
          have h_meq : minFac m = 2 := by
            rw [hp1_eq, hv1_zero]
            rfl
          exact hp1_ne_two h_meq
        have hp1_prime_rw : (2 ^ v_1 + 1).Prime := by
          rw [← hp1_eq]
          exact h_p1_prime
        rcases Nat.pow_of_pow_add_prime (by decide) hv1_ne_zero hp1_prime_rw with ⟨c_1, hc1⟩

        let k := m / minFac m
        have hk_eq : m = minFac m * k := by
          dsimp [k]
          exact (Nat.mul_div_cancel' h_p1_dvd_m).symm
        have hk_gt_1 : k > 1 := by
          by_contra hk_le
          have hk_le_1 : k ≤ 1 := Nat.le_of_not_lt hk_le
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk_le_1 with hk0 | hk1
          · rw [hk0] at hk_eq
            simp at hk_eq
            clear hk_le_1 k hk0 hk_le
            omega
          · rw [hk1] at hk_eq
            simp at hk_eq
            rw [hk_eq] at h_mprime
            exact h_mprime h_p1_prime

        have h_p2_prime : (minFac k).Prime := minFac_prime (by omega)
        have h_p2_dvd_k : minFac k ∣ k := minFac_dvd k
        have h_p2_dvd_m : minFac k ∣ m := by
          rcases h_p2_dvd_k with ⟨u, hu⟩
          have h_eq : m = minFac k * (minFac m * u) := by
            calc
              m = minFac m * k := hk_eq
              _ = minFac m * (minFac k * u) := by congr 1
              _ = minFac k * (minFac m * u) := by ring
          exact ⟨minFac m * u, h_eq⟩
        have h_tot_p2_dvd : totient (minFac k) ∣ totient m := totient_dvd_of_dvd h_p2_dvd_m
        have h_p2_pos : minFac k > 0 := h_p2_prime.pos
        have h_tot_p2 : totient (minFac k) = minFac k - 1 := (totient_eq_iff_prime h_p2_pos).mpr h_p2_prime
        have h_p2_sub_dvd : minFac k - 1 ∣ X := by
          rw [← h_tot_eq]
          rw [h_tot_p2] at h_tot_p2_dvd
          exact h_tot_p2_dvd
        have h_p2_sub_dvd_2 : minFac k - 1 ∣ 2 ^ N := by
          rw [← hX] at h_p2_sub_dvd
          exact h_p2_sub_dvd
        rcases dvd_two_pow h_p2_sub_dvd_2 with ⟨v_2, hv2_le, hv2_eq⟩
        have hp2_eq : minFac k = 2 ^ v_2 + 1 := by omega
        have hp2_ne_two : minFac k ≠ 2 := by
          intro hp2_two
          have h_p2_dvd_m_copy := h_p2_dvd_m
          rw [hp2_two] at h_p2_dvd_m_copy
          have h_even : Even m := even_iff_two_dvd.mpr h_p2_dvd_m_copy
          have h_not_odd : ¬ Odd m := Nat.not_odd_iff_even.mpr h_even
          exact h_not_odd h_odd
        have hv2_ne_zero : v_2 ≠ 0 := by
          intro hv2_zero
          have h_meq : minFac k = 2 := by
            rw [hp2_eq, hv2_zero]
            rfl
          exact hp2_ne_two h_meq
        have hp2_prime_rw : (2 ^ v_2 + 1).Prime := by
          rw [← hp2_eq]
          exact h_p2_prime
        rcases Nat.pow_of_pow_add_prime (by decide) hv2_ne_zero hp2_prime_rw with ⟨c_2, hc2⟩

        have hp1_ne_p2 : minFac m ≠ minFac k := by
          intro hp1_eq_p2
          have h_p1_sq_dvd : (minFac m) ^ 2 ∣ m := by
            rcases h_p2_dvd_k with ⟨u, hu⟩
            have h_eq : m = (minFac m) ^ 2 * u := by
              calc
                m = minFac m * k := hk_eq
                _ = minFac m * (minFac k * u) := by congr 1
                _ = minFac m * (minFac m * u) := by rw [← hp1_eq_p2]
                _ = (minFac m) ^ 2 * u := by ring
            exact ⟨u, h_eq⟩
          have h_tot_p1_sq_dvd : totient ((minFac m) ^ 2) ∣ totient m := totient_dvd_of_dvd h_p1_sq_dvd
          have h_tot_p1_sq : totient ((minFac m) ^ 2) = minFac m * (minFac m - 1) := by
            have : (minFac m) ^ 2 = (minFac m) ^ (1 + 1) := by ring
            rw [this, totient_prime_pow_succ h_p1_prime]
            ring
          rw [h_tot_p1_sq] at h_tot_p1_sq_dvd
          rw [h_tot_eq] at h_tot_p1_sq_dvd
          have h_p1_dvd_two_pow : minFac m ∣ 2 ^ N := by
            have h_p1_dvd_prod : minFac m ∣ minFac m * (minFac m - 1) := dvd_mul_right (minFac m) (minFac m - 1)
            have h_dvd_X := dvd_trans h_p1_dvd_prod h_tot_p1_sq_dvd
            rw [← hX] at h_dvd_X
            exact h_dvd_X
          have h_not_dvd : ¬ minFac m ∣ 2 ^ N := by
            have hp1_odd : Odd (minFac m) := by
              have hp1_gt_1 : minFac m > 1 := h_p1_prime.one_lt
              rcases Nat.even_or_odd (minFac m) with ⟨j, hj⟩ | ⟨j, hj⟩
              · have h_dvd_prime : 2 ∣ minFac m := even_iff_two_dvd.mp ⟨j, hj⟩
                rcases (dvd_prime h_p1_prime).mp h_dvd_prime with h21 | h2p
                · contradiction
                · exact (hp1_ne_two h2p.symm).elim
              · exact ⟨j, hj⟩
            have hp1_gt_1 : minFac m > 1 := h_p1_prime.one_lt
            exact @odd_not_dvd_two_pow (minFac m) N hp1_odd hp1_gt_1
          exact h_not_dvd h_p1_dvd_two_pow

        have hp1_lt_p2 : minFac m < minFac k := by
          have : minFac m ≤ minFac k := minFac_le_of_dvd h_p2_prime.two_le h_p2_dvd_m
          have : minFac m ≠ minFac k := hp1_ne_p2
          omega

        have h_v1_lt_v2 : v_1 < v_2 := by
          rw [hp1_eq, hp2_eq] at hp1_lt_p2
          have : 2 ^ v_1 < 2 ^ v_2 := by omega
          exact (Nat.pow_lt_pow_iff_right (by decide)).mp this

        have hc1_lt_c2 : c_1 < c_2 := by
          rw [hc1, hc2] at h_v1_lt_v2
          exact (Nat.pow_lt_pow_iff_right (by decide)).mp h_v1_lt_v2

        have h_sqfree : Squarefree m := by
          rw [squarefree_iff_prime_squarefree]
          intro x hx_prime h_dvd
          have h_p1_sq_dvd : x ^ 2 ∣ m := by
            have : x ^ 2 = x * x := sq x
            rw [this]
            exact h_dvd
          have h_tot_p1_sq_dvd : totient (x ^ 2) ∣ totient m := totient_dvd_of_dvd h_p1_sq_dvd
          have h_tot_p1_sq : totient (x ^ 2) = x * (x - 1) := by
            have : x ^ 2 = x ^ (1 + 1) := by ring
            rw [this, totient_prime_pow_succ hx_prime]
            ring
          rw [h_tot_p1_sq] at h_tot_p1_sq_dvd
          rw [h_tot_eq] at h_tot_p1_sq_dvd
          have h_p1_dvd_two_pow : x ∣ 2 ^ N := by
            have h_p1_dvd_prod : x ∣ x * (x - 1) := dvd_mul_right x (x - 1)
            have h_dvd_X := dvd_trans h_p1_dvd_prod h_tot_p1_sq_dvd
            rw [← hX] at h_dvd_X
            exact h_dvd_X
          have h_not_dvd : ¬ x ∣ 2 ^ N := by
            have hp1_odd : Odd x := by
              have hp1_gt_1 : x > 1 := hx_prime.one_lt
              rcases Nat.even_or_odd x with ⟨j, hj⟩ | ⟨j, hj⟩
              · have h_even_x : Even x := ⟨j, hj⟩
                have h_dvd_prime : 2 ∣ x := even_iff_two_dvd.mp h_even_x
                rcases (dvd_prime hx_prime).mp h_dvd_prime with h21 | h2p
                · contradiction
                · subst h2p
                  have h_even : Even m := even_iff_two_dvd.mpr (by
                    have : 2 * 2 ∣ m := h_p1_sq_dvd
                    exact dvd_of_mul_left_dvd this)
                  have h_not_odd : ¬ Odd m := Nat.not_odd_iff_even.mpr h_even
                  exact (h_not_odd h_odd).elim
              · exact ⟨j, hj⟩
            have hp1_gt_1 : x > 1 := hx_prime.one_lt
            exact @odd_not_dvd_two_pow x N hp1_odd hp1_gt_1
          exact h_not_dvd h_p1_dvd_two_pow

        have hm_ne_zero : m ≠ 0 := by omega
        have h_nodup : m.primeFactorsList.Nodup := (Nat.squarefree_iff_nodup_primeFactorsList hm_ne_zero).mp h_sqfree
        have h_prime_list : ∀ p ∈ m.primeFactorsList, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactorsList hp

        have h_tot_list : totient m = (m.primeFactorsList.map totient).prod := by
          have h_prod : m.primeFactorsList.prod = m := Nat.prod_primeFactorsList hm_ne_zero
          have h_tot_eq_prod := totient_eq_of_squarefree_list m.primeFactorsList h_prime_list h_nodup
          rw [h_prod] at h_tot_eq_prod
          exact h_tot_eq_prod

        have h_all_p_tot : ∀ p ∈ m.primeFactorsList, ∃ v, p.totient = 2 ^ v := by
          intro p hp
          have hp_prime : p.Prime := h_prime_list p hp
          have hp_dvd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
          have h_tot_p_dvd : totient p ∣ totient m := totient_dvd_of_dvd hp_dvd
          have h_tot_p : totient p = p - 1 := (totient_eq_iff_prime hp_prime.pos).mpr hp_prime
          have h_p_sub_dvd : p - 1 ∣ 2 ^ N := by
            rw [h_tot_p] at h_tot_p_dvd
            rw [h_tot_eq] at h_tot_p_dvd
            rw [← hX] at h_tot_p_dvd
            exact h_tot_p_dvd
          rcases dvd_two_pow h_p_sub_dvd with ⟨v, hv_le, hv_eq⟩
          use v
          rw [h_tot_p]
          exact hv_eq

        have h_all_p_tot' : ∀ p ∈ m.primeFactorsList, ∃ c, p.totient = 2 ^ (2 ^ c) := by
          intro p hp
          rcases h_all_p_tot p hp with ⟨v, hv_eq⟩
          have hp_prime : p.Prime := h_prime_list p hp
          have h_tot_p : totient p = p - 1 := (totient_eq_iff_prime hp_prime.pos).mpr hp_prime
          have hp_eq : p = 2 ^ v + 1 := by
            rw [hv_eq] at h_tot_p
            have : p > 1 := hp_prime.one_lt
            omega
          have hp_ne_two : p ≠ 2 := by
            intro hp_two
            have hp_dvd_m := Nat.dvd_of_mem_primeFactorsList hp
            rw [hp_two] at hp_dvd_m
            have h_even : Even m := even_iff_two_dvd.mpr hp_dvd_m
            have h_not_odd : ¬ Odd m := Nat.not_odd_iff_even.mpr h_even
            exact h_not_odd h_odd
          have hv_ne_zero : v ≠ 0 := by
            intro hv_zero
            subst hv_zero
            simp at hp_eq
            exact hp_ne_two hp_eq
          have hp_prime_rw : (2 ^ v + 1).Prime := by
            rw [← hp_eq]
            exact hp_prime
          rcases Nat.pow_of_pow_add_prime (by decide) hv_ne_zero hp_prime_rw with ⟨c, hc⟩
          use c
          rw [hv_eq, hc]

        let f : ℕ → ℕ := fun p ↦ if hp : p ∈ m.primeFactorsList then (h_all_p_tot' p hp).choose else 0
        have h_f : ∀ p ∈ m.primeFactorsList, totient p = 2 ^ (2 ^ (f p)) := by
          intro p hp
          dsimp [f]
          rw [dif_pos hp]
          exact (h_all_p_tot' p hp).choose_spec

        let E := m.primeFactorsList.map (fun p ↦ 2 ^ (f p))
        have h_tot_E : (m.primeFactorsList.map totient) = E.map (fun y ↦ 2 ^ y) := by
          dsimp [E]
          have h_gen : ∀ (L : List ℕ), (∀ p ∈ L, p ∈ m.primeFactorsList) → L.map totient = (L.map (fun p ↦ 2 ^ (f p))).map (fun y ↦ 2 ^ y) := by
            intro L hL
            induction' L with head tail ih
            · rfl
            · simp only [List.map_cons]
              have h_head : totient head = 2 ^ (2 ^ (f head)) := by
                apply h_f
                apply hL
                simp
              have h_tail : tail.map totient = (tail.map (fun p ↦ 2 ^ (f p))).map (fun y ↦ 2 ^ y) := by
                apply ih
                intro p hp
                apply hL
                simp [hp]
              rw [h_head, h_tail]
          apply h_gen m.primeFactorsList
          intro p hp
          exact hp

        have h_tot_prod : (m.primeFactorsList.map totient).prod = 2 ^ E.sum := by
          rw [h_tot_E]
          exact prod_pow_two_eq_pow_sum E

        have h_E_sum_eq : E.sum = N := by
          have h1 : 2 ^ E.sum = 2 ^ N := by
            rw [← h_tot_prod, ← h_tot_list, h_tot_eq, ← hX]
          exact (Nat.pow_right_injective (by decide)) h1

        have h_E_nodup : E.Nodup := by
          have h_inj : ∀ p1 ∈ m.primeFactorsList, ∀ p2 ∈ m.primeFactorsList, 2 ^ (f p1) = 2 ^ (f p2) → p1 = p2 := by
            intro p1 hp1 p2 hp2 heq
            have h_eq2 : 2 ^ (2 ^ (f p1)) = 2 ^ (2 ^ (f p2)) := by rw [heq]
            have h_tot1 : totient p1 = 2 ^ (2 ^ (f p1)) := h_f p1 hp1
            have h_tot2 : totient p2 = 2 ^ (2 ^ (f p2)) := h_f p2 hp2
            have h_tot_eq_p : totient p1 = totient p2 := by rw [h_tot1, h_tot2, h_eq2]
            have hp1_prime : p1.Prime := h_prime_list p1 hp1
            have hp2_prime : p2.Prime := h_prime_list p2 hp2
            have hp1_eq : p1 = totient p1 + 1 := by
              have h_tot := (totient_eq_iff_prime hp1_prime.pos).mpr hp1_prime
              have hp1_gt := hp1_prime.two_le
              omega
            have hp2_eq : p2 = totient p2 + 1 := by
              have h_tot := (totient_eq_iff_prime hp2_prime.pos).mpr hp2_prime
              have hp2_gt := hp2_prime.two_le
              omega
            rw [hp1_eq, hp2_eq, h_tot_eq_p]
          exact List.Nodup.map_on h_inj h_nodup

        have h_len : m.primeFactorsList.length ≥ 2 := by
          by_contra h_len_lt
          have h_len_cases : m.primeFactorsList.length = 0 ∨ m.primeFactorsList.length = 1 := by omega
          rcases h_len_cases with h0 | h1
          · rcases h_list_eq : m.primeFactorsList with _ | ⟨hd, tl⟩
            · have h_prod : m = 1 := by
                rw [← Nat.prod_primeFactorsList hm_ne_zero]
                rw [h_list_eq]
                rfl
              omega
            · simp [h_list_eq] at h0
          · rcases h_list_eq : m.primeFactorsList with _ | ⟨p, _ | ⟨hd2, tl2⟩⟩
            · simp [h_list_eq] at h1
            · have h_prod : m = p := by
                rw [← Nat.prod_primeFactorsList hm_ne_zero]
                rw [h_list_eq]
                simp
              have hp_mem : p ∈ m.primeFactorsList := by
                rw [h_list_eq]
                simp
              have hp_prime : p.Prime := h_prime_list p hp_mem
              rw [h_prod] at h_mprime
              exact h_mprime hp_prime
            · simp [h_list_eq] at h1

        have h_E_len : E.length ≥ 2 := by
          dsimp [E]
          rw [List.length_map]
          exact h_len

        have h_E_ne : E ≠ [] := by
          intro h_emp
          rw [h_emp] at h_E_len
          simp at h_E_len

        rcases list_min_achieved E h_E_ne with ⟨x_min, hx_min_mem, hx_min_le⟩
        rcases List.mem_iff_append.mp hx_min_mem with ⟨L1, L2, hE_eq⟩
        let E' := L1 ++ L2
        have h_E_sum : E.sum = x_min + E'.sum := by
          rw [hE_eq]
          dsimp [E']
          simp only [List.sum_append, List.sum_cons, List.sum_nil]
          omega
        have h_E_nodup_append : (L1 ++ x_min :: L2).Nodup := by
          rw [← hE_eq]
          exact h_E_nodup

        have h_xmin_mem_E : x_min ∈ E := by
          rw [hE_eq]
          simp
        rcases List.mem_map.mp h_xmin_mem_E with ⟨p_min, hp_min, h_xmin_eq⟩
        let c_min := f p_min
        have hx_min_val : x_min = 2 ^ c_min := h_xmin_eq.symm

        have h_E'_ne : E' ≠ [] := by
          intro h_E'_emp
          dsimp [E'] at h_E'_emp
          simp only [List.append_eq_nil_iff] at h_E'_emp
          rcases h_E'_emp with ⟨rfl, rfl⟩
          simp [hE_eq] at h_E_len

        have h_E'_prop : ∀ y ∈ E', ∃ c_y, y = 2 ^ c_y ∧ c_y ≥ c_min + 1 := by
          intro y hy
          have hy_E : y ∈ E := by
            rw [hE_eq]
            simp only [List.mem_append, List.mem_cons]
            dsimp [E'] at hy
            rcases List.mem_append.mp hy with hy1 | hy2
            · left; exact hy1
            · right; right; exact hy2
          have hy_ne : y ≠ x_min := by
            intro h_eq
            have h_nodup_app : (L1 ++ x_min :: L2).Nodup := h_E_nodup_append
            dsimp [E'] at hy
            rcases List.mem_append.mp hy with hL1 | hL2
            · have h_disj := List.disjoint_of_nodup_append h_nodup_app
              have h_not_mem : x_min ∉ x_min :: L2 := h_disj (by rwa [h_eq] at hL1)
              exact h_not_mem (by simp)
            · have h_nodup2 : (x_min :: L2).Nodup := List.Nodup.of_append_right h_nodup_app
              simp only [List.nodup_cons] at h_nodup2
              exact h_nodup2.1 (by rwa [h_eq] at hL2)
          rcases List.mem_map.mp hy_E with ⟨p_y, hp_y, hy_eq⟩
          let c_y := f p_y
          have hy_val : y = 2 ^ c_y := hy_eq.symm
          have h_le : x_min ≤ y := hx_min_le y hy_E
          have h_lt : x_min < y := by
            have : x_min ≠ y := hy_ne.symm
            omega
          rw [hx_min_val, hy_val] at h_lt
          have hc_lt : c_min < c_y := (Nat.pow_lt_pow_iff_right (by decide)).mp h_lt
          exact ⟨c_y, hy_val, by omega⟩

        have h_E'_div : ∀ y ∈ E', 2 ^ (c_min + 1) ∣ y := by
          intro y hy
          rcases h_E'_prop y hy with ⟨c_y, rfl, hc_y⟩
          use 2 ^ (c_y - (c_min + 1))
          rw [← pow_add]
          congr 1
          omega

        have h_E'_sum_div : 2 ^ (c_min + 1) ∣ E'.sum := dvd_sum_of_dvd_mem E' h_E'_div
        rcases h_E'_sum_div with ⟨M, h_sum_M⟩
        have h_M_pos : M > 0 := by
          by_contra h_M_zero
          have : M = 0 := by omega
          subst this
          simp at h_sum_M
          have h_E'_sum_pos : E'.sum > 0 := by
            rcases h_E'_eq : E' with _ | ⟨y, t⟩
            · contradiction
            · have : y > 0 := by
                rcases h_E'_prop y (by simp [h_E'_eq]) with ⟨c_y, rfl, _⟩
                positivity
              simp [h_E'_eq]
              omega
          omega

        have h_eq_final : 2 ^ c_min * (1 + 2 * M) = N := by
          calc
            2 ^ c_min * (1 + 2 * M) = 2 ^ c_min + 2 ^ c_min * (2 * M) := by ring
            _ = 2 ^ c_min + 2 ^ (c_min + 1) * M := by ring
            _ = x_min + E'.sum := by rw [hx_min_val, h_sum_M]
            _ = E.sum := h_E_sum.symm
            _ = N := h_E_sum_eq

        have h_dvd_final : (1 + 2 * M) ∣ N := by
          use 2 ^ c_min
          rw [mul_comm]
          exact h_eq_final.symm
        dsimp [N] at h_dvd_final
        have h_odd_final : Odd (1 + 2 * M) := by
          use M
          ring
        have h_gt_1_final : 1 < 1 + 2 * M := by omega
        have h_not_dvd_final := @odd_not_dvd_two_pow (1 + 2 * M) K h_odd_final h_gt_1_final
        exact h_not_dvd_final h_dvd_final


/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  intro N_idx N F33
  have hF33_eq : F33 = 2 ^ N + 1 := fermat_eq 33
  rw [hF33_eq]
  exact oeis_53576_conjecture_helper 33 (by decide)

