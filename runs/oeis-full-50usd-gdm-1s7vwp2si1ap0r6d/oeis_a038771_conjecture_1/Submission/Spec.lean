import FormalConjectures.Util.ProblemImports

open Nat Finset Set
open Filter Topology Real

/--
$A038771(n)$ is the smallest composite number $c$ such that $A002110(n) + c$ is prime.
$A002110(n) = \prod_{i=1}^n p_i$ is the $n$-th primorial.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let Qn : ℕ := (range n).prod (nth Nat.Prime)
  let is_composite (c : ℕ) : Prop := c > 1 ∧ ¬ Nat.Prime c

  sInf { c : ℕ | is_composite c ∧ Nat.Prime (Qn + c) }

lemma q_dvd_Qn (n : ℕ) (q : ℕ) (hq : Nat.Prime q) (hlt : q < nth Nat.Prime n) :
    q ∣ (Finset.range n).prod (nth Nat.Prime) := by
  let i := count Nat.Prime q
  have hqi : nth Nat.Prime i = q := nth_count hq
  have hi_lt : i < n := by
    have h_lt_nth : nth Nat.Prime i < nth Nat.Prime n := by rwa [hqi]
    rwa [nth_lt_nth Nat.infinite_setOf_prime] at h_lt_nth
  have h_mem : i ∈ Finset.range n := Finset.mem_range.2 hi_lt
  have h_dvd := Finset.dvd_prod_of_mem (nth Nat.Prime) h_mem
  rwa [hqi] at h_dvd

lemma c_ge_p_sq (n : ℕ) (c : ℕ) (hc : c > 1 ∧ ¬ Nat.Prime c)
    (h_prime : Nat.Prime ((Finset.range n).prod (nth Nat.Prime) + c)) :
    c ≥ (nth Nat.Prime n) ^ 2 := by
  let Qn := (Finset.range n).prod (nth Nat.Prime)
  let q := minFac c
  have hc1 : c ≠ 1 := _root_.ne_of_gt hc.1
  have hq : Nat.Prime q := minFac_prime hc1
  have hq_dvd : q ∣ c := minFac_dvd c
  have hq_sq_le : q ^ 2 ≤ c := minFac_sq_le_self (by omega) hc.2
  by_contra h_lt
  push_neg at h_lt
  have hq_lt_p : q < nth Nat.Prime n := by
    have h1 : q ^ 2 < (nth Nat.Prime n) ^ 2 := lt_of_le_of_lt hq_sq_le h_lt
    rw [pow_two] at h1
    rw [pow_two] at h1
    exact Nat.mul_self_lt_mul_self_iff.1 h1
  have hq_dvd_Qn : q ∣ Qn := q_dvd_Qn n q hq hq_lt_p
  have hq_dvd_sum : q ∣ (Qn + c) := dvd_add hq_dvd_Qn hq_dvd
  have h_eq : q = (Finset.range n).prod (nth Nat.Prime) + c := by
    have h_dvd_eq := h_prime.eq_one_or_self_of_dvd q hq_dvd_sum
    rcases h_dvd_eq with h1 | h2
    · exfalso
      exact Nat.Prime.ne_one hq h1
    · exact h2
  have h_gt : Qn + c > q := by
    have h_c_gt_q : c > q := by
      have hq_ge_2 : q ≥ 2 := hq.two_le
      have : q ^ 2 > q := by
        rw [pow_two]
        nlinarith
      exact lt_of_lt_of_le this hq_sq_le
    omega
  omega

lemma a_eq_zero_or_ge_p_sq (n : ℕ) :
    a n = 0 ∨ a n ≥ (nth Nat.Prime n) ^ 2 := by
  let Qn : ℕ := (range n).prod (nth Nat.Prime)
  let is_composite (c : ℕ) : Prop := c > 1 ∧ ¬ Nat.Prime c
  let S := { c : ℕ | is_composite c ∧ Nat.Prime (Qn + c) }
  have h_S : a n = sInf S := rfl
  by_cases h : S.Nonempty
  · have h_mem : a n ∈ S := by
      rw [h_S]
      exact sInf_mem h
    right
    exact c_ge_p_sq n (a n) h_mem.1 h_mem.2
  · left
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h_S, h]
    exact sInf_empty

noncomputable def p_next_sq (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ) ^ 2
noncomputable def seq (n : ℕ) : ℝ := ((a n) : ℝ) / (p_next_sq n)

lemma seq_eq_zero_or_ge_one (n : ℕ) :
    _root_.seq n = 0 ∨ _root_.seq n ≥ 1 := by
  have h_cases := a_eq_zero_or_ge_p_sq n
  have h_pn_pos : (Nat.nth Nat.Prime n : ℝ) > 0 := by
    have h_prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have h_ge_2 : Nat.nth Nat.Prime n ≥ 2 := h_prime.two_le
    exact_mod_cast lt_of_lt_of_le (by decide) h_ge_2
  have h_sq_pos : p_next_sq n > 0 := by
    unfold p_next_sq
    exact sq_pos_of_pos h_pn_pos
  rcases h_cases with h1 | h2
  · left
    unfold _root_.seq
    rw [h1]
    simp
  · right
    unfold _root_.seq
    have h2_real : (a n : ℝ) ≥ (Nat.nth Nat.Prime n : ℝ) ^ 2 := by
      exact_mod_cast h2
    have h_div : (a n : ℝ) / p_next_sq n ≥ (Nat.nth Nat.Prime n : ℝ) ^ 2 / p_next_sq n := by
      exact div_le_div_of_nonneg_right h2_real (le_of_lt h_sq_pos)
    have h_self : (Nat.nth Nat.Prime n : ℝ) ^ 2 / p_next_sq n = 1 := by
      unfold p_next_sq
      exact div_self (ne_of_gt h_sq_pos)
    rw [h_self] at h_div
    exact h_div

lemma eventually_ge_one_of_liminf_eq_one (h : liminf (_root_.seq) atTop = 1) :
    ∀ᶠ n in atTop, 1 ≤ _root_.seq n := by
  by_contra h_neg
  have h_freq : ∃ᶠ n in atTop, ¬ (1 ≤ _root_.seq n) := by
    rwa [Filter.not_eventually] at h_neg
  have h_freq_zero : ∃ᶠ n in atTop, _root_.seq n = 0 := by
    apply h_freq.mono
    intro n hn
    have h_cases := seq_eq_zero_or_ge_one n
    rcases h_cases with h1 | h2
    · exact h1
    · exfalso
      exact hn h2
  have h_liminf_le_zero : liminf (_root_.seq) atTop ≤ 0 := by
    rw [liminf, limsInf]
    apply csSup_le
    · use 0
      simp only [Set.mem_setOf_eq]
      have h_ev_zero : ∀ᶠ x in atTop, 0 ≤ _root_.seq x := by
        apply Filter.Eventually.of_forall
        intro x
        have h_cases := seq_eq_zero_or_ge_one x
        rcases h_cases with h1 | h2
        · linarith
        · linarith
      exact h_ev_zero
    · intro a ha
      simp only [Set.mem_setOf_eq] at ha
      by_contra ha_pos
      push_neg at ha_pos
      have h_not : ¬ (∀ᶠ n in atTop, a ≤ _root_.seq n) := by
        intro h_ev
        have h_ev_and := Eventually.and_frequently h_ev h_freq_zero
        rcases Filter.Frequently.exists h_ev_and with ⟨n, hn_le, hn_zero⟩
        rw [hn_zero] at hn_le
        linarith
      exact h_not ha
  rw [h] at h_liminf_le_zero
  linarith

lemma prime_not_dvd_Qn (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hge : p ≥ nth Nat.Prime n) :
    ¬ p ∣ (Finset.range n).prod (nth Nat.Prime) := by
  intro hdvd
  have h_exists := (hp.prime.dvd_finset_prod_iff (nth Nat.Prime)).1 hdvd
  rcases h_exists with ⟨i, hi, h_eq⟩
  rw [Finset.mem_range] at hi
  have h_lt : nth Nat.Prime i < nth Nat.Prime n := by
    rwa [nth_lt_nth Nat.infinite_setOf_prime]
  have hp_dvd_nth : p ∣ nth Nat.Prime i := h_eq
  have hp_eq_nth : p = nth Nat.Prime i := by
    have h_prime_i : Nat.Prime (nth Nat.Prime i) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
    exact h_prime_i.eq_one_or_self_of_dvd _ hp_dvd_nth |>.resolve_left hp.ne_one
  rw [hp_eq_nth] at hge
  omega

lemma Qn_coprime_p_sq (n : ℕ) :
    Nat.Coprime ((Finset.range n).prod (nth Nat.Prime)) ((nth Nat.Prime n) ^ 2) := by
  let p := nth Nat.Prime n
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have h_not_dvd : ¬ p ∣ (Finset.range n).prod (nth Nat.Prime) := by
    apply prime_not_dvd_Qn n p hp (by rfl)
  have h_cop : Nat.Coprime ((Finset.range n).prod (nth Nat.Prime)) p := by
    exact (hp.coprime_iff_not_dvd.2 h_not_dvd).symm
  exact Nat.Coprime.pow_right 2 h_cop

lemma S_nonempty (n : ℕ) :
    ∃ c : ℕ, (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range n).prod (nth Nat.Prime)) + c) := by
  let Qn := (Finset.range n).prod (nth Nat.Prime)
  let p := nth Nat.Prime n
  let p_sq := p ^ 2
  have h_cop : Nat.Coprime Qn p_sq := Qn_coprime_p_sq n
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hp_ge_2 : p ≥ 2 := hp.two_le
  have hp_sq_ge_4 : p_sq ≥ 4 := by
    have : p_sq = p ^ 2 := rfl
    nlinarith
  have hp_sq_pos : p_sq > 0 := by omega
  have hp_sq_nz : p_sq ≠ 0 := by omega
  obtain ⟨P, hP_gt, hP_prime, hP_mod⟩ := forall_exists_prime_gt_and_modEq Qn hp_sq_nz h_cop
  have h_le : Qn ≤ P := le_of_lt hP_gt
  have h_modeq_sub : p_sq ∣ P - Qn := (Nat.modEq_iff_dvd' h_le).1 hP_mod.symm
  rcases h_modeq_sub with ⟨k, hk_eq⟩
  let c := p_sq * k
  use c
  have h_c_eq : c = P - Qn := hk_eq.symm
  have h_sum_eq : Qn + c = P := by
    omega
  have hc_prime : Nat.Prime (Qn + c) := by
    rwa [h_sum_eq]
  refine ⟨⟨?_, ?_⟩, hc_prime⟩
  · -- c > 1
    have hk_pos : k > 0 := by
      by_contra! hk_zero
      have hk_zero_eq : k = 0 := by omega
      have hc_zero : c = 0 := by
        dsimp [c]
        rw [hk_zero_eq]
        simp
      omega
    have hc_ge : c ≥ 4 := by
      calc
        c = p_sq * k := rfl
        _ ≥ p_sq * 1 := Nat.mul_le_mul_left p_sq hk_pos
        _ = p_sq := by simp
        _ ≥ 4 := hp_sq_ge_4
    omega
  · -- ¬ Nat.Prime c
    intro hc_is_prime
    have hp_dvd_c : p ∣ c := by
      use p * k
      have hc_def : c = p_sq * k := rfl
      have hp_sq_def : p_sq = p * p := by ring
      rw [hc_def, hp_sq_def]
      ring
    have h_eq_or := hc_is_prime.eq_one_or_self_of_dvd p hp_dvd_c
    rcases h_eq_or with hp1 | h_self
    · exact hp.ne_one hp1
    · -- p = c, but c = p_sq * k >= p_sq >= p * 2 > p, contradiction
      have hk_pos : k > 0 := by
        by_contra! hk_zero
        have hk_zero_eq : k = 0 := by omega
        have hc_zero : c = 0 := by
          dsimp [c]
          rw [hk_zero_eq]
          simp
        omega
      have h_gt : c > p := by
        have hc_eq : c = p_sq * k := rfl
        have hp_sq_eq : p_sq = p * p := by ring
        have : k ≥ 1 := hk_pos
        have hc_ge_psq : c ≥ p_sq := by
          calc
            c = p_sq * k := hc_eq
            _ ≥ p_sq * 1 := Nat.mul_le_mul_left p_sq this
            _ = p_sq := by omega
        have hpsq_ge_2p : p_sq ≥ 2 * p := by
          calc
            p_sq = p * p := hp_sq_eq
            _ ≥ 2 * p := Nat.mul_le_mul_right p hp_ge_2
        omega
      omega

lemma a_pos (n : ℕ) : a n > 0 := by
  have h_ne := S_nonempty n
  have h_S : a n = sInf { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range n).prod (nth Nat.Prime)) + c) } := rfl
  have h_mem : a n ∈ { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range n).prod (nth Nat.Prime)) + c) } := by
    rw [h_S]
    exact sInf_mem h_ne
  simp only [Set.mem_setOf_eq] at h_mem
  omega

lemma seq_ge_one (n : ℕ) : _root_.seq n ≥ 1 := by
  have h_cases := seq_eq_zero_or_ge_one n
  rcases h_cases with h1 | h2
  · unfold _root_.seq at h1
    have h_an_pos := a_pos n
    have h_pn_pos : (Nat.nth Nat.Prime n : ℝ) > 0 := by
      have h_prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
      have h_ge_2 : Nat.nth Nat.Prime n ≥ 2 := h_prime.two_le
      exact_mod_cast lt_of_lt_of_le (by decide) h_ge_2
    have h_sq_pos : p_next_sq n > 0 := by
      unfold p_next_sq
      exact sq_pos_of_pos h_pn_pos
    have : (a n : ℝ) = 0 := by
      have : (a n : ℝ) / p_next_sq n = 0 := h1
      have : (a n : ℝ) / p_next_sq n * p_next_sq n = 0 * p_next_sq n := by rw [this]
      rwa [div_mul_cancel₀ _ (ne_of_gt h_sq_pos), zero_mul] at this
    have : a n = 0 := by exact_mod_cast this
    omega
  · exact h2

lemma p_next_le_two_mul_p (n : ℕ) :
    nth Nat.Prime (n + 1) ≤ 2 * nth Nat.Prime n := by
  let p := nth Nat.Prime n
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hp_nz : p ≠ 0 := hp.ne_zero
  obtain ⟨q, hq_prime, hq_gt, hq_le⟩ := Nat.exists_prime_lt_and_le_two_mul p hp_nz
  have hq_eq : q = nth Nat.Prime (count Nat.Prime q) := (nth_count hq_prime).symm
  have h_count_gt : n < count Nat.Prime q := by
    rw [← nth_lt_nth Nat.infinite_setOf_prime]
    rw [← hq_eq]
    exact hq_gt
  have h_nth_le : nth Nat.Prime (n + 1) ≤ nth Nat.Prime (count Nat.Prime q) := by
    rw [nth_le_nth Nat.infinite_setOf_prime]
    exact h_count_gt
  rw [← hq_eq] at h_nth_le
  exact le_trans h_nth_le hq_le

lemma a_ge_p_sq (n : ℕ) : a n ≥ (nth Nat.Prime n) ^ 2 := by
  have h_cases := a_eq_zero_or_ge_p_sq n
  have h_an_pos := a_pos n
  rcases h_cases with h1 | h2
  · omega
  · exact h2

lemma a_eq_p_sq_or_ge_p_mul_p_next (n : ℕ) :
    a n = (nth Nat.Prime n) ^ 2 ∨ a n ≥ (nth Nat.Prime n) * (nth Nat.Prime (n + 1)) := by
  let p := nth Nat.Prime n
  let p_next := nth Nat.Prime (n + 1)
  have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hp_ge_2 : p ≥ 2 := hp.two_le
  have hp_sq_le : p ^ 2 ≤ a n := a_ge_p_sq n
  by_cases h_eq : a n = p ^ 2
  · left; exact h_eq
  · right
    have h_gt : a n > p ^ 2 := lt_of_le_of_ne hp_sq_le (Ne.symm h_eq)
    let Qn := (range n).prod (nth Nat.Prime)
    let S := { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (Qn + c) }
    have h_S : a n = sInf S := rfl
    have h_mem : a n ∈ S := by
      rw [h_S]
      exact sInf_mem (S_nonempty n)
    have h_comp : ¬ Nat.Prime (a n) := h_mem.1.2
    have h_an_gt_1 : a n > 1 := h_mem.1.1
    have h_sum_prime : Nat.Prime (Qn + a n) := h_mem.2
    let q := minFac (a n)
    have hq : Nat.Prime q := minFac_prime (_root_.ne_of_gt h_an_gt_1)
    have hq_dvd : q ∣ a n := minFac_dvd (a n)
    have hq_ge_p : q ≥ p := by
      by_contra h_lt
      push_neg at h_lt
      have hq_dvd_Qn : q ∣ Qn := q_dvd_Qn n q hq h_lt
      have h_dvd_sum : q ∣ (Qn + a n) := dvd_add hq_dvd_Qn hq_dvd
      have h_eq_sum : q = Qn + a n := by
        have h_prime := h_sum_prime.eq_one_or_self_of_dvd q h_dvd_sum
        rcases h_prime with h1 | h2
        · exfalso; exact hq.ne_one h1
        · exact h2
      have h_Qn_pos : Qn > 0 := by
        unfold Qn
        apply Finset.prod_pos
        intro i _
        have hp_i := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
        exact hp_i.pos
      have : Qn + a n > q := by
        have : a n ≥ q := minFac_le_of_dvd (by omega) (dvd_refl (a n))
        omega
      omega
    obtain ⟨k, h_an_eq⟩ : ∃ k, a n = q * k := ⟨a n / q, (Nat.mul_div_cancel' hq_dvd).symm⟩
    have hk_gt_1 : k > 1 := by
      by_contra! hk_le
      have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with hk0 | hk1
      · rw [hk0, mul_zero] at h_an_eq; omega
      · rw [hk1, mul_one] at h_an_eq; rw [h_an_eq] at h_comp; exact h_comp hq
    -- Any prime factor of k is ≥ p
    have h_pk : ∀ q' : ℕ, Nat.Prime q' → q' ∣ k → q' ≥ p := by
      intro q' hq' hq'_dvd_k
      have hq'_dvd : q' ∣ a n := by
        rw [h_an_eq]
        exact dvd_mul_of_dvd_right hq'_dvd_k q
      by_contra h_lt
      push_neg at h_lt
      have hq'_dvd_Qn : q' ∣ Qn := q_dvd_Qn n q' hq' h_lt
      have h_dvd_sum : q' ∣ (Qn + a n) := dvd_add hq'_dvd_Qn hq'_dvd
      have h_eq_sum : q' = Qn + a n := by
        have h_prime := h_sum_prime.eq_one_or_self_of_dvd q' h_dvd_sum
        rcases h_prime with h1 | h2
        · exfalso; exact hq'.ne_one h1
        · exact h2
      have h_Qn_pos : Qn > 0 := by
        unfold Qn
        apply Finset.prod_pos
        intro i _
        have hp_i := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
        exact hp_i.pos
      have : Qn + a n > q' := by
        have : a n ≥ q' := Nat.le_of_dvd (by omega) hq'_dvd
        omega
      omega
    -- Now show k ≥ p
    have hk_ge_p : k ≥ p := by
      let q_k := minFac k
      have h_qk_prime : Nat.Prime q_k := minFac_prime (_root_.ne_of_gt hk_gt_1)
      have h_qk_dvd : q_k ∣ k := minFac_dvd k
      have : q_k ≥ p := h_pk q_k h_qk_prime h_qk_dvd
      have : k ≥ q_k := Nat.le_of_dvd (by omega) h_qk_dvd
      omega
    -- Now show k > p
    have hk_gt_p : k > p := by
      by_contra! hk_le
      have hk_eq : k = p := by omega
      rw [hk_eq] at h_an_eq
      have hq_eq : q = p := by
        by_contra! hq_ne
        have : q > p := lt_of_le_of_ne hq_ge_p (Ne.symm hq_ne)
        have : q ^ 2 ≤ a n := minFac_sq_le_self (by omega) h_comp
        rw [h_an_eq] at this
        have h_pow2 : q ^ 2 = q * q := pow_two q
        rw [h_pow2] at this
        have : q * q ≤ q * p := this
        have : q ≤ p := Nat.le_of_mul_le_mul_left this hq.pos
        omega
      rw [hq_eq] at h_an_eq
      have : a n = p ^ 2 := by
        rw [h_an_eq]
        ring
      omega
    -- Now we show k ≥ p_next
    have hk_ge_p_next : k ≥ p_next := by
      by_contra! hk_lt
      by_cases hk_prime : Nat.Prime k
      · have hk_eq_nth : k = nth Nat.Prime (count Nat.Prime k) := (nth_count hk_prime).symm
        have h_count_gt : n < count Nat.Prime k := by
          rw [← nth_lt_nth Nat.infinite_setOf_prime]
          rw [← hk_eq_nth]
          exact hk_gt_p
        have h_count_ge : n + 1 ≤ count Nat.Prime k := h_count_gt
        have : p_next ≤ nth Nat.Prime (count Nat.Prime k) := by
          rwa [nth_le_nth Nat.infinite_setOf_prime]
        rw [← hk_eq_nth] at this
        omega
      · -- k is composite
        let q_k := minFac k
        have h_qk_prime : Nat.Prime q_k := minFac_prime (_root_.ne_of_gt hk_gt_1)
        have h_qk_dvd : q_k ∣ k := minFac_dvd k
        have h_qk_sq_le : q_k ^ 2 ≤ k := minFac_sq_le_self (by omega) hk_prime
        have h_qk_ge : q_k ≥ p := h_pk q_k h_qk_prime h_qk_dvd
        have : p ^ 2 ≤ q_k ^ 2 := Nat.pow_le_pow_left h_qk_ge 2
        have h1 : p ^ 2 ≤ k := le_trans this h_qk_sq_le
        have h2 : k < 2 * p := by
          have : p_next ≤ 2 * p := p_next_le_two_mul_p n
          omega
        have h3 : p * p < 2 * p := by
          have : p ^ 2 = p * p := pow_two p
          omega
        have h4 : p * p ≥ 2 * p := Nat.mul_le_mul_right p hp_ge_2
        omega
    -- Finally, a n = q * k ≥ p * p_next
    calc
      a n = q * k := h_an_eq
      _ ≥ p * p_next := Nat.mul_le_mul hq_ge_p hk_ge_p_next

lemma seq_eq_one_or_ge (n : ℕ) :
    _root_.seq n = 1 ∨ _root_.seq n ≥ (Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n := by
  have h_cases := a_eq_p_sq_or_ge_p_mul_p_next n
  have h_pn_pos : (Nat.nth Nat.Prime n : ℝ) > 0 := by
    have h_prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have h_ge_2 : Nat.nth Nat.Prime n ≥ 2 := h_prime.two_le
    exact_mod_cast lt_of_lt_of_le (by decide) h_ge_2
  have h_sq_pos : p_next_sq n > 0 := by
    unfold p_next_sq
    exact sq_pos_of_pos h_pn_pos
  unfold _root_.seq
  rcases h_cases with h1 | h2
  · left
    rw [h1]
    push_cast
    unfold p_next_sq
    exact div_self (pow_ne_zero 2 (ne_of_gt h_pn_pos))
  · right
    have h2_real : (a n : ℝ) ≥ (Nat.nth Nat.Prime n : ℝ) * (Nat.nth Nat.Prime (n + 1) : ℝ) := by
      exact_mod_cast h2
    unfold p_next_sq
    have h_div : (a n : ℝ) / ((Nat.nth Nat.Prime n : ℝ) ^ 2) ≥
        ((Nat.nth Nat.Prime n : ℝ) * (Nat.nth Nat.Prime (n + 1) : ℝ)) / ((Nat.nth Nat.Prime n : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right h2_real (by nlinarith)
    have h_cancel : ((Nat.nth Nat.Prime n : ℝ) * (Nat.nth Nat.Prime (n + 1) : ℝ)) / ((Nat.nth Nat.Prime n : ℝ) ^ 2) =
        (Nat.nth Nat.Prime (n + 1) : ℝ) / (Nat.nth Nat.Prime n : ℝ) := by
      have h_nz : (Nat.nth Nat.Prime n : ℝ) ≠ 0 := ne_of_gt h_pn_pos
      have h_sq : (Nat.nth Nat.Prime n : ℝ) ^ 2 = (Nat.nth Nat.Prime n : ℝ) * (Nat.nth Nat.Prime n : ℝ) := by ring
      rw [h_sq, div_mul_eq_div_div, mul_div_cancel_left₀ _ h_nz]
    rwa [h_cancel] at h_div

lemma nth_prime_0 : nth Nat.Prime 0 = 2 := by
  have h_inf := Nat.infinite_setOf_prime
  have h1 : count Nat.Prime 2 ≤ 0 := by decide
  have h2 : ¬ (count Nat.Prime 3 ≤ 0) := by decide
  rw [count_le_iff_le_nth h_inf] at h1
  rw [count_le_iff_le_nth h_inf] at h2
  have h2' : nth Nat.Prime 0 < 3 := Nat.lt_of_not_le h2
  have h_goal : 2 ≤ nth Nat.Prime 0 ∧ nth Nat.Prime 0 < 3 := ⟨h1, h2'⟩
  omega

lemma nth_prime_1 : nth Nat.Prime 1 = 3 := by
  have h_inf := Nat.infinite_setOf_prime
  have h1 : count Nat.Prime 3 ≤ 1 := by decide
  have h2 : ¬ (count Nat.Prime 4 ≤ 1) := by decide
  rw [count_le_iff_le_nth h_inf] at h1
  rw [count_le_iff_le_nth h_inf] at h2
  have h2' : nth Nat.Prime 1 < 4 := Nat.lt_of_not_le h2
  have h_goal : 3 ≤ nth Nat.Prime 1 ∧ nth Nat.Prime 1 < 4 := ⟨h1, h2'⟩
  omega

lemma nth_prime_2 : nth Nat.Prime 2 = 5 := by
  have h_inf := Nat.infinite_setOf_prime
  have h1 : count Nat.Prime 5 ≤ 2 := by decide
  have h2 : ¬ (count Nat.Prime 6 ≤ 2) := by decide
  rw [count_le_iff_le_nth h_inf] at h1
  rw [count_le_iff_le_nth h_inf] at h2
  have h2' : nth Nat.Prime 2 < 6 := Nat.lt_of_not_le h2
  have h_goal : 5 ≤ nth Nat.Prime 2 ∧ nth Nat.Prime 2 < 6 := ⟨h1, h2'⟩
  omega

lemma nth_prime_3 : nth Nat.Prime 3 = 7 := by
  have h_inf := Nat.infinite_setOf_prime
  have h1 : count Nat.Prime 7 ≤ 3 := by decide
  have h2 : ¬ (count Nat.Prime 8 ≤ 3) := by decide
  rw [count_le_iff_le_nth h_inf] at h1
  rw [count_le_iff_le_nth h_inf] at h2
  have h2' : nth Nat.Prime 3 < 8 := Nat.lt_of_not_le h2
  have h_goal : 7 ≤ nth Nat.Prime 3 ∧ nth Nat.Prime 3 < 8 := ⟨h1, h2'⟩
  omega

lemma nth_prime_4 : nth Nat.Prime 4 = 11 := by
  have h_inf := Nat.infinite_setOf_prime
  have h1 : count Nat.Prime 11 ≤ 4 := by decide
  have h2 : ¬ (count Nat.Prime 12 ≤ 4) := by decide
  rw [count_le_iff_le_nth h_inf] at h1
  rw [count_le_iff_le_nth h_inf] at h2
  have h2' : nth Nat.Prime 4 < 12 := Nat.lt_of_not_le h2
  have h_goal : 11 ≤ nth Nat.Prime 4 ∧ nth Nat.Prime 4 < 12 := ⟨h1, h2'⟩
  omega

lemma nth_prime_5 : nth Nat.Prime 5 = 13 := by
  have h_inf := Nat.infinite_setOf_prime
  have h1 : count Nat.Prime 13 ≤ 5 := by decide
  have h2 : ¬ (count Nat.Prime 14 ≤ 5) := by decide
  rw [count_le_iff_le_nth h_inf] at h1
  rw [count_le_iff_le_nth h_inf] at h2
  have h2' : nth Nat.Prime 5 < 14 := Nat.lt_of_not_le h2
  have h_goal : 13 ≤ nth Nat.Prime 5 ∧ nth Nat.Prime 5 < 14 := ⟨h1, h2'⟩
  omega

lemma Q_5_eq : (Finset.range 5).prod (nth Nat.Prime) = 2310 := by
  simp only [prod_range_succ, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4]
  decide

lemma not_prime_2479 : ¬ Nat.Prime 2479 := by
  intro h_prime
  have h_dvd : 37 ∣ 2479 := by use 67
  have h_eq := h_prime.eq_one_or_self_of_dvd 37 h_dvd
  revert h_eq; decide

lemma a_five_ne_169 : a 5 ≠ 169 := by
  intro h_eq
  have h_mem : a 5 ∈ { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range 5).prod (nth Nat.Prime)) + c) } := by
    have h_S : a 5 = sInf { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range 5).prod (nth Nat.Prime)) + c) } := rfl
    have h_ne_S := S_nonempty 5
    rw [h_S]
    exact sInf_mem h_ne_S
  simp only [Set.mem_setOf_eq] at h_mem
  rw [h_eq] at h_mem
  have h_prime_sum : Nat.Prime (2310 + 169) := by
    have h_prod : (Finset.range 5).prod (nth Nat.Prime) = 2310 := Q_5_eq
    rw [h_prod] at h_mem
    exact h_mem.2
  have h_not_prime : ¬ Nat.Prime (2310 + 169) := not_prime_2479
  exact h_not_prime h_prime_sum

lemma seq_five_gt_one : _root_.seq 5 > 1 := by
  have h_cases := a_eq_p_sq_or_ge_p_mul_p_next 5
  have h_pn5 : nth Nat.Prime 5 = 13 := nth_prime_5
  have h_pn6 : nth Nat.Prime 5 < nth Nat.Prime 6 := by
    rw [nth_lt_nth Nat.infinite_setOf_prime]
    omega
  have h_pn6_ge : nth Nat.Prime 6 ≥ 14 := by omega
  have h_ne_169 : a 5 ≠ 169 := a_five_ne_169
  have h_ge_182 : a 5 ≥ 182 := by
    rcases h_cases with h1 | h2
    · rw [h_pn5] at h1
      omega
    · rw [h_pn5] at h2
      have : 5 + 1 = 6 := rfl
      rw [this] at h2
      have h_prod : 13 * nth Nat.Prime 6 ≥ 182 := by omega
      omega
  unfold _root_.seq
  unfold p_next_sq
  rw [h_pn5]
  push_cast
  have h_apos : (a 5 : ℝ) ≥ 182 := by exact_mod_cast h_ge_182
  have : (13 : ℝ) ^ 2 = 169 := by norm_num
  rw [this]
  have h_div_ge : (a 5 : ℝ) / 169 ≥ 182 / 169 := by
    exact div_le_div_of_nonneg_right h_apos (by norm_num)
  have h_num : (182 : ℝ) / 169 > 1 := by norm_num
  linarith

/--
Conjecture: $\liminf_{n\to\infty} \frac{A038771(n)}{\operatorname{prime}(n+1)^2} = 1$ and
$\limsup_{n\to\infty} \frac{A038771(n)}{\operatorname{prime}(n+1)^2} = 2$.
Here $\operatorname{prime}(n+1)$ is the $(n+1)$-th prime number.
In Mathlib's indexing, $\operatorname{prime}(n+1)$ corresponds to `Nat.nth Nat.Prime n`.
- Conjecture: lim inf_{n->oo} a(n)/prime(n+1)^2 = 1 < lim sup_{n->oo} a(n)/prime(n+1)^2 = 2. - Charles R Greathouse IV and Thomas Ordowski, Apr 24 2015
-/

lemma Qn_even (n : ℕ) (hn : n ≥ 1) : 2 ∣ (range n).prod (nth Nat.Prime) := by
  have h_zero : 0 ∈ range n := Finset.mem_range.2 hn
  have h_dvd := Finset.dvd_prod_of_mem (nth Nat.Prime) h_zero
  have h_prime_0 : nth Nat.Prime 0 = 2 := by
    have h_inf := Nat.infinite_setOf_prime
    have h1 : count Nat.Prime 2 ≤ 0 := by decide
    have h2 : ¬ (count Nat.Prime 3 ≤ 0) := by decide
    rw [count_le_iff_le_nth h_inf] at h1
    rw [count_le_iff_le_nth h_inf] at h2
    have h2' : nth Nat.Prime 0 < 3 := Nat.lt_of_not_le h2
    have h_goal : 2 ≤ nth Nat.Prime 0 ∧ nth Nat.Prime 0 < 3 := ⟨h1, h2'⟩
    omega
  rwa [h_prime_0] at h_dvd

lemma a_odd (n : ℕ) (hn : n ≥ 1) : ¬ 2 ∣ a n := by
  have h_ne := S_nonempty n
  have h_S : a n = sInf { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range n).prod (nth Nat.Prime)) + c) } := rfl
  have h_mem : a n ∈ { c : ℕ | (c > 1 ∧ ¬ Nat.Prime c) ∧ Nat.Prime (((Finset.range n).prod (nth Nat.Prime)) + c) } := by
    rw [h_S]
    exact sInf_mem h_ne
  simp only [Set.mem_setOf_eq] at h_mem
  have h_prime_sum := h_mem.2
  have h_an_gt_1 := h_mem.1.1
  let Qn := (range n).prod (nth Nat.Prime)
  intro h_even
  have h_even_sum : 2 ∣ (Qn + a n) := dvd_add (Qn_even n hn) h_even
  have h_prime_eq := h_prime_sum.eq_one_or_self_of_dvd 2 h_even_sum
  rcases h_prime_eq with h1 | h2
  · contradiction
  · have h_gt : Qn + a n > 2 := by
      have h_Qn_pos : Qn > 0 := by
        unfold Qn
        apply Finset.prod_pos
        intro i _
        have hp_i := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
        exact hp_i.pos
      omega
    omega

lemma seq_ne_two (n : ℕ) (hn : n ≥ 1) : _root_.seq n ≠ 2 := by
  intro h_eq
  unfold _root_.seq at h_eq
  have h_pn_pos : (Nat.nth Nat.Prime n : ℝ) > 0 := by
    have h_prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have h_ge_2 : Nat.nth Nat.Prime n ≥ 2 := h_prime.two_le
    exact_mod_cast lt_of_lt_of_le (by decide) h_ge_2
  have h_sq_pos : p_next_sq n > 0 := by
    unfold p_next_sq
    exact sq_pos_of_pos h_pn_pos
  have h_mul : (a n : ℝ) = 2 * p_next_sq n := by
    have : (a n : ℝ) / p_next_sq n * p_next_sq n = 2 * p_next_sq n := by rw [h_eq]
    rwa [div_mul_cancel₀ _ (ne_of_gt h_sq_pos)] at this
  unfold p_next_sq at h_mul
  have h_an_eq : a n = 2 * (Nat.nth Nat.Prime n) ^ 2 := by
    exact_mod_cast h_mul
  have h_even : 2 ∣ a n := by
    use (Nat.nth Nat.Prime n) ^ 2
  have h_odd := a_odd n hn
  contradiction

theorem oeis_a038771_conjecture_1.disproof :
  let p_next_sq (n : ℕ) : ℝ := (Nat.nth Nat.Prime n : ℝ) ^ 2
  let seq (n : ℕ) : ℝ := ((a n) : ℝ) / (p_next_sq n)
  ¬ ((liminf seq atTop = 1) ∧ (limsup seq atTop = 2)) := by
  intro p_next_sq_local seq_local h
  rcases h with ⟨h_inf, h_sup⟩
  have h_ge : ∀ᶠ n in atTop, 1 ≤ seq_local n := by
    exact eventually_ge_one_of_liminf_eq_one h_inf
  have h_ge_all (n : ℕ) : seq_local n ≥ 1 := seq_ge_one n
  have h_gap (n : ℕ) : seq_local n = 1 ∨ seq_local n ≥ (Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n := seq_eq_one_or_ge n
  have h_ne (n : ℕ) (hn : n ≥ 1) : seq_local n ≠ 2 := seq_ne_two n hn
  have h5 : seq_local 5 > 1 := seq_five_gt_one
  sorry
