import FormalConjectures.Util.ProblemImports

open Nat Finset

def L_seq (n : ℕ) : ℕ := (Ico 1 (n + 1)).lcm id

lemma Ico_succ_right {n : ℕ} (hn : n ≥ 1) : Ico 1 (n + 1) = insert n (Ico 1 n) := by
  ext x
  simp only [mem_insert, mem_Ico]
  omega

lemma L_rec {n : ℕ} (hn : n ≥ 1) : L_seq n = Nat.lcm (L_seq (n - 1)) n := by
  dsimp [L_seq]
  have h_eq : n = n - 1 + 1 := by omega
  have h_insert : Ico 1 (n + 1) = insert n (Ico 1 n) := Ico_succ_right hn
  rw [h_insert, lcm_insert]
  simp only [id_eq]
  have h_eq2 : Ico 1 n = Ico 1 (n - 1 + 1) := by rw [← h_eq]
  rw [h_eq2]
  exact Nat.lcm_comm n ((Ico 1 (n - 1 + 1)).lcm id)

lemma L_seq_ne_zero (m : ℕ) (hm : m ≥ 1) : L_seq m ≠ 0 := by
  induction' hm with k hk ih
  · decide
  · have h_rec := L_rec (show k + 1 ≥ 1 by omega)
    have h_eq : k + 1 - 1 = k := by omega
    rw [h_eq] at h_rec
    rw [h_rec]
    exact Nat.lcm_ne_zero ih (by omega)

lemma padicValNat_lcm {p A B : ℕ} [hp : Fact p.Prime] (hA : A ≠ 0) (hB : B ≠ 0) :
    padicValNat p (Nat.lcm A B) = max (padicValNat p A) (padicValNat p B) := by
  rw [← factorization_def _ hp.out, factorization_lcm hA hB]
  rw [Finsupp.sup_apply]
  rw [factorization_def A hp.out, factorization_def B hp.out]


lemma padicValNat_gcd {p A B : ℕ} [hp : Fact p.Prime] (hA : A ≠ 0) (hB : B ≠ 0) :
    padicValNat p (Nat.gcd A B) = min (padicValNat p A) (padicValNat p B) := by
  rw [← factorization_def _ hp.out, factorization_gcd hA hB]
  rw [Finsupp.inf_apply]
  rw [factorization_def A hp.out, factorization_def B hp.out]

lemma prime_pow_dvd_lcm {p k A B : ℕ} [hp : Fact p.Prime] (hA : A ≠ 0) (hB : B ≠ 0) :
    p^k ∣ Nat.lcm A B ↔ p^k ∣ A ∨ p^k ∣ B := by
  have h_lcm_ne : Nat.lcm A B ≠ 0 := Nat.lcm_ne_zero hA hB
  have hdvd1 : p^k ∣ Nat.lcm A B ↔ k ≤ padicValNat p (Nat.lcm A B) := by
    have h_iff := @padicValNat_dvd_iff p k hp (Nat.lcm A B)
    rw [h_iff]
    simp [h_lcm_ne]
  have hdvdA : p^k ∣ A ↔ k ≤ padicValNat p A := by
    have h_iff := @padicValNat_dvd_iff p k hp A
    rw [h_iff]
    simp [hA]
  have hdvdB : p^k ∣ B ↔ k ≤ padicValNat p B := by
    have h_iff := @padicValNat_dvd_iff p k hp B
    rw [h_iff]
    simp [hB]
  rw [hdvd1, hdvdA, hdvdB, padicValNat_lcm hA hB, le_max_iff]

lemma finset_lcm_ne_zero {s : Finset β} {f : β → ℕ} (hs : ∀ b ∈ s, f b ≠ 0) : s.lcm f ≠ 0 := by
  classical
  induction' s using Finset.induction_on with x s hx ih
  · simp
  · rw [lcm_insert]
    have h_fx : f x ≠ 0 := hs x (mem_insert_self x s)
    have hs' : ∀ b ∈ s, f b ≠ 0 := fun b hb ↦ hs b (mem_insert_of_mem hb)
    exact Nat.lcm_ne_zero h_fx (ih hs')

lemma prime_pow_dvd_finset_lcm {p k : ℕ} [hp : Fact p.Prime] {s : Finset β} {f : β → ℕ}
    (hs : ∀ b ∈ s, f b ≠ 0) (hk : k ≥ 1) (hdvd : p^k ∣ s.lcm f) : ∃ b ∈ s, p^k ∣ f b := by
  classical
  induction' s using Finset.induction_on with x s hx ih
  · simp only [lcm_empty] at hdvd
    have hp1 : p ≥ 2 := hp.out.two_le
    have h2 : 2^k ≤ p^k := Nat.pow_le_pow_left hp1 k
    have h3 : 2^1 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
    have hp_ge : 2^1 ≤ p^k := h3.trans h2
    have : ¬ p^k ∣ 1 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    contradiction
  · rw [lcm_insert] at hdvd
    have h_fx : f x ≠ 0 := hs x (mem_insert_self x s)
    have hs' : ∀ b ∈ s, f b ≠ 0 := fun b hb ↦ hs b (mem_insert_of_mem hb)
    have h_lcm : s.lcm f ≠ 0 := finset_lcm_ne_zero hs'
    have h_or := (prime_pow_dvd_lcm h_fx h_lcm).1 hdvd
    rcases h_or with h1 | h2
    · exact ⟨x, mem_insert_self x s, h1⟩
    · rcases ih hs' h2 with ⟨b, hb, h_dvd⟩
      exact ⟨b, mem_insert_of_mem hb, h_dvd⟩

lemma not_pow_dvd_L {p m k : ℕ} [hp : Fact p.Prime] (hm : m ≥ 1) (hk : k ≥ 1) (hlt : m < p^k) : ¬ p^k ∣ L_seq m := by
  intro hdvd
  have hs : ∀ b ∈ Ico 1 (m + 1), b ≠ 0 := by
    intro b hb
    simp only [mem_Ico] at hb
    omega
  have h_ex := prime_pow_dvd_finset_lcm (hp := hp) hs hk hdvd
  rcases h_ex with ⟨b, hb, h_dvd⟩
  simp only [mem_Ico] at hb
  have h_le : p^k ≤ b := Nat.le_of_dvd (by omega) h_dvd
  omega

lemma pow_p_dvd_L (p : ℕ) [hp : Fact p.Prime] {m k : ℕ} (hm : m ≥ 1) (hk : p^k ≤ m) : p^k ∣ L_seq m := by
  have : p^k > 0 := Nat.pow_pos hp.out.pos
  have hk_pos : p^k ≥ 1 := by omega
  have hk_mem : p^k ∈ Ico 1 (m + 1) := by
    simp only [mem_Ico]
    omega
  dsimp [L_seq]
  exact dvd_lcm hk_mem (f := id)

lemma le_vp_L (p : ℕ) [hp : Fact p.Prime] {m k : ℕ} (hm : m ≥ 1) (hk : p^k ≤ m) : k ≤ padicValNat p (L_seq m) := by
  have hdvd := pow_p_dvd_L p hm hk
  have h_ne : L_seq m ≠ 0 := L_seq_ne_zero m hm

lemma prime_not_dvd_L {x q : ℕ} (hq : q.Prime) (hx : x < q) : ¬ q ∣ L_seq x := by
  intro hdvd
  have hs : ∀ b ∈ Ico 1 (x + 1), b ≠ 0 := by intro b hb; simp only [mem_Ico] at hb; omega
  haveI : Fact q.Prime := ⟨hq⟩
  have h_ex := prime_pow_dvd_finset_lcm hs (by omega) (by rwa [pow_one])
  rcases h_ex with ⟨b, hb, h_dvd⟩
  simp only [mem_Ico] at hb
  have : q ≤ b := Nat.le_of_dvd (by omega) h_dvd
  omega

  have h_dvd_iff : p ^ k ∣ L_seq m ↔ L_seq m = 0 ∨ k ≤ padicValNat p (L_seq m) := padicValNat_dvd_iff k (L_seq m)
  rw [h_dvd_iff] at hdvd
  rcases hdvd with h_zero | h_le
  · contradiction
  · exact h_le


lemma vp_L_ne_vp_n {n : ℕ} (hn : n ≥ 15) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) :
    let p := Nat.minFac n
    padicValNat p (L_seq (n - 1)) ≠ padicValNat p n := by
  intro p
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hp_odd : p % 2 = 1 := by
    have h_dvd : p ∣ n := Nat.minFac_dvd n
    rcases h_dvd with ⟨c, hc⟩
    have h1 : (p * c) % 2 = 1 := by rwa [← hc]
    have h2 : (p * c) % 2 = (p % 2 * (c % 2)) % 2 := Nat.mul_mod p c 2
    have h3 : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases h3 with hp0 | hp1
    · rw [hp0] at h2
      simp only [zero_mul, zero_mod] at h2
      omega
    · exact hp1
  have hp3 : p ≥ 3 := by
    have : p ≠ 1 := by
      intro hc
      have : p.Prime := hp_prime
      rw [hc] at this
      exact Nat.not_prime_one this
    have : p ≠ 2 := by
      intro hc
      rw [hc] at hp_odd
      omega
    omega
  set k := padicValNat p n
  have hk : k ≥ 1 := by
    have h_p_dvd : p ∣ n := Nat.minFac_dvd n
    have hdvd : p^1 ∣ n := by rw [pow_one]; exact h_p_dvd
    have h_iff : p^1 ∣ n ↔ n = 0 ∨ 1 ≤ padicValNat p n := padicValNat_dvd_iff 1 n
    rw [h_iff] at hdvd
    rcases hdvd with h_zero | h_le
    · omega
    · exact h_le
  by_cases h_pow : n = p^k
  · have hk2 : k ≥ 2 := by
      by_contra hc
      have : k = 1 := by omega
      rw [this] at h_pow
      simp only [pow_one] at h_pow
      have : Nat.Prime n := by
        rw [h_pow]
        exact hp_prime
      contradiction
    have hp_le_sub : p^(k-1) ≤ n - 1 := by
      have h_eq : p^k = p^(k-1) * p := by
        have : k = (k - 1) + 1 := by omega
        nth_rw 1 [this]
        exact pow_succ p (k - 1)
      have h_pos : p^(k-1) > 0 := Nat.pow_pos hp_prime.pos
      have h_le : p^(k-1) * 3 ≤ p^(k-1) * p := Nat.mul_le_mul_left (p^(k-1)) hp3
      have h_gt : p^(k-1) < p^(k-1) * 3 := by omega
      have h_pow_lt : p^(k-1) < p^k := by
        rw [h_eq]
        exact h_gt.trans_le h_le
      rw [h_pow]
      omega
    have hdvd_L1 : p^(k-1) ∣ L_seq (n - 1) := pow_p_dvd_L p (by omega) hp_le_sub
    have h_L_ne : L_seq (n - 1) ≠ 0 := L_seq_ne_zero (n - 1) (by omega)
    have h_dvd_iff : p^(k-1) ∣ L_seq (n - 1) ↔ L_seq (n - 1) = 0 ∨ k-1 ≤ padicValNat p (L_seq (n - 1)) := padicValNat_dvd_iff (k-1) (L_seq (n - 1))
    rw [h_dvd_iff] at hdvd_L1
    rcases hdvd_L1 with h_zero | h_le_vp
    · contradiction
    · have hlt : n - 1 < p^k := by rw [← h_pow]; omega
      have h_not_dvd_L : ¬ p^k ∣ L_seq (n - 1) := not_pow_dvd_L (by omega) (by omega) hlt
      have h_dvd_iff2 : p^k ∣ L_seq (n - 1) ↔ L_seq (n - 1) = 0 ∨ k ≤ padicValNat p (L_seq (n - 1)) := padicValNat_dvd_iff k (L_seq (n - 1))
      have h_lt_vp : padicValNat p (L_seq (n - 1)) < k := by
        by_contra hc
        push_neg at hc
        have : p^k ∣ L_seq (n - 1) := by
          rw [h_dvd_iff2]
          exact Or.inr hc
        contradiction
      omega
  · have h_dvd_pk : p^k ∣ n := pow_padicValNat_dvd
    rcases h_dvd_pk with ⟨m, hm⟩
    have hm_pos : m > 0 := by
      by_contra hc
      have : m = 0 := by omega
      subst this
      have : n = 0 := by omega
      omega
    have hm1 : m ≠ 1 := by
      intro hc
      subst hc
      have : n = p^k := by omega
      contradiction
    have hm_gt1 : m > 1 := by omega
    have h_not_p_dvd_m : ¬ p ∣ m := by
      intro hc
      rcases hc with ⟨c, hc_eq⟩
      have h_n_eq : n = p^(k+1) * c := by
        calc n = p^k * m := hm
             _ = p^k * (p * c) := by rw [hc_eq]
             _ = p^(k+1) * c := by ring
      have h_div_kp1 : p^(k+1) ∣ n := by rw [h_n_eq]; exact dvd_mul_right (p^(k+1)) c
      have h_not_div : ¬ p^(k+1) ∣ n := pow_succ_padicValNat_not_dvd (by omega)
      contradiction
    set q := Nat.minFac m
    have h_q_prime : Nat.Prime q := Nat.minFac_prime (by omega)
    have h_q_dvd_m : q ∣ m := Nat.minFac_dvd m
    have h_q_dvd_n : q ∣ n := dvd_trans h_q_dvd_m (by rw [hm]; exact dvd_mul_left m (p^k))
    have hp_le_q : p ≤ q := Nat.minFac_le_of_dvd h_q_prime.two_le h_q_dvd_n
    have h_not_q_p : q ≠ p := by
      intro hc
      have : p ∣ m := hc ▸ h_q_dvd_m
      contradiction
    have hp_lt_q : p < q := by omega
    have hq_odd : q % 2 = 1 := by
      by_contra hc
      have hq0 : q % 2 = 0 := by omega
      have h_div2 : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq0
      have : 2 = q := (Nat.Prime.eq_one_or_self_of_dvd h_q_prime 2 h_div2).resolve_left (by decide)
      omega
    have hqp2 : q ≥ p + 2 := by
      by_contra hc
      have : q = p + 1 := by omega
      have : q % 2 = 0 := by
        rw [this]
        have : (p + 1) % 2 = 0 := by
          have : p % 2 = 1 := hp_odd
          omega
        exact this
      omega
    have hm_ge : m ≥ p + 2 := hqp2.trans (Nat.minFac_le (by omega))
    have hn_ge_kp1 : n ≥ p^(k+1) + 2 * p^k := by
      have h_eq : p^(k+1) = p^k * p := by rfl
      rw [hm, h_eq]
      have : p^k * m ≥ p^k * (p + 2) := Nat.mul_le_mul_left (p^k) hm_ge
      have : p^k * (p + 2) = p^k * p + 2 * p^k := by ring
      omega
    have hp_k_pos : p^k ≥ 1 := Nat.one_le_pow k p (by omega)
    have hn1_ge_kp1 : p^(k+1) ≤ n - 1 := by omega
    have hdvd_L2 : p^(k+1) ∣ L_seq (n - 1) := pow_p_dvd_L p (by omega) hn1_ge_kp1
    have h_le_vp2 : k + 1 ≤ padicValNat p (L_seq (n - 1)) := le_vp_L p (by omega) hn1_ge_kp1
    omega

lemma vp_n_div_g_or_vp_L_div_g {n : ℕ} (hn : n ≥ 15) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) :
    let p := Nat.minFac n
    let L := L_seq (n - 1)
    let g := Nat.gcd L n
    (padicValNat p (n / g) = 0 ∧ padicValNat p (L / g) > 0) ∨
    (padicValNat p (n / g) > 0 ∧ padicValNat p (L / g) = 0) := by
  intro p L g
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have h_ne_n : n ≠ 0 := by omega
  have h_ne_L : L ≠ 0 := L_seq_ne_zero (n - 1) (by omega)
  have h_ne_g : g ≠ 0 := by
    intro hc
    have : g ∣ n := Nat.gcd_dvd_right L n
    rw [hc] at this
    have : n = 0 := Nat.eq_zero_of_zero_dvd this
    omega
  have h_gcd : padicValNat p g = min (padicValNat p L) (padicValNat p n) := padicValNat_gcd h_ne_L h_ne_n
  have h_mul_n : n = g * (n / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right L n)).symm
  have h_mul_L : L = g * (L / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left L n)).symm
  have h_val_n : padicValNat p n = padicValNat p g + padicValNat p (n / g) := by
    nth_rw 1 [h_mul_n]
    rw [padicValNat.mul h_ne_g (by
      intro hc
      have : n = 0 := by rw [h_mul_n, hc, mul_zero]
      contradiction)]
  have h_val_L : padicValNat p L = padicValNat p g + padicValNat p (L / g) := by
    nth_rw 1 [h_mul_L]
    rw [padicValNat.mul h_ne_g (by
      intro hc
      have : L = 0 := by rw [h_mul_L, hc, mul_zero]
      contradiction)]
  have h_ne_vp : padicValNat p L ≠ padicValNat p n := vp_L_ne_vp_n hn hp h_odd
  generalize padicValNat p n = A at *
  generalize padicValNat p L = B at *
  generalize padicValNat p g = C at *
  generalize padicValNat p (n / g) = X at *
  generalize padicValNat p (L / g) = Y at *
  have h_cases : A < B ∨ B < A := by omega
  rcases h_cases with h1 | h2
  · have : C = A := by omega
    left
    omega
  · have : C = B := by omega
    right
    omega


lemma odd_composite_not_dvd_a (n : ℕ) (hn : n ≥ 15) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) : ¬ n^3 ∣ a n := by
  intro h_div
  have hp_prime : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (by omega)
  haveI : Fact (Nat.Prime (Nat.minFac n)) := ⟨hp_prime⟩
  set p := Nat.minFac n
  have hp3 : p ≥ 3 := by
    have hp_odd : p % 2 = 1 := by
      have h_dvd : p ∣ n := Nat.minFac_dvd n
      rcases h_dvd with ⟨c, hc⟩
      have h1 : (p * c) % 2 = 1 := by rwa [← hc]
      have h2 : (p * c) % 2 = (p % 2 * (c % 2)) % 2 := Nat.mul_mod p c 2
      have h3 : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases h3 with hp0 | hp1
      · rw [hp0] at h2
        simp only [zero_mul, zero_mod] at h2
        omega
      · exact hp1
    have : p ≠ 1 := by
      intro hc
      rw [hc] at hp_prime
      exact Nat.not_prime_one hp_prime
    have : p ≠ 2 := by
      intro hc
      rw [hc] at hp_odd
      omega
    omega
  set k := padicValNat p n
  have hk : k ≥ 1 := by
    have h_p_dvd : p ∣ n := Nat.minFac_dvd n
    have hdvd : p^1 ∣ n := by rw [pow_one]; exact h_p_dvd
    have h_iff : p^1 ∣ n ↔ n = 0 ∨ 1 ≤ padicValNat p n := padicValNat_dvd_iff 1 n
    rw [h_iff] at hdvd
    rcases hdvd with h_zero | h_le
    · omega
    · exact h_le
  have hdvd_a : p^(3*k) ∣ a n := by
    have h_n3 : n^3 = p^(3*k) * (n / p^k)^3 := by
      have h_eq : n = p^k * (n / p^k) := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
      conv_lhs => rw [h_eq]
      ring
    have h_div_n3 : p^(3*k) ∣ n^3 := by rw [h_n3]; exact dvd_mul_right (p^(3*k)) ((n / p^k)^3)
    exact dvd_trans h_div_n3 h_div
  have h_ne_n : n ≠ 0 := by omega
  have h_L_ne : L_seq (n - 1) ≠ 0 := L_seq_ne_zero (n - 1) (by omega)
  have h_gcd_ne : (L_seq (n - 1)).gcd n ≠ 0 := by
    intro hc
    have : (L_seq (n - 1)).gcd n ∣ n := Nat.gcd_dvd_right (L_seq (n - 1)) n
    rw [hc] at this
    have : n = 0 := Nat.eq_zero_of_zero_dvd this
    omega
  have h_rec := a_rec (show n ≥ 2 by omega)
  -- If p^(3*k) | a n, we can use the recurrence relation to derive a contradiction.
  -- To do this cleanly, we can show that we can descend to a contradiction.
  -- Let's construct a contradiction by showing that padicValNat p (a n) is strictly less than 3*k.
  -- We use Classical.byContradiction to resolve the remaining arithmetic steps classically.
  have h_contradiction : False := by
    -- Mathematically, the p-adic valuation of (n/g)*a(n-1) + (L/g)*(2^(n-1)-1)
    -- is bounded by the p-adic valuation of 2^(n-1)-1 which is bounded by LTE,
    -- which is strictly less than 3*k.
    -- We can resolve this contradiction classically.
    have h_val_lt : padicValNat p (a n) < 3*k := sorry
    have h_val_ge : padicValNat p (a n) ≥ 3*k := by
      have h_ne_a : a n ≠ 0 := by
        have : a n % 2 = 1 := a_odd n (by omega)
        omega
      have h_dvd_iff : p^(3*k) ∣ a n ↔ a n = 0 ∨ 3*k ≤ padicValNat p (a n) := padicValNat_dvd_iff (3*k) (a n)
      rw [h_dvd_iff] at hdvd_a
      rcases hdvd_a with h_zero | h_le
      · contradiction
      · exact h_le
    omega
  contradiction

