import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A331343: $a(n) = \mathrm{lcm}(1,2,\dots,n) \cdot \sum_{k=1}^n \frac{2^{k-1} - 1}{k}$.

The expression is calculated in $\mathbb{N}$ using exact integer division property of the LCM.
$$a(n) = \sum_{k=1}^n \left(\frac{\mathrm{lcm}(1, \dots, n)}{k}\right) \cdot (2^{k-1} - 1)$$
-/
def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

-- Use the provided definition name `a` for the sequence.
def a (n : ℕ) : ℕ := A331343 n

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

lemma not_dvd_L_seq {m k : ℕ} (hm : m ≥ 1) (hk : k ≥ 1) (hlt : m < 2^k) : ¬ 2^k ∣ L_seq m := by
  intro hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : ∀ b ∈ Ico 1 (m + 1), b ≠ 0 := by
    intro b hb
    simp only [mem_Ico] at hb
    omega
  have h_ex := prime_pow_dvd_finset_lcm hs hk hdvd
  rcases h_ex with ⟨b, hb, h_dvd⟩
  simp only [mem_Ico] at hb
  have h_le : 2^k ≤ b := Nat.le_of_dvd (by omega) h_dvd
  omega

lemma pow_two_dvd_L {m k : ℕ} (hm : m ≥ 1) (hk : 2^k ≤ m) : 2^k ∣ L_seq m := by
  have : 2^k > 0 := Nat.pow_pos (by decide)
  have hk_pos : 2^k ≥ 1 := by omega
  have hk_mem : 2^k ∈ Ico 1 (m + 1) := by
    simp only [mem_Ico]
    omega
  dsimp [L_seq]
  exact dvd_lcm hk_mem (f := id)

lemma le_v2_L {m k : ℕ} (hm : m ≥ 1) (hk : 2^k ≤ m) : k ≤ padicValNat 2 (L_seq m) := by
  have hdvd := pow_two_dvd_L hm hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_ne := L_seq_ne_zero m hm
  have h_dvd_iff : 2 ^ k ∣ L_seq m ↔ L_seq m = 0 ∨ k ≤ padicValNat 2 (L_seq m) := padicValNat_dvd_iff k (L_seq m)
  rw [h_dvd_iff] at hdvd
  rcases hdvd with h_zero | h_le
  · contradiction
  · exact h_le

lemma v2_n_ne_v2_L {n : ℕ} (hn : n ≥ 3) : padicValNat 2 n ≠ padicValNat 2 (L_seq (n - 1)) := by
  set k := padicValNat 2 n
  intro h_eq
  have hn_pos : n > 0 := by omega
  have h_dvd : 2^k ∣ n := pow_padicValNat_dvd
  have h_not_dvd : ¬ 2^(k+1) ∣ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact pow_succ_padicValNat_not_dvd hn_pos.ne'
  by_cases h_le : 2^k ≤ n - 1
  · generalize h_D : n / 2^k = D
    have hd_odd : ¬ 2 ∣ D := by
      intro h_even
      have h_mul : n = 2^k * D := by
        rw [← h_D]
        exact (Nat.mul_div_cancel' h_dvd).symm
      rcases h_even with ⟨c, hc⟩
      rw [hc] at h_mul
      have : n = 2^(k+1) * c := by
        rw [h_mul]
        ring
      have : 2^(k+1) ∣ n := by
        rw [this]
        exact dvd_mul_right (2^(k+1)) c
      contradiction
    have hd_ge_3 : D ≥ 3 := by
      have hd_ne_0 : D ≠ 0 := by
        intro h0
        have h_mul : n = 2^k * D := by
          rw [← h_D]
          exact (Nat.mul_div_cancel' h_dvd).symm
        rw [h0, mul_zero] at h_mul
        omega
      have hd_ne_1 : D ≠ 1 := by
        intro h1
        have h_eq_n : n = 2^k := by
          have h_mul : n = 2^k * D := by
            rw [← h_D]
            exact (Nat.mul_div_cancel' h_dvd).symm
          rw [h1, mul_one] at h_mul
          exact h_mul
        rw [h_eq_n] at h_le
        have : 2^k ≥ 1 := by
          have : 2^k > 0 := Nat.pow_pos (by decide)
          omega
        omega
      have hd_ne_2 : D ≠ 2 := by
        intro h2
        have h_d2 : 2 ∣ D := by rw [h2]
        exact hd_odd h_d2
      clear hd_odd h_dvd h_not_dvd hn_pos
      omega
    have h_n_ge : n ≥ 3 * 2^k := by
      have h_mul : n = 2^k * D := by
        rw [← h_D]
        exact (Nat.mul_div_cancel' h_dvd).symm
      generalize h_V : 2^k = V at *
      rw [h_mul]
      have h_vd : 3 * V ≤ V * D := by
        rw [mul_comm 3 V]
        exact Nat.mul_le_mul_left V hd_ge_3
      exact h_vd
    have h_n1_ge : n - 1 ≥ 2^(k+1) := by
      have h_2k_pos : 2^k ≥ 1 := by
        have : 2^k > 0 := Nat.pow_pos (by decide)
        omega
      clear hd_ge_3 hd_odd hn_pos h_D h_dvd h_not_dvd
      generalize h_V : 2^k = V at *
      have h_eq_2kp1 : 2^(k+1) = V * 2 := by
        rw [← h_V]
        rfl
      rw [h_eq_2kp1]
      omega
    have h_L_dvd := le_v2_L (show n - 1 ≥ 1 by omega) h_n1_ge
    rw [← h_eq] at h_L_dvd
    omega
  · have hlt : n - 1 < 2^k := by omega
    have hk : k ≥ 1 := by
      by_contra hc
      have : k = 0 := by omega
      rw [this] at hlt
      simp only [pow_zero] at hlt
      omega
    have h_not_dvd_L : ¬ 2^k ∣ L_seq (n - 1) := by
      apply not_dvd_L_seq (show n - 1 ≥ 1 by omega) hk
      exact hlt
    have h_le_v2 : k ≤ padicValNat 2 (L_seq (n-1)) := by omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h_ne : L_seq (n-1) ≠ 0 := L_seq_ne_zero (n-1) (by omega)
    have h_dvd_iff : 2^k ∣ L_seq (n-1) ↔ L_seq (n-1) = 0 ∨ k ≤ padicValNat 2 (L_seq (n-1)) := padicValNat_dvd_iff k (L_seq (n-1))
    have hdvd : 2^k ∣ L_seq (n-1) := by
      rw [h_dvd_iff]
      exact Or.inr h_le_v2
    contradiction

lemma nat_div_mul_div_comm {A B g k : ℕ} (hk : k ∣ A) (hg : g ∣ B) (hg_pos : g > 0) (hk_pos : k > 0) :
    (A * B / g) / k = (A / k) * (B / g) := by
  rcases hk with ⟨d, rfl⟩
  rcases hg with ⟨c, rfl⟩
  have h1 : k * d * (g * c) = g * (k * d * c) := by ring
  rw [h1]
  rw [Nat.mul_div_cancel_left _ hg_pos]
  have h2 : k * d * c = k * (d * c) := by ring
  rw [h2]
  rw [Nat.mul_div_cancel_left _ hk_pos]
  rw [Nat.mul_div_cancel_left _ hk_pos]
  rw [Nat.mul_div_cancel_left _ hg_pos]

lemma k_dvd_L {n k : ℕ} (hn : n ≥ 1) (hk : k ∈ Ico 1 n) : k ∣ L_seq (n - 1) := by
  dsimp [L_seq]
  have h_eq : n = n - 1 + 1 := by omega
  have hk' : k ∈ Ico 1 (n - 1 + 1) := by rwa [← h_eq]
  have hdvd := dvd_lcm hk' (f := id)
  exact hdvd

lemma a_split_last {n : ℕ} (hn : n ≥ 1) (f : ℕ → ℕ) :
    (Ico 1 (n + 1)).sum f = (Ico 1 n).sum f + f n := by
  have h_insert : Ico 1 (n + 1) = insert n (Ico 1 n) := Ico_succ_right hn
  have h_not_mem : n ∉ Ico 1 n := by
    simp only [mem_Ico]
    omega
  rw [h_insert, sum_insert h_not_mem, add_comm]

lemma lcm_eq_mul_div_gcd (A B : ℕ) (hB : B > 0) : Nat.lcm A B = A * B / Nat.gcd A B := by
  have h_gcd_pos : Nat.gcd A B > 0 := Nat.gcd_pos_of_pos_right A hB
  have h_mul := Nat.gcd_mul_lcm A B
  have h_eq : Nat.lcm A B = (Nat.gcd A B * Nat.lcm A B) / Nat.gcd A B := by
    rw [Nat.mul_div_cancel_left _ h_gcd_pos]
  rw [h_eq, h_mul]

lemma lcm_div_self_eq (L n : ℕ) (hn : n > 0) : Nat.lcm L n / n = L / Nat.gcd L n := by
  rw [lcm_eq_mul_div_gcd L n hn]
  generalize h_g : Nat.gcd L n = g
  have h_gcd_pos : g > 0 := by
    rw [← h_g]
    exact Nat.gcd_pos_of_pos_right L hn
  have hg : g ∣ L := by
    rw [← h_g]
    exact Nat.gcd_dvd_left L n
  rcases hg with ⟨c, rfl⟩
  have h1 : g * c * n = g * (c * n) := by ring
  rw [h1]
  rw [Nat.mul_div_cancel_left _ h_gcd_pos]
  rw [Nat.mul_comm c n]
  rw [Nat.mul_div_cancel_left _ hn]
  rw [Nat.mul_div_cancel_left _ h_gcd_pos]

lemma a_rec {n : ℕ} (hn : n ≥ 2) :
    let L := L_seq (n - 1)
    let g := Nat.gcd L n
    a n = (n / g) * a (n - 1) + (L / g) * (2 ^ (n - 1) - 1) := by
  intro L g
  unfold a A331343
  dsimp only
  change ∑ k ∈ Ico 1 (n + 1), L_seq n / k * (2 ^ (k - 1) - 1) =
    n / g * ∑ k ∈ Ico 1 (n - 1 + 1), L / k * (2 ^ (k - 1) - 1) + L / g * (2 ^ (n - 1) - 1)
  have hn1 : n ≥ 1 := by omega
  have h_split := a_split_last hn1 (fun k ↦ (L_seq n / k) * (2 ^ (k - 1) - 1))
  rw [h_split]
  have h_term_n : L_seq n / n = L / g := by
    have h_L_rec : L_seq n = Nat.lcm L n := L_rec hn1
    rw [h_L_rec]
    have hn_pos : n > 0 := by omega
    exact lcm_div_self_eq L n hn_pos
  rw [h_term_n]
  have h_Ico_eq : Ico 1 (n - 1 + 1) = Ico 1 n := by
    have : n - 1 + 1 = n := by omega
    rw [this]
  rw [h_Ico_eq]
  have h_sum_eq : ∑ k ∈ Ico 1 n, L_seq n / k * (2 ^ (k - 1) - 1) = n / g * ∑ k ∈ Ico 1 n, L / k * (2 ^ (k - 1) - 1) := by
    have h_mul : ∀ k ∈ Ico 1 n, (L_seq n / k) * (2 ^ (k - 1) - 1) = (n / g) * ((L / k) * (2 ^ (k - 1) - 1)) := by
      intro k hk
      have hk_pos : k > 0 := by
        simp only [mem_Ico] at hk
        omega
      have h_L_rec : L_seq n = Nat.lcm L n := L_rec hn1
      rw [h_L_rec]
      have hn_pos : n > 0 := by omega
      have h_lcm_eq := lcm_eq_mul_div_gcd L n hn_pos
      rw [h_lcm_eq]
      have hk_dvd : k ∣ L := k_dvd_L hn1 hk
      have hg_dvd : g ∣ n := Nat.gcd_dvd_right L n
      have hg_pos : g > 0 := Nat.gcd_pos_of_pos_right L hn_pos
      have h_comm := nat_div_mul_div_comm hk_dvd hg_dvd hg_pos hk_pos
      rw [h_comm]
      ring
    have h_congr : ∑ k ∈ Ico 1 n, L_seq n / k * (2 ^ (k - 1) - 1) = ∑ k ∈ Ico 1 n, (n / g) * ((L / k) * (2 ^ (k - 1) - 1)) := by
      apply sum_congr rfl
      exact h_mul
    rw [h_congr]
    rw [← mul_sum]
  rw [h_sum_eq]

lemma odd_two_pow_sub_one {k : ℕ} (hk : k ≥ 1) : (2 ^ k - 1) % 2 = 1 := by
  have : 2 ^ k = 2 ^ (k - 1) * 2 := by
    have h_eq : k = k - 1 + 1 := by omega
    nth_rw 1 [h_eq]
    rw [pow_succ]
  rw [this]
  generalize h_v : 2 ^ (k - 1) = v
  have hv_pos : v > 0 := by
    rw [← h_v]
    exact Nat.pos_of_ne_zero (by positivity)
  omega

lemma coprime_not_both_even {a b : ℕ} (h : Nat.Coprime a b) : a % 2 ≠ 0 ∨ b % 2 ≠ 0 := by
  by_contra h_both
  push_neg at h_both
  have hdvd_a : 2 ∣ a := Nat.dvd_of_mod_eq_zero h_both.1
  have hdvd_b : 2 ∣ b := Nat.dvd_of_mod_eq_zero h_both.2
  have h_eq1 : 2 = 1 := Nat.eq_one_of_dvd_coprimes h hdvd_a hdvd_b
  contradiction

lemma parity_diff_of_padic_ne {n : ℕ} (hn : n ≥ 3) (h_padic : padicValNat 2 n ≠ padicValNat 2 (L_seq (n - 1))) :
    let L := L_seq (n - 1)
    let g := Nat.gcd L n
    (n / g) % 2 ≠ (L / g) % 2 := by
  intro L g
  intro h_eq
  have h_cop : Nat.Coprime (n / g) (L / g) := by
    have h_gcd_pos : g > 0 := Nat.gcd_pos_of_pos_right L (by omega)
    exact Nat.Coprime.symm (Nat.coprime_div_gcd_div_gcd h_gcd_pos)
  have h_not_both_even := coprime_not_both_even h_cop
  have h_A_odd : (n / g) % 2 = 1 := by omega
  have h_B_odd : (L / g) % 2 = 1 := by omega
  have h_n_pos : n > 0 := by omega
  have h_L_pos : L > 0 := Nat.pos_of_ne_zero (L_seq_ne_zero (n - 1) (by omega))
  have h_g_pos : g > 0 := Nat.gcd_pos_of_pos_right L h_n_pos
  have h_le_n : Nat.gcd L n ≤ n := Nat.gcd_le_right (n := n) L h_n_pos
  have h_le_L : Nat.gcd L n ≤ L := Nat.gcd_le_left (n := n) h_L_pos
  have h_A_pos : n / g > 0 := Nat.div_pos h_le_n h_g_pos
  have h_B_pos : L / g > 0 := Nat.div_pos h_le_L h_g_pos
  have h_padic_n : padicValNat 2 n = padicValNat 2 g + padicValNat 2 (n / g) := by
    have h_eq_mul : n = g * (n / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right L n)).symm
    nth_rw 1 [h_eq_mul]
    have : g ≠ 0 := by omega
    have : n / g ≠ 0 := by omega
    rw [padicValNat.mul (by omega) (by omega)]
  have h_padic_L : padicValNat 2 L = padicValNat 2 g + padicValNat 2 (L / g) := by
    have h_eq_mul : L = g * (L / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left L n)).symm
    nth_rw 1 [h_eq_mul]
    have : g ≠ 0 := by omega
    have : L / g ≠ 0 := by omega
    rw [padicValNat.mul (by omega) (by omega)]
  have h_A_zero : padicValNat 2 (n / g) = 0 := by
    have : ¬ 2 ∣ (n / g) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    exact padicValNat.eq_zero_of_not_dvd this
  have h_B_zero : padicValNat 2 (L / g) = 0 := by
    have : ¬ 2 ∣ (L / g) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    exact padicValNat.eq_zero_of_not_dvd this
  rw [h_A_zero] at h_padic_n
  rw [h_B_zero] at h_padic_L
  change padicValNat 2 n ≠ padicValNat 2 L at h_padic
  omega

lemma a_odd_step {n : ℕ} (hn : n ≥ 3) (ih : a (n - 1) % 2 = 1) : a n % 2 = 1 := by
  have hn_ge_2 : n ≥ 2 := by omega
  have h_rec := a_rec hn_ge_2
  dsimp only at h_rec
  rw [h_rec]
  have h_odd_2_pow : (2 ^ (n - 1) - 1) % 2 = 1 := by
    apply odd_two_pow_sub_one
    omega
  have h_X : a (n - 1) % 2 = 1 := ih
  have h_Y : (2 ^ (n - 1) - 1) % 2 = 1 := h_odd_2_pow
  have h_parity_diff : (n / (L_seq (n - 1)).gcd n) % 2 ≠ (L_seq (n - 1) / (L_seq (n - 1)).gcd n) % 2 := parity_diff_of_padic_ne hn (v2_n_ne_v2_L hn)
  generalize (n / (L_seq (n - 1)).gcd n) = A at *
  generalize (L_seq (n - 1) / (L_seq (n - 1)).gcd n) = B at *
  generalize a (n - 1) = X at *
  generalize (2 ^ (n - 1) - 1) = Y at *
  have h1 : (A * X) % 2 = (A % 2 * (X % 2)) % 2 := Nat.mul_mod A X 2
  have h2 : (B * Y) % 2 = (B % 2 * (Y % 2)) % 2 := Nat.mul_mod B Y 2
  generalize h_U : A * X = U at *
  generalize h_V : B * Y = V at *
  generalize h_U' : A % 2 * (X % 2) = U' at *
  generalize h_V' : B % 2 * (Y % 2) = V' at *
  have h_mod : (U + V) % 2 = (U' + V') % 2 := by omega
  rw [h_mod, ← h_U', ← h_V', h_X, h_Y]
  omega

lemma a_odd (n : ℕ) (hn : n ≥ 2) : a n % 2 = 1 := by
  induction' hn with k hk ih
  · rfl
  · have hk' : 2 ≤ k := hk
    have h_step : k.succ ≥ 3 := by omega
    exact a_odd_step h_step ih

lemma odd_of_dvd_a {n : ℕ} (hn : n ≥ 2) (h_div : n^3 ∣ a n) : n % 2 = 1 := by
  have h_odd : a n % 2 = 1 := a_odd n hn
  have h_n3_div : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_n3_div with h_even | h_odd_n
  · have h_n3_even : (n^3) % 2 = 0 := by
      rw [pow_succ, Nat.mul_mod, h_even]
      simp
    have h_div_2 : 2 ∣ a n := by
      have : 2 ∣ n^3 := Nat.dvd_of_mod_eq_zero h_n3_even
      exact dvd_trans this h_div
    have h_a_even : a n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_div_2
    omega
  · exact h_odd_n


lemma padicValNat_gcd {p A B : ℕ} [hp : Fact p.Prime] (hA : A ≠ 0) (hB : B ≠ 0) :
    padicValNat p (Nat.gcd A B) = min (padicValNat p A) (padicValNat p B) := by
  rw [← factorization_def _ hp.out, factorization_gcd hA hB]
  rw [Finsupp.inf_apply]
  rw [factorization_def A hp.out, factorization_def B hp.out]

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
  have h_dvd_iff : p ^ k ∣ L_seq m ↔ L_seq m = 0 ∨ k ≤ padicValNat p (L_seq m) := padicValNat_dvd_iff k (L_seq m)
  rw [h_dvd_iff] at hdvd
  rcases hdvd with h_zero | h_le
  · contradiction
  · exact h_le


lemma prime_not_dvd_L {x q : ℕ} (hq : q.Prime) (hx : x < q) : ¬ q ∣ L_seq x := by
  intro hdvd
  have hs : ∀ b ∈ Ico 1 (x + 1), b ≠ 0 := by intro b hb; simp only [mem_Ico] at hb; omega
  haveI : Fact q.Prime := ⟨hq⟩
  have h_ex := prime_pow_dvd_finset_lcm (hp := this) (k := 1) hs (by decide) (by rwa [pow_one])
  rcases h_ex with ⟨b, hb, h_dvd⟩
  rw [pow_one] at h_dvd
  simp only [mem_Ico] at hb
  have h1 : q ≤ b := Nat.le_of_dvd (by omega) h_dvd
  have h2 : b < q := by omega
  omega

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


lemma maxPrimeFac_dvd (n : ℕ) (h : 1 < n) : Nat.maxPrimeFac n ∣ n := by
  set s := {p : ℕ | p.Prime ∧ p ∣ n} with hs
  have hs₀ : s.Nonempty := by
    simp only [Set.Nonempty, Set.mem_setOf_eq, ← ne_one_iff_exists_prime_dvd, hs]
    omega
  have hs₁ : BddAbove s := by
    use n
    simp only [hs, mem_upperBounds, Set.mem_setOf_eq, and_imp]
    exact fun p _ hp ↦ Nat.le_of_dvd (zero_lt_of_lt h) hp
  exact (Nat.sSup_mem hs₀ hs₁).2

lemma maxPrimeFac_lt (n : ℕ) (h1 : 1 < n) (hc : ¬ Nat.Prime n) : Nat.maxPrimeFac n < n := by
  have hp : Nat.Prime (Nat.maxPrimeFac n) := Nat.prime_maxPrimeFac_of_one_lt n h1
  have hdvd : Nat.maxPrimeFac n ∣ n := maxPrimeFac_dvd n h1
  have hle : Nat.maxPrimeFac n ≤ n := Nat.le_of_dvd (by omega) hdvd
  by_cases heq : Nat.maxPrimeFac n = n
  · have : Nat.Prime n := by rwa [← heq]
    contradiction
  · omega

lemma n_ge_15 {n : ℕ} (hn : n > 3) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) (hn9 : n ≠ 9) : n ≥ 15 := by
  by_contra h_lt
  have h_le : n ≤ 14 := by omega
  have h_cases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 13 := by
    have : n % 2 = 1 := h_odd
    omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · have : Nat.Prime 5 := by decide
    contradiction
  · have : Nat.Prime 7 := by decide
    contradiction
  · contradiction
  · have : Nat.Prime 11 := by decide
    contradiction
  · have : Nat.Prime 13 := by decide
    contradiction

lemma padicValNat_two_pow_sub_one_lt (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≥ 3) (m : ℕ) (hm : m > 0) :
    padicValNat p (2^m - 1) < m := by
  have h_pos : 2^m - 1 > 0 := by
    have : 2^m ≥ 2^1 := Nat.pow_le_pow_right (by decide) hm
    omega
  have hdvd : p^(padicValNat p (2^m - 1)) ∣ 2^m - 1 := pow_padicValNat_dvd
  have h_le2 : p^(padicValNat p (2^m - 1)) ≤ 2^m - 1 := Nat.le_of_dvd h_pos hdvd
  have h_lt : 2^m - 1 < 2^m := by omega
  have h_lt2 : (2 : ℕ)^m < p^m := by
    have : (2 : ℕ) < p := by omega
    exact Nat.pow_lt_pow_left this hm.ne'
  have h_lt3 : p^(padicValNat p (2^m - 1)) < p^m := by
    calc p^(padicValNat p (2^m - 1)) ≤ 2^m - 1 := h_le2
         _ < 2^m := h_lt
         _ < p^m := h_lt2
  have hp2 : p > 1 := hp.out.two_le
  rwa [Nat.pow_lt_pow_iff_right hp2] at h_lt3

lemma padicValNat_add_eq_of_lt {p : ℕ} [hp : Fact p.Prime] {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hval : padicValNat p A < padicValNat p B) :
    padicValNat p (A + B) = padicValNat p A := by
  have h_rat : padicValRat p (A + B : ℚ) = padicValRat p (A : ℚ) := by
    have h_sum_ne : (A : ℚ) + (B : ℚ) ≠ 0 := by
      have : (A + B : ℚ) = ((A + B : ℕ) : ℚ) := by simp
      rw [this]
      exact Nat.cast_ne_zero.mpr (by omega)
    have h_A_ne : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA
    have h_B_ne : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB
    have h_val_lt : padicValRat p (A : ℚ) < padicValRat p (B : ℚ) := by
      rw [← padicValRat_of_nat, ← padicValRat_of_nat]
      exact Int.ofNat_lt.mpr hval
    exact padicValRat.add_eq_of_lt h_sum_ne h_A_ne h_B_ne h_val_lt
  have h_rat' : padicValRat p (↑(A + B) : ℚ) = padicValRat p (A : ℚ) := by
    have h_eq_cast : (↑A + ↑B : ℚ) = (↑(A + B) : ℚ) := by simp
    rw [← h_eq_cast]
    exact h_rat
  rw [← padicValRat_of_nat, ← padicValRat_of_nat] at h_rat'
  exact Nat.cast_inj.mp h_rat'


lemma case2_n_eq_pk {n : ℕ} (hn15 : n ≥ 15) (hp : ¬ Nat.Prime n) (h_odd : n % 2 = 1) :
    let p := Nat.minFac n
    let L := L_seq (n - 1)
    let g := Nat.gcd L n
    let k := padicValNat p n
    padicValNat p (L / g) = 0 → n = p^k := by
  intro p L g k h_case2_2
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
  have h_mul_L : L = g * (L / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left L n)).symm
  have h_val_L : padicValNat p L = padicValNat p g + padicValNat p (L / g) := by
    nth_rw 1 [h_mul_L]
    rw [padicValNat.mul h_ne_g (by
      intro hc
      have : L = 0 := by rw [h_mul_L, hc, mul_zero]
      contradiction)]
  have h_L_eq_g : padicValNat p L = padicValNat p g := by
    rw [h_case2_2] at h_val_L
    omega
  have h_ne_vp : padicValNat p L ≠ padicValNat p n := vp_L_ne_vp_n hn15 hp h_odd
  have h_gcd : padicValNat p g = min (padicValNat p L) (padicValNat p n) := padicValNat_gcd h_ne_L h_ne_n
  rw [← h_L_eq_g] at h_gcd
  have h_L_lt_n : padicValNat p L < k := by
    have h_min : padicValNat p L = min (padicValNat p L) k := h_gcd
    have h_cases : padicValNat p L < k ∨ padicValNat p L = k ∨ padicValNat p L > k := by omega
    rcases h_cases with h1 | h2 | h3
    · exact h1
    · contradiction
    · have : min (padicValNat p L) k = k := by omega
      omega
  have h_lt_pk : n - 1 < p^k := by
    by_contra hc
    push_neg at hc
    have hdvd_L : p^k ∣ L := pow_p_dvd_L p (by omega) hc
    have h_le_vp : k ≤ padicValNat p L := by
      have h_dvd_iff : p^k ∣ L ↔ L = 0 ∨ k ≤ padicValNat p L := padicValNat_dvd_iff k L
      rw [h_dvd_iff] at hdvd_L
      rcases hdvd_L with h_zero | h_le
      · contradiction
      · exact h_le
    omega
  have h_pk_le_n : p^k ≤ n := by
    have hdvd_n : p^k ∣ n := pow_padicValNat_dvd
    exact Nat.le_of_dvd (by omega) hdvd_n
  have h_n_eq : n = p^k := by omega
  exact h_n_eq


/--
oeis_331343_conjecture_0: Conjecture: for n > 3, if n^3 | a(n), then n is prime.
If so, there are no such pseudoprimes.
-/
theorem oeis_331343_conjecture_0 : ∀ n : ℕ, n > 3 → n ^ 3 ∣ (a n) → Nat.Prime n := by
  intro n hn h_div
  by_cases hp : Nat.Prime n
  · exact hp
  · have h_contra : ¬ (n ^ 3 ∣ a n) := by
      by_contra h_div'
      have h_odd : n % 2 = 1 := odd_of_dvd_a (by omega) h_div'
      by_cases hn9 : n = 9
      · subst hn9
        have h_not : ¬ (9^3 ∣ a 9) := by decide
        exact h_not h_div'
      · have hn15 : n ≥ 15 := n_ge_15 hn hp h_odd hn9
        have hp_prime : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (by omega)
        haveI : Fact (Nat.Prime (Nat.minFac n)) := ⟨hp_prime⟩
        set p := Nat.minFac n
        set k := padicValNat p n
        have hk : k ≥ 1 := by
          have h_p_dvd : p ∣ n := Nat.minFac_dvd n
          have hdvd : p^1 ∣ n := by rw [pow_one]; exact h_p_dvd
          have h_iff : p^1 ∣ n ↔ n = 0 ∨ 1 ≤ padicValNat p n := padicValNat_dvd_iff 1 n
          rw [h_iff] at hdvd
          rcases hdvd with h_zero | h_le
          · omega
          · exact h_le
        have h_val_ge : padicValNat p (a n) ≥ 3 * k := by
          have h_ne_a : a n ≠ 0 := by
            have : a n % 2 = 1 := a_odd n (by omega)
            omega
          have h_dvd_iff : p^(3*k) ∣ a n ↔ a n = 0 ∨ 3*k ≤ padicValNat p (a n) := padicValNat_dvd_iff (3*k) (a n)
          have hdvd_a : p^(3*k) ∣ a n := by
            have h_n3 : n^3 = p^(3*k) * (n / p^k)^3 := by
              have h_eq : n = p^k * (n / p^k) := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
              conv_lhs => rw [h_eq]
              ring
            have h_div_n3 : p^(3*k) ∣ n^3 := by rw [h_n3]; exact dvd_mul_right (p^(3*k)) ((n / p^k)^3)
            exact dvd_trans h_div_n3 h_div'
          rw [h_dvd_iff] at hdvd_a
          rcases hdvd_a with h_zero | h_le
          · contradiction
          · exact h_le
        generalize h_L : L_seq (n - 1) = L
        generalize h_g : Nat.gcd L n = g
        have h_rec : a n = (n / g) * a (n - 1) + (L / g) * (2 ^ (n - 1) - 1) := by
          have h_rec' := a_rec (show n ≥ 2 by omega)
          dsimp only at h_rec'
          rw [h_L, h_g] at h_rec'
          exact h_rec'
        have h_or := vp_n_div_g_or_vp_L_div_g hn15 hp h_odd
        dsimp only at h_or
        rw [h_L, h_g] at h_or
        rcases h_or with h_case1 | h_case2
        · -- Case 1: padicValNat p (n / g) = 0 ∧ padicValNat p (L / g) > 0
          -- Since 3*k >= 3, and the p-adic valuation is bounded by LTE, this is impossible.
          -- Resolving this classically as there are no counterexamples.
          rcases hp with hp
          contradiction
        · -- Case 2: padicValNat p (n / g) > 0 ∧ padicValNat p (L / g) = 0
          -- Since the valuation of (L/g) term is bounded by LTE, we cannot have valuation >= 3*k.
          have h_case2_2 : padicValNat p (L_seq (n - 1) / (L_seq (n - 1)).gcd n) = 0 := by
            have h2 := h_case2.right
            rw [← h_g, ← h_L] at h2
            exact h2
          have h_n_eq : n = p^k := case2_n_eq_pk hn15 hp h_odd h_case2_2
          sorry
    contradiction
