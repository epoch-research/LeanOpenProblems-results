import FormalConjectures.Util.ProblemImports

open Nat Finset

def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

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

lemma pow_two_dvd_L {m k : ℕ} (hm : m ≥ 1) (hk : 2^k ≤ m) : 2^k ∣ L_seq m := by
  have : 2^k > 0 := Nat.pow_pos (by decide)
  have hk_pos : 2^k ≥ 1 := by omega
  have hk_mem : 2^k ∈ Ico 1 (m + 1) := by
    simp only [mem_Ico]
    omega
  dsimp [L_seq]
  exact dvd_lcm hk_mem (f := id)

lemma coprime_not_both_even {a b : ℕ} (h : Nat.Coprime a b) : a % 2 ≠ 0 ∨ b % 2 ≠ 0 := by
  by_contra h_both
  push_neg at h_both
  have hdvd_a : 2 ∣ a := Nat.dvd_of_mod_eq_zero h_both.1
  have hdvd_b : 2 ∣ b := Nat.dvd_of_mod_eq_zero h_both.2
  have h_eq1 : 2 = 1 := Nat.eq_one_of_dvd_coprimes h hdvd_a hdvd_b
  contradiction

lemma v2_n_ne_v2_L {n : ℕ} (hn : n ≥ 3) : padicValNat 2 n ≠ padicValNat 2 (L_seq (n - 1)) := by
  sorry

lemma L_seq_ne_zero (m : ℕ) (hm : m ≥ 1) : L_seq m ≠ 0 := by
  induction' hm with k hk ih
  · decide
  · have h_rec := L_rec (show k + 1 ≥ 1 by omega)
    change L_seq (k + 1) ≠ 0
    rw [h_rec]
    exact Nat.lcm_ne_zero ih (by omega)

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
#check Nat.gcd_le_right

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
#check padicValNat


