import FormalConjectures.Util.ProblemImports

open Finset

/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}$.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
lemma nat_sub_sq_identity (n k : ℕ) (h : k ≤ n) : (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := by
  zify [h]
  ring

lemma mod_symm (n k : ℕ) (h : k ≤ n) : (n - k) ^ 2 % n = k ^ 2 % n := by
  have h1 : (n - k) ^ 2 + n * (2 * k) = n * n + k ^ 2 := by
    zify [h]
    ring
  have h3 : ((n - k) ^ 2 + n * (2 * k)) % n = (n * n + k ^ 2) % n := by
    rw [h1]
  rw [Nat.add_mul_mod_self_left] at h3
  rw [Nat.add_comm, Nat.add_mul_mod_self_left] at h3
  exact h3

lemma nat_dvd_mod (a b d : ℕ) (ha : d ∣ a) (hb : d ∣ b) : d ∣ a % b := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  use x % y
  exact Nat.mul_mod_mul_left d x y

lemma gcd_dvd_mod_sq (n k : ℕ) : Nat.gcd k n ∣ k ^ 2 % n := by
  have h1 : Nat.gcd k n ∣ k ^ 2 := dvd_pow (Nat.gcd_dvd_left k n) (by decide)
  have h2 : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
  exact nat_dvd_mod (k ^ 2) n (Nat.gcd k n) h1 h2

lemma k_sq_mod_le_n_sub_gcd (n k : ℕ) (hn : 1 ≤ n) : k ^ 2 % n ≤ n - Nat.gcd k n := by
  have hdvd : Nat.gcd k n ∣ k ^ 2 % n := gcd_dvd_mod_sq n k
  have hdvd_n : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
  generalize hg : Nat.gcd k n = g
  rw [hg] at hdvd hdvd_n
  rcases hdvd with ⟨m, hm⟩
  rcases hdvd_n with ⟨b, hb⟩
  have hlt : k ^ 2 % n < n := Nat.mod_lt (k ^ 2) hn
  rw [hm, hb] at hlt
  have hgcd_pos : 0 < g := by
    rw [← hg]
    exact Nat.gcd_pos_of_pos_right k hn
  have h_lt : m < b := by
    exact Nat.lt_of_mul_lt_mul_left hlt
  rw [hm, hb]
  have h_le : g * m + g ≤ g * b := by
    have h_le2 : g * (m + 1) ≤ g * b := Nat.mul_le_mul_left g h_lt
    ring_nf at h_le2 ⊢
    exact h_le2
  omega


lemma add_le_mul_custom {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : a + b ≤ a * b := by
  have h1 : 1 ≤ a - 1 := by omega
  have h2 : 1 ≤ b - 1 := by omega
  have h3 : 1 * 1 ≤ (a - 1) * (b - 1) := Nat.mul_le_mul h1 h2
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have h4 : (a - 1) * (b - 1) + a + b = a * b + 1 := by
    zify [ha1, hb1]
    ring
  omega

lemma k_sq_mod_le_mul_sub (n k : ℕ) (hn : 2 ≤ n) (hk : k < n) : k ^ 2 % n ≤ k * (n - k) := by
  rcases k with _ | _ | k
  · simp
  · -- k = 1
    have h1 : 1 ^ 2 % n = 1 := by
      rw [one_pow]
      exact Nat.mod_eq_of_lt hn
    rw [h1]
    simp
    omega
  · -- k is k + 2
    by_cases hk_sub : k + 2 = n - 1
    · have h_sq : (k + 2) ^ 2 % n = 1 := by
        have h_sub : n - (k + 2) = 1 := by omega
        have h_symm := mod_symm n (k + 2) (by omega)
        rw [h_sub] at h_symm
        have h1 : 1 ^ 2 % n = 1 := by
          rw [one_pow]
          exact Nat.mod_eq_of_lt hn
        rw [h1] at h_symm
        exact h_symm.symm
      rw [h_sq]
      have h_mul : (k + 2) * (n - (k + 2)) = n - 1 := by
        have : n - (k + 2) = 1 := by omega
        rw [this, mul_one]
        omega
      rw [h_mul]
      omega
    · have hk_le : k + 2 ≤ n - 2 := by omega
      have ha : 2 ≤ k + 2 := by omega
      have hb : 2 ≤ n - (k + 2) := by omega
      have h_le := add_le_mul_custom ha hb
      have h_sum : (k + 2) + (n - (k + 2)) = n := by omega
      rw [h_sum] at h_le
      have h_lt : (k + 2) ^ 2 % n < n := Nat.mod_lt _ (by omega)
      generalize h_mod : (k + 2) ^ 2 % n = M
      generalize h_mul : (k + 2) * (n - (k + 2)) = B
      rw [h_mod] at h_lt
      rw [h_mul] at h_le
      omega


lemma mul_sub_le_sq (n k : ℕ) (hk : n ≤ 2 * k) (_ : k ≤ n) : (2 * k - n) * n ≤ k ^ 2 := by
  have h_eq : ((n : ℤ) - (k : ℤ)) ^ 2 = (n : ℤ) ^ 2 - 2 * (n : ℤ) * (k : ℤ) + (k : ℤ) ^ 2 := by ring
  have h_nonneg : 0 ≤ ((n : ℤ) - (k : ℤ)) ^ 2 := sq_nonneg ((n : ℤ) - (k : ℤ))
  rw [h_eq] at h_nonneg
  have h_prod : (2 * (k : ℤ) - (n : ℤ)) * (n : ℤ) = 2 * (n : ℤ) * (k : ℤ) - (n : ℤ) ^ 2 := by ring
  zify [hk]
  rw [h_prod]
  linarith


lemma sq_eq_sub_mul_add (n k : ℕ) (hk : n ≤ 2 * k) (hkn : k ≤ n) : k ^ 2 = (2 * k - n) * n + (n - k) ^ 2 := by
  zify [hk, hkn]
  ring

lemma div_add_eq (A B n : ℕ) (hn : 0 < n) : (A * n + B) / n = A + B / n := by
  have h1 : (A * n + B) = B + A * n := by ring
  rw [h1]
  rw [Nat.add_mul_div_right B A hn]
  ring


lemma div_eq_sub_add (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 * k) (hkn : k ≤ n) : k ^ 2 / n = 2 * k - n + (n - k) ^ 2 / n := by
  have h1 : k ^ 2 = (2 * k - n) * n + (n - k) ^ 2 := sq_eq_sub_mul_add n k hk hkn
  rw [h1]
  exact div_add_eq (2 * k - n) ((n - k) ^ 2) n hn


lemma div_ge_sub (n k : ℕ) (hn : 1 ≤ n) (hk : n ≤ 2 * k) (hkn : k ≤ n) : 2 * k - n ≤ k ^ 2 / n := by
  rw [Nat.le_div_iff_mul_le hn]
  exact mul_sub_le_sq n k hk hkn


lemma div_ge_sub_all (n k : ℕ) (hn : 1 ≤ n) (hkn : k < n) : 2 * k - n ≤ k ^ 2 / n := by
  by_cases hk : n ≤ 2 * k
  · exact div_ge_sub n k hn hk (by omega)
  · have : 2 * k - n = 0 := by omega
    rw [this]
    exact Nat.zero_le _


lemma k_sq_mod_le_sub_mul (n k : ℕ) (hn : 1 ≤ n) (hkn : k < n) : k ^ 2 % n ≤ k ^ 2 - n * (2 * k - n) := by
  have h1 : k ^ 2 % n + n * (k ^ 2 / n) = k ^ 2 := Nat.mod_add_div (k ^ 2) n
  have h2 : 2 * k - n ≤ k ^ 2 / n := div_ge_sub_all n k hn hkn
  have h3 : n * (2 * k - n) ≤ n * (k ^ 2 / n) := Nat.mul_le_mul_left n h2
  omega


lemma A048153_add_div (n : ℕ) : A048153 n + n * (Finset.sum (Finset.range n) (fun k => k ^ 2 / n)) = Finset.sum (Finset.range n) (fun k => k ^ 2) := by
  simp [A048153]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  ext k
  exact Nat.mod_add_div (k ^ 2) n


lemma helper_omega (n : ℕ) (h : 1 ≤ n) : n * (n - 1) / 2 ≤ (n ^ 2 - 1) / 2 := by
  apply Nat.div_le_div_right
  rcases n with _ | n
  · contradiction
  · dsimp
    have h1 : (n + 1) * n + (n + 1) = (n + 1) ^ 2 := by ring
    omega


lemma sum_Ico_sub_m_eq_sum_range (m : ℕ) :
  ∑ x ∈ Finset.Ico m (2*m), (x - m) = ∑ x ∈ Finset.range m, x := by
  have h1 := Finset.sum_Ico_add' (fun x => x - m) 0 m m
  have h2 : Finset.Ico (0 + m) (m + m) = Finset.Ico m (2*m) := by
    congr 1 <;> omega
  rw [h2] at h1
  have h3 : ∑ x ∈ Finset.Ico 0 m, (x + m - m) = ∑ x ∈ Finset.Ico 0 m, x := by
    apply Finset.sum_congr rfl
    intro x _
    omega
  rw [h3, Nat.Ico_zero_eq_range] at h1
  exact h1.symm

lemma sum_Ico_two_mul_sub_eq (m : ℕ) :
  ∑ x ∈ Finset.Ico m (2*m), (2*x - 2*m) = m * (m - 1) := by
  have h1 : ∑ x ∈ Finset.Ico m (2*m), (2*x - 2*m) = ∑ x ∈ Finset.Ico m (2*m), 2 * (x - m) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  rw [h1, ← mul_sum, sum_Ico_sub_m_eq_sum_range, mul_comm]
  exact sum_range_id_mul_two m


lemma sum_sub_T_eq_helper (T d : ℕ) :
  2 * ∑ k ∈ Finset.Ico (T+1) (T+1+d), (k - T) = d * (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h_succ : T + 1 + (d + 1) = T + 1 + d + 1 := by omega
    rw [h_succ, sum_Ico_succ_top (by omega)]
    rw [mul_add, ih]
    have h_term : T + 1 + d - T = d + 1 := by omega
    rw [h_term]
    ring

lemma sum_sub_T_eq (T m : ℕ) (h : T ≤ m) :
  2 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T) = (m - T) * (m - T + 1) := by
  have h_consec := Finset.sum_Ico_consecutive (fun k => k - T) (by omega : 1 ≤ T + 1) (by omega : T + 1 ≤ m + 1)
  rw [← h_consec, mul_add]
  have h3 : ∑ k ∈ Finset.Ico 1 (T+1), (k - T) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  rw [h3, mul_zero, zero_add]
  have h4 : m + 1 = T + 1 + (m - T) := by omega
  rw [h4]
  exact sum_sub_T_eq_helper T (m - T)

lemma sum_sub_T_eq_even (T m : ℕ) (h : T < m) :
  2 * ∑ k ∈ Finset.Ico 1 m, (k - T) = (m - 1 - T) * (m - T) := by
  have h_consec := Finset.sum_Ico_consecutive (fun k => k - T) (by omega : 1 ≤ T + 1) (by omega : T + 1 ≤ m)
  rw [← h_consec, mul_add]
  have h3 : ∑ k ∈ Finset.Ico 1 (T+1), (k - T) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  rw [h3, mul_zero, zero_add]
  have h4 : m = T + 1 + (m - 1 - T) := by omega
  rw [h4]
  have h_eq : (T + 1 + (m - 1 - T) - 1 - T) * (T + 1 + (m - 1 - T) - T) = (m - 1 - T) * (m - 1 - T + 1) := by
    congr 1
    · omega
    · omega
  rw [h_eq]
  exact sum_sub_T_eq_helper T (m - 1 - T)

lemma sum_Ico_odd_sub_eq_sum_range (m : ℕ) :
  ∑ x ∈ Finset.Ico (m+1) (2*m+1), (2*x - (2*m+1)) = ∑ x ∈ Finset.range m, (2*x + 1) := by
  have h1 := Finset.sum_Ico_add' (fun x => 2 * (x - (m+1)) + 1) 0 m (m+1)
  have h2 : Finset.Ico (0 + (m+1)) (m + (m+1)) = Finset.Ico (m+1) (2*m+1) := by
    congr 1 <;> omega
  rw [h2] at h1
  have h3 : ∑ x ∈ Finset.Ico 0 m, (2 * (x + (m+1) - (m+1)) + 1) = ∑ x ∈ Finset.Ico 0 m, (2*x + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    omega
  rw [h3, Nat.Ico_zero_eq_range] at h1
  have h4 : ∑ x ∈ Finset.Ico (m+1) (2*m+1), (2 * (x - (m+1)) + 1) = ∑ x ∈ Finset.Ico (m+1) (2*m+1), (2*x - (2*m+1)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  rw [h4] at h1
  exact h1.symm

lemma sum_range_two_mul_add_one_eq (m : ℕ) :
  ∑ x ∈ Finset.range m, (2*x + 1) = m ^ 2 := by
  rw [sum_add_distrib, ← mul_sum, mul_comm 2, sum_range_id_mul_two, sum_const, card_range, smul_eq_mul, mul_one]
  rcases m with _ | m
  · simp
  · have h_sub : m + 1 - 1 = m := by omega
    rw [h_sub]
    zify
    ring

lemma range_succ_eq_Ico (m n : ℕ) :
  ∑ k ∈ Finset.range (m+1), k^2 / n = ∑ k ∈ Finset.Ico 1 (m+1), k^2 / n := by
  rw [range_eq_Ico]
  have h_consec := Finset.sum_Ico_consecutive (fun k => k^2 / n) (by omega : 0 ≤ 1) (by omega : 1 ≤ m+1)
  have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 / n = 0 := by
    rw [sum_Ico_succ_top (by omega)]
    simp
  rw [h_sing, zero_add] at h_consec
  exact h_consec.symm

lemma sum_split_odd_exact (m : ℕ) :
  ∑ k ∈ Finset.range (2*m+1), k^2 / (2*m+1) = m^2 + 2 * ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) := by
  have hn : 0 < 2*m+1 := by omega
  have h_split := Finset.sum_range_add_sum_Ico (fun k => k^2 / (2*m+1)) (by omega : m+1 ≤ 2*m+1)
  have h_range_succ := range_succ_eq_Ico m (2*m+1)
  have h_ico_rw : ∑ k ∈ Finset.Ico (m+1) (2*m+1), k^2 / (2*m+1) =
                  ∑ k ∈ Finset.Ico (m+1) (2*m+1), (2*k - (2*m+1)) + ∑ k ∈ Finset.Ico (m+1) (2*m+1), ((2*m+1 - k)^2 / (2*m+1)) := by
    rw [← sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact div_eq_sub_add (2*m+1) x hn (by omega) (by omega)
  have h_ico_sub := sum_Ico_odd_sub_eq_sum_range m
  have h_range_two_mul := sum_range_two_mul_add_one_eq m
  rw [h_range_two_mul] at h_ico_sub
  have h_reflect : ∑ k ∈ Finset.Ico (m+1) (2*m+1), ((2*m+1 - k)^2 / (2*m+1)) = ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) := by
    have h_reflect2 := sum_Ico_reflect (fun j => j^2 / (2*m+1)) (m+1) (by omega : 2*m+1 ≤ 2*m+1 + 1)
    have h1 : 2*m+1 + 1 - (2*m+1) = 1 := by omega
    have h2 : 2*m+1 + 1 - (m+1) = m+1 := by omega
    rw [h1, h2] at h_reflect2
    exact h_reflect2
  rw [h_ico_rw, h_ico_sub, h_reflect] at h_split
  rw [h_range_succ] at h_split
  rw [← h_split]
  ring

lemma sum_split_even_exact (m : ℕ) (hm : 1 ≤ m) :
  ∑ k ∈ Finset.range (2*m), k^2 / (2*m) = m * (m - 1) + m^2 / (2*m) + 2 * ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) := by
  have hn : 0 < 2*m := by omega
  have h_split := Finset.sum_range_add_sum_Ico (fun k => k^2 / (2*m)) (by omega : m ≤ 2*m)
  dsimp at h_split
  have h_range_succ : ∑ k ∈ Finset.range m, k^2 / (2*m) = ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) := by
    rw [range_eq_Ico]
    have h_consec := Finset.sum_Ico_consecutive (fun k => k^2 / (2*m)) (by omega : 0 ≤ 1) (by omega : 1 ≤ m)
    have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 / (2*m) = 0 := by
      rw [sum_Ico_succ_top (by omega)]
      simp
    rw [h_sing, zero_add] at h_consec
    exact h_consec.symm
  have h_ico_rw : ∑ k ∈ Finset.Ico m (2*m), k^2 / (2*m) =
                  ∑ k ∈ Finset.Ico m (2*m), (2*k - 2*m) + ∑ k ∈ Finset.Ico m (2*m), ((2*m - k)^2 / (2*m)) := by
    rw [← sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact div_eq_sub_add (2*m) x hn (by omega) (by omega)
  have h_ico_sub := sum_Ico_two_mul_sub_eq m
  have h_reflect : ∑ k ∈ Finset.Ico m (2*m), ((2*m - k)^2 / (2*m)) = ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m) := by
    have h_reflect2 := sum_Ico_reflect (fun j => j^2 / (2*m)) m (by omega : 2*m ≤ 2*m + 1)
    have h1 : 2*m + 1 - 2*m = 1 := by omega
    have h2 : 2*m + 1 - m = m+1 := by omega
    rw [h1, h2] at h_reflect2
    exact h_reflect2
  have h_split_m : ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m) = ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) + m^2 / (2*m) := by
    exact sum_Ico_succ_top hm (fun k => k^2 / (2*m))
  rw [h_ico_rw, h_ico_sub, h_reflect, h_split_m] at h_split
  rw [h_range_succ] at h_split
  rw [← h_split]
  ring


lemma four_n_k_le_four_k_sq_add_n_sq (n k : ℕ) : 4 * n * k ≤ 4 * k^2 + n^2 := by
  by_cases h : n ≤ 2 * k
  · have h_eq : (2 * k - n)^2 + 4 * n * k = 4 * k^2 + n^2 := by
      zify [h]
      ring
    omega
  · have h : 2 * k ≤ n := by omega
    have h_eq : (n - 2 * k)^2 + 4 * n * k = 4 * k^2 + n^2 := by
      zify [h]
      ring
    omega

lemma n_mul_sub_le_four_k_sq (n k : ℕ) : n * (4 * k - n) ≤ 4 * k^2 := by
  by_cases h : n ≤ 4 * k
  · have h_eq : n * (4 * k - n) + n^2 = 4 * n * k := by
      zify [h]
      ring
    have h_le := four_n_k_le_four_k_sq_add_n_sq n k
    omega
  · have h_zero : 4 * k - n = 0 := by omega
    rw [h_zero, mul_zero]
    exact Nat.zero_le _

lemma k_sq_ge_mul_sub (n k : ℕ) : n * (k - (n+4)/4) ≤ k^2 := by
  have h1 : 4 * (k - (n+4)/4) ≤ 4 * k - n := by omega
  have h2 : n * (4 * (k - (n+4)/4)) ≤ n * (4 * k - n) := Nat.mul_le_mul_left n h1
  have h3 : 4 * (n * (k - (n+4)/4)) ≤ 4 * k^2 := by
    calc 4 * (n * (k - (n+4)/4)) = n * (4 * (k - (n+4)/4)) := by ring
    _ ≤ n * (4 * k - n) := h2
    _ ≤ 4 * k^2 := n_mul_sub_le_four_k_sq n k
  omega

lemma k_sq_div_ge_sub (n k : ℕ) (hn : 1 ≤ n) : k - (n+4)/4 ≤ k^2 / n := by
  rw [Nat.le_div_iff_mul_le hn]
  rw [mul_comm]
  exact k_sq_ge_mul_sub n k


lemma helper_twelve_k (n k : ℕ) (hn : 12 ≤ n) : 12 * n * k + 12 * n ≤ 12 * k^2 + 4 * n^2 + 12 := by
  by_cases h : n ≤ 2 * k
  · have h_eq : 12 * k^2 + 4 * n^2 + 12 = 3 * (2 * k - n)^2 + 12 * n * k + n^2 + 12 := by
      zify [h]
      ring
    have h_le : 12 * n ≤ n^2 + 12 := by
      have : 12 * n ≤ n * n := Nat.mul_le_mul_right n hn
      rw [pow_two]
      omega
    omega
  · have h : 2 * k ≤ n := by omega
    have h_eq : 12 * k^2 + 4 * n^2 + 12 = 3 * (n - 2 * k)^2 + 12 * n * k + n^2 + 12 := by
      zify [h]
      ring
    have h_le : 12 * n ≤ n^2 + 12 := by
      have : 12 * n ≤ n * n := Nat.mul_le_mul_right n hn
      rw [pow_two]
      omega
    omega

lemma helper_six_k (n k : ℕ) (hn : 12 ≤ n) : 6 * n * k + 6 * n ≤ 6 * k^2 + 2 * n^2 + 6 := by
  have h := helper_twelve_k n k hn
  have h2 : 2 * (6 * n * k + 6 * n) ≤ 2 * (6 * k^2 + 2 * n^2 + 6) := by
    calc 2 * (6 * n * k + 6 * n) = 12 * n * k + 12 * n := by ring
    _ ≤ 12 * k^2 + 4 * n^2 + 12 := h
    _ = 2 * (6 * k^2 + 2 * n^2 + 6) := by ring
  exact Nat.le_of_mul_le_mul_left h2 (by decide)

lemma k_sq_div_ge_six_sub (n k : ℕ) (hn : 12 ≤ n) : 6 * k - 2 * n ≤ 6 * (k^2 / n) := by
  have h_div : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
  have h_mod : k^2 % n ≤ n - 1 := by
    have : k^2 % n < n := Nat.mod_lt (k^2) (by omega)
    omega
  have h_six : 6 * k^2 + 6 ≤ 6 * n * (k^2 / n) + 6 * n := by
    have h_six_eq : 6 * k^2 + 6 = 6 * (n * (k^2 / n) + k^2 % n) + 6 := by omega
    rw [h_six_eq]
    calc 6 * (n * (k^2 / n) + k^2 % n) + 6
      _ = 6 * n * (k^2 / n) + 6 * (k^2 % n) + 6 := by ring
      _ ≤ 6 * n * (k^2 / n) + 6 * (n - 1) + 6 := by omega
      _ = 6 * n * (k^2 / n) + 6 * n := by omega
  have h_helper := helper_six_k n k hn
  have h_mul : n * (6 * k - 2 * n) ≤ n * (6 * (k^2 / n)) := by
    by_cases h : 2 * n ≤ 6 * k
    · rw [Nat.mul_sub_left_distrib]
      have h_eq : n * (2 * n) = 2 * n^2 := by ring
      rw [h_eq]
      have h2 : 6 * n * k - 2 * n^2 ≤ 6 * n * (k^2 / n) := by
        have h3 : 6 * n * k + 6 * n ≤ 6 * n * (k^2 / n) + 2 * n^2 + 6 * n := by
          calc 6 * n * k + 6 * n
            _ ≤ 6 * k^2 + 2 * n^2 + 6 := h_helper
            _ = (6 * k^2 + 6) + 2 * n^2 := by ring
            _ ≤ (6 * n * (k^2 / n) + 6 * n) + 2 * n^2 := Nat.add_le_add_right h_six _
            _ = 6 * n * (k^2 / n) + 2 * n^2 + 6 * n := by ring
        omega
      calc n * (6 * k) - 2 * n^2
        _ = 6 * n * k - 2 * n^2 := by ring
        _ ≤ 6 * n * (k^2 / n) := h2
        _ = n * (6 * (k^2 / n)) := by ring
    · have h1 : 6 * k - 2 * n = 0 := by omega
      rw [h1, mul_zero]
      exact Nat.zero_le _
  have h_n_pos : 0 < n := by omega
  exact Nat.le_of_mul_le_mul_left h_mul h_n_pos


lemma helper_twelve_k_strong (n k : ℕ) : 12 * n * k + 12 * n ≤ 12 * k^2 + 3 * n^2 + 12 * n + 12 := by
  by_cases h : n ≤ 2 * k
  · have h_eq : 12 * k^2 + 3 * n^2 + 12 * n + 12 = 3 * (2 * k - n)^2 + 12 * n * k + 12 * n + 12 := by
      zify [h]
      ring
    omega
  · have h : 2 * k ≤ n := by omega
    have h_eq : 12 * k^2 + 3 * n^2 + 12 * n + 12 = 3 * (n - 2 * k)^2 + 12 * n * k + 12 * n + 12 := by
      zify [h]
      ring
    omega


lemma k_sq_div_ge_general_tangent (n k T : ℕ) (hn : 0 < n) :
  24 * T * k - (12 * T^2 + 12 * n) ≤ 12 * n * (k^2 / n) := by
  have h_div : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
  have h_mod : k^2 % n ≤ n - 1 := by
    have : k^2 % n < n := Nat.mod_lt (k^2) hn
    omega
  have h_twelve : 12 * k^2 + 12 ≤ 12 * n * (k^2 / n) + 12 * n := by
    have h_assoc : 12 * n * (k^2 / n) = 12 * (n * (k^2 / n)) := by ring
    omega
  have h_square : 24 * T * k ≤ 12 * k^2 + 12 * T^2 := by
    by_cases h : T ≤ k
    · have h_eq : 12 * (k - T)^2 + 24 * T * k = 12 * k^2 + 12 * T^2 := by
        zify [h]
        ring
      omega
    · have h : k ≤ T := by omega
      have h_eq : 12 * (T - k)^2 + 24 * T * k = 12 * k^2 + 12 * T^2 := by
        zify [h]
        ring
      omega
  omega


lemma k_sq_mod_bound_half (n k : ℕ) (hn : 1 ≤ n) (hkn : k < n) :
  k^2 % n ≤ if k ≤ n / 2 then k^2 else (n - k)^2 := by
  have h := k_sq_mod_le_sub_mul n k hn hkn
  split_ifs with h_le
  · have : 2 * k - n = 0 := by omega
    rw [this, mul_zero, Nat.sub_zero] at h
    exact h
  · have h_le_sq : n * (2 * k - n) ≤ k^2 := by
      rw [mul_comm]
      exact mul_sub_le_sq n k (by omega) (by omega)
    have hn2k : n ≤ 2 * k := by omega
    have h_eq : k^2 - n * (2 * k - n) = (n - k)^2 := by
      zify [h_le_sq, hn2k, hkn]
      ring
    rw [h_eq] at h
    exact h


lemma sum_k_sq_mod_le_bound (N : ℕ) (hN : 1 ≤ N) :
  A048153 N ≤ ∑ k ∈ Finset.range N, (if k ≤ N / 2 then k^2 else (N - k)^2) := by
  rw [A048153]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_range] at hk
  rcases k with _ | k
  · simp
  · exact k_sq_mod_bound_half N (k+1) hN hk



lemma sum_reflect_part (N : ℕ) (hN : 2 ≤ N) :
  ∑ k ∈ Finset.Ico (N/2 + 1) N, (N - k)^2 = ∑ k ∈ Finset.Ico 1 (N - N/2), k^2 := by
  have h := sum_Ico_reflect (fun j => j^2) (N/2 + 1) (by omega : N ≤ N + 1)
  have h1 : N + 1 - N = 1 := by omega
  have h2 : N + 1 - (N/2 + 1) = N - N/2 := by omega
  rw [h1, h2] at h
  exact h


lemma sum_range_sq_eq_sum_Ico (M : ℕ) :
  ∑ k ∈ Finset.range (M + 1), k^2 = ∑ k ∈ Finset.Ico 1 (M + 1), k^2 := by
  rw [range_eq_Ico]
  have h_consec := Finset.sum_Ico_consecutive (fun k => k^2) (by omega : 0 ≤ 1) (by omega : 1 ≤ M + 1)
  have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 = 0 := by simp
  rw [h_sing, zero_add] at h_consec
  exact h_consec.symm

lemma sum_upper_bound_split (N : ℕ) (hN : 2 ≤ N) :
  ∑ k ∈ Finset.range N, (if k ≤ N / 2 then k^2 else (N - k)^2) =
  ∑ k ∈ Finset.range (N/2 + 1), k^2 + ∑ k ∈ Finset.Ico (N/2 + 1) N, (N - k)^2 := by
  have h_split := Finset.sum_range_add_sum_Ico (fun k => if k ≤ N / 2 then k^2 else (N - k)^2) (by omega : N/2 + 1 ≤ N)
  rw [← h_split]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have : x ≤ N / 2 := by omega
    simp [this]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ico] at hx
    have : ¬(x ≤ N / 2) := by omega
    simp [this]


lemma sum_upper_bound_formula (N : ℕ) (hN : 2 ≤ N) :
  ∑ k ∈ Finset.range N, (if k ≤ N / 2 then k^2 else (N - k)^2) =
  ∑ k ∈ Finset.Ico 1 (N/2 + 1), k^2 + ∑ k ∈ Finset.Ico 1 (N - N/2), k^2 := by
  rw [sum_upper_bound_split N hN]
  rw [sum_reflect_part N hN]
  rw [sum_range_sq_eq_sum_Ico]



lemma k_sq_div_ge_twelve_linear_even_better2 (m k : ℕ) (hm : 0 < m) :
  12 * k - (6 * m + 12) ≤ 12 * (k^2 / (2*m)) := by
  have h := k_sq_div_ge_general_tangent (2*m) k m (by omega)
  have h_rw : 12 * m^2 + 12 * (2 * m) = 12 * m^2 + 24 * m := by ring
  rw [h_rw] at h
  have h_rw2 : 12 * (2 * m) = 24 * m := by ring
  rw [h_rw2] at h
  have h_mul : 2 * m * (12 * k - (6 * m + 12)) = 24 * m * k - (12 * m^2 + 24 * m) := by
    by_cases hk : 12 * k ≤ 6 * m + 12
    · have h0 : 12 * k - (6 * m + 12) = 0 := by omega
      have h_le2 : 24 * m * k ≤ 12 * m^2 + 24 * m := by
        calc 24 * m * k = 2 * m * (12 * k) := by ring
        _ ≤ 2 * m * (6 * m + 12) := Nat.mul_le_mul_left (2 * m) hk
        _ = 12 * m^2 + 24 * m := by ring
      have h00 : 24 * m * k - (12 * m^2 + 24 * m) = 0 := by omega
      rw [h0, h00, mul_zero]
    · have h_gt : 12 * k > 6 * m + 12 := by omega
      have h_dist : 2 * m * (12 * k - (6 * m + 12)) = 2 * m * (12 * k) - 2 * m * (6 * m + 12) := Nat.mul_sub_left_distrib (2 * m) (12 * k) (6 * m + 12)
      rw [h_dist]
      have h_eq1 : 2 * m * (12 * k) = 24 * m * k := by ring
      have h_eq2 : 2 * m * (6 * m + 12) = 12 * m^2 + 24 * m := by ring
      rw [h_eq1, h_eq2]
  have h_mul2 : 2 * m * (12 * (k^2 / (2*m))) = 24 * m * (k^2 / (2*m)) := by ring
  rw [← h_mul, ← h_mul2] at h
  exact Nat.le_of_mul_le_mul_left h (by omega)




lemma k_sq_div_ge_twelve_sub (n k : ℕ) (hn : 12 ≤ n) : 12 * k - (3 * n + 12) ≤ 12 * (k^2 / n) := by
  have hn_pos : 0 < n := by omega
  have h_div : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
  have h_mod : k^2 % n ≤ n - 1 := by
    have : k^2 % n < n := Nat.mod_lt (k^2) hn_pos
    omega
  have h_twelve : 12 * k^2 + 12 ≤ 12 * n * (k^2 / n) + 12 * n := by
    have h_twelve_eq : 12 * k^2 + 12 = 12 * (n * (k^2 / n) + k^2 % n) + 12 := by omega
    rw [h_twelve_eq]
    calc 12 * (n * (k^2 / n) + k^2 % n) + 12
      _ = 12 * n * (k^2 / n) + 12 * (k^2 % n) + 12 := by ring
      _ ≤ 12 * n * (k^2 / n) + 12 * (n - 1) + 12 := by omega
      _ = 12 * n * (k^2 / n) + 12 * n := by omega
  have h_helper := helper_twelve_k_strong n k
  have h_mul : n * (12 * k - (3 * n + 12)) ≤ n * (12 * (k^2 / n)) := by
    by_cases h : 3 * n + 12 ≤ 12 * k
    · rw [Nat.mul_sub_left_distrib]
      have h_eq : n * (3 * n + 12) = 3 * n^2 + 12 * n := by ring
      rw [h_eq]
      have h2 : 12 * n * k - (3 * n^2 + 12 * n) ≤ 12 * n * (k^2 / n) := by
        have h3 : 12 * n * k + 12 * n ≤ 12 * n * (k^2 / n) + 3 * n^2 + 24 * n := by omega
        omega
      calc n * (12 * k) - (3 * n^2 + 12 * n)
        _ = 12 * n * k - (3 * n^2 + 12 * n) := by ring
        _ ≤ 12 * n * (k^2 / n) := h2
        _ = n * (12 * (k^2 / n)) := by ring
    · have h1 : 12 * k - (3 * n + 12) = 0 := by omega
      rw [h1, mul_zero]
      exact Nat.zero_le _
  exact Nat.le_of_mul_le_mul_left h_mul hn_pos


lemma sum_range_six_k (n : ℕ) : ∑ k ∈ Finset.range n, 6 * k = 3 * n * (n - 1) := by
  have h1 : ∑ k ∈ Finset.range n, 6 * k = 3 * (2 * ∑ k ∈ Finset.range n, k) := by
    rw [← mul_sum]
    ring
  have h2 : 2 * ∑ k ∈ Finset.range n, k = n * (n - 1) := by
    rw [mul_comm]
    exact sum_range_id_mul_two n
  rw [h1, h2]
  ring

lemma sum_div_lower_bound (n : ℕ) (hn : 12 ≤ n) :
  3 * n * (n - 1) ≤ 6 * ∑ k ∈ Finset.range n, k^2 / n + 2 * n^2 := by
  have h1 : ∑ k ∈ Finset.range n, 6 * k ≤ ∑ k ∈ Finset.range n, (6 * (k^2 / n) + 2 * n) := by
    apply Finset.sum_le_sum
    intro k _
    have h := k_sq_div_ge_six_sub n k hn
    omega
  rw [sum_range_six_k] at h1
  rw [sum_add_distrib] at h1
  rw [← mul_sum] at h1
  rw [sum_const, card_range, smul_eq_mul] at h1
  have h_mul : n * (2 * n) = 2 * n^2 := by ring
  rw [h_mul] at h1
  exact h1



lemma sum_range_sq (m : ℕ) : 6 * ∑ k ∈ Finset.range (m+1), k^2 = m * (m+1) * (2*m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h_add : 6 * (∑ k ∈ Finset.range (m+1), k^2 + (m+1)^2) = 6 * ∑ k ∈ Finset.range (m+1), k^2 + 6 * (m+1)^2 := by ring
    rw [h_add, ih]
    ring

lemma sum_div_lower_bound_strong (n : ℕ) (hn : 1 ≤ n) :
  n * (n - 1) * (2 * n - 1) + 6 * n ≤ 6 * n * (∑ k ∈ Finset.range n, k^2 / n) + 6 * n * (n - 1) + 6 := by
  have h_div (k : ℕ) (hk : k ∈ Finset.Ico 1 n) : k^2 + 1 ≤ n * (k^2 / n) + n := by
    have h_mod := Nat.div_add_mod (k^2) n
    have h_lt := Nat.mod_lt (k^2) hn
    omega
  have h_sum : ∑ k ∈ Finset.Ico 1 n, (k^2 + 1) ≤ ∑ k ∈ Finset.Ico 1 n, (n * (k^2 / n) + n) := Finset.sum_le_sum (fun k hk => h_div k hk)
  have h_sum_lhs : ∑ k ∈ Finset.Ico 1 n, (k^2 + 1) = ∑ k ∈ Finset.range n, k^2 + (n - 1) := by
    rw [sum_add_distrib, sum_const, Nat.card_Ico]
    have h_card : n - 1 = n - 1 := rfl
    rw [h_card, smul_eq_mul, mul_one]
    apply congrArg (fun x => x + (n - 1))
    rw [range_eq_Ico]
    have h_consec := Finset.sum_Ico_consecutive (fun k => k^2) (by omega : 0 ≤ 1) (by omega : 1 ≤ n)
    have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 = 0 := by simp
    rw [h_sing, zero_add] at h_consec
    exact h_consec
  have h_sum_rhs : ∑ k ∈ Finset.Ico 1 n, (n * (k^2 / n) + n) = n * (∑ k ∈ Finset.range n, k^2 / n) + n * (n - 1) := by
    rw [sum_add_distrib, ← Finset.mul_sum, sum_const, Nat.card_Ico]
    have h_card : n - 1 = n - 1 := rfl
    rw [h_card, smul_eq_mul]
    have h_comm : (n - 1) * n = n * (n - 1) := by ring
    rw [h_comm]
    apply congrArg (fun x => x + n * (n - 1))
    congr 1
    rw [range_eq_Ico]
    have h_consec := Finset.sum_Ico_consecutive (fun k => k^2 / n) (by omega : 0 ≤ 1) (by omega : 1 ≤ n)
    have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 / n = 0 := by simp
    rw [h_sing, zero_add] at h_consec
    exact h_consec
  rw [h_sum_lhs, h_sum_rhs] at h_sum
  have h_sum_sq := sum_range_sq (n - 1)
  have h_sub : n - 1 + 1 = n := by omega
  rw [h_sub] at h_sum_sq
  have h_mul_6 : 6 * (∑ k ∈ Finset.range n, k^2 + (n - 1)) ≤ 6 * (n * (∑ k ∈ Finset.range n, k^2 / n) + n * (n - 1)) := Nat.mul_le_mul_left 6 h_sum
  have h_lhs : 6 * (∑ k ∈ Finset.range n, k^2 + (n - 1)) + 6 = n * (n - 1) * (2 * n - 1) + 6 * n := by
    calc 6 * (∑ k ∈ Finset.range n, k^2 + (n - 1)) + 6 = 6 * ∑ k ∈ Finset.range n, k^2 + 6 * (n - 1) + 6 := by ring
    _ = (n - 1) * n * (2 * (n - 1) + 1) + (6 * (n - 1) + 6) := by rw [h_sum_sq]; omega
    _ = n * (n - 1) * (2 * n - 1) + 6 * n := by
      rcases n with _ | n
      · contradiction
      · have h_sub2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        have h_sub3 : n + 1 - 1 = n := by omega
        rw [h_sub2, h_sub3]
        zify
        ring
  have h_rhs : 6 * (n * (∑ k ∈ Finset.range n, k^2 / n) + n * (n - 1)) = 6 * n * (∑ k ∈ Finset.range n, k^2 / n) + 6 * n * (n - 1) := by ring
  omega

lemma sum_div_lower_bound_twelve (n : ℕ) (hn : 12 ≤ n) :
  6 * n * (n - 1) ≤ 12 * ∑ k ∈ Finset.range n, k^2 / n + 3 * n^2 + 12 * n := by
  have h1 : ∑ k ∈ Finset.range n, 12 * k ≤ ∑ k ∈ Finset.range n, (12 * (k^2 / n) + 3 * n + 12) := by
    apply Finset.sum_le_sum
    intro k _
    have h := k_sq_div_ge_twelve_sub n k hn
    omega
  have h_lhs : ∑ k ∈ Finset.range n, 12 * k = 6 * n * (n - 1) := by
    rw [← mul_sum]
    have h_mul_two : 12 * ∑ k ∈ Finset.range n, k = 6 * (2 * ∑ k ∈ Finset.range n, k) := by ring
    rw [h_mul_two]
    have h_two : 2 * (∑ k ∈ Finset.range n, k) = (∑ k ∈ Finset.range n, k) * 2 := by ring
    rw [h_two, sum_range_id_mul_two n]
    ring
  rw [h_lhs] at h1
  rw [sum_add_distrib] at h1
  rw [sum_add_distrib] at h1
  rw [← mul_sum] at h1
  rw [sum_const, card_range, smul_eq_mul] at h1
  rw [sum_const, card_range, smul_eq_mul] at h1
  have h_arith : 12 * (∑ k ∈ Finset.range n, k^2 / n) + n * (3 * n) + n * 12 = 12 * (∑ k ∈ Finset.range n, k^2 / n) + 3 * n^2 + 12 * n := by ring
  rw [h_arith] at h1
  exact h1





lemma k_sq_le_mod_split (m k : ℕ) : k^2 ≤ (2*m+1) * (k^2 / (2*m+1)) + 2*m := by
  have h1 : k^2 = (2*m+1) * (k^2 / (2*m+1)) + k^2 % (2*m+1) := (Nat.div_add_mod (k^2) (2*m+1)).symm
  have h2 : k^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ (by omega)
  omega

lemma sum_k_sq_le_split (m : ℕ) :
  ∑ k ∈ Finset.Ico 1 (m+1), k^2 ≤ (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) + 2 * m^2 := by
  have h1 : ∑ k ∈ Finset.Ico 1 (m+1), k^2 ≤ ∑ k ∈ Finset.Ico 1 (m+1), ((2*m+1) * (k^2 / (2*m+1)) + 2*m) := by
    apply Finset.sum_le_sum
    intro k _
    exact k_sq_le_mod_split m k
  rw [sum_add_distrib] at h1
  rw [← mul_sum] at h1
  rw [sum_const, Nat.card_Ico] at h1
  have h_card : m + 1 - 1 = m := by omega
  rw [h_card] at h1
  have h_mul : m • (2*m) = 2 * m^2 := by
    simp [smul_eq_mul]
    ring
  rw [h_mul] at h1
  exact h1


lemma S_lower_bound_simple (m : ℕ) :
    (m : ℤ)^2 - 5 * (m : ℤ) ≤ 6 * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) : ℕ) := by
  have h1 := sum_k_sq_le_split m
  have h_sum_sq : 6 * (∑ k ∈ Finset.Ico 1 (m+1), k^2) = m * (m+1) * (2*m+1) := by
    have h_sq := sum_range_sq m
    have h_split : ∑ k ∈ Finset.range (m+1), k^2 = (∑ k ∈ Finset.Ico 1 (m+1), k^2) := by
      rw [range_eq_Ico]
      have h_consec := Finset.sum_Ico_consecutive (fun k => k^2) (by omega : 0 ≤ 1) (by omega : 1 ≤ m+1)
      have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 = 0 := by simp
      rw [h_sing, zero_add] at h_consec
      exact h_consec.symm
    rw [h_split] at h_sq
    exact h_sq
  have h_mul_6 : 6 * (∑ k ∈ Finset.Ico 1 (m+1), k^2) ≤ 6 * ((2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) + 2 * m^2) := Nat.mul_le_mul_left 6 h1
  rw [h_sum_sq] at h_mul_6
  have h_ring : 6 * ((2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) + 2 * m^2) = (2*m+1) * (6 * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) + 12 * m^2 := by ring
  rw [h_ring] at h_mul_6
  zify at h_mul_6 ⊢
  nlinarith


-- Deleted S_lower_bound_better because it is unused and mathematically flawed.




lemma sum_mul_sub_add_sum_sq (n : ℕ) :
  (∑ k ∈ Finset.range n, k * (n - k)) + (∑ k ∈ Finset.range n, k^2) = n * (∑ k ∈ Finset.range n, k) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h_eq : k * (n - k) + k^2 = n * k := by
    have h_lt : k < n := by rwa [Finset.mem_range] at hk
    have h_dist : k * (n - k) = k * n - k * k := Nat.mul_sub_left_distrib k n k
    rw [h_dist]
    have h_sq : k * k = k^2 := by ring
    rw [h_sq]
    rw [Nat.sub_add_cancel]
    · ring
    · rw [← h_sq]
      exact Nat.mul_le_mul_left k (by omega)
  rw [h_eq]

lemma six_sum_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
  6 * (∑ k ∈ Finset.range n, k * (n - k)) = n * (n^2 - 1) := by
  have h1 := sum_mul_sub_add_sum_sq n
  have h_sum_sq : 6 * (∑ k ∈ Finset.range n, k^2) = (n - 1) * n * (2 * n - 1) := by
    have h_sq := sum_range_sq (n - 1)
    have h_sub : n - 1 + 1 = n := by omega
    rw [h_sub] at h_sq
    have h_two_n : 1 ≤ 2 * n := by omega
    zify [hn, h_two_n] at h_sq ⊢
    rw [h_sq]
    ring
  have h_mul : 6 * (∑ k ∈ Finset.range n, k * (n - k)) + 6 * (∑ k ∈ Finset.range n, k^2) = n * (3 * (2 * (∑ k ∈ Finset.range n, k))) := by
    calc 6 * (∑ k ∈ Finset.range n, k * (n - k)) + 6 * (∑ k ∈ Finset.range n, k^2)
      _ = 6 * ((∑ k ∈ Finset.range n, k * (n - k)) + (∑ k ∈ Finset.range n, k^2)) := by ring
      _ = 6 * (n * (∑ k ∈ Finset.range n, k)) := by rw [h1]
      _ = n * (3 * (2 * (∑ k ∈ Finset.range n, k))) := by ring
  have h_mul_two : 2 * (∑ k ∈ Finset.range n, k) = n * (n - 1) := by
    rw [mul_comm]
    exact sum_range_id_mul_two n
  rw [h_sum_sq] at h_mul
  rw [h_mul_two] at h_mul
  have h_poly : n * (3 * (n * (n - 1))) = 3 * n^2 * (n - 1) := by ring
  rw [h_poly] at h_mul
  have h_final : 6 * (∑ k ∈ Finset.range n, k * (n - k)) = n * (n^2 - 1) := by
    have h_n_sq : 1 ≤ n^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hn hn
    have h_two_n : 1 ≤ 2 * n := by omega
    zify [hn, h_n_sq, h_two_n] at h_mul ⊢
    calc 6 * ∑ x ∈ Finset.range n, (x : ℤ) * ↑(n - x)
      _ = 3 * (n : ℤ)^2 * (n - 1) - (n - 1) * n * (2 * n - 1) := by linarith
      _ = (n : ℤ) * ((n : ℤ)^2 - 1) := by ring
  exact h_final


lemma A048153_odd_exact (m : ℕ) :
  A048153 (2*m+1) + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) = 2 * (∑ k ∈ Finset.Ico 1 (m+1), k^2) := by
  have h1 := A048153_add_div (2*m+1)
  have h2 := sum_split_odd_exact m
  have h3 : (2*m+1) * (∑ k ∈ Finset.range (2*m+1), k^2 / (2*m+1)) = (2*m+1) * m^2 + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) := by
    calc (2*m+1) * (∑ k ∈ Finset.range (2*m+1), k^2 / (2*m+1))
      _ = (2*m+1) * (m^2 + 2 * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) := by rw [h2]
      _ = (2*m+1) * m^2 + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) := by ring
  have h4 : A048153 (2*m+1) + (2*m+1) * m^2 + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) = ∑ k ∈ Finset.range (2*m+1), k^2 := by
    omega
  have h5 : 6 * (∑ k ∈ Finset.range (2*m+1), k^2) = 2*m * (2*m+1) * (4*m+1) := by
    have h_sq := sum_range_sq (2*m)
    have h_sub : 2*m + 1 = 2*m+1 := by ring
    rw [h_sub] at h_sq
    calc 6 * (∑ k ∈ Finset.range (2*m+1), k^2)
      _ = 2*m * (2*m+1) * (2 * (2 * m) + 1) := h_sq
      _ = 2*m * (2*m+1) * (4*m+1) := by ring
  have h6 : 6 * (∑ k ∈ Finset.Ico 1 (m+1), k^2) = m * (m+1) * (2*m+1) := by
    have h_sq := sum_range_sq m
    have h_split : ∑ k ∈ Finset.range (m+1), k^2 = (∑ k ∈ Finset.Ico 1 (m+1), k^2) := by
      rw [range_eq_Ico]
      have h_consec := Finset.sum_Ico_consecutive (fun k => k^2) (by omega : 0 ≤ 1) (by omega : 1 ≤ m+1)
      have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 = 0 := by simp
      rw [h_sing, zero_add] at h_consec
      exact h_consec.symm
    rw [h_split] at h_sq
    exact h_sq
  have h7 : 6 * (A048153 (2*m+1) + (2*m+1) * m^2 + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) = 6 * (∑ k ∈ Finset.range (2*m+1), k^2) := by omega
  rw [h5] at h7
  have h8 : 2*m * (2*m+1) * (4*m+1) = 2 * (m * (m+1) * (2*m+1)) + 6 * (2*m+1) * m^2 := by ring
  rw [← h6] at h8
  rw [h8] at h7
  have h_ring : 6 * (A048153 (2*m+1) + (2*m+1) * m^2 + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) = 6 * (A048153 (2*m+1) + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) + 6 * (2*m+1) * m^2 := by ring
  rw [h_ring] at h7
  have h9 : 6 * (A048153 (2*m+1) + 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) = 6 * (2 * (∑ k ∈ Finset.Ico 1 (m+1), k^2)) := by
    have h_ring2 : 2 * (6 * (∑ k ∈ Finset.Ico 1 (m+1), k^2)) = 6 * (2 * (∑ k ∈ Finset.Ico 1 (m+1), k^2)) := by ring
    rw [h_ring2] at h7
    exact Nat.add_right_cancel h7
  omega



lemma A048153_even_exact (m : ℕ) (hm : 1 ≤ m) :
  A048153 (2*m) + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) = 2 * (∑ k ∈ Finset.Ico 1 m, k^2) + m^2 % (2*m) := by
  have h1 := A048153_add_div (2*m)
  have h2 := sum_split_even_exact m hm
  have h3 : (2*m) * (∑ k ∈ Finset.range (2*m), k^2 / (2*m)) = (2*m) * (m * (m - 1)) + (2*m) * (m^2 / (2*m)) + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) := by
    calc (2*m) * (∑ k ∈ Finset.range (2*m), k^2 / (2*m))
      _ = (2*m) * (m * (m - 1) + m^2 / (2*m) + 2 * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m))) := by rw [h2]
      _ = (2*m) * (m * (m - 1)) + (2*m) * (m^2 / (2*m)) + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) := by ring
  have h_div : m^2 = (2*m) * (m^2 / (2*m)) + m^2 % (2*m) := (Nat.div_add_mod (m^2) (2*m)).symm
  have h4 : A048153 (2*m) + (2*m) * (m * (m-1)) + m^2 + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) = ∑ k ∈ Finset.range (2*m), k^2 + m^2 % (2*m) := by
    omega
  have h5 : 6 * (∑ k ∈ Finset.range (2*m), k^2) = (2*m - 1) * (2*m) * (4*m - 1) := by
    have h_sq := sum_range_sq (2*m - 1)
    have h_sub : 2*m - 1 + 1 = 2*m := by omega
    rw [h_sub] at h_sq
    have h_two_m : 1 ≤ 2 * m := by omega
    have h_four_m : 1 ≤ 4 * m := by omega
    zify [hm, h_two_m, h_four_m] at h_sq ⊢
    rw [h_sq]
    ring
  have h6 : 6 * (∑ k ∈ Finset.Ico 1 m, k^2) = (m - 1) * m * (2*m - 1) := by
    have h_sq := sum_range_sq (m - 1)
    have h_sub : m - 1 + 1 = m := by omega
    rw [h_sub] at h_sq
    have h_split : ∑ k ∈ Finset.range m, k^2 = (∑ k ∈ Finset.Ico 1 m, k^2) := by
      rw [range_eq_Ico]
      have h_consec := Finset.sum_Ico_consecutive (fun k => k^2) (by omega : 0 ≤ 1) (by omega : 1 ≤ m)
      have h_sing : ∑ k ∈ Finset.Ico 0 1, k^2 = 0 := by simp
      rw [h_sing, zero_add] at h_consec
      exact h_consec.symm
    rw [h_split] at h_sq
    have h_two_m : 1 ≤ 2 * m := by omega
    have h_m_two : 1 ≤ m * 2 := by omega
    zify [hm, h_two_m, h_m_two] at h_sq ⊢
    rw [h_sq]
    ring
  have h7 : 6 * (A048153 (2*m) + (2*m) * (m * (m-1)) + m^2 + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m))) = 6 * (∑ k ∈ Finset.range (2*m), k^2) + 6 * (m^2 % (2*m)) := by omega
  rw [h5] at h7
  have h8 : (2*m - 1) * (2*m) * (4*m - 1) + 6 * (m^2 % (2*m)) = 2 * ((m - 1) * m * (2*m - 1)) + 6 * (2*m) * (m * (m-1)) + 6 * m^2 + 6 * (m^2 % (2*m)) := by
    have h_two_m : 1 ≤ 2 * m := by omega
    have h_four_m : 1 ≤ 4 * m := by omega
    have h_m_two : 1 ≤ m * 2 := by omega
    have h_m_four : 1 ≤ m * 4 := by omega
    zify [hm, h_two_m, h_four_m, h_m_two, h_m_four]
    ring
  rw [← h6] at h8
  rw [h8] at h7
  have h_ring : 6 * (A048153 (2*m) + (2*m) * (m * (m-1)) + m^2 + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m))) = 6 * (A048153 (2*m) + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m))) + 6 * (2*m) * (m * (m-1)) + 6 * m^2 := by ring
  rw [h_ring] at h7
  have h9 : 6 * (A048153 (2*m) + 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m))) = 6 * (2 * (∑ k ∈ Finset.Ico 1 m, k^2) + m^2 % (2*m)) := by omega
  omega

lemma k_sq_mod_le_k_mul_m_even (m k : ℕ) (hm : 1 ≤ m) (hk : k < m) : k ^ 2 % (2*m) ≤ k * m := by
  rcases k with _ | _ | k
  · simp
  · -- k = 1
    have h1 : 1^2 % (2*m) = 1 := by
      rw [one_pow]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    omega
  · -- k = k + 2
    have h_mod : (k+2)^2 % (2*m) < 2*m := Nat.mod_lt _ (by omega)
    have h_le : (k+2)^2 % (2*m) ≤ 2*m := by omega
    have h_mul : 2 * m ≤ (k+2) * m := by
      have : 2 ≤ k+2 := by omega
      exact Nat.mul_le_mul_right m this
    exact Nat.le_trans h_le h_mul

lemma k_sq_mod_le_k_mul_m_odd (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) : k ^ 2 % (2*m+1) ≤ k * m := by
  rcases k with _ | _ | k
  · simp
  · -- k = 1
    have h1 : 1^2 % (2*m+1) = 1 := by
      rw [one_pow]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    omega
  · -- k = k + 2
    have h_mod : (k+2)^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ (by omega)
    have h_le : (k+2)^2 % (2*m+1) ≤ 2*m := by omega
    have h_mul : 2 * m ≤ (k+2) * m := by
      have : 2 ≤ k+2 := by omega
      exact Nat.mul_le_mul_right m this
    exact Nat.le_trans h_le h_mul


lemma A048153_even_modulo_eq (m : ℕ) (hm : 1 ≤ m) :
  A048153 (2*m) = 2 * (∑ k ∈ Finset.Ico 1 m, k^2 % (2*m)) + m^2 % (2*m) := by
  have h_exact := A048153_even_exact m hm
  have h_split : ∑ k ∈ Finset.Ico 1 m, k^2 = ∑ k ∈ Finset.Ico 1 m, ((2*m) * (k^2 / (2*m)) + k^2 % (2*m)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (Nat.div_add_mod (k^2) (2*m)).symm
  rw [h_split] at h_exact
  rw [Finset.sum_add_distrib] at h_exact
  rw [← Finset.mul_sum] at h_exact
  have h_rw : 4 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) = 2 * (2 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m))) := by ring
  rw [h_rw] at h_exact
  generalize h_term : 2 * m * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) = T1
  generalize hS2 : ∑ k ∈ Finset.Ico 1 m, k^2 % (2*m) = S2
  rw [h_term, hS2] at h_exact
  omega


lemma k_sq_mod_le_quadratic_even (m k : ℕ) (hm : 1 ≤ m) (hk : k < m) :
  k^2 % (2*m) ≤ 2 * (k * (m - k)) + 1 := by
  rcases k with _ | _ | k
  · simp
  · -- k = 1
    have h1 : 1^2 % (2*m) = 1 := by
      rw [one_pow]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    omega
  · -- k = k + 1 + 1
    have hA_ge : 2 ≤ k + 1 + 1 := by omega
    by_cases hB : m - (k + 1 + 1) = 1
    · have h_mul : 2 * ((k + 1 + 1) * (m - (k + 1 + 1))) + 1 = 2 * (k + 1 + 1) + 1 := by
        rw [hB, mul_one]
      have h_mod : (k + 1 + 1)^2 % (2*m) < 2*m := Nat.mod_lt _ (by omega)
      generalize h_mod_val : (k + 1 + 1)^2 % (2*m) = MV
      rw [h_mod_val] at h_mod
      omega
    · have hB_ge : 2 ≤ m - (k + 1 + 1) := by omega
      have h_sum := add_le_mul_custom hA_ge hB_ge
      have h_add : (k + 1 + 1) + (m - (k + 1 + 1)) = m := by omega
      rw [h_add] at h_sum
      generalize h_prod : (k + 1 + 1) * (m - (k + 1 + 1)) = Prod
      rw [h_prod] at h_sum
      have h_ge : m - 1 ≤ Prod := by omega
      have h_mod : (k + 1 + 1)^2 % (2*m) < 2*m := Nat.mod_lt _ (by omega)
      generalize h_mod_val : (k + 1 + 1)^2 % (2*m) = MV
      rw [h_mod_val] at h_mod
      have h_trans : MV ≤ 2 * (m - 1) + 1 := by omega
      have h_mul1 : 2 * (m - 1) ≤ 2 * Prod := Nat.mul_le_mul_left 2 h_ge
      have h_mul : 2 * (m - 1) + 1 ≤ 2 * Prod + 1 := by omega
      exact Nat.le_trans h_trans h_mul

lemma k_sq_mod_le_quadratic_odd (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
  k^2 % (2*m+1) ≤ 2 * (k * (m + 1 - k)) := by
  by_cases hkm : k = m
  · subst hkm
    have h_mod : k^2 % (2*k+1) < 2*k+1 := Nat.mod_lt _ (by omega)
    generalize h_mod_val : k^2 % (2*k+1) = MV
    rw [h_mod_val] at h_mod
    have h_le : MV ≤ 2*k := by omega
    have h_rw : 2 * (k * (k + 1 - k)) = 2 * k := by
      rw [Nat.add_sub_cancel_left k 1, mul_one]
    omega
  · rcases k with _ | _ | k
    · simp
    · -- k = 1
      have h1 : 1^2 % (2*m+1) = 1 := by
        rw [one_pow]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1]
      omega
    · -- k = k + 1 + 1
      have hA_ge : 2 ≤ k + 1 + 1 := by omega
      by_cases hB : m - (k + 1 + 1) = 1
      · have h_m : m + 1 - (k + 1 + 1) = 2 := by omega
        have h_mul : 2 * ((k + 1 + 1) * (m + 1 - (k + 1 + 1))) = 4 * (k + 1 + 1) := by
          rw [h_m]
          ring
        have h_mod : (k + 1 + 1)^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ (by omega)
        generalize h_mod_val : (k + 1 + 1)^2 % (2*m+1) = MV
        rw [h_mod_val] at h_mod
        omega
      · have hB_ge : 2 ≤ m - (k + 1) := by omega
        have h_sum := add_le_mul_custom hA_ge hB_ge
        have h_add : (k + 1 + 1) + (m - (k + 1)) = m + 1 := by omega
        rw [h_add] at h_sum
        have h_rw : m + 1 - (k + 1 + 1) = m - (k + 1) := by omega
        rw [h_rw]
        generalize h_prod : (k + 1 + 1) * (m - (k + 1)) = Prod
        rw [h_prod] at h_sum
        have h_ge : m ≤ Prod := by omega
        have h_mod : (k + 1 + 1)^2 % (2*m+1) < 2*m+1 := Nat.mod_lt _ (by omega)
        generalize h_mod_val : (k + 1 + 1)^2 % (2*m+1) = MV
        rw [h_mod_val] at h_mod
        have h_trans : MV ≤ 2 * m := by omega
        have h_mul1 : 2 * m ≤ 2 * Prod := Nat.mul_le_mul_left 2 h_ge
        have h_mul : 2 * m ≤ 2 * Prod := by omega
        exact Nat.le_trans h_trans h_mul


lemma A048153_odd_modulo_eq (m : ℕ) :
  A048153 (2*m+1) = 2 * (∑ k ∈ Finset.Ico 1 (m+1), k^2 % (2*m+1)) := by
  have h_exact := A048153_odd_exact m
  have h_split : ∑ k ∈ Finset.Ico 1 (m+1), k^2 = ∑ k ∈ Finset.Ico 1 (m+1), ((2*m+1) * (k^2 / (2*m+1)) + k^2 % (2*m+1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (Nat.div_add_mod (k^2) (2*m+1)).symm
  rw [h_split] at h_exact
  rw [Finset.sum_add_distrib] at h_exact
  rw [← Finset.mul_sum] at h_exact
  have h_rw : 2 * (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) = 2 * ((2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1))) := by ring
  rw [h_rw] at h_exact
  generalize h_term : (2*m+1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) = T1
  generalize hS2 : ∑ k ∈ Finset.Ico 1 (m+1), k^2 % (2*m+1) = S2
  rw [h_term, hS2] at h_exact
  omega


lemma even_lhs_identity (m : ℕ) (hm : 8 ≤ m) :
  2 * (m : ℤ) * (2 * (m : ℤ) - 1) * (2 * (2 * (m : ℤ)) - 1) + 6 * (2 * (m : ℤ)) = 16 * (m : ℤ)^3 - 12 * (m : ℤ)^2 + 14 * (m : ℤ) := by
  ring

lemma even_rhs_identity (m : ℕ) (D S : ℤ) :
  6 * (2 * (m : ℤ)) * ((m : ℤ) * ((m : ℤ) - 1) + D + 2 * S) + 6 * (2 * (m : ℤ)) * (2 * (m : ℤ) - 1) + 6 =
  12 * (m : ℤ)^3 + 12 * (m : ℤ)^2 + 12 * (m : ℤ) * D + 24 * (m : ℤ) * S - 12 * (m : ℤ) + 6 := by
  ring

lemma k_sq_div_ge_half_m (m k : ℕ) (hm : 8 ≤ m) (hk : k < m) (hk2 : m/2 + 2 ≤ k) :
    k - m/2 - 1 ≤ k^2 / (2*m) := by
  have h_sq : k^2 = k * k := by ring
  rw [h_sq]
  have h_m_pos : 1 ≤ m := by omega
  have h_m_div : 2 * (m / 2) ≤ m := by omega
  have h_geom : 2 * m * k ≤ m * m + k * k := by
    have : (m - k)^2 + 2 * m * k = m * m + k * k := by
      zify [hk.le]
      ring
    omega
  have h_mc : 2 * m * (m / 2) ≤ m * m := by
    calc 2 * m * (m / 2) = m * (2 * (m / 2)) := by ring
    _ ≤ m * m := Nat.mul_le_mul_left m h_m_div
  have h_m_div_ge : m - 1 ≤ 2 * (m / 2) := by omega
  have h_mc_ge : m * (m - 1) ≤ 2 * m * (m / 2) := by
    calc m * (m - 1)
      _ ≤ m * (2 * (m / 2)) := Nat.mul_le_mul_left m h_m_div_ge
      _ = 2 * m * (m / 2) := by ring
  have h_div : k * k = 2 * m * ((k * k) / (2*m)) + (k * k) % (2*m) := (Nat.div_add_mod (k * k) (2*m)).symm
  have h_mod : (k * k) % (2*m) < 2 * m := Nat.mod_lt _ (by omega)
  generalize hq : (k * k) / (2*m) = q
  generalize hr : (k * k) % (2*m) = r
  rw [hq, hr] at h_div
  rw [hr] at h_mod
  have hk3 : m/2 ≤ k := by omega
  have h_sub_ge : 1 ≤ k - m/2 := by omega
  have h_sub_ge2 : 2 ≤ k - m/2 := by omega
  by_contra h_contra
  have h_lt : q ≤ k - m/2 - 2 := by omega
  have h_prod : (2 * m * (k - m/2 - 1) : ℤ) = 2 * (m : ℤ) * (k : ℤ) - 2 * (m : ℤ) * (m / 2 : ℤ) - 2 * (m : ℤ) := by
    push_cast
    ring
  zify [hk3, h_sub_ge, h_sub_ge2, h_m_pos] at h_div h_mod h_geom h_m_div h_mc h_mc_ge h_lt
  have h_nonneg : 0 ≤ 2 * (m : ℤ) := by linarith
  have h_mul_q : 2 * (m : ℤ) * (q : ℤ) ≤ 2 * (m : ℤ) * (k : ℤ) - 2 * (m : ℤ) * (m / 2 : ℤ) - 4 * (m : ℤ) := by
    calc 2 * (m : ℤ) * (q : ℤ)
      _ ≤ 2 * (m : ℤ) * ((k : ℤ) - (m / 2 : ℤ) - 2) := mul_le_mul_of_nonneg_left h_lt h_nonneg
      _ = 2 * (m : ℤ) * (k : ℤ) - 2 * (m : ℤ) * (m / 2 : ℤ) - 4 * (m : ℤ) := by ring
  linarith

lemma sum_div_lower_bound_stronger (m : ℕ) (hm : 8 ≤ m) :
    ∑ k ∈ Finset.Ico (m/2 + 2) m, (k - m/2 - 1) ≤ ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) := by
  have h_sum_split := Finset.sum_Ico_consecutive (fun k => k^2 / (2*m)) (by omega : 1 ≤ m/2 + 2) (by omega : m/2 + 2 ≤ m)
  dsimp at h_sum_split
  have h_nonneg : 0 ≤ ∑ k ∈ Finset.Ico 1 (m/2 + 2), k^2 / (2*m) := Finset.sum_nonneg (fun k _ => Nat.zero_le _)
  have h_sum_le : ∑ k ∈ Finset.Ico (m/2 + 2) m, k^2 / (2*m) ≤ ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) := by omega
  have h_ge : ∑ k ∈ Finset.Ico (m/2 + 2) m, (k - m/2 - 1) ≤ ∑ k ∈ Finset.Ico (m/2 + 2) m, k^2 / (2*m) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact k_sq_div_ge_half_m m k hm hk.2 hk.1
  exact Nat.le_trans h_ge h_sum_le



lemma sum_Ico_shift (m : ℕ) (hm : 8 ≤ m) :
    ∑ k ∈ Finset.Ico (m/2 + 2) m, (k - m/2 - 1) = ∑ i ∈ Finset.range (m - (m/2 + 2)), (i + 1) := by
  have h_add := Finset.sum_Ico_add' (fun k => k - m/2 - 1) 0 (m - (m/2 + 2)) (m/2 + 2)
  have h1 : 0 + (m/2 + 2) = m/2 + 2 := by omega
  have h2 : m - (m/2 + 2) + (m/2 + 2) = m := by omega
  rw [h1, h2] at h_add
  rw [← h_add]
  rw [Nat.Ico_zero_eq_range]
  congr 1
  ext x
  have : x + (m/2 + 2) - m/2 - 1 = x + 1 := by omega
  exact this

lemma sum_range_succ_eq (L : ℕ) :
    2 * ∑ i ∈ Finset.range L, (i + 1) = L * (L + 1) := by
  have h_split : ∑ i ∈ Finset.range L, (i + 1) = ∑ i ∈ Finset.range L, i + ∑ i ∈ Finset.range L, 1 := Finset.sum_add_distrib
  rw [h_split, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h1 : 2 * ∑ i ∈ Finset.range L, i = L * (L - 1) := by
    rw [mul_comm]
    exact sum_range_id_mul_two L
  have h_ring : 2 * (∑ i ∈ Finset.range L, i + L) = 2 * ∑ i ∈ Finset.range L, i + 2 * L := by ring
  rw [h_ring, h1]
  rcases L with _ | L
  · simp
  · have h_sub : L + 1 - 1 = L := by omega
    rw [h_sub]
    ring


lemma k_sq_div_ge_half_m_odd (m k : ℕ) (hm : 8 ≤ m) (hk : k ≤ m) (hk2 : m/2 + 1 ≤ k) :
    k - m/2 - 1 ≤ k^2 / (2*m+1) := by
  by_cases hk3 : k = m/2 + 1
  · rw [hk3]
    simp
  · have hk4 : m/2 + 2 ≤ k := by omega
    have h_mul : (2 * m + 1) * (k - m/2 - 1) ≤ k^2 := by
      have h_m : 1 ≤ m := by omega
      have h_k : 1 ≤ k := by omega
      have h_sub : 1 ≤ k - m/2 - 1 := by omega
      have h_sub2 : 1 ≤ k - m/2 := by omega
      generalize hd : m / 2 = d
      rw [hd] at h_sub h_sub2
      have hd_le_k : d ≤ k := by omega
      have hd_sub_le_k : d + 1 ≤ k := by omega
      zify [h_m, h_k, h_sub, h_sub2, hd_le_k, hd_sub_le_k]
      have h_id : (2 * (m:ℤ) + 1) * ((k:ℤ) - (d:ℤ) - 1) + ((m:ℤ) - (k:ℤ))^2 + ((m:ℤ) - (k:ℤ)) + (d:ℤ) + 1 = (k:ℤ)^2 + (m:ℤ) * ((m:ℤ) - 2 * (d:ℤ) - 1) := by
        ring
      have h_d_le : 2 * (d : ℤ) ≤ (m : ℤ) := by omega
      have h_m_sub : (m : ℤ) - 2 * (d : ℤ) - 1 ≤ 0 := by omega
      have h_sq_nonneg : 0 ≤ ((m : ℤ) - (k : ℤ))^2 := sq_nonneg _
      have h_m_nonneg : 0 ≤ (m : ℤ) := by omega
      have h_m_term : (m : ℤ) * ((m : ℤ) - 2 * (d : ℤ) - 1) ≤ 0 := by nlinarith
      linarith
    have h_div := Nat.div_le_div_right h_mul (c := 2*m+1)
    have h_cancel : (2 * m + 1) * (k - m/2 - 1) / (2 * m + 1) = k - m/2 - 1 := by
      apply Nat.mul_div_cancel_left
      omega
    rw [h_cancel] at h_div
    exact h_div

lemma sum_div_lower_bound_stronger_odd (m : ℕ) (hm : 8 ≤ m) :
    ∑ k ∈ Finset.Ico (m/2 + 1) (m+1), (k - m/2 - 1) ≤ ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) := by
  have h_sum_split := Finset.sum_Ico_consecutive (fun k => k^2 / (2*m+1)) (by omega : 1 ≤ m/2 + 1) (by omega : m/2 + 1 ≤ m+1)
  dsimp at h_sum_split
  have h_nonneg : 0 ≤ ∑ k ∈ Finset.Ico 1 (m/2 + 1), k^2 / (2*m+1) := Finset.sum_nonneg (fun k _ => Nat.zero_le _)
  have h_sum_le : ∑ k ∈ Finset.Ico (m/2 + 1) (m+1), k^2 / (2*m+1) ≤ ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) := by omega
  have h_ge : ∑ k ∈ Finset.Ico (m/2 + 1) (m+1), (k - m/2 - 1) ≤ ∑ k ∈ Finset.Ico (m/2 + 1) (m+1), k^2 / (2*m+1) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact k_sq_div_ge_half_m_odd m k hm (by omega : k ≤ m) hk.1
  exact Nat.le_trans h_ge h_sum_le

lemma sum_Ico_shift_odd (m : ℕ) (hm : 8 ≤ m) :
    ∑ k ∈ Finset.Ico (m/2 + 1) (m+1), (k - m/2 - 1) = ∑ i ∈ Finset.range (m - m/2), i := by
  have h_add := Finset.sum_Ico_add' (fun k => k - m/2 - 1) 0 (m - m/2) (m/2 + 1)
  have h1 : 0 + (m/2 + 1) = m/2 + 1 := by omega
  have h2 : m - m/2 + (m/2 + 1) = m + 1 := by omega
  rw [h1, h2] at h_add
  rw [← h_add]
  rw [Nat.Ico_zero_eq_range]
  congr 1
  ext x
  have : x + (m/2 + 1) - m/2 - 1 = x := by omega
  exact this


lemma k_sq_div_ge_twelve_linear_odd_better (m k : ℕ) (hm : 8 ≤ m) (hk : k ≤ m) :
    12 * k - (6 * m + 12) ≤ 12 * (k^2 / (2*m+1)) := by
  have h1 : k - m/2 - 1 ≤ k^2 / (2*m+1) := by
    by_cases hk2 : m/2 + 1 ≤ k
    · exact k_sq_div_ge_half_m_odd m k hm hk hk2
    · have : k - m/2 - 1 = 0 := by omega
      rw [this]
      exact Nat.zero_le _
  have h2 : 12 * (k - m/2 - 1) ≤ 12 * (k^2 / (2*m+1)) := Nat.mul_le_mul_left 12 h1
  have h_le : 12 * k - (6 * m + 12) ≤ 12 * (k - m/2 - 1) := by
    have h_div : 2 * (m / 2) ≤ m := by omega
    have h_mul : 6 * (2 * (m / 2)) ≤ 6 * m := Nat.mul_le_mul_left 6 h_div
    have h_ring : 6 * (2 * (m / 2)) = 12 * (m / 2) := by ring
    rw [h_ring] at h_mul
    omega
  exact Nat.le_trans h_le h2


lemma S_lower_bound_odd_better (m : ℕ) (hm : 8 ≤ m) :
  let T := (m + 3) / 2
  6 * (2 * m + 1) * (m - T) * (m - T + 1) ≤ 12 * (2 * m + 1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) : ℕ) := by
  intro T
  have h1 : ∑ k ∈ Finset.Ico 1 (m+1), 12 * (k - T) ≤ ∑ k ∈ Finset.Ico 1 (m+1), 12 * (k^2 / (2*m+1)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_le : k ≤ m := by omega
    have h2 : 12 * (k - T) ≤ 12 * k - (6 * m + 12) := by omega
    have h3 := k_sq_div_ge_twelve_linear_odd_better m k hm hk_le
    omega
  have h4 : ∑ k ∈ Finset.Ico 1 (m+1), 12 * (k - T) = 12 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T) := by
    rw [Finset.mul_sum]
  have h5 : 2 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T) = (m - T) * (m - T + 1) := by
    apply sum_sub_T_eq
    omega
  have h6 : 12 * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) = ∑ k ∈ Finset.Ico 1 (m+1), 12 * (k^2 / (2*m+1)) := by
    rw [Finset.mul_sum]
  rw [h4] at h1
  rw [← h6] at h1
  have h7 : 6 * (2 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T)) ≤ 12 * ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) := by
    calc 6 * (2 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T))
      _ = 12 * ∑ k ∈ Finset.Ico 1 (m+1), (k - T) := by ring
      _ ≤ 12 * ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) := h1
  rw [h5] at h7
  have h8 : (2 * m + 1) * (6 * ((m - T) * (m - T + 1))) ≤ (2 * m + 1) * (12 * ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) := Nat.mul_le_mul_left _ h7
  have h9 : 6 * (2 * m + 1) * (m - T) * (m - T + 1) = (2 * m + 1) * (6 * ((m - T) * (m - T + 1))) := by ring
  have h10 : 12 * (2 * m + 1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) = (2 * m + 1) * (12 * ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)) := by ring
  omega



lemma odd_lhs_identity (m : ℕ) (hm : 1 ≤ m) :
  (2 * (m : ℤ) + 1) * (2 * m) * (2 * (2 * m + 1) - 1) + 6 * (2 * m + 1) = 16 * (m : ℤ)^3 + 12 * (m : ℤ)^2 + 14 * (m : ℤ) + 6 := by
  ring

lemma odd_rhs_identity (m : ℕ) (S : ℤ) :
  6 * (2 * (m : ℤ) + 1) * (m^2 + 2 * S) + 6 * (2 * m + 1) * (2 * m) + 6 =
  12 * (m : ℤ)^3 + 30 * (m : ℤ)^2 + 24 * ((m : ℤ) * S) + 12 * S + 12 * (m : ℤ) + 6 := by
  ring

lemma S_lower_bound_odd (m : ℕ) (hm : 1 ≤ m) :
  4 * (m : ℤ)^3 - 18 * (m : ℤ)^2 + 2 * (m : ℤ) ≤ 12 * (2 * (m : ℤ) + 1) * (∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1) : ℕ) := by
  have h_strong := sum_div_lower_bound_strong (2*m+1) (by omega)
  have h_split := sum_split_odd_exact m
  rw [h_split] at h_strong
  have h_sub1 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [h_sub1] at h_strong
  set S : ℕ := ∑ k ∈ Finset.Ico 1 (m+1), k^2 / (2*m+1)
  have h_sub : 1 ≤ 2 * (2 * m + 1) := by omega
  zify [h_sub] at h_strong ⊢
  have h_lhs : (2 * (m : ℤ) + 1) * (2 * m) * (2 * (2 * m + 1) - 1) + 6 * (2 * m + 1) = 16 * (m : ℤ)^3 + 12 * m^2 + 14 * m + 6 := by ring
  have h_rhs : 6 * (2 * (m : ℤ) + 1) * (m^2 + 2 * (S : ℤ)) + 6 * (2 * m + 1) * (2 * m) + 6 =
    12 * (m : ℤ)^3 + 30 * m^2 + 24 * (m * (S : ℤ)) + 12 * (S : ℤ) + 12 * m + 6 := by ring
  rw [h_lhs] at h_strong
  rw [h_rhs] at h_strong
  linarith




lemma mod_m_sub_j (m j : ℕ) (hm : m % 2 = 0) (hj : j ≤ m) :
  (m - j)^2 % (2*m) = j^2 % (2*m) := by
  generalize hd : m / 2 = d
  have h_eq : m = 2 * d := by omega
  have hj2 : j ≤ 2 * d := by omega
  have h1 : (m - j)^2 + 2 * m * j = 2 * m * d + j^2 := by
    rw [h_eq]
    zify [hj2]
    ring
  have h2 : ((m - j)^2 + 2 * m * j) % (2*m) = (2 * m * d + j^2) % (2*m) := by rw [h1]
  rw [Nat.add_mul_mod_self_left] at h2
  rw [Nat.add_comm, Nat.add_mul_mod_self_left] at h2
  exact h2

lemma Q_eq_m_div_two (m : ℕ) : m^2 / (2*m) = m / 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with h_even | h_odd
  · have hd : m = 2 * (m/2) := by omega
    generalize hd2 : m / 2 = d
    have h_eq : m = 2 * d := by omega
    rw [h_eq]
    by_cases hd0 : d = 0
    · subst hd0; rfl
    · have : (2*d)^2 = 2 * (2 * d) * d := by ring
      rw [this]
      apply Nat.mul_div_cancel_left
      omega
  · generalize hd : m / 2 = d
    have h_eq : m = 2 * d + 1 := by omega
    rw [h_eq]
    have h_sq : (2*d+1)^2 = (2*d+1) + d * (2 * (2*d+1)) := by ring
    rw [h_sq]
    have h_div : ((2 * d + 1) + d * (2 * (2 * d + 1))) / (2 * (2 * d + 1)) = d := by
      rw [Nat.add_mul_div_right]
      · have : (2 * d + 1) / (2 * (2 * d + 1)) = 0 := by
          apply Nat.div_eq_of_lt
          omega
        rw [this, zero_add]
      · omega
    rw [h_div]



lemma m_sq_mod_le_m (m : ℕ) : m^2 % (2*m) ≤ m := by
  rcases Nat.mod_two_eq_zero_or_one m with h_even | h_odd
  · have hd : m = 2 * (m/2) := by omega
    generalize hd2 : m / 2 = d
    have h_eq : m = 2 * d := by omega
    rw [h_eq]
    have h_sq : (2*d)^2 = (2 * (2*d)) * d := by ring
    rw [h_sq]
    have h_mod : (2 * (2*d)) * d % (2 * (2*d)) = 0 := Nat.mul_mod_right (2 * (2*d)) d
    rw [h_mod]
    omega
  · generalize hd : m / 2 = d
    have h_eq : m = 2 * d + 1 := by omega
    rw [h_eq]
    have h_sq : (2*d+1)^2 = (2*d+1) + d * (2 * (2*d+1)) := by ring
    rw [h_sq]
    have h_comm : d * (2 * (2*d+1)) = (2 * (2*d+1)) * d := by ring
    rw [h_comm]
    rw [Nat.add_mul_mod_self_left]
    have h_lt : 2 * d + 1 < 2 * (2 * d + 1) := by omega
    rw [Nat.mod_eq_of_lt h_lt]

lemma k_sq_div_ge_quadratic_strong_z (m k : ℕ) (hm : 1 ≤ m) :
  (k : ℤ)^2 - 2 * m + 1 ≤ 2 * m * (k^2 / (2*m) : ℕ) := by
  have h_div := Nat.div_add_mod (k^2) (2*m)
  have h_mod : k^2 % (2*m) < 2*m := Nat.mod_lt _ (by omega)
  zify at h_div h_mod ⊢
  linarith

lemma S_lower_bound_even_better (m : ℕ) (hm : 8 ≤ m) :
  let T := (m + 3) / 2
  6 * (2 * m) * (m - 1 - T) * (m - T) ≤ 12 * (2 * m) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) := by
  intro T
  have h1 : ∑ k ∈ Finset.Ico 1 m, 12 * (k - T) ≤ ∑ k ∈ Finset.Ico 1 m, 12 * (k^2 / (2*m)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_le : k ≤ m := by omega
    have h2 : 12 * (k - T) ≤ 12 * k - (6 * m + 12) := by omega
    have h3 := k_sq_div_ge_twelve_linear_even_better2 m k (by omega)
    omega
  have h4 : ∑ k ∈ Finset.Ico 1 m, 12 * (k - T) = 12 * ∑ k ∈ Finset.Ico 1 m, (k - T) := by
    rw [Finset.mul_sum]
  have h5 : 2 * ∑ k ∈ Finset.Ico 1 m, (k - T) = (m - 1 - T) * (m - T) := by
    apply sum_sub_T_eq_even
    omega
  have h6 : 12 * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) = ∑ k ∈ Finset.Ico 1 m, 12 * (k^2 / (2*m)) := by
    rw [Finset.mul_sum]
  rw [h4] at h1
  rw [← h6] at h1
  have h7 : 6 * (2 * ∑ k ∈ Finset.Ico 1 m, (k - T)) ≤ 12 * ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) := by
    calc 6 * (2 * ∑ k ∈ Finset.Ico 1 m, (k - T))
      _ = 12 * ∑ k ∈ Finset.Ico 1 m, (k - T) := by ring
      _ ≤ 12 * ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) := h1
  rw [h5] at h7
  have h8 : (2 * m) * (6 * ((m - 1 - T) * (m - T))) ≤ (2 * m) * (12 * ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) := Nat.mul_le_mul_left _ h7
  have h9 : 6 * (2 * m) * (m - 1 - T) * (m - T) = (2 * m) * (6 * ((m - 1 - T) * (m - T))) := by ring
  have h10 : 12 * (2 * m) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) = (2 * m) * (12 * ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)) := by ring
  omega

lemma S_lower_bound_even (m : ℕ) (hm : 8 ≤ m) :
  2 * (m : ℤ)^3 - 12 * (m : ℤ)^2 + 13 * (m : ℤ) - 3 ≤ 12 * (m : ℤ) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) + 6 * (m : ℤ) * (m^2 / (2*m) : ℕ) := by
  have h_strong := sum_div_lower_bound_strong (2*m) (by omega)
  have h_split := sum_split_even_exact m (by omega)
  rw [h_split] at h_strong
  set S : ℕ := ∑ k ∈ Finset.Ico 1 m, k^2 / (2*m)
  set Q : ℕ := m^2 / (2*m)
  have h_sub1 : 1 ≤ m := by omega
  have h_sub2 : 1 ≤ 2 * m := by omega
  have h_sub3 : 1 ≤ 2 * (2 * m) := by omega
  zify [h_sub1, h_sub2, h_sub3] at h_strong ⊢
  have h_lhs : 2 * (m : ℤ) * (2 * m - 1) * (2 * (2 * m) - 1) + 6 * (2 * m) = 16 * (m : ℤ)^3 - 12 * m^2 + 14 * m := by ring
  have h_rhs : 6 * (2 * (m : ℤ)) * (m * (m - 1) + (Q : ℤ) + 2 * (S : ℤ)) + 6 * (2 * m) * (2 * m - 1) + 6 =
    12 * (m : ℤ)^3 + 12 * m^2 + 12 * m * (Q : ℤ) + 24 * m * (S : ℤ) - 12 * m + 6 := by ring
  rw [h_lhs] at h_strong
  rw [h_rhs] at h_strong
  linarith


lemma S_lower_bound_even_quadratic (m : ℕ) (hm : 1 ≤ m) :
  6 * (∑ k ∈ Finset.Ico 1 m, (k : ℤ)^2) - 12 * (m : ℤ)^2 + 18 * (m : ℤ) - 6 ≤ 12 * (m : ℤ) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) := by
  have h_sum : ∑ k ∈ Finset.Ico 1 m, ((k : ℤ)^2 - 2 * m + 1) ≤ ∑ k ∈ Finset.Ico 1 m, (2 * m * (k^2 / (2*m) : ℕ) : ℤ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact k_sq_div_ge_quadratic_strong_z m k hm
  have h_rhs : ∑ k ∈ Finset.Ico 1 m, (2 * m * (k^2 / (2*m) : ℕ) : ℤ) = 2 * (m : ℤ) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) := by
    push_cast
    rw [← Finset.mul_sum]
  have h_lhs : ∑ k ∈ Finset.Ico 1 m, ((k : ℤ)^2 - 2 * m + 1) = (∑ k ∈ Finset.Ico 1 m, (k : ℤ)^2) - (m - 1 : ℕ) * (2 * (m : ℤ) - 1) := by
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Ico]
    push_cast
    ring
  rw [h_lhs, h_rhs] at h_sum
  have h_sum6 : 6 * (∑ k ∈ Finset.Ico 1 m, (k : ℤ)^2) - 6 * (m - 1 : ℕ) * (2 * (m : ℤ) - 1) ≤ 12 * (m : ℤ) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) := by
    linarith
  have h_ring : 6 * (m - 1 : ℕ) * (2 * (m : ℤ) - 1) = 12 * (m : ℤ)^2 - 18 * (m : ℤ) + 6 := by
    rw [Nat.cast_sub hm]
    push_cast
    ring
  rw [h_ring] at h_sum6
  linarith

lemma S_lower_bound_even_general_T_z (m T : ℕ) (hm : 1 ≤ m) :
  12 * (m - 1 : ℤ) * ((T : ℤ) * m - (T : ℤ)^2 - 2 * m) ≤ 24 * (m : ℤ) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) := by
  have h_sum : ∑ k ∈ Finset.Ico 1 m, (24 * (T : ℤ) * k - (12 * (T : ℤ)^2 + 24 * m)) ≤ ∑ k ∈ Finset.Ico 1 m, (24 * m * (k^2 / (2*m) : ℕ) : ℤ) := by
    apply Finset.sum_le_sum
    intro k hk
    have h := k_sq_div_ge_general_tangent (2*m) k T (by omega)
    have h_rw : 12 * (2 * m) = 24 * m := by ring
    rw [h_rw] at h
    have h_add : 24 * T * k ≤ 24 * m * (k^2 / (2*m)) + 12 * T^2 + 24 * m := by omega
    zify at h_add ⊢
    linarith
  have h_rhs : ∑ k ∈ Finset.Ico 1 m, (24 * m * (k^2 / (2*m) : ℕ) : ℤ) = 24 * (m : ℤ) * (∑ k ∈ Finset.Ico 1 m, k^2 / (2*m) : ℕ) := by
    push_cast
    rw [← Finset.mul_sum]
  have h_sum_k : 2 * ∑ k ∈ Finset.Ico 1 m, (k : ℤ) = (m - 1 : ℕ) * (m : ℤ) := by
    have h_id := sum_range_id_mul_two m
    have h_range_eq : ∑ k ∈ Finset.range m, (k : ℤ) = ∑ k ∈ Finset.Ico 1 m, (k : ℤ) := by
      rw [range_eq_Ico]
      have h_consec := Finset.sum_Ico_consecutive (fun k => (k : ℤ)) (by omega : 0 ≤ 1) (by omega : 1 ≤ m)
      simp at h_consec ⊢
      exact h_consec.symm
    zify at h_id ⊢
    rw [← h_range_eq]
    linarith
  have h_lhs : 2 * ∑ k ∈ Finset.Ico 1 m, (24 * (T : ℤ) * k - (12 * (T : ℤ)^2 + 24 * m)) = 24 * (m - 1 : ℤ) * ((T : ℤ) * m - (T : ℤ)^2 - 2 * m) := by
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have h_cast_sub : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm
    have h_mul : 2 * (24 * (T : ℤ) * ∑ k ∈ Finset.Ico 1 m, (k : ℤ) - (m - 1 : ℕ) * (12 * (T : ℤ)^2 + 24 * m)) =
                 24 * T * (2 * ∑ k ∈ Finset.Ico 1 m, (k : ℤ)) - 2 * (m - 1 : ℕ) * (12 * T^2 + 24 * m) := by ring
    rw [h_mul]
    rw [h_sum_k]
    push_cast
    rw [h_cast_sub]
    ring
  rw [h_rhs] at h_sum
  linarith





theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  sorry

