import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

open Nat Classical

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

theorem digits_append_zeroes_append_digits_10 {k m n : ℕ} (hm : 0 < m) :
    digits 10 n ++ List.replicate k 0 ++ digits 10 m =
    digits 10 (n + 10 ^ ((digits 10 n).length + k) * m) := by
  exact digits_append_zeroes_append_digits (by decide) hm

theorem list_reverse_repeat (A : List ℕ) (k : ℕ) :
    (A ++ List.replicate k 0 ++ A ++ List.replicate k 0 ++ A).reverse =
    A.reverse ++ List.replicate k 0 ++ A.reverse ++ List.replicate k 0 ++ A.reverse := by
  simp

theorem ofDigits_append_replicate_zero (b : ℕ) (L : List ℕ) (k : ℕ) :
    ofDigits b (L ++ List.replicate k 0) = ofDigits b L := by
  rw [ofDigits_append]
  rw [Nat.ofDigits_replicate_zero]
  ring

lemma ten_pow_algebra (N : ℕ) (hN : 10^N ≥ 1) :
    (10^N - 1) * (1 + 10^N + 10^(2*N)) = 10^(3*N) - 1 := by
  have h1 : 3 * N = N + 2 * N := by ring
  rw [h1, Nat.pow_add]
  have h2 : 2 * N = N + N := by ring
  rw [h2, Nat.pow_add]
  let X := 10^N
  change (X - 1) * (1 + X + X * X) = X * (X * X) - 1
  have h_add : (X - 1) * (1 + X + X * X) + (1 + X + X * X) = X * (X * X) - 1 + (1 + X + X * X) := by
    have h_left : (X - 1) * (1 + X + X * X) + (1 + X + X * X) = X * (1 + X + X * X) := by
      rw [← Nat.add_one_mul]
      have : X - 1 + 1 = X := Nat.sub_add_cancel hN
      rw [this]
    rw [h_left]
    have h_sub_add : X * (X * X) - 1 + (1 + X + X * X) = X * (X * X) + X + X * X := by
      have : 1 + X + X * X = 1 + (X + X * X) := by omega
      rw [this, ← Nat.add_assoc]
      have hX3 : X * (X * X) ≥ 1 := by
        have : 1 ≤ X := hN
        have hsq : 1 ≤ X * X := one_le_mul this this
        exact one_le_mul this hsq
      rw [Nat.sub_add_cancel hX3]
      omega
    rw [h_sub_add]
    ring
  omega

lemma three_dvd_ten_pow_add (M : ℕ) : 3 ∣ 1 + 10^M + 10^(2*M) := by
  have h1 : 10 ≡ 1 [MOD 3] := by decide
  have h2 : 10^M ≡ 1^M [MOD 3] := ModEq.pow M h1
  have h3 : 1^M = 1 := by simp
  rw [h3] at h2
  have h4 : 10^(2*M) ≡ 1 [MOD 3] := by
    have h_pow := ModEq.pow (2*M) h1
    simp at h_pow
    exact h_pow
  have h_add : 1 + 10^M + 10^(2*M) ≡ 1 + 1 + 1 [MOD 3] := by
    apply ModEq.add
    · apply ModEq.add
      · rfl
      · exact h2
    · exact h4
  have h_zero : 1 + 10^M + 10^(2*M) ≡ 0 [MOD 3] := h_add.trans (by decide)
  exact modEq_zero_iff_dvd.mp h_zero

theorem reverse_nat_repeat (M N : ℕ) (hM_pos : M > 0) (hM : M < 10^N) :
    let k := N - (digits 10 M).length
    digits 10 (M + M * 10^N + M * 10^(2*N)) =
    digits 10 M ++ List.replicate k 0 ++ digits 10 M ++ List.replicate k 0 ++ digits 10 M := by
  intro k
  have h_len : (digits 10 M).length ≤ N := by
    exact (digits_length_le_iff (by decide) M).mpr hM
  have h_eq : (digits 10 M).length + k = N := by
    dsimp [k]
    omega
  let Y := M + M * 10^N
  have h_Y_eq : Y = M + 10^((digits 10 M).length + k) * M := by
    rw [h_eq]
    ring
  have h1 := digits_append_zeroes_append_digits_10 hM_pos (k := k) (n := M) (m := M)
  rw [← h_Y_eq] at h1
  have h2 := digits_append_zeroes_append_digits_10 hM_pos (k := k) (n := Y) (m := M)
  have h_len_Y : (digits 10 Y).length = N + (digits 10 M).length := by
    rw [← h1]
    simp
    omega
  have h_pow : (digits 10 Y).length + k = 2 * N := by
    omega
  rw [h_pow] at h2
  have h_assoc : Y + 10^(2*N) * M = M + M * 10^N + M * 10^(2*N) := by
    ring
  rw [h_assoc] at h2
  rw [← h2]
  rw [← h1]

theorem reverse_nat_repeat_mul (M N : ℕ) (hM_pos : M > 0) (hM : M < 10^N) :
    reverse_nat (M * (1 + 10^N + 10^(2*N))) = reverse_nat M * (1 + 10^N + 10^(2*N)) := by
  let k := N - (digits 10 M).length
  have h_len : (digits 10 M).length ≤ N := by
    exact (digits_length_le_iff (by decide) M).mpr hM
  have h_eq : (digits 10 M).length + k = N := by
    dsimp [k]
    omega
  have h_X : M * (1 + 10^N + 10^(2*N)) = M + M * 10^N + M * 10^(2*N) := by ring
  unfold reverse_nat
  rw [h_X]
  have h_digits := reverse_nat_repeat M N hM_pos hM
  dsimp [k] at h_digits
  rw [h_digits]
  have h_rev := list_reverse_repeat (digits 10 M) k
  rw [h_rev]
  let L1 := (digits 10 M).reverse ++ List.replicate k 0
  have h_L1_len : L1.length = N := by
    dsimp [L1]
    rw [List.length_append, List.length_reverse, List.length_replicate]
    exact h_eq
  have h_append3 : (digits 10 M).reverse ++ List.replicate k 0 ++ (digits 10 M).reverse ++ List.replicate k 0 ++ (digits 10 M).reverse = L1 ++ L1 ++ (digits 10 M).reverse := by
    dsimp [L1]
    simp
  rw [h_append3]
  rw [ofDigits_append, ofDigits_append]
  rw [h_L1_len]
  have h_L1_val : ofDigits 10 L1 = ofDigits 10 (digits 10 M).reverse := by
    dsimp [L1]
    exact ofDigits_append_replicate_zero 10 (digits 10 M).reverse k
  rw [h_L1_val]
  have h_L2_len : (L1 ++ L1).length = N * 2 := by
    rw [List.length_append, h_L1_len]
    ring
  rw [h_L2_len]
  have h_ring : 2 * N = N * 2 := by ring
  rw [h_ring]
  ring

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

lemma a_ne_target_of_exists_candidate (m T : ℕ) (hm_pos : m > 0) (h_ex : ∃ C, C > 0 ∧ m ∣ C ∧ m ∣ reverse_nat C ∧ C < T) :
    a m ≠ T := by
  intro h_eq
  rcases h_ex with ⟨C, hC_pos, h_div, h_rev, h_lt⟩
  have hm_ne : m ≠ 0 := by omega
  dsimp [a] at h_eq
  rw [if_neg hm_ne] at h_eq
  have h_prop : ∃ k, k > 0 ∧ m ∣ reverse_nat (k * m) := by
    rcases h_div with ⟨k, hk⟩
    use k
    have hk_pos : k > 0 := by
      by_contra hk0
      have : k = 0 := by omega
      subst this
      simp [hk] at hC_pos
    refine ⟨hk_pos, ?_⟩
    have hk_eq : k * m = C := by
      rw [Nat.mul_comm, ← hk]
    rw [hk_eq]
    exact h_rev
  rw [dif_pos h_prop] at h_eq
  rcases h_div with ⟨k, hk⟩
  have hk_pos : k > 0 := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp [hk] at hC_pos
  have h_spec_k : k > 0 ∧ m ∣ reverse_nat (k * m) := by
    refine ⟨hk_pos, ?_⟩
    have hk_eq : k * m = C := by
      rw [Nat.mul_comm, ← hk]
    rw [hk_eq]
    exact h_rev
  have h_le : Nat.find h_prop ≤ k := Nat.find_min' h_prop h_spec_k
  have h_le_mul : Nat.find h_prop * m ≤ k * m := Nat.mul_le_mul_right m h_le
  have hk_eq : k * m = C := by
    rw [Nat.mul_comm, ← hk]
  rw [hk_eq] at h_le_mul
  omega

def W : ℕ → ℕ
  | 0 => 4899999987
  | d + 1 => W d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d))

def W_rev_val : ℕ → ℕ
  | 0 => 7899999984
  | d + 1 => W_rev_val d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d))

lemma W_pos (d : ℕ) : W d > 0 := by
  induction d with
  | zero =>
    unfold W
    decide
  | succ d ih =>
    unfold W
    have h_term : 1 + 10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d) > 0 := by
      have : 1 + 10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d) = succ (10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d)) := by omega
      rw [this]
      exact Nat.succ_pos _
    exact Nat.mul_pos ih h_term

lemma ten_pow_ge_one (N : ℕ) : 10^N ≥ 1 := by
  have : 10 ≥ 1 := by decide
  exact Nat.one_le_pow N 10 this

lemma W_lt (d : ℕ) : W d < 10 ^ (10 * 3^d) := by
  induction d with
  | zero =>
    unfold W
    decide
  | succ d ih =>
    unfold W
    let N := 10 * 3^d
    have h_ih : W d < 10^N := ih
    have h_le : W d ≤ 10^N - 1 := by omega
    have h_mul_le : W d * (1 + 10^N + 10^(2*N)) ≤ (10^N - 1) * (1 + 10^N + 10^(2*N)) := Nat.mul_le_mul_right (1 + 10^N + 10^(2*N)) h_le
    have h_alg := ten_pow_algebra N (ten_pow_ge_one N)
    rw [h_alg] at h_mul_le
    have h_ring : 3 * N = 10 * 3^(d + 1) := by ring
    have h_lt_term : 10^(3 * N) - 1 < 10^(3 * N) := by
      have := ten_pow_ge_one (3 * N)
      omega
    have h_final : W d * (1 + 10^N + 10^(2*N)) < 10^(3 * N) := Nat.lt_of_le_of_lt h_mul_le h_lt_term
    rw [h_ring] at h_final
    have h_ring2 : W d * (1 + 10^N + 10^(2*N)) = W d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d)) := by
      dsimp [N]
      ring
    rw [h_ring2] at h_final
    exact h_final

lemma W_div (d : ℕ) : 3^(d + 5) ∣ W d := by
  induction d with
  | zero =>
    unfold W
    decide
  | succ d ih =>
    unfold W
    have h_three := three_dvd_ten_pow_add (10 * 3^d)
    have h_mul := Nat.mul_dvd_mul ih h_three
    have h_ring_L : 3^(d + 5) * 3 = 3^(d + 6) := by ring
    rw [← h_ring_L]
    have h_ring_R : W d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d)) = W d * (1 + 10^(10 * 3^d) + 10^(2 * (10 * 3^d))) := by ring
    rw [h_ring_R]
    exact h_mul

lemma W_rev (d : ℕ) : reverse_nat (W d) = W_rev_val d := by
  induction d with
  | zero =>
    unfold W W_rev_val reverse_nat
    simp
    decide
  | succ d ih =>
    let N := 10 * 3^d
    have h_pos := W_pos d
    have h_lt := W_lt d
    change W d < 10^N at h_lt
    have h_repeat := reverse_nat_repeat_mul (W d) N h_pos h_lt
    have h_unfold : W (d + 1) = W d * (1 + 10^N + 10^(2*N)) := by
      change W d * (1 + 10 ^ (10 * 3 ^ d) + 10 ^ (20 * 3 ^ d)) = W d * (1 + 10 ^ N + 10 ^ (2 * N))
      dsimp [N]
      ring
    unfold W_rev_val
    rw [h_unfold, h_repeat, ih]
    dsimp [N]
    ring

lemma W_rev_div (d : ℕ) : 3^(d + 5) ∣ reverse_nat (W d) := by
  rw [W_rev d]
  induction d with
  | zero =>
    unfold W_rev_val
    decide
  | succ d ih =>
    unfold W_rev_val
    have h_three := three_dvd_ten_pow_add (10 * 3^d)
    have h_mul := Nat.mul_dvd_mul ih h_three
    have h_ring_L : 3^(d + 5) * 3 = 3^(d + 6) := by ring
    rw [← h_ring_L]
    have h_ring_R : W_rev_val d * (1 + 10^(10 * 3^d) + 10^(20 * 3^d)) = W_rev_val d * (1 + 10^(10 * 3^d) + 10^(2 * (10 * 3^d))) := by ring
    rw [h_ring_R]
    exact h_mul

theorem a_ge_seven_ne (n : ℕ) : a (3^(n+7)) ≠ 10 ^ (3 ^ (n + 5)) - 1 := by
  let m := 3^(n+7)
  let T := 10 ^ (3 ^ (n + 5)) - 1
  have hm_pos : m > 0 := Nat.one_le_pow (n+7) 3 (by decide)
  have h_ex : ∃ C, C > 0 ∧ m ∣ C ∧ m ∣ reverse_nat C ∧ C < T := by
    let d := n + 2
    use W d
    refine ⟨W_pos d, ?_, ?_, ?_⟩
    · have h_div := W_div d
      have h_ring : d + 5 = n + 7 := by ring
      rw [h_ring] at h_div
      exact h_div
    · have h_rev_div := W_rev_div d
      have h_ring : d + 5 = n + 7 := by ring
      rw [h_ring] at h_rev_div
      exact h_rev_div
    · have h_lt := W_lt d
      have h_exp_ring : 3^(n + 5) = 27 * 3^(n + 2) := by ring
      have h_lt_exp : 10 * 3^(n + 2) < 3^(n + 5) := by
        rw [h_exp_ring]
        have h3_pos : 3^(n+2) > 0 := Nat.one_le_pow (n+2) 3 (by decide)
        exact Nat.mul_lt_mul_of_pos_right (by decide) h3_pos
      have h_pow_lt : 10 ^ (10 * 3^(n + 2)) < 10 ^ (3 ^ (n + 5)) := by
        have : 1 < 10 := by decide
        exact Nat.pow_lt_pow_right this h_lt_exp
      have h_pow_le : 10 ^ (10 * 3^(n + 2)) ≤ 10 ^ (3 ^ (n + 5)) - 1 := by
        omega
      exact Nat.lt_of_lt_of_le h_lt h_pow_le
  exact a_ne_target_of_exists_candidate m T hm_pos h_ex
