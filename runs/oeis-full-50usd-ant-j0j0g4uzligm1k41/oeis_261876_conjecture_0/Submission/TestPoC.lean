import FormalConjectures.Util.ProblemImports
open Finset BigOperators
set_option maxHeartbeats 1000000

lemma low_bound (W : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < 2^W) (k : ℕ) :
    (∑ i ∈ range k, c i * 2^(W*i)) < 2^(W*k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hexp : 2^(W*(n+1)) = 2^W * 2^(W*n) := by rw [← pow_add]; ring_nf
    rw [hexp]
    have h1 : c n + 1 ≤ 2^W := hc n
    calc (∑ i ∈ range n, c i * 2^(W*i)) + c n * 2^(W*n)
        < 2^(W*n) + c n * 2^(W*n) := by exact Nat.add_lt_add_right ih _
      _ = (c n + 1) * 2^(W*n) := by ring
      _ ≤ 2^W * 2^(W*n) := by exact Nat.mul_le_mul_right _ h1

-- divisibility of upper part
lemma upper_dvd (W : ℕ) (c : ℕ → ℕ) (k M : ℕ) :
    2^(W*(k+1)) ∣ (∑ i ∈ Ico (k+1) M, c i * 2^(W*i)) := by
  apply Finset.dvd_sum
  intro i hi
  rw [Finset.mem_Ico] at hi
  have : 2^(W*(k+1)) ∣ 2^(W*i) := by
    apply pow_dvd_pow
    exact Nat.mul_le_mul_left W hi.1
  exact Dvd.dvd.mul_left this _

lemma digit_extract (W : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < 2^W) (M k : ℕ) (hk : k < M) :
    ((∑ i ∈ range M, c i * 2^(W*i)) / 2^(W*k)) % 2^W = c k := by
  -- split
  have hsplit : (∑ i ∈ range M, c i * 2^(W*i))
      = (∑ i ∈ range k, c i * 2^(W*i)) + (∑ i ∈ Ico k M, c i * 2^(W*i)) := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (le_of_lt hk)]
  have hpeel : (∑ i ∈ Ico k M, c i * 2^(W*i))
      = c k * 2^(W*k) + (∑ i ∈ Ico (k+1) M, c i * 2^(W*i)) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  obtain ⟨U', hU'⟩ := upper_dvd W c k M
  set L := ∑ i ∈ range k, c i * 2^(W*i) with hLdef
  have hLlt : L < 2^(W*k) := low_bound W c hc k
  have hexp : 2^(W*(k+1)) = 2^(W*k) * 2^W := by rw [← pow_add]; ring_nf
  have hN : (∑ i ∈ range M, c i * 2^(W*i)) = L + (c k + 2^W * U') * 2^(W*k) := by
    rw [hsplit, hpeel, hU', hexp]; ring
  rw [hN]
  rw [Nat.add_mul_div_right _ _ (by positivity)]
  rw [Nat.div_eq_of_lt hLlt]
  simp only [Nat.zero_add]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (hc k)

-- Count machinery: connect tuple-count to digit
noncomputable def Fpoly (W B : ℕ) : ℕ := ∑ k ∈ range B, 2^(W*k^2)

-- expansion of F^4
lemma F4_expand (W B : ℕ) :
    (Fpoly W B)^4 = ∑ x ∈ range B, ∑ y ∈ range B, ∑ z ∈ range B, ∑ w ∈ range B,
       2^(W*(x^2+y^2+z^2+w^2)) := by
  unfold Fpoly
  have h2 : (∑ k ∈ range B, (2:ℕ)^(W*k^2))^2
      = ∑ x ∈ range B, ∑ y ∈ range B, 2^(W*(x^2+y^2)) := by
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    rw [← pow_add]; ring_nf
  have h4 : (∑ k ∈ range B, (2:ℕ)^(W*k^2))^4
      = (∑ x ∈ range B, ∑ y ∈ range B, 2^(W*(x^2+y^2)))
        * (∑ z ∈ range B, ∑ w ∈ range B, 2^(W*(z^2+w^2))) := by
    rw [show (4:ℕ) = 2+2 by rfl, pow_add, h2]
  rw [h4, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w _
  rw [← pow_add]; ring_nf
