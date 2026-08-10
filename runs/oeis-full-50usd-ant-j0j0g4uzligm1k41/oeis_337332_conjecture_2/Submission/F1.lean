import FormalConjectures.Util.ProblemImports

open Finset Nat

theorem chsymm (n k : ℕ) : (n + k).choose n = (n + k).choose k := by
  conv_lhs => rw [← Nat.choose_symm (Nat.le_add_right n k)]
  congr 1; omega

theorem key1 (n k : ℕ) : (n + 1) ∣ (n + k + 1) * (n + k).choose k := by
  have h := Nat.succ_mul_choose_eq (n + k) n
  rw [chsymm] at h
  simp only [Nat.succ_eq_add_one] at h
  rw [h]
  exact dvd_mul_left (n + 1) _

theorem key2 (n k : ℕ) : (n + 1) ∣ k * (n + k).choose k := by
  have h1 := key1 n k
  have hsplit : (n + k + 1) * (n + k).choose k
      = (n + 1) * (n + k).choose k + k * (n + k).choose k := by ring
  rw [hsplit] at h1
  exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp h1

theorem key3 (n k : ℕ) (hk : k ≤ n) : (n + 1) ∣ (n - k + 1) * (n + k).choose k := by
  have hsum : k * (n + k).choose k + (n - k + 1) * (n + k).choose k
      = (n + 1) * (n + k).choose k := by
    rw [← add_mul]
    congr 1; omega
  have hd : (n + 1) ∣ k * (n + k).choose k + (n - k + 1) * (n + k).choose k := by
    rw [hsum]; exact Dvd.intro _ rfl
  exact (Nat.dvd_add_right (key2 n k)).mp hd

theorem F1core (n k : ℕ) (hk : k ≤ n) :
    (n + 1) ∣ (n + k).choose k * Nat.centralBinom (n - k) := by
  have hcat : (n - k + 1) * catalan (n - k) = Nat.centralBinom (n - k) :=
    succ_mul_catalan_eq_centralBinom (n - k)
  have h3 := key3 n k hk
  have hrw : (n + k).choose k * Nat.centralBinom (n - k)
      = ((n - k + 1) * (n + k).choose k) * catalan (n - k) := by
    rw [← hcat]; ring
  rw [hrw]
  exact Dvd.dvd.mul_right h3 (catalan (n - k))

-- The original sequence a(n)
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)

-- F1: (n+1) divides a(n)
theorem F1 (n : ℕ) : ((n : ℤ) + 1) ∣ a n := by
  unfold a
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  have hNat : (n + 1) ∣ (n + k).choose k * Nat.centralBinom (n - k) := F1core n k hkn
  have hInt : ((n : ℤ) + 1) ∣ ((n + k).choose k : ℤ) * (Nat.centralBinom (n - k) : ℤ) := by
    have : ((n + 1 : ℕ) : ℤ) ∣ (((n + k).choose k * Nat.centralBinom (n - k) : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hNat
    push_cast at this ⊢
    convert this using 2
  -- the summand equals (C(n+k,k)*centralBinom(n-k)) * (rest)
  have hrw : (n.choose k : ℤ) * ((n + k).choose k : ℤ) * ((2 * k).choose k : ℤ) *
      (centralBinom (n - k) : ℤ) * ((-8 : ℤ) ^ (n - k))
      = (((n + k).choose k : ℤ) * (Nat.centralBinom (n - k) : ℤ)) *
        ((n.choose k : ℤ) * ((2 * k).choose k : ℤ) * ((-8 : ℤ) ^ (n - k))) := by
    ring
  rw [hrw]
  exact Dvd.dvd.mul_right hInt _

def conjecture_sum (n : ℕ) : ℤ :=
  Finset.sum (range n) fun k =>
    let k_int : ℤ := k;
    let exp : ℕ := n - 1 - k;
    (-1 : ℤ) ^ k * (4 * k_int + 1) * (48 : ℤ) ^ exp * a k

theorem recurrence (m : ℕ) :
    conjecture_sum (m + 1) = 48 * conjecture_sum m + (-1)^m * (4 * (m:ℤ) + 1) * a m := by
  unfold conjecture_sum
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hexp : m - k = (m - 1 - k) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  · rw [Nat.sub_self, pow_zero]
    ring

-- The supercongruence (the genuine open core of the divisibility)
theorem superc (m : ℕ) : ((m : ℤ) + 1) ∣ 48 * conjecture_sum m := by
  sorry

theorem div_n (n : ℕ) (hn : n > 0) : (n : ℤ) ∣ conjecture_sum n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [recurrence]
  push_cast
  apply dvd_add
  · exact superc m
  · have hF := F1 m
    have hr : (-1:ℤ)^m * (4*(m:ℤ)+1) * a m = ((-1)^m*(4*(m:ℤ)+1)) * a m := by ring
    rw [hr]
    exact Dvd.dvd.mul_left hF _
