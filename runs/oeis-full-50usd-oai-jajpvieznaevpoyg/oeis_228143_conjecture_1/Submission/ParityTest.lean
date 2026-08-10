import FormalConjectures.Util.ProblemImports
open BigOperators Nat

lemma central_choose_even (k : ℕ) (hk : 0 < k) : Even ((2*k).choose k) := by
  cases k with
  | zero => omega
  | succ t =>
    use (2*t+1).choose t
    have hsym : (2*t+1).choose (t+1) = (2*t+1).choose t := by
      apply Nat.choose_symm_of_eq_add
      omega
    have htwo : 2 * (t+1) = (2*t+1).succ := by omega
    calc
      (2*(t+1)).choose (t+1) = ((2*t+1).succ).choose (t+1) := by rw [htwo]
      _ = (2*t+1).choose t + (2*t+1).choose (t+1) := Nat.choose_succ_succ (2*t+1) t
      _ = (2*t+1).choose t + (2*t+1).choose t := by rw [hsym]

lemma choose_prod_even {n k : ℕ} (hk : 0 < k) : Even (n.choose k * (n+k).choose k) := by
  by_cases hkn : k ≤ n
  · have hident : n.choose k * (n+k).choose k = (n+k).choose (2*k) * (2*k).choose k := by
      have h := Nat.choose_mul (n := n+k) (k := 2*k) (s := k) (by omega : k ≤ 2*k)
      have hsub1 : n + k - k = n := by omega
      have hsub2 : 2 * k - k = k := by omega
      calc
        n.choose k * (n+k).choose k = (n+k).choose k * n.choose k := by ring
        _ = (n+k).choose k * ((n+k)-k).choose ((2*k)-k) := by rw [hsub1, hsub2]
        _ = (n+k).choose (2*k) * (2*k).choose k := h.symm
    rw [hident]
    exact Even.mul_left (central_choose_even k hk) ((n+k).choose (2*k))
  · have hkgt : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hkgt]
    simp

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

lemma apery_term_even {n k : ℕ} (hk : 0 < k) :
    Even ((n.choose k)^2 * ((Nat.choose (n + k) k))^2) := by
  have hp : Even (n.choose k * (n+k).choose k) := choose_prod_even hk
  rcases hp with ⟨z, hz⟩
  use 2 * z^2
  calc
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2 = (n.choose k * (n+k).choose k)^2 := by ring
    _ = (z+z)^2 := by rw [hz]
    _ = (2 * z^2) + (2 * z^2) := by ring

lemma A005259_odd (n : ℕ) : Odd (A005259' n) := by
  unfold A005259'
  rw [Finset.sum_eq_add_sum_diff_singleton (show (0:ℕ) ∈ Finset.range (n+1) by simp)]
  simp
  have heven : Even (∑ x ∈ Finset.range (n + 1) \ {0}, (n.choose x)^2 * ((n + x).choose x)^2) := by
    apply Finset.even_sum
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
    exact apery_term_even (Nat.pos_of_ne_zero hk.2)
  rcases heven with ⟨z, hz⟩
  use z
  rw [hz]
  omega
