import FormalConjectures.Util.ProblemImports

open scoped BigOperators

def A240088 (n : ℕ) : ℕ :=
  let triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2
  let square_number (k : ℕ) : ℕ := k ^ 2
  let pentagonal_number (k : ℕ) : ℕ := k * (3 * k - 1) / 2
  let M : ℕ := Nat.sqrt (2 * n) + 1
  Finset.sum (Finset.range M) $ λ i =>
  Finset.sum (Finset.range M) $ λ j =>
  Finset.sum (Finset.range M) $ λ k =>
    if triangular_number i + square_number j + pentagonal_number k = n then 1 else 0

-- key reduction: a Nat solution gives positivity
example (n : ℕ)
    (h : ∃ i j k : ℕ, i * (i + 1) / 2 + j ^ 2 + k * (3 * k - 1) / 2 = n) :
    A240088 n > 0 := by
  obtain ⟨i, j, k, hijk⟩ := h
  -- bounds
  have hM : ∀ x : ℕ, x * (x + 1) / 2 ≤ n → x < Nat.sqrt (2 * n) + 1 := by
    intro x hx
    have hev : 2 ∣ x * (x + 1) := by
      rcases Nat.even_or_odd x with he | ho
      · exact Dvd.dvd.mul_right he.two_dvd _
      · have : Even (x + 1) := by simpa [Nat.even_add_one] using ho
        exact Dvd.dvd.mul_left this.two_dvd _
    have hxx : x * (x + 1) ≤ 2 * n := by
      obtain ⟨c, hc⟩ := hev
      rw [hc] at hx ⊢
      omega
    have hx2 : x * x ≤ 2 * n := by nlinarith [hxx]
    have := Nat.le_sqrt.2 hx2
    omega
  -- bounds for i, j, k
  have hi : i < Nat.sqrt (2 * n) + 1 := hM i (by omega)
  have hj : j < Nat.sqrt (2 * n) + 1 := by
    have hjn : j * j ≤ 2 * n := by
      have : j ^ 2 ≤ n := by omega
      nlinarith [this]
    have := Nat.le_sqrt.2 hjn
    omega
  have hk : k < Nat.sqrt (2 * n) + 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; positivity
    · have hev : 2 ∣ k * (3 * k - 1) := by
        rcases Nat.even_or_odd k with he | ho
        · exact Dvd.dvd.mul_right he.two_dvd _
        · have : Even (3 * k - 1) := by
            rcases ho with ⟨t, ht⟩
            exact ⟨3 * t + 1, by omega⟩
          exact Dvd.dvd.mul_left this.two_dvd _
      have hkn : k * (3 * k - 1) ≤ 2 * n := by
        obtain ⟨c, hc⟩ := hev
        have : k * (3 * k - 1) / 2 ≤ n := by omega
        rw [hc] at this ⊢; omega
      have hkk : k * k ≤ 2 * n := by
        have : k * k ≤ k * (3 * k - 1) := by
          apply Nat.mul_le_mul_left
          omega
        omega
      have := Nat.le_sqrt.2 hkk
      omega
  -- conclude positivity
  set M := Nat.sqrt (2 * n) + 1 with hMdef
  have key : (if i * (i + 1) / 2 + j ^ 2 + k * (3 * k - 1) / 2 = n then (1:ℕ) else 0) = 1 := by
    rw [if_pos hijk]
  show 0 < A240088 n
  unfold A240088
  simp only
  calc 0 < 1 := one_pos
    _ = (if i * (i + 1) / 2 + j ^ 2 + k * (3 * k - 1) / 2 = n then (1:ℕ) else 0) := key.symm
    _ ≤ _ := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun i => Finset.sum (Finset.range M) (fun j => Finset.sum (Finset.range M) (fun k => if i * (i+1)/2 + j^2 + k*(3*k-1)/2 = n then (1:ℕ) else 0))) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi))
        refine le_trans ?_ (Finset.single_le_sum (f := fun j => Finset.sum (Finset.range M) (fun k => if i * (i+1)/2 + j^2 + k*(3*k-1)/2 = n then (1:ℕ) else 0)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj))
        exact Finset.single_le_sum (f := fun k => if i * (i+1)/2 + j^2 + k*(3*k-1)/2 = n then (1:ℕ) else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hk)
