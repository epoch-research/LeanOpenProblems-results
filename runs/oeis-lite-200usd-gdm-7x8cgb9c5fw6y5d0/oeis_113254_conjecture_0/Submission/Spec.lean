import FormalConjectures.Util.ProblemImports

open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

def y (k : ℕ) : ℤ :=
  match k with
  | 0 => -2
  | 1 => -352
  | k' + 1 + 1 => 112 * y (k' + 1) - 4096 * y k'

def z (k : ℕ) : ℤ :=
  match k with
  | 0 => -56
  | 1 => -2176
  | k' + 1 + 1 => 112 * z (k' + 1) - 4096 * z k'

theorem z_eq_y (k : ℕ) : z (k + 1) = 12 * y (k + 1) - 1024 * y k := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | _ | k
  · rfl
  · rfl
  · have ih1 : z (k + 1 + 1) = 12 * y (k + 1 + 1) - 1024 * y (k + 1) := by
      apply ih (k + 1)
      omega
    have ih2 : z (k + 1) = 12 * y (k + 1) - 1024 * y k := by
      apply ih k
      omega
    unfold z
    unfold y
    rw [ih1, ih2]
    ring

theorem y_eq_z (k : ℕ) : 4 * y (k + 1) = - z (k + 1) + 64 * z k := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | _ | k
  · rfl
  · rfl
  · have ih1 : 4 * y (k + 1 + 1) = - z (k + 1 + 1) + 64 * z (k + 1) := by
      apply ih (k + 1)
      omega
    have ih2 : 4 * y (k + 1) = - z (k + 1) + 64 * z k := by
      apply ih k
      omega
    have hy : y (k + 1 + 1 + 1) = 112 * y (k + 1 + 1) - 4096 * y (k + 1) := rfl
    have h_LHS : 4 * y (k + 1 + 1 + 1) = 112 * (4 * y (k + 1 + 1)) - 4096 * (4 * y (k + 1)) := by
      rw [hy]
      ring
    have hz : z (k + 1 + 1 + 1) = 112 * z (k + 1 + 1) - 4096 * z (k + 1) := rfl
    have hz2 : z (k + 1 + 1) = 112 * z (k + 1) - 4096 * z k := rfl
    rw [hz, h_LHS, ih1, ih2, hz2]
    ring

theorem zk_rel (k : ℕ) : 4 * z k = y (k + 1) - 64 * y k := by
  have h1 := z_eq_y k
  have h2 := y_eq_z k
  linarith

theorem z_sq_step (k : ℕ) : 16 * z (k + 1) ^ 2 = -768 * y (k + 1) ^ 2 + 3072 * (4 * z k) ^ 2 + 4194304 * y k ^ 2 := by
  have h1 := z_eq_y k
  have h2 := zk_rel k
  rw [h1, h2]
  ring

theorem yk2_rel (k : ℕ) : 4 * y (k + 1 + 1) = -48 * z (k + 1) + 1024 * (4 * z k) := by
  have h1 := y_eq_z (k + 1)
  have hz : z (k + 1 + 1) = 112 * z (k + 1) - 4096 * z k := rfl
  linarith

theorem y_sq_step (k : ℕ) : 16 * y (k + 1 + 1) ^ 2 = -768 * z (k + 1) ^ 2 + 3072 * (4 * y (k + 1)) ^ 2 + 262144 * (4 * z k) ^ 2 := by
  have h_yk2 := yk2_rel k
  have h_yk1 := y_eq_z k
  have h_LHS : 16 * y (k + 1 + 1) ^ 2 = (4 * y (k + 1 + 1)) ^ 2 := by ring
  rw [h_LHS, h_yk2, h_yk1]
  ring

theorem a_recurrence (n : ℕ) : a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  have h1 : a (n + 6) = -4 * a (n + 5) + 256 * a (n + 3) + 4096 * a (n + 2) := rfl
  have h2 : a (n + 5) = -4 * a (n + 4) + 256 * a (n + 2) + 4096 * a (n + 1) := rfl
  have h3 : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := rfl
  linarith

theorem a_odd_eq (k : ℕ) : a (4 * k + 1) = y k ^ 2 ∧ a (4 * k + 3) = z k ^ 2 := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | _ | k
  · constructor <;> rfl
  · constructor <;> rfl
  · have ih1 : a (4 * (k + 1) + 1) = y (k + 1) ^ 2 ∧ a (4 * (k + 1) + 3) = z (k + 1) ^ 2 := by
      apply ih (k + 1)
      omega
    have ih2 : a (4 * k + 1) = y k ^ 2 ∧ a (4 * k + 3) = z k ^ 2 := by
      apply ih k
      omega
    have h_a_1 : a (4 * (k + 2) + 1) = y (k + 2) ^ 2 := by
      have h_rec := a_recurrence (4 * k + 3)
      have h_comm1 : 4 * (k + 2) + 1 = 4 * k + 3 + 6 := by omega
      have h_comm2 : 4 * k + 3 + 4 = 4 * (k + 1) + 3 := by omega
      have h_comm3 : 4 * k + 3 + 2 = 4 * (k + 1) + 1 := by omega
      rw [h_comm1]
      rw [h_rec, h_comm2, h_comm3]
      rw [ih1.left, ih1.right, ih2.right]
      have h_ysq := y_sq_step k
      linarith
    have h_a_2 : a (4 * (k + 2) + 3) = z (k + 2) ^ 2 := by
      have h_rec := a_recurrence (4 * k + 5)
      have h_comm1 : 4 * (k + 2) + 3 = 4 * k + 5 + 6 := by omega
      have h_comm2 : 4 * k + 5 + 4 = 4 * (k + 2) + 1 := by omega
      have h_comm3 : 4 * k + 5 + 2 = 4 * (k + 1) + 3 := by omega
      have h_comm4 : 4 * k + 5 = 4 * (k + 1) + 1 := by omega
      rw [h_comm1]
      rw [h_rec, h_comm2, h_comm3, h_comm4]
      rw [h_a_1, ih1.right, ih1.left]
      have h_zsq := z_sq_step (k + 1)
      linarith
    exact ⟨h_a_1, h_a_2⟩

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h_even : ∃ k, n = 2 * k := Nat.dvd_of_mod_eq_zero h
    rcases h_even with ⟨k, rfl⟩
    have h_eq : 2 * (2 * k) + 1 = 4 * k + 1 := by omega
    rw [h_eq]
    have h_sq := (a_odd_eq k).left
    use y k
    rw [h_sq]
    ring
  · have h_odd : n = 2 * (n / 2) + 1 := by
      have h_div := Nat.div_add_mod n 2
      rw [h] at h_div
      omega
    generalize hn : n / 2 = k
    rw [hn] at h_odd
    rw [h_odd]
    have h_eq : 2 * (2 * k + 1) + 1 = 4 * k + 3 := by omega
    rw [h_eq]
    have h_sq := (a_odd_eq k).right
    use z k
    rw [h_sq]
    ring

