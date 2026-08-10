import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

def mBlocks (n : ℕ) : ℕ := Nat.findGreatest (fun m => m * (m + 1) / 2 ≤ n) n

def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

lemma tri_mono {a b : ℕ} (h : a ≤ b) : a * (a+1)/2 ≤ b * (b+1)/2 := by
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul h (by omega)

lemma mBlocks_spec (n : ℕ) : (mBlocks n) * (mBlocks n + 1) / 2 ≤ n := by
  have := Nat.findGreatest_spec (P := fun m => m*(m+1)/2 ≤ n) (m := 0) (Nat.zero_le n) (by simp)
  simpa [mBlocks] using this

lemma mBlocks_lt (n m : ℕ) (h : n < m * (m+1)/2) : mBlocks n < m := by
  by_contra hc
  push_neg at hc
  have := tri_mono hc
  have := mBlocks_spec n
  omega

lemma le_mBlocks {n m : ℕ} (h : m * (m+1)/2 ≤ n) : m ≤ mBlocks n := by
  have hmn : m ≤ n := by
    have hb : m*2 ≤ m*(m+1) := Nat.mul_le_mul (le_refl m) (by omega)
    have h2 : m ≤ m*(m+1)/2 := by rw [Nat.le_div_iff_mul_le (by norm_num)]; exact hb
    exact le_trans h2 h
  exact Nat.le_findGreatest (P := fun m => m*(m+1)/2 ≤ n) hmn h

lemma mBlocks_eq_iff (n m : ℕ) :
    mBlocks n = m ↔ m*(m+1)/2 ≤ n ∧ n < (m+1)*(m+2)/2 := by
  constructor
  · rintro rfl
    refine ⟨mBlocks_spec n, ?_⟩
    by_contra hc
    push_neg at hc
    have := le_mBlocks hc
    omega
  · rintro ⟨h1, h2⟩
    have hle := le_mBlocks h1
    have hlt := mBlocks_lt n (m+1) h2
    omega
