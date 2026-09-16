import Submission.Proof2

open Nat

lemma zmod_cast_mod (a : ℕ) : ((a % p : ℕ) : M) = (a : M) := by
  change ((a % 195318521017 : ℕ) : ZMod 195318521017) = (a : ZMod 195318521017)
  exact ZMod.natCast_mod a 195318521017

def b (n : ℕ) : ℕ := (A355898_copy n + 1) % p

def fib_like : ℕ → ℕ
| 0 => b 3773
| 1 => b 3774
| n + 2 => (fib_like (n + 1) + fib_like n) % p

lemma b_eq_fib_like (h_conj : ∀ n ≥ 3775, A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2)) (k : ℕ) :
  b (3773 + k) = fib_like k := by
  induction k using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => dsimp [fib_like]
    | succ m =>
      cases m with
      | zero => dsimp [fib_like]
      | succ j =>
        have h_eq : 3773 + (j + 2) = 3775 + j := by omega
        rw [h_eq]
        have hc := h_conj (3775 + j) (by omega)
        have h_1 : 3775 + j - 1 = 3774 + j := by omega
        have h_2 : 3775 + j - 2 = 3773 + j := by omega
        change (A355898_copy (3775 + j) + 1) % p = (fib_like (j + 1) + fib_like j) % p
        rw [hc, h_1, h_2]
        have h1 : 1 + A355898_copy (3774 + j) + A355898_copy (3773 + j) + 1 = (A355898_copy (3774 + j) + 1) + (A355898_copy (3773 + j) + 1) := by omega
        rw [h1, Nat.add_mod]
        have IH1 := ih (j + 1) (by omega)
        have IH2 := ih j (by omega)
        have h_eq1 : 3773 + (j + 1) = 3774 + j := by omega
        have h_eq2 : 3773 + j = 3773 + j := by rfl
        rw [h_eq1] at IH1
        rw [h_eq2] at IH2
        change (A355898_copy (3774 + j) + 1) % p = fib_like (j + 1) at IH1
        change (A355898_copy (3773 + j) + 1) % p = fib_like j at IH2
        rw [IH1, IH2]

def fib_Z : ℕ → M
| 0 => 77940394259
| 1 => 99768150822
| n + 2 => fib_Z (n + 1) + fib_Z n

lemma vec_mul_mul_Z (A B : MatZ) (v : M × M) : vec_mul_Z (mul_Z A B) v = vec_mul_Z A (vec_mul_Z B v) := by
  rcases A with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases B with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  rcases v with ⟨x, y⟩
  dsimp [vec_mul_Z, mul_Z]
  apply Prod.ext <;> ring

lemma fib_Z_eq_vec_mul_full (n : ℕ) : (fib_Z (n + 1), fib_Z n) = vec_mul_Z (mat_pow_Z n) (99768150822, 77940394259) := by
  induction n with
  | zero => dsimp [fib_Z, mat_pow_Z, m0_Z, vec_mul_Z]; ring_nf
  | succ k ih =>
    dsimp [mat_pow_Z]
    rw [vec_mul_mul_Z]
    rw [← ih]
    dsimp [T_Z, vec_mul_Z]
    have h_eq : fib_Z (k + 1 + 1) = fib_Z (k + 1) + fib_Z k := rfl
    rw [h_eq]
    apply Prod.ext <;> ring

def K : ℕ := 249580073233

lemma fib_Z_eval_1 : fib_Z K = 1 := by
  have h := fib_Z_eq_vec_mul_full K
  have h_final : (fib_Z (K + 1), fib_Z K) = (1, 1) := @Eq.trans (M × M) (fib_Z (K + 1), fib_Z K) (vec_mul_Z (mat_pow_Z K) (99768150822, 77940394259)) (1, 1) h hit_one_one_Z
  exact @congrArg (M × M) M (fib_Z (K + 1), fib_Z K) (1, 1) Prod.snd h_final

lemma fib_Z_eval_2 : fib_Z (K + 1) = 1 := by
  have h := fib_Z_eq_vec_mul_full K
  have h_final : (fib_Z (K + 1), fib_Z K) = (1, 1) := @Eq.trans (M × M) (fib_Z (K + 1), fib_Z K) (vec_mul_Z (mat_pow_Z K) (99768150822, 77940394259)) (1, 1) h hit_one_one_Z
  exact @congrArg (M × M) M (fib_Z (K + 1), fib_Z K) (1, 1) Prod.fst h_final

