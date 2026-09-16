import Submission.Proof3
open Nat

lemma fib_like_to_Z (k : ℕ) : (fib_like k : M) = fib_Z k := by
  induction k using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      unfold fib_like fib_Z b
      have hb_cast : (((A355898_copy 3773 + 1) % p : ℕ) : M) = (77940394259 : ℕ) := by rw [A355898_copy_3773_mod_b]
      exact hb_cast
    | succ m =>
      cases m with
      | zero =>
        unfold fib_like fib_Z b
        have hb_cast : (((A355898_copy 3774 + 1) % p : ℕ) : M) = (99768150822 : ℕ) := by rw [A355898_copy_3774_mod_b]
        exact hb_cast
      | succ j =>
        have ih1 := ih (j + 1) (by omega)
        have ih2 := ih j (by omega)
        unfold fib_like fib_Z
        have hc : (((fib_like (j + 1) + fib_like j) % p : ℕ) : M) = (fib_like (j + 1) : M) + (fib_like j : M) := by
          rw [zmod_cast_mod]
          push_cast
          rfl
        rw [hc, ih1, ih2]

lemma hc_lemma (n : ℕ) : (b n : M) = (A355898_copy n : M) + 1 := by
  dsimp [b]
  rw [zmod_cast_mod]
  push_cast
  rfl

lemma A355898_copy_K_mod_p (h_conj : ∀ n ≥ 3775, A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2)) :
  (A355898_copy (3773 + K) : M) = 0 := by
  have hb := b_eq_fib_like h_conj K
  have hz := fib_like_to_Z K
  have heq : fib_Z K = 1 := fib_Z_eval_1
  have hz2 : (fib_like K : M) = 1 := Eq.trans hz heq
  have H : (b (3773 + K) : M) = (fib_like K : M) :=
    @congrArg ℕ M (b (3773 + K)) (fib_like K) (fun x => (x : M)) hb
  have H2 : (b (3773 + K) : M) = 1 := Eq.trans H hz2
  have hc := hc_lemma (3773 + K)
  have H3 : (A355898_copy (3773 + K) : M) + 1 = 1 := Eq.trans hc.symm H2
  exact add_right_cancel H3

lemma A355898_copy_K_plus_1_mod_p (h_conj : ∀ n ≥ 3775, A355898_copy n = 1 + A355898_copy (n - 1) + A355898_copy (n - 2)) :
  (A355898_copy (3774 + K) : M) = 0 := by
  have hb := b_eq_fib_like h_conj (K + 1)
  have hz := fib_like_to_Z (K + 1)
  have heq : fib_Z (K + 1) = 1 := by
    have h1 : K + 1 = 249580073234 := rfl
    rw [h1]
    exact fib_Z_eval_2
  have hz2 : (fib_like (K + 1) : M) = 1 := Eq.trans hz heq
  have H : (b (3773 + (K + 1)) : M) = (fib_like (K + 1) : M) :=
    @congrArg ℕ M (b (3773 + (K + 1))) (fib_like (K + 1)) (fun x => (x : M)) hb
  have h_idx : 3773 + (K + 1) = 3774 + K := by omega
  have H2 : b (3773 + (K + 1)) = b (3774 + K) := by rw [h_idx]
  have H3 : (b (3773 + (K + 1)) : M) = (b (3774 + K) : M) :=
    @congrArg ℕ M (b (3773 + (K + 1))) (b (3774 + K)) (fun x => (x : M)) H2
  have H4 : (b (3774 + K) : M) = (fib_like (K + 1) : M) := Eq.trans H3.symm H
  have H5 : (b (3774 + K) : M) = 1 := Eq.trans H4 hz2
  have hc := hc_lemma (3774 + K)
  have H6 : (A355898_copy (3774 + K) : M) + 1 = 1 := Eq.trans hc.symm H5
  exact add_right_cancel H6

