import Submission.AllScale
open Nat Finset BigOperators Int

theorem test_final (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1))
      [ZMOD (p ^ (3 * k) : ℤ)] := by
  let N := n*p^(k-1)
  have hN : 0<N := by
    dsimp [N]
    exact mul_pos hn (pow_pos hp.pos _)
  have hdiv : p^(k-1)∣N := by
    dsimp [N]
    exact dvd_mul_left _ _
  have hs := a_gen_scale_all m hp hp5 hN hdiv
  have hkpow : p^k=p^(k-1)*p := by
    conv_lhs => rw [show k=(k-1)+1 by omega, pow_succ]
  have hhigh : p*N=n*p^k := by
    dsimp [N]
    rw [hkpow]
    ring
  have hlow : N=n*p^(k-1) := rfl
  have hexp : 3*((k-1)+1)=3*k := by omega
  rw [hhigh, hlow, hexp] at hs
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs
