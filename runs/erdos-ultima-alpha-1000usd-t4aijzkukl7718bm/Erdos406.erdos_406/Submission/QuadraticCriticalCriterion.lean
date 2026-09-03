import Submission.CriticalScaledCarry

/-! A sufficient criterion for a quadratic critical potential. The potential and
its global bounds remain hypotheses; no instance or conjecture settlement is asserted. -/
namespace Erdos406QuadraticCritical
open Erdos406AffineCertificate

lemma good_quadratic_upper (S : ℕ → ℝ) (r : ℕ) (h1 : 0 ≤ S 1)
    (hstep : ∀ n : ℕ, 0 < n → Nat.digits 3 (n % 3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val) ≤ 9*S n)
    (n : ℕ) (hn : 0 < n) (hg : Nat.digits 3 n ⊆ [0,1]) :
    S n ≤ (n:ℝ)^2*S 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · subst n; simp
    have hd : n%3 < 2 := by
      rcases good_unit_mod_three hn hg with hh | hh <;> omega
    have hqpos : 0 < n/3 := by omega
    have hgood := good_div_three hg
    have hq := ih (n/3) (Nat.div_lt_self hn (by decide)) hqpos hgood
    have hs := hstep (n/3) hqpos
      (Erdos406BinaryCertificate.good_mod hgood r) ⟨n%3,hd⟩
    have hid : 3*(n/3)+n%3 = n := by omega
    change S (3*(n/3)+n%3) ≤ 9*S (n/3) at hs
    rw [hid] at hs
    have hle : 3*(n/3:ℕ) ≤ n := by omega
    have hleR : 3*(n/3:ℕ) ≤ (n:ℝ) := by exact_mod_cast hle
    have hsq : (3*(n/3:ℕ):ℝ)^2 ≤ (n:ℝ)^2 := by
      exact pow_le_pow_left₀ (by positivity) hleR 2
    have hm := mul_le_mul_of_nonneg_right hsq h1
    nlinarith

theorem criterion (S : ℕ → ℝ) (r : ℕ) (γ B : ℝ)
    (h1 : 0 ≤ S 1) (hγ : 0 < γ)
    (hstep : ∀ n : ℕ, 0 < n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val) ≤ 9*S n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] →
      γ*k*((2:ℝ)^k)^2 ≤ S (2^k)+B*((2:ℝ)^k)^2) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((S 1+B)/γ)
  have hN' : S 1+B < (N:ℝ)*γ := (div_lt_iff₀ hγ).mp hN
  have hcut (k : ℕ) (hk : N ≤ k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    have hu := good_quadratic_upper S r h1 hstep (2^k) (by positivity) hg
    have hp := hpower k (Erdos406BinaryCertificate.good_mod hg r)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hu
    have hbound : γ*k ≤ S 1+B := by
      apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ) < ((2:ℝ)^k)^2)).mp
      nlinarith
    have hNk : (N:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^N,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  have hk : k < N := by by_contra h; exact hcut k (by omega) hg
  exact Nat.pow_le_pow_right (by decide) hk.le

#print axioms good_quadratic_upper
#print axioms criterion
end Erdos406QuadraticCritical
