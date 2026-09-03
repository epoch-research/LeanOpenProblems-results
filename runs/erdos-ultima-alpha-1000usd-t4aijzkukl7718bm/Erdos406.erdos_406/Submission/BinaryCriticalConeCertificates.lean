import Submission.BinaryCriticalMatrixCertificates

/-! Exact invariant-cone criteria for binary critical-rate potentials.
No positive-seed instance, and hence no settlement of Erdős 406, is asserted. -/
namespace Erdos406BinaryCriticalCone
open Erdos406BinaryCriticalMatrix
open scoped Matrix BigOperators

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

/-- A finite cone of row inequalities is inductive on the positive binary orbit. -/
theorem row_invariant (W : ℕ → σ → ℝ)
    (T : Fin 2 → Matrix σ σ ℝ) (R : Matrix κ σ ℝ)
    (C : Fin 2 → Matrix κ κ ℝ)
    (hC : ∀ d i j, 0 ≤ C d i j)
    (h1 : 0 ≤ R *ᵥ W 1)
    (hstep : ∀ n : ℕ, 0 < n → ∀ d : Fin 2,
      W (2*n+d.val) = T d *ᵥ W n)
    (hclose : ∀ d, R * T d = C d * R) :
    ∀ n : ℕ, 0 < n → 0 ≤ R *ᵥ W n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : n=1
    · simpa [he] using h1
    have hq : 0<n/2 := by omega
    have hi := ih (n/2) (Nat.div_lt_self hn (by decide)) hq
    let d : Fin 2 := ⟨n%2, Nat.mod_lt _ (by decide)⟩
    have hid : 2*(n/2)+d.val=n := by dsimp [d]; omega
    have hs := hstep (n/2) hq d
    rw [hid] at hs
    rw [hs, Matrix.mulVec_mulVec, hclose, ← Matrix.mulVec_mulVec]
    intro i
    exact dotProduct_nonneg_of_nonneg (hC d i) hi

/-- A nonnegative combination of certified rows proves a scalar construction
inequality. The observable itself need not have nonnegative coefficients. -/
theorem cone_construction (W : ℕ → σ → ℝ)
    (T : Fin 2 → Matrix σ σ ℝ) (R : Matrix κ σ ℝ)
    (C : Fin 2 → Matrix κ κ ℝ) (S : ℕ → ℝ)
    (L : Fin 2 → κ → ℝ)
    (hC : ∀ d i j, 0 ≤ C d i j)
    (hL : ∀ d i, 0 ≤ L d i)
    (h1 : 0 ≤ R *ᵥ W 1)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      W (2*n+d.val)=T d *ᵥ W n)
    (hclose : ∀ d, R*T d=C d*R)
    (htarget : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      L d ⬝ᵥ (R *ᵥ W n) = 3*S n-S (3*n+d.val)) :
    ∀ n : ℕ, 0<n → ∀ d : Fin 2, S (3*n+d.val) ≤ 3*S n := by
  intro n hn d
  have hi := row_invariant W T R C hC h1 hstep hclose n hn
  have hp := dotProduct_nonneg_of_nonneg (hL d) hi
  rw [htarget n hn d] at hp
  linarith

lemma good_positive_linear_upper (S : ℕ → ℝ) (h1 : 0≤S 1)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 n ⊆ [0,1]) : S n≤n*S 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n=1
    · subst n; simp
    have hd : n%3<2 := by
      rcases Erdos406AffineCertificate.good_unit_mod_three hn hg with hh | hh <;> omega
    have hqpos : 0<n/3 := by omega
    have hq := ih (n/3) (Nat.div_lt_self hn (by decide)) hqpos
      (Erdos406AffineCertificate.good_div_three hg)
    have hs := hstep (n/3) hqpos ⟨n%3,hd⟩
    have hid : 3*(n/3)+n%3=n := by omega
    change S (3*(n/3)+n%3)≤3*S (n/3) at hs
    rw [hid] at hs
    have hle : 3*(n/3:ℕ)≤n := by omega
    have hleR : 3*(n/3:ℕ)≤(n:ℝ) := by exact_mod_cast hle
    have hm := mul_le_mul_of_nonneg_right hleR h1
    nlinarith

/-- Critical-rate bounds need only construction at positive inputs. -/
theorem positive_critical_criterion (S : ℕ → ℝ) (γ B : ℝ)
    (h1 : 0≤S 1) (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((S 1+B)/γ)
  have hN' : S 1+B<(N:ℝ)*γ := (div_lt_iff₀ hγ).mp hN
  have hcut (k : ℕ) (hk : N≤k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    have hu := good_positive_linear_upper S h1 hstep (2^k) (by positivity) hg
    have hp := hpower k
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hu
    have hbound : γ*k≤S 1+B := by
      apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<2^k)).mp
      nlinarith
    have hNk : (N:ℝ)≤k := by exact_mod_cast hk
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^N,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  have hk : k<N := by by_contra h; exact hcut k (by omega) hg
  exact Nat.pow_le_pow_right (by decide) hk.le

/-- Combined conditional certificate. All finite cone equalities and the positive
Jordan lower bound remain obligations for any proposed instance. -/
theorem finiteness (W : ℕ → σ → ℝ)
    (T : Fin 2 → Matrix σ σ ℝ) (R : Matrix κ σ ℝ)
    (C : Fin 2 → Matrix κ κ ℝ) (S : ℕ → ℝ)
    (L : Fin 2 → κ → ℝ) (γ B : ℝ)
    (hC : ∀ d i j, 0≤C d i j) (hL : ∀ d i, 0≤L d i)
    (h1 : 0≤R *ᵥ W 1) (hS1 : 0≤S 1) (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, W (2*n+d.val)=T d *ᵥ W n)
    (hclose : ∀ d, R*T d=C d*R)
    (htarget : ∀ n : ℕ, 0<n → ∀ d : Fin 2,
      L d ⬝ᵥ (R *ᵥ W n)=3*S n-S (3*n+d.val))
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite :=
  positive_critical_criterion S γ B hS1 hγ
    (cone_construction W T R C S L hC hL h1 hstep hclose htarget) hpower

end Erdos406BinaryCriticalCone
