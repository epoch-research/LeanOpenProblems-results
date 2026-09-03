import Submission.BinaryCriticalJointOrbit
import Submission.BinaryCertificates

/-! Residue-guarded critical binary certificates. These criteria weaken the
all-input construction requirement, but no sufficient instance is supplied. -/
namespace Erdos406BinaryCriticalGuard
open Erdos406BinaryCriticalCone Erdos406AffineCertificate
open scoped Matrix BigOperators

variable {σ κ ρ : Type*} [Fintype σ] [Fintype κ]

/-- Row cones indexed by a finite-state observation of the binary input. -/
theorem row_invariant (W : ℕ → σ → ℝ) (Q : ℕ → ρ)
    (next : ρ → Fin 2 → ρ) (T : Fin 2 → Matrix σ σ ℝ)
    (R : ρ → Matrix κ σ ℝ) (C : ρ → Fin 2 → Matrix κ κ ℝ)
    (hC : ∀ q d i j, 0≤C q d i j) (h1 : 0≤R (Q 1) *ᵥ W 1)
    (hQ : ∀ n : ℕ, 0<n → ∀ d : Fin 2, Q (2*n+d.val)=next (Q n) d)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, W (2*n+d.val)=T d *ᵥ W n)
    (hclose : ∀ q d, R (next q d)*T d=C q d*R q) :
    ∀ n : ℕ, 0<n → 0≤R (Q n) *ᵥ W n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : n=1
    · simpa [he] using h1
    have hq : 0<n/2 := by omega
    have hi := ih (n/2) (Nat.div_lt_self hn (by decide)) hq
    let d : Fin 2 := ⟨n%2,Nat.mod_lt _ (by decide)⟩
    have hid : 2*(n/2)+d.val=n := by dsimp [d]; omega
    have hs := hstep (n/2) hq d
    have hqs := hQ (n/2) hq d
    rw [hid] at hs hqs
    rw [hs,hqs,Matrix.mulVec_mulVec,hclose,← Matrix.mulVec_mulVec]
    intro i
    exact dotProduct_nonneg_of_nonneg (hC _ d i) hi

def residueState (r n : ℕ) : Fin (3^r) :=
  ⟨n%3^r,Nat.mod_lt _ (by positivity)⟩

def residueNext (r : ℕ) (q : Fin (3^r)) (d : Fin 2) : Fin (3^r) :=
  ⟨(2*q.val+d.val)%3^r,Nat.mod_lt _ (by positivity)⟩

lemma residue_step (r n : ℕ) (d : Fin 2) :
    residueState r (2*n+d.val)=residueNext r (residueState r n) d := by
  apply Fin.ext
  simp [residueState,residueNext,Nat.add_mod,Nat.mul_mod]

/-- Guard preservation is arithmetic, independent of any candidate potential. -/
lemma good_residue_step (r n : ℕ) (d : Fin 2)
    (hg : Nat.digits 3 (n%3^r) ⊆ [0,1]) :
    Nat.digits 3 ((3*n+d.val)%3^r) ⊆ [0,1] := by
  have hh := good_three_mul_add hg (show d.val ∈ [0,1] from by fin_cases d <;> simp)
  have hm := Erdos406BinaryCertificate.good_mod hh r
  have he : (3*(n%3^r)+d.val)%3^r=(3*n+d.val)%3^r := by
    simp [Nat.add_mod,Nat.mul_mod]
  rwa [he] at hm

lemma good_linear_upper (S : ℕ → ℝ) (r : ℕ) (h1 : 0≤S 1)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 n ⊆ [0,1]) : S n≤n*S 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n=1
    · subst n; simp
    have hd : n%3<2 := by
      rcases good_unit_mod_three hn hg with hh | hh <;> omega
    have hqpos : 0<n/3 := by omega
    have hgood := good_div_three hg
    have hq := ih (n/3) (Nat.div_lt_self hn (by decide)) hqpos hgood
    have hs := hstep (n/3) hqpos (Erdos406BinaryCertificate.good_mod hgood r) ⟨n%3,hd⟩
    have hid : 3*(n/3)+n%3=n := by omega
    change S (3*(n/3)+n%3)≤3*S (n/3) at hs
    rw [hid] at hs
    have hle : 3*(n/3:ℕ)≤n := by omega
    have hleR : 3*(n/3:ℕ)≤(n:ℝ) := by exact_mod_cast hle
    have hm := mul_le_mul_of_nonneg_right hleR h1
    nlinarith

/-- The power lower bound also need only hold in the good residue classes. -/
theorem critical_criterion (S : ℕ → ℝ) (r : ℕ) (γ B : ℝ)
    (h1 : 0≤S 1) (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] →
      γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((S 1+B)/γ)
  have hN' : S 1+B<(N:ℝ)*γ := (div_lt_iff₀ hγ).mp hN
  have hcut (k : ℕ) (hk : N≤k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    have hu := good_linear_upper S r h1 hstep (2^k) (by positivity) hg
    have hp := hpower k (Erdos406BinaryCertificate.good_mod hg r)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hu
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

/-- A residue-indexed joint cone establishes the guarded scalar inequality. -/
theorem construction (v : ℕ → σ → ℝ) (A : Fin 2 → Matrix σ σ ℝ)
    (u : σ → ℝ) (r : ℕ) (R : Fin (3^r) → Matrix κ (Fin 4 × σ) ℝ)
    (C : Fin (3^r) → Fin 2 → Matrix κ κ ℝ) (L : Fin (3^r) → Fin 2 → κ → ℝ)
    (hC : ∀ q d i j, 0≤C q d i j)
    (hL : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d i, 0≤L q d i)
    (h1 : 0≤R (residueState r 1) *ᵥ jointValue v 1)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, v (2*n+d.val)=A d *ᵥ v n)
    (hclose : ∀ q d, R (residueNext r q d)*jointMatrix A d=C q d*R q)
    (htarget : ∀ q, Nat.digits 3 q.val ⊆ [0,1] → ∀ d,
      Matrix.vecMul (L q d) (R q)=constructionRow u d)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 (n%3^r) ⊆ [0,1]) (d : Fin 2) :
    u ⬝ᵥ v (3*n+d.val)≤3*(u ⬝ᵥ v n) := by
  have hi := row_invariant (jointValue v) (residueState r) (residueNext r)
    (jointMatrix A) R C hC h1 (fun n _ d => residue_step r n d)
    (joint_recurrence v A hstep) hclose n hn
  have hp := dotProduct_nonneg_of_nonneg (hL (residueState r n) hg d) hi
  rw [Matrix.dotProduct_mulVec,htarget _ hg,constructionRow_value] at hp
  linarith

end Erdos406BinaryCriticalGuard
