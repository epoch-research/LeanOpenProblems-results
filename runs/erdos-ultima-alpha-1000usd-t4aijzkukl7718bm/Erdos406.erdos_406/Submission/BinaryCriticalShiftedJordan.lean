import Submission.BinaryCriticalGuardCertificates

/-! Explicit lower-bound error for signed observables. No sufficient concrete
matrix or guarded-cone instance is asserted. -/
namespace Erdos406BinaryCriticalGuard
open Erdos406BinaryCriticalMatrix
open scoped Matrix BigOperators

lemma shifted_jordan_power_lower (x y S : ℕ → ℝ) (B : ℝ)
    (hx1 : 0≤x 1)
    (hx : ∀ n : ℕ, 0<n → 2*x n+2*y n≤x (2*n))
    (hy : ∀ n : ℕ, 0<n → y (2*n)=2*y n)
    (hdom : ∀ n : ℕ, 0<n → x n≤S n+B*y n) (k : ℕ) :
    (y 1)*k*(2:ℝ)^k≤S (2^k)+(B*y 1)*(2:ℝ)^k := by
  have hyp : ∀ j : ℕ, y (2^j)=(2:ℝ)^j*y 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',hy _ (by positivity),ih,pow_succ']
      ring
  have hl := jordan_power_lower x y hx (fun n hn => le_of_eq (hy n hn).symm) k
  have hd := hdom (2^k) (by positivity)
  rw [hyp] at hd
  have hp : (0:ℝ)≤2^k := by positivity
  nlinarith

variable {σ : Type*} [Fintype σ]

lemma positive_orbit_nonneg (v : ℕ → σ → ℝ)
    (A : ℕ → Fin 2 → Matrix σ σ ℝ) (h1 : 0≤v 1)
    (hA : ∀ n : ℕ, 0<n → ∀ d i j, 0≤A n d i j)
    (hstep : ∀ n : ℕ, 0<n → ∀ d : Fin 2, v (2*n+d.val)=A n d *ᵥ v n) :
    ∀ n : ℕ, 0<n → 0≤v n := by
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
    rw [hid] at hs
    rw [hs]
    intro i
    exact dotProduct_nonneg_of_nonneg (hA _ hq d i) hi

/-- The observable u(n) may be signed and may depend on a finite residue phase.
The row error B is compensated by an exact eigen-row, not silently discarded. -/
lemma shifted_matrix_power_lower (v u : ℕ → σ → ℝ)
    (A : ℕ → Matrix σ σ ℝ) (r s : σ → ℝ) (B : ℝ)
    (hv : ∀ n : ℕ, 0<n → 0≤v n) (hr : 0≤r)
    (hstep : ∀ n : ℕ, 0<n → v (2*n)=A n *ᵥ v n)
    (hrowr : ∀ n : ℕ, 0<n → ∀ j, 2*r j+2*s j≤Matrix.vecMul r (A n) j)
    (hrows : ∀ n : ℕ, 0<n → Matrix.vecMul s (A n)=fun j => 2*s j)
    (hdom : ∀ n : ℕ, 0<n → ∀ j, r j≤u n j+B*s j) (k : ℕ) :
    (s ⬝ᵥ v 1)*k*(2:ℝ)^k≤u (2^k) ⬝ᵥ v (2^k)+(B*(s ⬝ᵥ v 1))*(2:ℝ)^k := by
  apply shifted_jordan_power_lower (fun n => r ⬝ᵥ v n) (fun n => s ⬝ᵥ v n)
    (fun n => u n ⬝ᵥ v n) B (dotProduct_nonneg_of_nonneg hr (hv 1 (by decide)))
  · intro n hn
    have hh := Erdos406Matrix.dot_mono_left (hrowr n hn) (hv n hn)
    rw [hstep n hn,Matrix.dotProduct_mulVec]
    calc
      _ = (fun j => 2*r j+2*s j) ⬝ᵥ v n := by
        simp [dotProduct,Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_assoc]
      _ ≤ _ := hh
  · intro n hn
    rw [hstep n hn,Matrix.dotProduct_mulVec,hrows n hn]
    simp [dotProduct,Finset.mul_sum,mul_assoc]
  · intro n hn
    have hh := Erdos406Matrix.dot_mono_left (hdom n hn) (hv n hn)
    simpa [dotProduct,Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_assoc] using hh

end Erdos406BinaryCriticalGuard
