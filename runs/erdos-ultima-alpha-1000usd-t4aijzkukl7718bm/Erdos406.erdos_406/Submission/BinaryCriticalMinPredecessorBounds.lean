import Submission.BinaryCriticalMinObserverCone
import Submission.BinaryCriticalPredecessorTower

/-! Necessary linear bounds on EVERY observer at guarded predecessors of
powers, and an upper bound attained by SOME observer at a single good input.
They may be used to reject fixed matrix tables, not the original conjecture. -/
namespace Erdos406BinaryCriticalMinObserver
open Erdos406BinaryCriticalGuard Erdos406BinaryCriticalTower
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma every_observer_predecessor_lower (S : ι → ℕ → ℝ) (r : ℕ) (γ B : ℝ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, ∀ j, ∃ i, S i (3*n+d.val)≤3*S j n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] → ∀ i,
      γ*k*(2:ℝ)^k≤S i (2^k)+B*(2:ℝ)^k)
    (n s k : ℕ) (hn : 0<n) (hg : Nat.digits 3 (n%3^r) ⊆ [0,1])
    (he : 3^(s+1)*n+1=2^k) (i : ι) :
    γ*k*(2:ℝ)^k≤(3:ℝ)^(s+1)*S i n+B*(2:ℝ)^k := by
  let V : ℕ → ℝ := fun m => minValue (fun j => S j m)
  have hs : ∀ m : ℕ, 0 < m → Nat.digits 3 (m%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, V (3*m+d.val)≤3*V m := by
    intro m hm hmg d
    exact min_construction _ _ (hstep m hm hmg d)
  have hh := guarded_zero_one_bound V r hs n hn hg s
  rw [he] at hh
  obtain ⟨j,hj⟩ := minValue_attained (fun j => S j (2^k))
  have hp := hpower k hh.1 j
  have hev : V (2^k)=S j (2^k) := hj
  have hu : V n≤S i n := minValue_le _ i
  have hm := mul_le_mul_of_nonneg_left hu (show (0:ℝ)≤3^(s+1) by positivity)
  rw [← hev] at hp
  linarith [hh.2]

/-- The same observer need not attain the minimum at two different good
inputs. Thus these upper tests must be applied ONE input at a time. -/
lemma exists_observer_good_upper (S : ι → ℕ → ℝ) (r : ℕ) (C : ℝ)
    (h1 : ∀ i, 0≤S i 1) (hseed : minValue (fun i => S i 1)≤C)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, ∀ j, ∃ i, S i (3*n+d.val)≤3*S j n)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ i, S i n≤n*C := by
  let V : ℕ → ℝ := fun m => minValue (fun i => S i m)
  have hs : ∀ m : ℕ, 0 < m → Nat.digits 3 (m%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, V (3*m+d.val)≤3*V m := by
    intro m hm hmg d
    exact min_construction _ _ (hstep m hm hmg d)
  have hh := good_linear_upper V r (le_minValue _ 0 h1) hs n hn hg
  have hm := mul_le_mul_of_nonneg_left hseed (show (0:ℝ)≤n by positivity)
  obtain ⟨i,hi⟩ := minValue_attained (fun i => S i n)
  have he : V n=S i n := hi
  refine ⟨i,?_⟩
  rw [← he]
  exact hh.trans hm

#print axioms every_observer_predecessor_lower
#print axioms exists_observer_good_upper
end Erdos406BinaryCriticalMinObserver
