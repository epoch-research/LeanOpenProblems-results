import Submission.SupportMomentBounds

/-! The ten degree-at-most-three moments form a closed positive recurrence
for the support-two state. This is an auxiliary, finite-law theorem. -/
namespace Erdos7SupportMomentMatrix
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportPolynomialTail Erdos7SupportTailIteration
open Erdos7SupportMomentBounds Erdos7CompressionSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

def monoR (i : Fin 10) (s t : ℚ) : ℚ :=
  match i.val with
  | 0 => 1
  | 1 => t
  | 2 => t^2
  | 3 => t^3
  | 4 => s
  | 5 => s*t
  | 6 => s*t^2
  | 7 => s^2
  | 8 => s^2*t
  | 9 => s^3
  | _ => 0

def coeff (k : Fin 3) (i j : Fin 10) : ℚ :=
  match k.val,i.val,j.val with
  | 0,1,4 => 1
  | 0,2,5 => 2
  | 0,3,6 => 3
  | 0,4,0 => 1
  | 0,5,1 => 1
  | 0,5,7 => 1
  | 0,6,2 => 1
  | 0,6,8 => 2
  | 0,7,4 => 2
  | 0,8,5 => 2
  | 0,8,9 => 1
  | 0,9,7 => 3
  | 1,2,7 => 1
  | 1,3,8 => 3
  | 1,5,4 => 1
  | 1,6,5 => 2
  | 1,6,9 => 1
  | 1,7,0 => 1
  | 1,8,1 => 1
  | 1,8,7 => 2
  | 1,9,4 => 3
  | 2,3,9 => 1
  | 2,6,7 => 1
  | 2,8,4 => 1
  | 2,9,0 => 1
  | _,_,_ => 0

def mono (i : Fin 10) (x : TripleState) : ℚ := monoR i x.1 x.2

lemma coeff_nonneg : ∀ k i j, 0 ≤ coeff k i j := by decide +kernel

lemma monoR_nonneg (i : Fin 10) (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) : 0 ≤ monoR i s t := by
  fin_cases i <;> norm_num [monoR] <;> positivity

lemma mono_nonneg (i : Fin 10) (x : TripleState) : 0 ≤ mono i x :=
  monoR_nonneg i _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma monoR_update (i : Fin 10) (s t a : ℚ) :
    monoR i (s+a) (t+a*s)=monoR i s t+
      a*(∑ j,coeff 0 i j*monoR j s t)+a^2*(∑ j,coeff 1 i j*monoR j s t)+
      a^3*(∑ j,coeff 2 i j*monoR j s t) := by
  fin_cases i <;> norm_num [monoR,coeff,Fin.sum_univ_succ] <;> ring

def advance (p : ℕ) (c : ℚ) (H : Fin 10 → ℚ) (i : Fin 10) : ℚ :=
  H i+c/((p:ℚ)-1)*(∑ j,coeff 0 i j*H j)+
    c*((p:ℚ)+1)/(p-1)^2*(∑ j,coeff 1 i j*H j)+
    c*((p:ℚ)^2+4*p+1)/(p-1)^3*(∑ j,coeff 2 i j*H j)

lemma advance_mono (p : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c)
    {H J : Fin 10 → ℚ} (h : ∀ i,H i ≤ J i) (i : Fin 10) : advance p c H i ≤ advance p c J i := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hm : 0 ≤ (p:ℚ)-1 := by linarith
  have hs (k : Fin 3) : (∑ j,coeff k i j*H j) ≤ ∑ j,coeff k i j*J j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (coeff_nonneg k i j))
  unfold advance
  exact add_le_add (add_le_add (add_le_add (h i)
    (mul_le_mul_of_nonneg_left (hs 0) (by positivity)))
      (mul_le_mul_of_nonneg_left (hs 1) (by positivity)))
        (mul_le_mul_of_nonneg_left (hs 2) (by positivity))

lemma point_moment_step (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c)
    (i : Fin 10) (x : TripleState) :
    op E (powerTail p c E) (fun a => mono i (tripleUpdate a x)) ≤
      advance p c (fun j => mono j x) i := by
  have hcoeff (k : Fin 3) : 0 ≤ ∑ j,coeff k i j*mono j x :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (coeff_nonneg k i j) (mono_nonneg j x))
  have he (a : ℕ) : mono i (tripleUpdate a x)=mono i x+
      (∑ j,coeff 0 i j*mono j x)*(a:ℚ)+
      (∑ j,coeff 1 i j*mono j x)*(a:ℚ)^2+
      (∑ j,coeff 2 i j*mono j x)*(a:ℚ)^3 := by
    simp only [mono,tripleUpdate,Nat.cast_add,Nat.cast_mul]
    rw [monoR_update]
    ring
  simp_rw [he]
  apply (cubic_polynomial_op p E hp c hc (mono i x) _ _ _ (hcoeff 0) (hcoeff 1) (hcoeff 2)).trans_eq
  unfold advance
  ring

lemma pairExpect_advance (p : ℕ) (c : ℚ) (μ : TripleState →₀ ℚ) (i : Fin 10) :
    pairExpect μ (fun x => advance p c (fun j => mono j x) i)=
      advance p c (fun j => pairExpect μ (mono j)) i := by
  simp only [advance,pairExpect_test_add,pairExpect_test_mul,pairExpect_test_sum]

lemma actual_moment_step (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c)
    (μ : TripleState →₀ ℚ) (hμ : ∀ x, 0 ≤ μ x) (i : Fin 10) :
    pairExpect (tripleStep E (powerTail p c E) μ) (mono i) ≤
      advance p c (fun j => pairExpect μ (mono j)) i := by
  have h := pairExpect_mono μ hμ (point_moment_step p E hp c hc i)
  simpa only [pairExpect_op,pairExpect_advance] using h

/-- All ten upper moments propagate through every finite exponent cap. -/
theorem moment_bounds_step (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c)
    (μ : TripleState →₀ ℚ) (hμ : ∀ x, 0 ≤ μ x) (H J : Fin 10 → ℚ)
    (hH : ∀ i,pairExpect μ (mono i) ≤ H i) (hJ : ∀ i,advance p c H i ≤ J i) :
    ∀ i,pairExpect (tripleStep E (powerTail p c E) μ) (mono i) ≤ J i := by
  intro i
  exact (actual_moment_step p E hp c hc μ hμ i).trans ((advance_mono p hp c hc hH i).trans (hJ i))

#print axioms monoR_update
#print axioms moment_bounds_step
end Erdos7SupportMomentMatrix
