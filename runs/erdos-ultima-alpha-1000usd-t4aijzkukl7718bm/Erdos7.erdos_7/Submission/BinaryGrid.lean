import Submission.ArithmeticReduction

/-! Exact binary-exponent resampling for node-wise hinge bounds. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000
section Binary
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma completeHingeBound_binary_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (hE : E ⟨t,ht⟩=1) (θ : ℚ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq0 : q ⟨t,ht⟩ 0=θ) (hq1 : q ⟨t,ht⟩ 1=0)
    (hc : 1 ≤ c ⟨t,ht⟩) (u H J : ℚ)
    (hu : CompleteHingeBound κ A E c q t μ u H)
    (hh : CompleteHingeBound κ A E c q t μ (u/2) J)
    (B : Finset (∀ i,A i)) :
    CompleteHingeBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) u
      ((1-θ)*H+2*θ*J) := by
  intro M
  let G (a : ℕ) : ℚ := if a=0 then (M:ℚ)*H else 2*M*J
  have hb (a : ℕ) (ha : a ≤ E ⟨t,ht⟩) :
      CompleteTestBound κ A E c q t μ ((a+1)*M) (fun z => max 0 (z-(M:ℚ)*u)) (G a) := by
    rw [hE] at ha
    interval_cases a
    · simpa only [G,if_pos rfl,Nat.zero_add,Nat.one_mul] using hu M
    · have hid : (2:ℚ)*M*(u/2)=(M:ℚ)*u := by ring
      simpa only [G,if_neg (by decide : 1≠0),Nat.cast_mul,Nat.cast_ofNat,hid] using hh (2*M)
  have hr := completeTestBound_resample κ A E c q t ht μ hμ M
    (fun z => max 0 (z-(M:ℚ)*u))
    (by simpa only [one_mul,sub_eq_add_neg] using hinge_convex 1 (-((M:ℚ)*u)))
    (by intro x y hxy; exact max_le_max le_rfl (sub_le_sub_right hxy _)) G hb B hc
    (by simpa only [hq0] using hθ1)
    (by intro g hg; rw [hE] at hg; have hg0 : g=0 := by omega
        simpa only [hg0,Nat.zero_add,hq0,hq1] using hθ0)
    (by simpa only [hE] using hq1)
  convert hr using 1
  simp only [hE,Finset.sum_range_one,Nat.zero_add,hq0,hq1,sub_zero,G,
    if_pos rfl,if_neg (by decide : 1≠0)]
  ring

end Binary
#print axioms completeHingeBound_binary_resample
end Erdos7KilledSieve
