import Submission.BalancedAffineCertificates

/-! A concrete control for the balanced-LSD certificate pipeline. Its slope
is one, which is not subcritical; this is not a solution of Erdős 406. -/
namespace Erdos406BalancedLengthControl
open Erdos406Balanced Erdos406BalancedCertificate Erdos406AffinePotential

def D : DFA ℕ Unit := ⟨fun _ _ => (), (), ∅⟩

def lower : Lower Unit where
  D := D
  w := fun _ _ => 1
  lam := 1
  delta := 1
  R := fun _ _ _ => True
  H := fun _ _ _ => 0
  relation_start := trivial
  lower_start := le_rfl
  relation_step := by intros; trivial
  lower_step := by intros; norm_num
  finish_empty := by simp [weightFrom]
  finish_one := by
    intro s t c hc _
    change 1 ≤ 0 + weightFrom D (fun _ _ => 1) _ (digits (nextCarry 2 c).toNat)
    rcases nextCarry_two hc with he | he <;> simp [he,weightFrom]

def upper : GoodUpper lower.D lower.w where
  c := 1
  B := 0
  G := fun _ => True
  J := fun _ => 0
  start := trivial
  initial := rfl
  zero_bound := le_rfl
  step := by intros; trivial
  upper_step := by intros; norm_num [lower]
  terminal := by intros; norm_num

lemma weight_one_length {σ : Type*} (A : DFA ℕ σ) (s : σ) (u : List ℕ) :
    weightFrom A (fun _ _ => 1) s u = (u.length : ℝ) := by
  induction u generalizing s with
  | nil => simp [weightFrom]
  | cons d u ih => simp [weightFrom,ih,Nat.cast_add,add_comm]

theorem balanced_length_growth (n : ℕ) :
    (digits n).length + 1 ≤ (digits (4*n+1)).length := by
  have hh := lower.affine_lower n
  change 1 * weightFrom D (fun _ _ => 1) () (digits n) + 1 ≤
    weightFrom D (fun _ _ => 1) () (digits (4*n+1)) at hh
  rw [one_mul,weight_one_length,weight_one_length] at hh
  exact_mod_cast hh

theorem control_not_subcritical : ¬ upper.c * Real.log 4 < Real.log 3 := by
  change ¬ 1 * Real.log 4 < Real.log 3
  have hh : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  simpa using not_lt_of_ge hh

#print axioms balanced_length_growth
#print axioms control_not_subcritical
end Erdos406BalancedLengthControl
