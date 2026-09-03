import Submission.BinaryAcceptingMinplusCertificates

/-! An accepting-endpoint control showing a genuine difference from the old
all-terminal minimum. Its construction inequality is false, so it is NOT
an instance settling the conjecture. -/
namespace Erdos406BinaryAcceptingEndpointControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
noncomputable section

def D : Automaton (Fin 3) where
  start := 0
  next s d := if s = 0 then (if d = 0 then {0} else {1})
    else if s = 2 ∧ d = 0 then {2} else {1,2}
  nonempty := by intro s d; split_ifs <;> simp
  weight s d t := if s = 1 ∧ d = 0 ∧ t = 1 then 1 else 0

def F (s : Fin 3) : Prop := s ≠ 2
instance (s : Fin 3) : Decidable (F s) := by unfold F; infer_instance

lemma total : Total D F := by
  apply total_of_closed_accepting (by decide : F D.start)
  intro s d hd hs
  have hc : ∀ (s : Fin 3) (d : Fin 2), F s → ∃ t, t ∈ D.next s d.val ∧ F t := by
    decide +kernel
  exact hc s ⟨d,hd⟩ hs

lemma weight_nonnegative (s t : Fin 3) (d : ℕ) : 0 ≤ D.weight s d t := by
  dsimp [D]; split_ifs <;> norm_num

lemma run_nonnegative {s t L v} (hr : Run D s L t v) : 0 ≤ v := by
  induction hr with
  | nil => exact le_rfl
  | cons ht hr ih => exact add_nonneg (weight_nonnegative ..) ih

lemma value_nonnegative (n : ℕ) : 0 ≤ value D F total n := by
  obtain ⟨t,ht,_⟩ := exists_min_run total n
  exact run_nonnegative ht

def powerBound : PowerBound D F where
  a := 1
  B := 0
  G s := s ≠ 0
  Z := F
  J _ := 0
  start := by decide +kernel
  forward := by decide +kernel
  accepting := by intro t ht; exact ht
  backward := by decide +kernel
  lower_step := by
    intro s t hs ht he
    have hc : ∀ s t : Fin 3, s ≠ 0 → F t → t ∈ D.next s 0 → s = 1 ∧ t = 1 := by decide +kernel
    obtain ⟨rfl,rfl⟩ := hc s t hs ht he
    norm_num [D]
  lower_end := by
    intro s t hs ht hf hz
    simpa using weight_nonnegative D.start s 1

lemma active_zeros (k : ℕ) : Run D 1 (List.replicate k 0) 1 (k:ℝ) := by
  induction k with
  | zero => simpa using Run.nil (D:=D) 1
  | succ k ih =>
    have hh := Run.cons (by decide : (1:Fin 3) ∈ D.next 1 0) ih
    simpa [D,List.replicate_succ,Nat.cast_add,Nat.cast_one,add_comm] using hh

lemma word_power (k : ℕ) : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
  have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
  simpa using congrArg List.reverse hh

lemma accepting_power_value (k : ℕ) : value D F total (2^k) = k := by
  have hlo := powerBound.power_lower total k
  have hr := Run.cons (by decide : (1:Fin 3) ∈ D.next D.start 1) (active_zeros k)
  have hr' : Run D D.start (Nat.digits 2 (2^k)).reverse 1 (k:ℝ) := by
    rw [word_power]
    simpa [D] using hr
  have hhi := value_le_run total hr' (by decide : F 1)
  change 1*(k:ℝ)-0 ≤ value D F total (2^k) at hlo
  linarith

lemma inactive_zeros (k : ℕ) : Run D 2 (List.replicate k 0) 2 0 := by
  induction k with
  | zero => simpa using Run.nil (D:=D) 2
  | succ k ih =>
    have hh := Run.cons (by decide : (2:Fin 3) ∈ D.next 2 0) ih
    simpa [D,List.replicate_succ] using hh

lemma all_terminal_power_value (k : ℕ) : Erdos406BinaryMinplus.value D (2^(k+1)) = 0 := by
  have hr := Run.cons (by decide : (1:Fin 3) ∈ D.next D.start 1)
    (Run.cons (by decide : (2:Fin 3) ∈ D.next 1 0) (inactive_zeros k))
  have hr' : Run D D.start (Nat.digits 2 (2^(k+1))).reverse 2 0 := by
    rw [word_power,List.replicate_succ]
    simpa [D] using hr
  have hhi := Erdos406Minplus.valueFrom_le_run hr'
  obtain ⟨t,ht⟩ := Erdos406Minplus.exists_min_run D D.start (Nat.digits 2 (2^(k+1))).reverse
  have hlo := run_nonnegative ht
  change Erdos406BinaryMinplus.value D (2^(k+1)) ≤ 0 at hhi
  change 0 ≤ Erdos406BinaryMinplus.value D (2^(k+1)) at hlo
  exact le_antisymm hhi hlo

lemma accepting_five_value : value D F total 5 = 0 := by
  have hr := Run.cons (by decide : (1:Fin 3) ∈ D.next D.start 1)
    (Run.cons (by decide : (2:Fin 3) ∈ D.next 1 0)
      (Run.cons (by decide : (1:Fin 3) ∈ D.next 2 1) (Run.nil (D:=D) 1)))
  have hr' : Run D D.start (Nat.digits 2 5).reverse 1 0 := by
    norm_num [Nat.digits_of_two_le_of_pos]
    simpa [D] using hr
  exact le_antisymm (value_le_run total hr' (by decide : F 1)) (value_nonnegative 5)

/-- This control has the desired rate on powers but fails construction at5. -/
lemma construction_fails : ¬ (∀ n d : ℕ, d < 2 →
    value D F total (3*n+d) ≤ value D F total n+1) := by
  intro h
  have hh := h 5 1 (by decide)
  rw [accepting_five_value] at hh
  have hp := accepting_power_value 4
  norm_num at hp hh
  linarith

#print axioms total
#print axioms accepting_power_value
#print axioms all_terminal_power_value
#print axioms construction_fails
end
end Erdos406BinaryAcceptingEndpointControl
