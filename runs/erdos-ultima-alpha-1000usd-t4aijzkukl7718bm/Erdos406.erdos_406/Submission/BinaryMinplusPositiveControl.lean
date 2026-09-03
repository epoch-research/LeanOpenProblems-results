import Submission.BinaryAcceptingMinplusCertificates

/-! An exact positive-gap min-plus control. Its power rate599/1000 is below
log(2)/log(3), so this is not a proof of Erdős406. -/
namespace Erdos406BinaryMinplusPositiveControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def nextTable (s : Fin 8) (d : Fin 2) : Finset (Fin 8) :=
  if s = 0 then (if d = 0 then {0} else {1})
  else if s = 1 then (if d = 0 then {7} else {4,6})
  else if s = 2 then (if d = 0 then {2,3} else {3})
  else if s = 3 then (if d = 0 then {5} else {6})
  else if s = 4 then (if d = 0 then {4} else {2,4})
  else if s = 5 then (if d = 0 then {6} else {6})
  else if s = 6 then (if d = 0 then {6} else {6})
  else if s = 7 then (if d = 0 then {4} else {3,4})
  else {0}
lemma next_nonempty : ∀ s d, (nextTable s d).Nonempty := by decide +kernel

def digit (d : ℕ) : Fin 2 := if d = 0 then 0 else 1
private def weightData : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, -96000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 599, 0, 0, 0, 0, -96000, 0, 96000, 0, 0, 0, 1794, 1800, 0, 0, 0, 0, 0, 0, 0, 1799, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1799, 0, 0, 0, 0, 0, 0, 0, 0, 1798, 0, 0, 0, 0, 0, 1797, 0, 0, 0, 0, 0, 96000, 0, 1797, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1794, 0, 0, 0, 0, 0, 0, 0, 1795, 0, 0, 0, 0, 0, 0, 0, 1797, 0, 0, 0, 0, 0, 0, 0, 1797, 0, 0, 0, 0, 0, -96000, 0, 0, 0, 0, 0, 0, 96000, -95401, 0, 0, 0]
private def hData : List ℤ := [0, 0, 0, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -95401, 0, 0, 0, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -95401, -94802, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, 0, 0, 0, -96000, -96000, -96000, 2995, -96000, -96000, -96000, 3000, -96000, -96000, -91208, -91205, -96000, -96000, 3005, -96000, -96000, -96000, -96000, -96000, -96000, 0, 0, 0, -96000, -96000, -96000, 2993, -96000, 2996, 2995, 2994, -96000, -96000, -91207, -91211, -96000, -96000, 2999, 2999, 3000, 3001, -96000, -96000, -96000, 0, 0, 0, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, 2995, 2995, 2995, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, 0, 0, 0, -96000, -96000, -96000, 2988, -96000, -96000, -96000, 2993, -96000, -96000, -96000, -91209, 2995, -96000, 2994, 2997, 2997, 2998, -96000, -96000, -96000, 0, 0, 0, -96000, -96000, -96000, 2996, 2992, 2996, 2994, 2999, 2998, -91208, -91207, -91207, 2996, 3000, 3001, 3000, 3000, 3000, -96000, -96000, -96000, 0, 0, 0, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -94802, -94802, -94203, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000, -96000]
private def jData : List ℤ := [0, 96000, -96000, -96000, -96000, -96000, -96000, 1797]
def W (s : Fin 8) (d : ℕ) (t : Fin 8) : ℤ :=
  weightData.getD (s.val*16+(digit d).val*8+t.val) 0
def H (s t : Fin 8) (c : ℕ) : ℤ := hData.getD (s.val*24+t.val*3+c) 0
def J (s : Fin 8) : ℤ := jData.getD s.val 0
private def relations : List (ℕ × ℕ × ℕ) := [(0,0,0),(0,1,1),(0,7,2),(1,4,0),(1,4,1),(1,4,2),(2,2,0),(2,3,1),(2,4,1),(2,4,2),(2,5,2),(3,2,0),(3,2,2),(3,3,0),(3,3,1),(3,4,1),(3,4,2),(3,5,2),(3,6,0),(3,6,1),(3,6,2),(4,4,0),(4,4,1),(4,4,2),(5,2,0),(5,3,1),(5,4,2),(5,5,0),(5,5,2),(5,6,0),(5,6,1),(5,6,2),(6,2,0),(6,2,1),(6,2,2),(6,3,0),(6,3,1),(6,3,2),(6,4,0),(6,4,1),(6,4,2),(6,5,0),(6,5,1),(6,5,2),(6,6,0),(6,6,1),(6,6,2),(7,4,0),(7,4,1),(7,4,2)]
def R (s t : Fin 8) (c : ℕ) : Prop := (s.val,t.val,c) ∈ relations
instance (s t : Fin 8) (c : ℕ) : Decidable (R s t c) := by unfold R; infer_instance

def D : Automaton (Fin 8) where
  start := 0
  next s d := nextTable s (digit d)
  nonempty s d := next_nonempty s (digit d)
  weight s d t := (W s d t:ℝ)/3000

def total : Total D (fun _ => True) := by
  apply total_of_closed_accepting trivial
  intro s d hd hs
  obtain ⟨t,ht⟩ := D.nonempty s d
  exact ⟨t,ht,trivial⟩

lemma seed_checks : 0 ≤ H 0 0 0 ∧ W 0 1 1 ≤ H 0 1 1 ∧
    W 0 1 1+W 1 0 7 ≤ H 0 7 2 := by decide +kernel
lemma step_checks : ∀ (s t : Fin 8) (c : Fin 3) (d e : Fin 2) (cp : Fin 3),
    3*d.val+cp.val = 2*c.val+e.val → R s t c.val →
    ∀ sp, sp ∈ D.next s d.val → ∃ tp, tp ∈ D.next t e.val ∧ R sp tp cp.val ∧
      H s t c.val+W t e.val tp-W s d.val sp ≤ H sp tp cp.val := by decide +kernel
lemma finish_checks : ∀ (s t : Fin 8) (c : Fin 2), R s t c.val → H s t c.val ≤ 3000 := by
  decide +kernel

def construction : Construction D (fun _ => True) where
  R := R
  H s t c := (H s t c:ℝ)/3000
  seed := by
    intro c hc
    interval_cases c
    · refine ⟨0,0,?_,by decide +kernel,?_⟩
      · simpa using Run.nil (D:=D) (0:Fin 8)
      · have hh : (0:ℝ) ≤ H 0 0 0 := by exact_mod_cast seed_checks.1
        exact div_nonneg hh (by norm_num)
    · refine ⟨1,(W 0 1 1:ℝ)/3000,?_,by decide +kernel,?_⟩
      · have hh := Run.cons (by decide : (1:Fin 8) ∈ D.next D.start 1) (Run.nil (D:=D) 1)
        simpa [D,Nat.digits_of_two_le_of_pos] using hh
      · have hh : (W 0 1 1:ℝ) ≤ H 0 1 1 := by exact_mod_cast seed_checks.2.1
        change (W 0 1 1:ℝ)/3000 ≤ (H 0 1 1:ℝ)/3000
        linarith
    · refine ⟨7,(W 0 1 1:ℝ)/3000+(W 1 0 7:ℝ)/3000,?_,by decide +kernel,?_⟩
      · have hh := Run.cons (by decide : (1:Fin 8) ∈ D.next D.start 1)
          (Run.cons (by decide : (7:Fin 8) ∈ D.next 1 0) (Run.nil (D:=D) 7))
        simpa [D,Nat.digits_of_two_le_of_pos] using hh
      · have hh : (W 0 1 1:ℝ)+W 1 0 7 ≤ H 0 7 2 := by exact_mod_cast seed_checks.2.2
        change (W 0 1 1:ℝ)/3000+(W 1 0 7:ℝ)/3000 ≤ (H 0 7 2:ℝ)/3000
        linarith
  step := by
    intro s t c d e cp hc hd he hcp har hr sp hsp
    obtain ⟨tp,ht,hr',hw⟩ := step_checks s t ⟨c,hc⟩ ⟨d,hd⟩ ⟨e,he⟩ ⟨cp,hcp⟩ har hr sp hsp
    refine ⟨tp,ht,hr',?_⟩
    have hwR : (H s t c:ℝ)+W t e tp-W s d sp ≤ H sp tp cp := by exact_mod_cast hw
    change (H s t c:ℝ)/3000+(W t e tp:ℝ)/3000-(W s d sp:ℝ)/3000 ≤ (H sp tp cp:ℝ)/3000
    linarith
  finish := by
    intro s t c hc hr hf
    refine ⟨trivial,?_⟩
    have hh : (H s t c:ℝ) ≤ 3000 := by exact_mod_cast finish_checks s t ⟨c,hc⟩ hr
    change (H s t c:ℝ)/3000 ≤ 1
    linarith

def G (s : Fin 8) : Prop := s.val ∈ [1,4,7]
instance (s : Fin 8) : Decidable (G s) := by unfold G; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s t, G s → t ∈ D.next s 0 → G t) ∧
    (∀ s t, G s → t ∈ D.next s 0 → 1797+J t-J s ≤ W s 0 t) ∧
    (∀ s t, s ∈ D.next D.start 1 → G t → -288000 ≤ W D.start 1 s+J t-J s) := by
  decide +kernel

def powerBound : PowerBound D (fun _ => True) where
  a := 599/1000
  B := 96
  G := G
  Z _ := True
  J s := (J s:ℝ)/3000
  start := power_checks.1
  forward := power_checks.2.1
  accepting := by intros; trivial
  backward := by intros; trivial
  lower_step := by
    intro s t hs hz he
    have hh : (1797:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.1 s t hs he
    change (599/1000:ℝ)+(J t:ℝ)/3000-(J s:ℝ)/3000 ≤ (W s 0 t:ℝ)/3000
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-288000:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2 s t hs ht
    change -(96:ℝ) ≤ (W D.start 1 s:ℝ)/3000+(J t:ℝ)/3000-(J s:ℝ)/3000
    linarith

def V (n : ℕ) : ℝ := value D (fun _ => True) total n
lemma construction_bound (n d : ℕ) (hd : d < 2) : V (3*n+d) ≤ V n+1 :=
  construction.construction_bound total n d hd
lemma power_lower (k : ℕ) : (599/1000:ℝ)*k-96 ≤ V (2^k) := powerBound.power_lower total k

lemma loop_weight : D.weight 2 0 2 = (299/500:ℝ) := by
  have hh : W 2 0 2 = 1794 := by decide +kernel
  change (W 2 0 2:ℝ)/3000 = _
  rw [hh]; norm_num
lemma prefix_weight : D.weight 0 1 1+D.weight 1 1 4+D.weight 4 1 2 = -32 := by
  have hh : W 0 1 1+W 1 1 4+W 4 1 2 = -96000 := by decide +kernel
  have hR : (W 0 1 1:ℝ)+W 1 1 4+W 4 1 2 = -96000 := by exact_mod_cast hh
  change (W 0 1 1:ℝ)/3000+(W 1 1 4:ℝ)/3000+(W 4 1 2:ℝ)/3000 = -32
  linarith
lemma cheap_zeros (k : ℕ) : Run D 2 (List.replicate k 0) 2 ((299/500:ℝ)*k) := by
  induction k with
  | zero => simpa using Run.nil (D:=D) 2
  | succ k ih =>
    have hh := Run.cons (by decide : (2:Fin 8) ∈ D.next 2 0) ih
    rw [loop_weight] at hh
    simpa only [List.replicate_succ,Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm] using hh

lemma cheap_family (k : ℕ) : V (7*2^k) ≤ (299/500:ℝ)*k-32 := by
  have hword : (Nat.digits 2 (7*2^k)).reverse = 1::1::1::List.replicate k 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=7) (by decide) (by decide)
    have hr := congrArg List.reverse hh
    simpa [Nat.mul_comm,Nat.digits_of_two_le_of_pos] using hr
  have hr := Run.cons (by decide : (1:Fin 8) ∈ D.next D.start 1)
    (Run.cons (by decide : (4:Fin 8) ∈ D.next 1 1)
      (Run.cons (by decide : (2:Fin 8) ∈ D.next 4 1) (cheap_zeros k)))
  have hr' : Run D D.start (Nat.digits 2 (7*2^k)).reverse 2 ((299/500:ℝ)*k-32) := by
    rw [hword]
    convert hr using 1
    have hh := prefix_weight
    change _ = D.weight 0 1 1+(D.weight 1 1 4+(D.weight 4 1 2+(299/500:ℝ)*k))
    linarith
  exact value_le_run total hr' trivial

/-- Unlike earlier selected controls, this one does NOT admit the same
leading lower rate on all positive binary words. -/
lemma no_global_same_slope_lower : ¬ ∃ B : ℝ, ∀ n : ℕ, 0 < n →
    (599/1000:ℝ)*(Nat.digits 2 n).length-B ≤ V n := by
  rintro ⟨B,hB⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (1000*(B+100))
  have hh := hB (7*2^k) (by positivity)
  have hu := cheap_family k
  have hlen : (Nat.digits 2 (7*2^k)).length = k+3 := by
    have h := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=7) (by decide) (by decide)
    have hl := congrArg List.length h
    simpa [Nat.mul_comm,Nat.digits_of_two_le_of_pos] using hl
  rw [hlen] at hh
  push_cast at hh
  nlinarith

lemma not_supercritical : ¬ Real.log 2 < (599/1000:ℝ)*Real.log 3 := by
  have hh := Real.log_lt_log (by positivity : (0:ℝ)<3^5) (by norm_num : (3:ℝ)^5<2^8)
  rw [Real.log_pow,Real.log_pow] at hh
  have h3 := Real.log_pos (by norm_num : (1:ℝ)<3)
  norm_num at hh
  nlinarith

#print axioms construction_bound
#print axioms power_lower
#print axioms cheap_family
#print axioms no_global_same_slope_lower
#print axioms not_supercritical
end
end Erdos406BinaryMinplusPositiveControl
