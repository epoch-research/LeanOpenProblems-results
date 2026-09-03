import Submission.BinaryMinplusCertificates

/-! A checked six-state binary min-plus control. Its rate5/8 is NOT
supercritical, so this is not a settlement of Erdős 406. -/
namespace Erdos406BinaryMinplusControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryMinplus

def next (s : Fin 6) (d : ℕ) : Finset (Fin 6) :=
  if s = 0 ∧ d = 0 then {0} else Finset.univ.erase 0

def wTable : Fin 6 → Fin 2 → Fin 6 → ℤ := ![![![0, 0, 0, 0, 0, 0], ![0, 8, 64, 64, 64, 64]], ![![0, 64, (-2), 64, 64, 64], ![0, 64, 64, 0, 64, 64]], ![![0, 64, 64, 4, 64, 64], ![0, 64, 64, 64, 6, 64]], ![![0, 64, 64, 64, 64, 5], ![0, 64, 64, 64, 64, 6]], ![![0, 64, 64, 4, 64, 64], ![0, 64, 64, 64, 64, 5]], ![![0, 64, 64, 64, 64, 5], ![0, 64, 64, 64, 64, 5]]]

def hTable : Fin 6 → Fin 6 → Fin 3 → ℤ := ![![![0, 0, 0], ![(-256), 8, (-256)], ![(-256), (-256), 6], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)]], ![![0, 0, 0], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)], ![0, 2, (-256)], ![(-256), (-256), 4], ![0, 2, 3]], ![![0, 0, 0], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)], ![(-56), 7, (-256)], ![(-256), (-256), (-52)], ![7, 8, 9]], ![![0, 0, 0], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)], ![(-56), 8, (-256)], ![(-256), (-256), (-52)], ![8, 8, 9]], ![![0, 0, 0], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)], ![(-56), 7, (-256)], ![(-256), (-256), (-52)], ![7, 8, 8]], ![![0, 0, 0], ![(-256), (-256), (-256)], ![(-256), (-256), (-256)], ![(-56), 7, (-256)], ![(-256), (-256), (-52)], ![8, 8, 8]]]

def jz : Fin 6 → ℤ := ![0, (-248), (-255), (-256), (-255), (-256)]

def rList : List (ℕ × ℕ × ℕ) := [(0, 0, 0), (0, 1, 1), (0, 2, 2), (1, 3, 0), (1, 3, 1), (1, 4, 2), (1, 5, 0), (1, 5, 1), (1, 5, 2), (2, 3, 0), (2, 3, 1), (2, 4, 2), (2, 5, 0), (2, 5, 1), (2, 5, 2), (3, 3, 0), (3, 3, 1), (3, 4, 2), (3, 5, 0), (3, 5, 1), (3, 5, 2), (4, 3, 0), (4, 3, 1), (4, 4, 2), (4, 5, 0), (4, 5, 1), (4, 5, 2), (5, 3, 0), (5, 3, 1), (5, 4, 2), (5, 5, 0), (5, 5, 1), (5, 5, 2)]

def wz (s : Fin 6) (d : ℕ) (t : Fin 6) : ℤ := wTable s (if d = 0 then 0 else 1) t
def hz (s t : Fin 6) (c : ℕ) : ℤ := hTable s t (if c = 0 then 0 else if c = 1 then 1 else 2)
def R (s t : Fin 6) (c : ℕ) : Prop := (s.val, t.val, c) ∈ rList
instance (s t : Fin 6) (c : ℕ) : Decidable (R s t c) :=
  inferInstanceAs (Decidable (_ ∈ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma step_checked : ∀ (s t : Fin 6) (c cp : Fin 3) (d e : Fin 2),
    3*d.val+cp.val = 2*c.val+e.val → R s t c.val →
    ∀ sp ∈ next s d.val, ∃ tp ∈ next t e.val, R sp tp cp.val ∧
      hz s t c.val + wz t e.val tp - wz s d.val sp ≤ hz sp tp cp.val := by
  decide +kernel

lemma finish_checked : ∀ (s t : Fin 6) (c : Fin 2), R s t c.val → hz s t c.val ≤ 8 := by
  decide +kernel

lemma power_checked : ∀ s t : Fin 6, s ≠ 0 → t ∈ next s 0 →
    5 + jz t - jz s ≤ wz s 0 t := by
  decide +kernel

lemma end_checked : ∀ s t : Fin 6, s ≠ 0 → t ≠ 0 →
    0 ≤ wz 0 1 s + jz t - jz s := by
  decide +kernel

noncomputable def control : Automaton (Fin 6) where
  next := next
  nonempty s d := by
    simp only [next]
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  weight s d t := (wz s d t : ℝ) / 8
  start := 0

lemma seed_integer_values :
    wz 0 1 1 = 8 ∧ wz 1 0 2 = -2 ∧ hz 0 0 0 = 0 ∧ hz 0 1 1 = 8 ∧ hz 0 2 2 = 6 := by
  decide +kernel

lemma control_weight01 : control.weight 0 1 1 = 1 := by
  change (wz 0 1 1 : ℝ)/8 = 1
  rw [seed_integer_values.1]
  norm_num

lemma control_weight10 : control.weight 1 0 2 = -(1/4 : ℝ) := by
  change (wz 1 0 2 : ℝ)/8 = -(1/4 : ℝ)
  rw [seed_integer_values.2.1]
  norm_num

noncomputable def controlConstruction : Construction control where
  R := R
  H s t c := (hz s t c : ℝ) / 8
  seed c hc := by
    interval_cases c
    · refine ⟨0, 0, ?_, ?_, ?_⟩
      · simpa [control] using Run.nil (D := control) (0 : Fin 6)
      · decide +kernel
      · change (0 : ℝ) ≤ (hz 0 0 0 : ℝ)/8
        rw [seed_integer_values.2.2.1]
        norm_num
    · refine ⟨1, 1, ?_, ?_, ?_⟩
      · have h := Run.cons (D := control) (s := 0) (d := 1)
          (show (1 : Fin 6) ∈ control.next 0 1 from by simp [control, next]) (Run.nil 1)
        have hd : Nat.digits 2 1 = [1] := by decide +kernel
        simpa [hd, control_weight01] using h
      · decide +kernel
      · change (1 : ℝ) ≤ (hz 0 1 1 : ℝ)/8
        rw [seed_integer_values.2.2.2.1]
        norm_num
    · refine ⟨2, (3/4 : ℝ), ?_, ?_, ?_⟩
      · have h := Run.cons (D := control) (s := 0) (d := 1)
          (show (1 : Fin 6) ∈ control.next 0 1 from by simp [control, next])
          (Run.cons (s := 1) (d := 0)
            (show (2 : Fin 6) ∈ control.next 1 0 from by simp [control, next]) (Run.nil 2))
        have hd : Nat.digits 2 2 = [0, 1] := by decide +kernel
        convert h using 1 <;> norm_num [hd, control_weight01, control_weight10]
      · decide +kernel
      · change (3/4 : ℝ) ≤ (hz 0 2 2 : ℝ)/8
        rw [seed_integer_values.2.2.2.2]
        norm_num
  step s t c d e cp hc hd he hcp hid hr sp hs := by
    obtain ⟨tp, ht, hr', hh⟩ := step_checked s t ⟨c,hc⟩ ⟨cp,hcp⟩
      ⟨d,hd⟩ ⟨e,he⟩ hid hr sp hs
    refine ⟨tp, ht, hr', ?_⟩
    change (hz s t c : ℝ)/8 + (wz t e tp : ℝ)/8 - (wz s d sp : ℝ)/8 ≤
      (hz sp tp cp : ℝ)/8
    have hR : (hz s t c : ℝ) + (wz t e tp : ℝ) - (wz s d sp : ℝ) ≤
      (hz sp tp cp : ℝ) := by exact_mod_cast hh
    linarith
  finish s t c hc hr := by
    have hh := finish_checked s t ⟨c,hc⟩ hr
    have hR : (hz s t c : ℝ) ≤ 8 := by exact_mod_cast hh
    linarith

noncomputable def controlPowerBound : PowerBound control where
  a := 5/8
  B := 0
  G s := s ≠ 0
  J s := (jz s : ℝ)/8
  start s hs := by simpa [control, next] using hs
  step s t hs ht := by simpa [control, next, hs] using ht
  lower_step s t hs ht := by
    have hh := power_checked s t hs ht
    have hR : (5 : ℝ) + (jz t : ℝ) - (jz s : ℝ) ≤ (wz s 0 t : ℝ) := by
      exact_mod_cast hh
    change (5/8 : ℝ) + (jz t : ℝ)/8 - (jz s : ℝ)/8 ≤ (wz s 0 t : ℝ)/8
    linarith
  lower_end s t hs ht := by
    have hs' : s ≠ 0 := by simpa [control, next] using hs
    have hh := end_checked s t hs' ht
    have hR : (0 : ℝ) ≤ (wz 0 1 s : ℝ) + (jz t : ℝ) - (jz s : ℝ) := by
      exact_mod_cast hh
    change -(0 : ℝ) ≤ (wz 0 1 s : ℝ)/8 + (jz t : ℝ)/8 - (jz s : ℝ)/8
    linarith

theorem control_construction_bound (n d : ℕ) (hd : d < 2) :
    value control (3*n+d) ≤ value control n + 1 :=
  controlConstruction.construction_bound n d hd

theorem control_power_bound (k : ℕ) : (5/8 : ℝ)*k ≤ value control (2^k) := by
  simpa [controlPowerBound] using controlPowerBound.power_lower k

theorem control_not_supercritical : ¬ Real.log 2 < (5/8 : ℝ)*Real.log 3 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^5)
    (by norm_num : (3 : ℝ)^5 < 2^8)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  intro hh
  nlinarith

#print axioms control_construction_bound
#print axioms control_power_bound
#print axioms control_not_supercritical
end Erdos406BinaryMinplusControl
