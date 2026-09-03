import Submission.BinaryPartialProfileCertificates

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryJointPolicyControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def nextData : Array (List (Fin 8)) := #[[0],[1],[2,6],[3,7],[3],[4],[5],[5],[3],[5],[5],[5],[6],[5,6],[7],[5,7]]
private def weightData : Array (Array (ℤ)) := #[#[0,0,0,0],#[531,893,1068,1407],#[893,893,1040,1040],#[888,888,1066,1066],#[921,921,1097,1097],#[890,890,890,890],#[916,916,892,890],#[926,926,737,904]]
private def sourceData : Array (Fin 8) := #[0,0,0,1,1,1,2,6,2,6,2,6,3,7,7,3,7,3,7,3,4,5,4,4,5,5]
private def carryData : Array ℕ := #[0,1,2,0,1,2,0,0,1,1,2,2,0,0,1,2,2,1,1,1,0,0,1,2,1,2]
private def endData : Array (List (Fin 8)) := #[[0],[1],[2,6],[3],[3],[4,6],[5],[5],[5],[5],[5],[5],[5],[5],[3],[5],[5],[5],[5],[3,6],[5],[5],[5],[5],[5],[5]]
private def hData : Array (Array (ℤ)) := #[#[0,0],#[0,0],#[531,893],#[1068,1068],#[1424,1424],#[1571,1783],#[1425,1425],#[1428,1428],#[1603,1603],#[1426,1426],#[1781,1781],#[1426,1426],#[1422,1422],#[1257,1257],#[1085,1085],#[1600,1600],#[1261,1261],#[1422,1422],#[1265,1265],#[1424,1631],#[1453,1453],#[1424,1424],#[1631,1631],#[1631,1631],#[1424,1424],#[1424,1424]]
private def destData : Array (Array (Fin 26)) := #[#[0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,0,0,2,0,3,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,0,5,0],#[6,7,8,9,0,0,0,0,0,0,0,0],#[0,0,0,0,10,11,12,13,0,0,0,0],#[0,0,0,0,0,0,0,0,19,14,15,16],#[12,0,17,0,0,0,0,0,0,0,0,0],#[7,0,9,0,0,0,0,0,0,0,0,0],#[0,0,0,0,15,0,20,0,0,0,0,0],#[0,0,0,0,11,0,21,7,0,0,0,0],#[0,0,0,0,0,0,0,0,22,0,23,0],#[0,0,0,0,0,0,0,0,24,9,25,11],#[21,0,24,0,0,0,0,0,0,0,0,0],#[13,0,18,0,0,0,0,0,0,0,0,0],#[0,0,0,0,16,0,21,13,0,0,0,0],#[0,0,0,0,0,0,0,0,24,0,25,0],#[0,0,0,0,0,0,0,0,24,18,25,16],#[0,0,0,0,25,0,21,0,0,0,0,0],#[0,0,0,0,16,0,21,13,0,0,0,0],#[0,0,0,0,25,0,21,0,0,0,0,0],#[12,0,17,0,0,0,0,0,0,0,0,0],#[21,0,24,0,0,0,0,0,0,0,0,0],#[0,0,0,0,15,0,21,0,0,0,0,0],#[0,0,0,0,0,0,0,0,24,0,25,0],#[0,0,0,0,25,0,21,0,0,0,0,0],#[0,0,0,0,0,0,0,0,24,0,25,0]]
private def parentData : Array (Array (Fin 8)) := #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,6,0,0],#[3,3,3,3,3,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,3,3,3,3,3,3,3,3,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,6,4,4,4,4,4,4],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,5,5,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,3,3,0,0,3,3,3,3,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,5,5,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,3,3,0,0,3,3,0,0,0,0,0,0,0,0,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0]]
private def finishData : Array (Fin 8) := #[0,1,0,3,3,0,0,0,0,0,0,0,5,0,0,0,0,5,0,3,0,5,0,0,5,0]
private def jData : Array ℤ := #[0,359,0,3,0,1,0,0]
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 8) (d : ℕ) : List (Fin 8) := nextData[s.val*2+(digit d).val]?.getD []
def nextTable (s : Fin 8) (d : ℕ) : Finset (Fin 8) := (nextList s d).toFinset
def slot (s : Fin 8) (d : ℕ) (t : Fin 8) : ℕ := if t=(nextList s d).getD 0 0 then 0 else 1
def W (s : Fin 8) (d : ℕ) (t : Fin 8) : ℤ := (weightData[s.val]?.getD #[])[(digit d).val*2+slot s d t]?.getD 0
def source (p : Fin 26) : Fin 8 := sourceData[p.val]?.getD 0
def carry (p : Fin 26) : ℕ := carryData[p.val]?.getD 0
def endsList (p : Fin 26) : List (Fin 8) := endData[p.val]?.getD []
def ends (p : Fin 26) : Finset (Fin 8) := (endsList p).toFinset
def eslot (p : Fin 26) (t : Fin 8) : ℕ := if t=(endsList p).getD 0 0 then 0 else 1
def H (p : Fin 26) (t : Fin 8) : ℤ := (hData[p.val]?.getD #[])[eslot p t]?.getD 0
def index (p : Fin 26) (d cp : ℕ) (sp : Fin 8) : ℕ := ((digit d).val*3+cp)*2+slot (source p) d sp
def target (p : Fin 26) (d cp : ℕ) (sp : Fin 8) : Fin 26 := (destData[p.val]?.getD #[])[index p d cp sp]?.getD 0
def parent (p : Fin 26) (d cp : ℕ) (sp tp : Fin 8) : Fin 8 :=
  (parentData[p.val]?.getD #[])[(index p d cp sp)*2+eslot (target p d cp sp) tp]?.getD 0
def finish (p : Fin 26) : Fin 8 := finishData[p.val]?.getD 0
def J (s : Fin 8) : ℤ := jData[s.val]?.getD 0
def F (s : Fin 8) : Prop := s.val ∈ [0,1,3,5]
instance (s : Fin 8) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 8) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/1424

def R (s : Fin 8) (p : Fin 26) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 8) (p : Fin 26) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_profiles : R 0 0 0 ∧ R 0 1 1 ∧ R 0 2 2 := by decide +kernel
lemma seed_zero : ∀ t ∈ ends 0, t=0 ∧ 0 ≤ H 0 t := by decide +kernel
lemma seed_one : ∀ t ∈ ends 1, t=1 ∧ W 0 1 1 ≤ H 1 t := by decide +kernel
lemma seed_two : ∀ t ∈ ends 2, t ∈ D.next 1 0 ∧ W 0 1 1+W 1 0 t ≤ H 2 t := by decide +kernel
lemma first_one : (1:Fin 8) ∈ D.next D.start 1 := by decide +kernel

def StepRow (p : Fin 26) : Prop := ∀ (d e : Fin 2) (cp : Fin 3),
    3*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp
lemma step_row_0 : StepRow 0 := by
  unfold StepRow R
  decide +kernel
lemma step_row_1 : StepRow 1 := by
  unfold StepRow R
  decide +kernel
lemma step_row_2 : StepRow 2 := by
  unfold StepRow R
  decide +kernel
lemma step_row_3 : StepRow 3 := by
  unfold StepRow R
  decide +kernel
lemma step_row_4 : StepRow 4 := by
  unfold StepRow R
  decide +kernel
lemma step_row_5 : StepRow 5 := by
  unfold StepRow R
  decide +kernel
lemma step_row_6 : StepRow 6 := by
  unfold StepRow R
  decide +kernel
lemma step_row_7 : StepRow 7 := by
  unfold StepRow R
  decide +kernel
lemma step_row_8 : StepRow 8 := by
  unfold StepRow R
  decide +kernel
lemma step_row_9 : StepRow 9 := by
  unfold StepRow R
  decide +kernel
lemma step_row_10 : StepRow 10 := by
  unfold StepRow R
  decide +kernel
lemma step_row_11 : StepRow 11 := by
  unfold StepRow R
  decide +kernel
lemma step_row_12 : StepRow 12 := by
  unfold StepRow R
  decide +kernel
lemma step_row_13 : StepRow 13 := by
  unfold StepRow R
  decide +kernel
lemma step_row_14 : StepRow 14 := by
  unfold StepRow R
  decide +kernel
lemma step_row_15 : StepRow 15 := by
  unfold StepRow R
  decide +kernel
lemma step_row_16 : StepRow 16 := by
  unfold StepRow R
  decide +kernel
lemma step_row_17 : StepRow 17 := by
  unfold StepRow R
  decide +kernel
lemma step_row_18 : StepRow 18 := by
  unfold StepRow R
  decide +kernel
lemma step_row_19 : StepRow 19 := by
  unfold StepRow R
  decide +kernel
lemma step_row_20 : StepRow 20 := by
  unfold StepRow R
  decide +kernel
lemma step_row_21 : StepRow 21 := by
  unfold StepRow R
  decide +kernel
lemma step_row_22 : StepRow 22 := by
  unfold StepRow R
  decide +kernel
lemma step_row_23 : StepRow 23 := by
  unfold StepRow R
  decide +kernel
lemma step_row_24 : StepRow 24 := by
  unfold StepRow R
  decide +kernel
lemma step_row_25 : StepRow 25 := by
  unfold StepRow R
  decide +kernel
lemma step_checks : ∀ p : Fin 26, StepRow p := by
  intro p
  fin_cases p
  · exact step_row_0
  · exact step_row_1
  · exact step_row_2
  · exact step_row_3
  · exact step_row_4
  · exact step_row_5
  · exact step_row_6
  · exact step_row_7
  · exact step_row_8
  · exact step_row_9
  · exact step_row_10
  · exact step_row_11
  · exact step_row_12
  · exact step_row_13
  · exact step_row_14
  · exact step_row_15
  · exact step_row_16
  · exact step_row_17
  · exact step_row_18
  · exact step_row_19
  · exact step_row_20
  · exact step_row_21
  · exact step_row_22
  · exact step_row_23
  · exact step_row_24
  · exact step_row_25

lemma finish_checks : ∀ p : Fin 26, carry p < 2 → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 1424 := by decide +kernel

def construction : Erdos406BinaryProfileMinplus.Construction D F (Fin 26) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/1424
  seed := by
    intro c hc
    interval_cases c
    · refine ⟨0,seed_profiles.1,?_⟩
      intro t ht
      obtain ⟨rfl,hh⟩ := seed_zero t ht
      refine ⟨0,?_,?_⟩
      · simpa [D] using Run.nil (D:=D) (0:Fin 8)
      · have hR : (0:ℝ) ≤ H 0 0 := by exact_mod_cast hh
        exact div_nonneg hR (by norm_num)
    · refine ⟨1,seed_profiles.2.1,?_⟩
      intro t ht
      obtain ⟨rfl,hh⟩ := seed_one t ht
      refine ⟨(W 0 1 1:ℝ)/1424,?_,?_⟩
      · have hr := Run.cons first_one (Run.nil (D:=D) 1)
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ) ≤ H 1 1 := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/1424 ≤ (H 1 1:ℝ)/1424
        linarith
    · refine ⟨2,seed_profiles.2.2,?_⟩
      intro t ht
      obtain ⟨he,hh⟩ := seed_two t ht
      refine ⟨(W 0 1 1:ℝ)/1424+(W 1 0 t:ℝ)/1424,?_,?_⟩
      · have hr := Run.cons first_one (Run.cons he (Run.nil (D:=D) t))
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ)+W 1 0 t ≤ H 2 t := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/1424+(W 1 0 t:ℝ)/1424 ≤ (H 2 t:ℝ)/1424
        linarith
  step := by
    intro s p c d e cp hc hd he hcp har hr sp hsp
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨hr',hs⟩ := step_checks p ⟨d,hd⟩ ⟨e,he⟩ ⟨cp,hcp⟩ har sp hsp
    refine ⟨target p d cp sp,hr',?_⟩
    intro tp ht
    obtain ⟨hp,he',hh⟩ := hs tp ht
    refine ⟨parent p d cp sp tp,hp,he',?_⟩
    have hR : (H p (parent p d cp sp tp):ℝ)+W (parent p d cp sp tp) e tp-
        W (source p) d sp ≤ H (target p d cp sp) tp := by exact_mod_cast hh
    change (H p (parent p d cp sp tp):ℝ)/1424+(W (parent p d cp sp tp) e tp:ℝ)/1424-
      (W (source p) d sp:ℝ)/1424 ≤ (H (target p d cp sp) tp:ℝ)/1424
    linarith
  finish := by
    intro s p c hc hr hf
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨ht,hf',hh⟩ := finish_checks p hc hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 1424 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/1424 ≤ 1
    linarith

def G (s : Fin 8) : Prop := s.val ∉ [0,4,7]
def Z (s : Fin 8) : Prop := s.val ∉ [6,7]
instance (s : Fin 8) : Decidable (G s) := by unfold G; infer_instance
instance (s : Fin 8) : Decidable (Z s) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, G t) ∧
    (∀ t, F t → Z t) ∧
    (∀ s, ∀ t ∈ D.next s 0, Z t → Z s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, Z t → 890+J t-J s ≤ W s 0 t) ∧
    (∀ s ∈ D.next D.start 1, ∀ t, G t → F t → Z s → -546816 ≤ W D.start 1 s+J t-J s) := by decide +kernel

def powerBound : PowerBound D F where
  a := 890/1424
  B := 384
  G := G
  Z := Z
  J s := (J s:ℝ)/1424
  start := power_checks.1
  forward := by intro s t hs ht; exact power_checks.2.1 s hs t ht
  accepting := power_checks.2.2.1
  backward := by intro s t ht he; exact power_checks.2.2.2.1 s t he ht
  lower_step := by
    intro s t hs hz he
    have hh : (890:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s hs t he hz
    change (890/1424:ℝ)+(J t:ℝ)/1424-(J s:ℝ)/1424 ≤ (W s 0 t:ℝ)/1424
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-546816:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2.2.2 s hs t ht hf hz
    change -(384:ℝ) ≤ (W D.start 1 s:ℝ)/1424+(J t:ℝ)/1424-(J s:ℝ)/1424
    linarith

lemma start_accepts : F D.start := by decide +kernel
lemma good_run_bound (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t ∧
      v ≤ (Nat.digits 3 n).length :=
  Erdos406BinaryPartialProfile.exists_good_run construction start_accepts n hg
lemma accepted_power_lower (k : ℕ) {t v}
    (hr : Run D D.start (Nat.digits 2 (2^k)).reverse t v) (hF : F t) :
    (890/1424:ℝ)*k-384 ≤ v := by
  have hword : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  exact powerBound.power_run_lower k (hword ▸ hr) hF

lemma not_supercritical : ¬ Real.log 2 < (890/1424:ℝ)*Real.log 3 := by
  have hn : (3:ℕ)^5 ≤ 2^8 := by decide +kernel
  have hh : (3:ℝ)^5 ≤ (2:ℝ)^8 := by exact_mod_cast hn
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^5) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos406BinaryJointPolicyControl
