import Submission.BinaryProfileMinplusCertificates
import Submission.BinaryAcceptingMinplusCoverage

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryProfileControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def nextData : Array (List (Fin 8)) := #[[0],[1],[7],[4],[2],[5],[4],[5],[6],[5],[2],[5,6],[5],[5],[4,6],[3,6]]
private def weightData : Array ℤ := #[0,0,-1024,-1024,5,5,-1010,-1010,5,5,5,5,5,5,-1024,-1024,-6,-6,-1024,-1024,5,5,5,1024,-1014,-1014,-1014,-1014,-1013,1024,-1012,1024]
private def sourceData : Array (Fin 8) := #[0,0,0,1,1,1,7,7,7,4,4,4,6,4,6,4,6,3,3,3,6,6,6,5,5,5,5,5,5,5,4,2,2,2,5,6,6,6]
private def carryData : Array ℕ := #[0,1,2,0,1,2,0,1,2,0,1,2,0,1,1,2,2,0,1,2,2,0,2,0,1,2,0,1,2,2,0,0,1,2,1,1,2,1]
private def endData : Array (List (Fin 8)) := #[[0],[1],[7],[4],[4],[3],[6],[5],[6],[5],[4],[5],[5],[5],[5],[2],[2],[5],[5],[5],[5],[2],[6],[5],[2],[5,6],[2],[5],[2],[5],[2],[2],[5],[2],[2,5],[2,5],[5,6],[2]]
private def hData : Array ℤ := #[0,0,-1024,-1024,-1019,-1019,-1010,-1010,-1008,-1008,-1007,-1007,-1021,-1021,-2039,-2039,-1019,-1019,-1022,-1022,8,8,-1021,-1021,-1011,-1011,-1022,-1022,-1011,-1011,-1021,-1021,-1011,-1011,-1022,-1022,-1021,-1021,-1021,-1021,-1011,-1011,-1011,-1011,8,8,8,8,8,8,8,1027,8,8,8,8,8,8,8,8,-1022,-1022,8,8,8,8,8,8,8,2048,-1011,2048,-1011,8,-1011,-1011]
private def destData : Array (Fin 38) := #[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,5,0,6,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,9,0,0,0,0,0,0,0,0,0,0,0,0,0,10,0,11,0,9,12,13,14,0,0,0,0,0,0,0,0,0,0,0,0,15,16,17,12,0,0,0,0,0,0,0,0,0,0,0,0,18,14,19,20,21,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,22,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,25,0,26,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,23,0,0,0,0,0,0,0,0,0,28,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,29,0,0,0,0,0,0,0,0,0,24,0,29,0,30,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,29,0,0,0,0,0,0,0,0,0,24,0,29,0,26,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,27,0,29,0,31,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,23,12,0,0,0,0,0,0,0,0,0,0,0,0,34,35,29,36,31,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,23,12,0,0,0,0,0,0,0,0,0,0,0,0,24,37,29,20,0,0,0,0,0,0,0,0,24,37,29,22,21,0,14,0,0,0,0,0,0,0,0,0,31,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,29,0,0,0,0,0,33,0,23,12,0,0,0,0,0,0,0,0,28,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,34,0,29,0,0,0,0,0,28,0,23,0,0,0,0,0]
private def parentData : Array (Fin 8) := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,0,0,3,3,0,0,6,6,6,6,6,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,6,5,6,5,5,6,5,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,6,0,0,5,5,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0]
private def finishData : Array (Fin 8) := #[0,1,0,4,4,0,6,5,0,5,4,0,5,5,5,0,0,5,5,0,0,2,0,5,2,0,2,5,0,0,2,2,5,0,2,2,0,2]
private def jData : Array ℤ := #[0,1024,-1024,0,6,-1024,-5,1024]
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 8) (d : ℕ) : List (Fin 8) := nextData[s.val*2+(digit d).val]?.getD []
def nextTable (s : Fin 8) (d : ℕ) : Finset (Fin 8) := (nextList s d).toFinset
def slot (s : Fin 8) (d : ℕ) (t : Fin 8) : ℕ := if t=(nextList s d).getD 0 0 then 0 else 1
def W (s : Fin 8) (d : ℕ) (t : Fin 8) : ℤ := weightData[(s.val*2+(digit d).val)*2+slot s d t]?.getD 0
def source (p : Fin 38) : Fin 8 := sourceData[p.val]?.getD 0
def carry (p : Fin 38) : ℕ := carryData[p.val]?.getD 0
def endsList (p : Fin 38) : List (Fin 8) := endData[p.val]?.getD []
def ends (p : Fin 38) : Finset (Fin 8) := (endsList p).toFinset
def eslot (p : Fin 38) (t : Fin 8) : ℕ := if t=(endsList p).getD 0 0 then 0 else 1
def H (p : Fin 38) (t : Fin 8) : ℤ := hData[p.val*2+eslot p t]?.getD 0
def index (p : Fin 38) (d cp : ℕ) (sp : Fin 8) : ℕ := (p.val*6+(digit d).val*3+cp)*2+slot (source p) d sp
def target (p : Fin 38) (d cp : ℕ) (sp : Fin 8) : Fin 38 := destData[index p d cp sp]?.getD 0
def parent (p : Fin 38) (d cp : ℕ) (sp tp : Fin 8) : Fin 8 :=
  parentData[(index p d cp sp)*2+eslot (target p d cp sp) tp]?.getD 0
def finish (p : Fin 38) : Fin 8 := finishData[p.val]?.getD 0
def J (s : Fin 8) : ℤ := jData[s.val]?.getD 0
def F (s : Fin 8) : Prop := s.val ∈ [0,1,2,3,4,5,6,7]
instance (s : Fin 8) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 8) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/8

private def familyData : Array (Finset (Fin 8)) := #[{0},{1},{2},{2,5},{2,6},{3,6},{4},{4,5},{4,6},{5},{5,6},{6},{7}]
def memberSet (i : Fin 13) : Finset (Fin 8) := familyData[i.val]?.getD ∅
private def covDestData : Array (Fin 13) := #[0,1,12,6,2,9,2,10,3,9,7,9,11,9,4,10,10,9,2,10,3,10,9,9,8,5]
def covDest (i : Fin 13) (d : Fin 2) : Fin 13 := covDestData[i.val*2+d.val]?.getD 0
def family : Finset (Finset (Fin 8)) := Finset.univ.image memberSet
lemma coverage_steps : ∀ i (d : Fin 2), nextSet D (memberSet i) d.val=memberSet (covDest i d) := by decide +kernel
lemma coverage_accepting : ∀ i : Fin 13, ∃ t, t ∈ memberSet i ∧ F t := by decide +kernel

def coverage : Coverage D F where
  family := family
  start := by
    have hh : memberSet 0 = {D.start} := by decide +kernel
    rw [← hh]
    exact Finset.mem_image_of_mem memberSet (Finset.mem_univ 0)
  step := by
    intro A hA d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hA
    rw [coverage_steps i ⟨d,hd⟩]
    exact Finset.mem_image_of_mem memberSet (Finset.mem_univ _)
  accepting := by
    intro A hA
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hA
    exact coverage_accepting i
lemma total : Total D F := coverage.total

def R (s : Fin 8) (p : Fin 38) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 8) (p : Fin 38) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_profiles : R 0 0 0 ∧ R 0 1 1 ∧ R 0 2 2 := by decide +kernel
lemma seed_zero : ∀ t ∈ ends 0, t=0 ∧ 0 ≤ H 0 t := by decide +kernel
lemma seed_one : ∀ t ∈ ends 1, t=1 ∧ W 0 1 1 ≤ H 1 t := by decide +kernel
lemma seed_two : ∀ t ∈ ends 2, t ∈ D.next 1 0 ∧ W 0 1 1+W 1 0 t ≤ H 2 t := by decide +kernel
lemma first_one : (1:Fin 8) ∈ D.next D.start 1 := by decide +kernel

def StepRow (p : Fin 38) : Prop := ∀ (d e : Fin 2) (cp : Fin 3),
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
lemma step_row_26 : StepRow 26 := by
  unfold StepRow R
  decide +kernel
lemma step_row_27 : StepRow 27 := by
  unfold StepRow R
  decide +kernel
lemma step_row_28 : StepRow 28 := by
  unfold StepRow R
  decide +kernel
lemma step_row_29 : StepRow 29 := by
  unfold StepRow R
  decide +kernel
lemma step_row_30 : StepRow 30 := by
  unfold StepRow R
  decide +kernel
lemma step_row_31 : StepRow 31 := by
  unfold StepRow R
  decide +kernel
lemma step_row_32 : StepRow 32 := by
  unfold StepRow R
  decide +kernel
lemma step_row_33 : StepRow 33 := by
  unfold StepRow R
  decide +kernel
lemma step_row_34 : StepRow 34 := by
  unfold StepRow R
  decide +kernel
lemma step_row_35 : StepRow 35 := by
  unfold StepRow R
  decide +kernel
lemma step_row_36 : StepRow 36 := by
  unfold StepRow R
  decide +kernel
lemma step_row_37 : StepRow 37 := by
  unfold StepRow R
  decide +kernel
lemma step_checks : ∀ p : Fin 38, StepRow p := by
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
  · exact step_row_26
  · exact step_row_27
  · exact step_row_28
  · exact step_row_29
  · exact step_row_30
  · exact step_row_31
  · exact step_row_32
  · exact step_row_33
  · exact step_row_34
  · exact step_row_35
  · exact step_row_36
  · exact step_row_37

lemma finish_checks : ∀ p : Fin 38, carry p < 2 → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 8 := by decide +kernel

def construction : Erdos406BinaryProfileMinplus.Construction D F (Fin 38) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/8
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
      refine ⟨(W 0 1 1:ℝ)/8,?_,?_⟩
      · have hr := Run.cons first_one (Run.nil (D:=D) 1)
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ) ≤ H 1 1 := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/8 ≤ (H 1 1:ℝ)/8
        linarith
    · refine ⟨2,seed_profiles.2.2,?_⟩
      intro t ht
      obtain ⟨he,hh⟩ := seed_two t ht
      refine ⟨(W 0 1 1:ℝ)/8+(W 1 0 t:ℝ)/8,?_,?_⟩
      · have hr := Run.cons first_one (Run.cons he (Run.nil (D:=D) t))
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ)+W 1 0 t ≤ H 2 t := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/8+(W 1 0 t:ℝ)/8 ≤ (H 2 t:ℝ)/8
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
    change (H p (parent p d cp sp tp):ℝ)/8+(W (parent p d cp sp tp) e tp:ℝ)/8-
      (W (source p) d sp:ℝ)/8 ≤ (H (target p d cp sp) tp:ℝ)/8
    linarith
  finish := by
    intro s p c hc hr hf
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨ht,hf',hh⟩ := finish_checks p hc hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 8 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/8 ≤ 1
    linarith

def G (s : Fin 8) : Prop := s.val ∈ [1,2,4,5,6,7]
def Z (s : Fin 8) : Prop := s.val ∈ [0,1,2,3,4,5,6,7]
instance (s : Fin 8) : Decidable (G s) := by unfold G; infer_instance
instance (s : Fin 8) : Decidable (Z s) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s t, G s → t ∈ D.next s 0 → G t) ∧
    (∀ t, F t → Z t) ∧
    (∀ s t, Z t → t ∈ D.next s 0 → Z s) ∧
    (∀ s t, G s → Z t → t ∈ D.next s 0 → 5+J t-J s ≤ W s 0 t) ∧
    (∀ s t, s ∈ D.next D.start 1 → G t → F t → Z s → -3072 ≤ W D.start 1 s+J t-J s) := by decide +kernel

def powerBound : PowerBound D F where
  a := 5/8
  B := 384
  G := G
  Z := Z
  J s := (J s:ℝ)/8
  start := power_checks.1
  forward := power_checks.2.1
  accepting := power_checks.2.2.1
  backward := power_checks.2.2.2.1
  lower_step := by
    intro s t hs hz he
    have hh : (5:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s t hs hz he
    change (5/8:ℝ)+(J t:ℝ)/8-(J s:ℝ)/8 ≤ (W s 0 t:ℝ)/8
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-3072:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2.2.2 s t hs ht hf hz
    change -(384:ℝ) ≤ (W D.start 1 s:ℝ)/8+(J t:ℝ)/8-(J s:ℝ)/8
    linarith

def V (n : ℕ) : ℝ := value D F total n
lemma construction_bound (n d : ℕ) (hd : d<2) : V (3*n+d) ≤ V n+1 := construction.construction_bound total n d hd
lemma power_lower (k : ℕ) : (5/8:ℝ)*k-384 ≤ V (2^k) := powerBound.power_lower total k

lemma not_supercritical : ¬ Real.log 2 < (5/8:ℝ)*Real.log 3 := by
  have hh : (3:ℝ)^5 ≤ (2:ℝ)^8 := by norm_num
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^5) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos406BinaryProfileControl
