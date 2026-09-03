import Submission.BinaryEvenProfileCertificates
import Submission.BinaryAcceptingMinplusCoverage

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryEvenPrunedProfileControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def nextData : Array (List (Fin 10)) := #[[0],[1],[2,3],[4,5],[6],[7],[8],[9],[6],[7],[8],[9],[2],[4],[2],[4],[3],[5],[3],[5]]
private def weightData : Array (Array (ℤ)) := #[#[0,0,-256,-256],#[-256,-256,-256,-256],#[0,0,0,0],#[256,256,-254,-254],#[0,0,0,0],#[256,256,-254,-254],#[2,2,2,2],#[2,2,2,2],#[-254,-254,-254,-254],#[256,256,256,256]]
private def sourceData : Array (Fin 10) := #[0,0,0,1,1,1,2,3,2,3,2,3,4,5,4,5,4,5,6,6,8,8,6,7,8,9,7,7,9,9,6,6,8,8,6,7,8,9,2,4,3,5,4,4,5,5,2,2,3,3,7,7,9,9]
private def carryData : Array ℕ := #[0,1,2,0,1,2,0,0,1,1,2,2,0,0,1,1,2,2,0,1,0,1,2,0,2,0,1,2,1,2,0,1,0,1,2,0,2,0,2,0,2,0,1,2,1,2,0,1,0,1,1,2,1,2]
private def endData : Array (List (Fin 10)) := #[[0],[1],[2,3],[4,5],[6,8],[7,9],[6,8],[6,8],[7,9],[7,9],[2,3],[2,3],[4,5],[4,5],[2,3],[2,3],[4,5],[4,5],[2,3],[4,5],[2,3],[4,5],[2,3],[4,5],[2,3],[4,5],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[6,8],[7,9],[2,3],[4,5],[2,3],[4,5],[2,3],[4,5],[2,3],[4,5]]
private def hData : Array (Array (ℤ)) := #[#[0,0],#[-256,-256],#[-512,-512],#[-256,-256],#[-256,0],#[-256,-510],#[0,256],#[0,256],#[0,-254],#[0,-254],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[-254,-254],#[-254,-254],#[2,2],#[2,2],#[-254,-254],#[256,256],#[2,258],#[2,-252],#[256,512],#[256,2],#[2,258],#[2,-252],#[-254,2],#[-254,-508],#[2,258],#[2,-252],#[-254,2],#[256,2],#[0,256],#[0,-254],#[0,256],#[0,-254],#[0,256],#[0,-254],#[0,256],#[0,-254],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[2,2],#[256,256],#[256,256]]
private def destData : Array (Array (Fin 54)) := #[#[0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,0,0,2,0,3,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,0,5,0],#[6,7,8,9,0,0,0,0,0,0,0,0],#[0,0,0,0,10,11,12,13,0,0,0,0],#[0,0,0,0,0,0,0,0,14,15,16,17],#[18,0,19,0,0,0,0,0,0,0,0,0],#[20,0,21,0,0,0,0,0,0,0,0,0],#[0,0,0,0,22,0,23,0,0,0,0,0],#[0,0,0,0,24,0,25,0,0,0,0,0],#[0,0,0,0,0,0,0,0,26,0,27,0],#[0,0,0,0,0,0,0,0,28,0,29,0],#[30,0,31,0,0,0,0,0,0,0,0,0],#[32,0,33,0,0,0,0,0,0,0,0,0],#[0,0,0,0,34,0,35,0,0,0,0,0],#[0,0,0,0,36,0,37,0,0,0,0,0],#[0,0,0,0,0,0,0,0,26,0,27,0],#[0,0,0,0,0,0,0,0,28,0,29,0],#[6,0,8,0,0,0,0,0,0,0,0,0],#[0,0,0,0,38,0,39,0,0,0,0,0],#[7,0,9,0,0,0,0,0,0,0,0,0],#[0,0,0,0,40,0,41,0,0,0,0,0],#[0,0,0,0,0,0,0,0,42,0,43,0],#[6,0,8,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,44,0,45,0],#[7,0,9,0,0,0,0,0,0,0,0,0],#[0,0,0,0,10,0,12,0,0,0,0,0],#[0,0,0,0,0,0,0,0,14,0,16,0],#[0,0,0,0,11,0,13,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,0,17,0],#[46,0,47,0,0,0,0,0,0,0,0,0],#[0,0,0,0,10,0,12,0,0,0,0,0],#[48,0,49,0,0,0,0,0,0,0,0,0],#[0,0,0,0,11,0,13,0,0,0,0,0],#[0,0,0,0,0,0,0,0,14,0,16,0],#[46,0,47,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,0,17,0],#[48,0,49,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,50,0,51,0],#[18,0,19,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,53,0],#[20,0,21,0,0,0,0,0,0,0,0,0],#[0,0,0,0,22,0,23,0,0,0,0,0],#[0,0,0,0,0,0,0,0,50,0,51,0],#[0,0,0,0,24,0,25,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,53,0],#[30,0,31,0,0,0,0,0,0,0,0,0],#[0,0,0,0,34,0,35,0,0,0,0,0],#[32,0,33,0,0,0,0,0,0,0,0,0],#[0,0,0,0,36,0,37,0,0,0,0,0],#[0,0,0,0,38,0,39,0,0,0,0,0],#[0,0,0,0,0,0,0,0,42,0,43,0],#[0,0,0,0,40,0,41,0,0,0,0,0],#[0,0,0,0,0,0,0,0,44,0,45,0]]
private def parentData : Array (Array (Fin 10)) := #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0],#[4,5,4,5,4,5,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,8,6,8,6,8,6,8,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,9,7,9,7,9,7,9],#[6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0],#[4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0],#[2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0],#[2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0],#[4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0],#[4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0],#[0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0],#[6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0],#[7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0],#[7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0],#[7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0],#[7,9,0,0,7,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0],#[0,0,0,0,0,0,0,0,6,8,0,0,6,8,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,9,0,0,7,9,0,0],#[2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0],#[2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0],#[0,0,0,0,0,0,0,0,2,3,0,0,2,3,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,0,0,4,5,0,0]]
private def finishData : Array (Fin 10) := #[0,1,0,5,6,0,0,6,0,7,0,0,0,5,0,3,0,0,3,5,0,0,0,5,0,0,6,0,0,0,6,7,0,0,0,7,0,0,0,0,0,7,0,0,6,0,0,0,3,5,3,0,0,0]
private def jData : Array ℤ := #[0,0,256,0,0,-255,0,0,0,0,0,0,-256,0,0,0,0,0,0,0]
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 10) (d : ℕ) : List (Fin 10) := nextData[s.val*2+(digit d).val]?.getD []
def nextTable (s : Fin 10) (d : ℕ) : Finset (Fin 10) := (nextList s d).toFinset
def slot (s : Fin 10) (d : ℕ) (t : Fin 10) : ℕ := if t=(nextList s d).getD 0 0 then 0 else 1
def W (s : Fin 10) (d : ℕ) (t : Fin 10) : ℤ := (weightData[s.val]?.getD #[])[(digit d).val*2+slot s d t]?.getD 0
def source (p : Fin 54) : Fin 10 := sourceData[p.val]?.getD 0
def carry (p : Fin 54) : ℕ := carryData[p.val]?.getD 0
def endsList (p : Fin 54) : List (Fin 10) := endData[p.val]?.getD []
def ends (p : Fin 54) : Finset (Fin 10) := (endsList p).toFinset
def eslot (p : Fin 54) (t : Fin 10) : ℕ := if t=(endsList p).getD 0 0 then 0 else 1
def H (p : Fin 54) (t : Fin 10) : ℤ := (hData[p.val]?.getD #[])[eslot p t]?.getD 0
def index (p : Fin 54) (d cp : ℕ) (sp : Fin 10) : ℕ := ((digit d).val*3+cp)*2+slot (source p) d sp
def target (p : Fin 54) (d cp : ℕ) (sp : Fin 10) : Fin 54 := (destData[p.val]?.getD #[])[index p d cp sp]?.getD 0
def parent (p : Fin 54) (d cp : ℕ) (sp tp : Fin 10) : Fin 10 :=
  (parentData[p.val]?.getD #[])[(index p d cp sp)*2+eslot (target p d cp sp) tp]?.getD 0
def finish (p : Fin 54) : Fin 10 := finishData[p.val]?.getD 0
def J (s : Fin 10) (p : Bool) : ℤ := jData[s.val*2+(if p then 1 else 0)]?.getD 0
def F (s : Fin 10) : Prop := s.val ∉ [2,4,8,9]
instance (s : Fin 10) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 10) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/2

private def familyData : Array (Finset (Fin 10)) := #[{0},{1},{2,3},{4,5},{6,8},{7,9}]
def memberSet (i : Fin 6) : Finset (Fin 10) := familyData[i.val]?.getD ∅
private def covDestData : Array (Fin 6) := #[0,1,2,3,4,5,4,5,2,3,2,3]
def covDest (i : Fin 6) (d : Fin 2) : Fin 6 := covDestData[i.val*2+d.val]?.getD 0
def family : Finset (Finset (Fin 10)) := Finset.univ.image memberSet
lemma coverage_steps : ∀ i (d : Fin 2), nextSet D (memberSet i) d.val=memberSet (covDest i d) := by decide +kernel
private def covAcceptData : Array (Fin 10) := #[0,1,3,5,6,7]
def covAccept (i : Fin 6) : Fin 10 := covAcceptData[i.val]?.getD 0
lemma coverage_accepting : ∀ i : Fin 6, covAccept i ∈ memberSet i ∧ F (covAccept i) := by decide +kernel

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
    exact ⟨covAccept i,coverage_accepting i⟩
lemma total : Total D F := coverage.total

def R (s : Fin 10) (p : Fin 54) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 10) (p : Fin 54) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_profiles : R 0 0 0 ∧ R 0 1 1 ∧ R 0 2 2 := by decide +kernel
lemma seed_zero : ∀ t ∈ ends 0, t=0 ∧ 0 ≤ H 0 t := by decide +kernel
lemma seed_one : ∀ t ∈ ends 1, t=1 ∧ W 0 1 1 ≤ H 1 t := by decide +kernel
lemma seed_two : ∀ t ∈ ends 2, t ∈ D.next 1 0 ∧ W 0 1 1+W 1 0 t ≤ H 2 t := by decide +kernel
lemma first_one : (1:Fin 10) ∈ D.next D.start 1 := by decide +kernel

def StepRow (p : Fin 54) : Prop := ∀ (d e : Fin 2) (cp : Fin 3),
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
lemma step_row_38 : StepRow 38 := by
  unfold StepRow R
  decide +kernel
lemma step_row_39 : StepRow 39 := by
  unfold StepRow R
  decide +kernel
lemma step_row_40 : StepRow 40 := by
  unfold StepRow R
  decide +kernel
lemma step_row_41 : StepRow 41 := by
  unfold StepRow R
  decide +kernel
lemma step_row_42 : StepRow 42 := by
  unfold StepRow R
  decide +kernel
lemma step_row_43 : StepRow 43 := by
  unfold StepRow R
  decide +kernel
lemma step_row_44 : StepRow 44 := by
  unfold StepRow R
  decide +kernel
lemma step_row_45 : StepRow 45 := by
  unfold StepRow R
  decide +kernel
lemma step_row_46 : StepRow 46 := by
  unfold StepRow R
  decide +kernel
lemma step_row_47 : StepRow 47 := by
  unfold StepRow R
  decide +kernel
lemma step_row_48 : StepRow 48 := by
  unfold StepRow R
  decide +kernel
lemma step_row_49 : StepRow 49 := by
  unfold StepRow R
  decide +kernel
lemma step_row_50 : StepRow 50 := by
  unfold StepRow R
  decide +kernel
lemma step_row_51 : StepRow 51 := by
  unfold StepRow R
  decide +kernel
lemma step_row_52 : StepRow 52 := by
  unfold StepRow R
  decide +kernel
lemma step_row_53 : StepRow 53 := by
  unfold StepRow R
  decide +kernel
lemma step_checks : ∀ p : Fin 54, StepRow p := by
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
  · exact step_row_38
  · exact step_row_39
  · exact step_row_40
  · exact step_row_41
  · exact step_row_42
  · exact step_row_43
  · exact step_row_44
  · exact step_row_45
  · exact step_row_46
  · exact step_row_47
  · exact step_row_48
  · exact step_row_49
  · exact step_row_50
  · exact step_row_51
  · exact step_row_52
  · exact step_row_53

lemma finish_checks : ∀ p : Fin 54, carry p < 2 → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 2 := by decide +kernel

def construction : Erdos406BinaryProfileMinplus.Construction D F (Fin 54) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/2
  seed := by
    intro c hc
    interval_cases c
    · refine ⟨0,seed_profiles.1,?_⟩
      intro t ht
      obtain ⟨rfl,hh⟩ := seed_zero t ht
      refine ⟨0,?_,?_⟩
      · simpa [D] using Run.nil (D:=D) (0:Fin 10)
      · have hR : (0:ℝ) ≤ H 0 0 := by exact_mod_cast hh
        exact div_nonneg hR (by norm_num)
    · refine ⟨1,seed_profiles.2.1,?_⟩
      intro t ht
      obtain ⟨rfl,hh⟩ := seed_one t ht
      refine ⟨(W 0 1 1:ℝ)/2,?_,?_⟩
      · have hr := Run.cons first_one (Run.nil (D:=D) 1)
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ) ≤ H 1 1 := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/2 ≤ (H 1 1:ℝ)/2
        linarith
    · refine ⟨2,seed_profiles.2.2,?_⟩
      intro t ht
      obtain ⟨he,hh⟩ := seed_two t ht
      refine ⟨(W 0 1 1:ℝ)/2+(W 1 0 t:ℝ)/2,?_,?_⟩
      · have hr := Run.cons first_one (Run.cons he (Run.nil (D:=D) t))
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ)+W 1 0 t ≤ H 2 t := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/2+(W 1 0 t:ℝ)/2 ≤ (H 2 t:ℝ)/2
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
    change (H p (parent p d cp sp tp):ℝ)/2+(W (parent p d cp sp tp) e tp:ℝ)/2-
      (W (source p) d sp:ℝ)/2 ≤ (H (target p d cp sp) tp:ℝ)/2
    linarith
  finish := by
    intro s p c hc hr hf
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨ht,hf',hh⟩ := finish_checks p hc hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 2 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/2 ≤ 1
    linarith

def G (s : Fin 10) (p : Bool) : Prop := (s.val,p) ∈ [(1,false),(2,true),(3,true),(6,false),(8,false)]
def Z (s : Fin 10) (p : Bool) : Prop := (s.val,p) ∈ [(0,false),(0,true),(1,false),(1,true),(2,true),(3,false),(4,true),(5,false),(6,false),(7,false),(8,true),(9,true)]
instance (s : Fin 10) (p : Bool) : Decidable (G s p) := by unfold G; infer_instance
instance (s : Fin 10) (p : Bool) : Decidable (Z s p) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s false) ∧
    (∀ s (p : Bool), G s p → ∀ t ∈ D.next s 0, G t (!p)) ∧
    (∀ t, F t → Z t false) ∧
    (∀ s (p : Bool), ∀ t ∈ D.next s 0, Z t (!p) → Z s p) ∧
    (∀ s (p : Bool), G s p → ∀ t ∈ D.next s 0, Z t (!p) → 1+J t (!p)-J s p ≤ W s 0 t) ∧
    (∀ s ∈ D.next D.start 1, ∀ t, G t false → F t → Z s false → -768 ≤ W D.start 1 s+J t false-J s false) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

def powerBound : Erdos406BinaryEvenProfile.PowerBound D F where
  a := 1/2
  B := 384
  G := G
  Z := Z
  J s p := (J s p:ℝ)/2
  start := power_checks.1
  forward := by intro s t p hs ht; exact power_checks.2.1 s p hs t ht
  accepting := power_checks.2.2.1
  backward := by intro s t p ht he; exact power_checks.2.2.2.1 s p t he ht
  lower_step := by
    intro s t p hs hz he
    have hh : (1:ℝ)+J t (!p)-J s p ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s p hs t he hz
    change (1/2:ℝ)+(J t (!p):ℝ)/2-(J s p:ℝ)/2 ≤ (W s 0 t:ℝ)/2
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-768:ℝ) ≤ W D.start 1 s+J t false-J s false := by exact_mod_cast power_checks.2.2.2.2.2 s hs t ht hf hz
    change -(384:ℝ) ≤ (W D.start 1 s:ℝ)/2+(J t false:ℝ)/2-(J s false:ℝ)/2
    linarith

def V (n : ℕ) : ℝ := value D F total n
lemma construction_bound (n d : ℕ) (hd : d<2) : V (3*n+d) ≤ V n+1 := construction.construction_bound total n d hd
lemma power_lower (k : ℕ) : (1/2:ℝ)*(2*k)-384 ≤ V (2^(2*k)) := powerBound.power_lower total k

lemma not_supercritical : ¬ Real.log 2 < (1/2:ℝ)*Real.log 3 := by
  have hh : (3:ℝ)^1 ≤ (2:ℝ)^2 := by norm_num
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^1) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos406BinaryEvenPrunedProfileControl
