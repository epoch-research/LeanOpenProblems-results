import Submission.BinaryGroupedProfileCertificates

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryGroupedBooleanPairControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000

private def nextData : Array (List (Fin 9)) := #[[0],[1],[2],[3],[4],[5],[6,8],[6,8],[6],[7],[3],[6,8],[6],[6,8],[6,8],[6,8],[6,8],[6,8]]
private def weightData : Array (Array (ℤ)) := #[#[0,0,8,8],#[4,4,8,8],#[4,4,6,6],#[3,3,4,4],#[5,5,8,8],#[6,6,5,5],#[5,5,5,5],#[3,3,3,3],#[5,5,5,5]]
private def sourceData : Array (Fin 9) := #[0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,3,2,2,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,4,5,5,5,5,5,6,6,8,8,6,8,5,5,6,8,6,6,8,8,6,8,6,6,8,8,6,8,6,8,6,6,8,8,6,8,6,8,6,8,6,8,7,7,7,7,7,7,7,7,3,7]
private def carryData : Array ℕ := #[0,1,2,3,4,5,6,7,8,6,7,0,1,2,3,4,3,5,6,5,7,8,0,1,2,3,5,4,6,7,0,8,6,1,2,4,3,1,5,6,6,8,7,1,0,3,2,5,4,7,6,0,2,1,8,3,4,6,5,8,1,1,1,1,0,0,7,3,2,2,3,3,3,3,4,4,5,5,5,5,4,4,6,6,7,7,7,7,8,8,8,8,6,6,2,2,0,2,1,4,6,5,3,8,5,7]
private def endData : Array (List (Fin 9)) := #[[0],[1],[2],[3],[4],[5],[6],[6],[6],[6,8],[6,8],[7],[3],[6,8],[6],[6,8],[6,8],[6],[6,8],[6,8],[6],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6],[6,8],[6,8],[6,8],[6,8],[6],[6,8],[6,8],[6,8],[6,8],[6],[6],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6],[6,8],[6,8],[6,8],[6,8],[6],[6,8],[6],[6,8],[6,8],[6,8],[6,8],[6,8],[6],[6],[6],[6,8],[6],[6,8],[6],[6],[6],[6,8],[6],[6,8],[6,8],[6,8],[6],[6],[6],[6,8],[6],[6,8],[6],[6],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8],[6,8]]
private def hData : Array (Array (ℤ)) := #[#[0,0],#[8,8],#[12,12],#[16,16],#[16,16],#[18,18],#[19,19],#[20,20],#[21,21],#[19,19],#[20,20],#[16,16],#[16,16],#[15,15],#[16,16],#[16,16],#[16,16],#[17,17],#[17,17],#[17,17],#[18,18],#[18,18],#[15,15],#[15,15],#[15,15],#[16,16],#[16,16],#[16,16],#[17,17],#[17,17],#[14,14],#[17,17],#[17,17],#[14,14],#[14,14],#[14,14],#[14,14],#[14,14],#[15,15],#[15,15],#[15,15],#[15,15],#[15,15],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[17,17],#[17,17],#[15,15],#[15,15],#[15,15],#[17,17],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[16,16],#[13,13],#[13,13],#[13,13],#[14,14],#[14,14],#[14,14],#[14,14],#[14,14],#[14,14],#[14,14]]
private def destData : Array (Array (Fin 106)) := #[#[0,0,1,0,0,0,0,0],#[2,0,3,0,0,0,0,0],#[4,0,5,0,0,0,0,0],#[9,0,10,0,0,0,0,0],#[8,0,0,0,11,0,0,0],#[0,0,0,0,13,0,12,0],#[0,0,0,0,15,0,14,0],#[0,0,0,0,18,0,17,0],#[0,0,0,0,21,0,20,0],#[0,0,0,0,15,0,16,0],#[0,0,0,0,18,0,19,0],#[22,0,23,0,0,0,0,0],#[24,0,25,0,0,0,0,0],#[27,0,26,0,0,0,0,0],#[28,0,29,0,0,0,0,0],#[31,0,0,0,30,0,0,0],#[32,0,29,0,0,0,0,0],#[0,0,0,0,34,0,33,0],#[0,0,0,0,35,0,36,0],#[0,0,0,0,34,0,37,0],#[0,0,0,0,40,0,38,0],#[0,0,0,0,41,0,42,0],#[44,0,43,0,0,0,0,0],#[46,0,45,0,0,0,0,0],#[48,0,47,0,0,0,0,0],#[50,0,49,0,0,0,0,0],#[0,0,0,0,52,0,53,0],#[54,0,0,0,51,0,0,0],#[0,0,0,0,56,0,55,0],#[0,0,0,0,57,0,58,0],#[64,65,61,63,0,0,0,0],#[0,0,0,0,59,0,66,0],#[0,0,0,0,56,0,67,0],#[68,69,71,73,0,0,0,0],#[80,81,77,79,0,0,0,0],#[90,91,0,0,64,65,0,0],#[92,93,85,87,0,0,0,0],#[94,95,71,73,0,0,0,0],#[0,0,0,0,94,95,60,62],#[0,0,0,0,80,81,70,72],#[0,0,0,0,80,81,71,73],#[0,0,0,0,90,91,85,87],#[0,0,0,0,92,93,77,79],#[94,0,71,0,0,0,0,0],#[64,0,61,0,0,0,0,0],#[92,0,85,0,0,0,0,0],#[80,0,77,0,0,0,0,0],#[0,0,0,0,97,0,98,0],#[90,0,0,0,96,0,0,0],#[0,0,0,0,100,0,101,0],#[0,0,0,0,99,0,102,0],#[30,0,37,0,0,0,0,0],#[35,0,104,0,0,0,0,0],#[34,0,36,0,0,0,0,0],#[0,0,0,0,103,0,105,0],#[39,0,42,0,0,0,0,0],#[41,0,0,0,64,65,0,0],#[0,0,0,0,80,81,71,73],#[0,0,0,0,94,95,61,63],#[0,0,0,0,90,91,85,87],#[68,0,71,0,0,0,0,0],#[94,0,71,0,0,0,0,0],#[68,69,71,73,0,0,0,0],#[94,95,71,73,0,0,0,0],#[64,0,61,0,0,0,0,0],#[64,65,61,63,0,0,0,0],#[0,0,0,0,92,93,77,79],#[40,0,42,0,0,0,0,0],#[74,0,77,0,0,0,0,0],#[74,75,77,79,0,0,0,0],#[82,0,85,0,0,0,0,0],#[92,0,85,0,0,0,0,0],#[82,83,85,87,0,0,0,0],#[92,93,85,87,0,0,0,0],#[88,0,0,0,64,65,0,0],#[88,89,0,0,64,65,0,0],#[0,0,0,0,94,95,60,62],#[0,0,0,0,94,95,61,63],#[0,0,0,0,94,95,60,62],#[0,0,0,0,94,95,61,63],#[90,0,0,0,64,65,0,0],#[90,91,0,0,64,65,0,0],#[0,0,0,0,80,81,70,72],#[0,0,0,0,80,81,70,72],#[0,0,0,0,92,93,76,78],#[0,0,0,0,92,93,77,79],#[0,0,0,0,92,93,76,78],#[0,0,0,0,92,93,77,79],#[0,0,0,0,90,91,84,86],#[0,0,0,0,90,91,84,86],#[0,0,0,0,90,91,85,87],#[0,0,0,0,90,91,85,87],#[0,0,0,0,80,81,71,73],#[0,0,0,0,80,81,71,73],#[80,0,77,0,0,0,0,0],#[80,81,77,79,0,0,0,0],#[64,65,61,63,0,0,0,0],#[80,81,77,79,0,0,0,0],#[94,95,71,73,0,0,0,0],#[90,91,0,0,64,65,0,0],#[0,0,0,0,80,81,71,73],#[0,0,0,0,94,95,61,63],#[92,93,85,87,0,0,0,0],#[0,0,0,0,90,91,85,87],#[0,0,0,0,94,95,61,63],#[0,0,0,0,92,93,77,79]]
private def parentData : Array (Array (Fin 9)) := #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0],#[2,2,0,0,2,2,0,0,0,0,0,0,0,0,0,0],#[3,3,0,0,3,3,0,0,0,0,0,0,0,0,0,0],#[4,4,0,0,0,0,0,0,4,4,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0],#[3,3,0,0,3,3,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,6,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,0,0,0,0,6,6,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,8,0,0,0,0,0,0,6,6,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,6,6,6,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,0,0,0,0,6,6,6,6,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,8,0,0,0,0,0,0,6,6,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,0,0,6,8,0,0],#[6,6,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,0,0,0,0,6,6,6,6,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[6,6,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,6,6,6,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,6,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,6,6,6,6,6,6,6,0,0,0,0,0,0,0,0],#[6,6,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,6,6,6,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,6,0,0,0,0,0,0,6,6,6,6,0,0,0,0],#[6,6,6,6,0,0,0,0,6,6,6,6,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[6,8,0,0,0,0,0,0,6,6,6,6,0,0,0,0],#[6,8,6,8,0,0,0,0,6,6,6,6,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,6,6,6],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[6,8,0,0,6,6,0,0,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[6,8,6,8,0,0,0,0,6,6,6,6,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[6,8,6,8,6,6,6,6,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8],#[0,0,0,0,0,0,0,0,6,6,6,6,6,8,6,8]]
private def finishData : Array (Fin 9) := #[0,1,0,3,4,0,0,0,0,0,0,7,3,0,6,6,6,0,0,0,0,0,6,6,0,6,0,6,0,0,6,0,0,6,0,6,6,6,0,0,0,0,0,6,6,6,0,0,6,0,0,6,0,6,0,6,6,0,0,0,6,6,6,6,6,6,0,6,0,0,6,6,6,6,6,6,0,0,0,0,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,6,6,0,0,6,0,0,0]
private def jData : Array ℤ := #[0,0,-1,0,-2,0,-2,0,0]
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 9) (d : ℕ) : List (Fin 9) := nextData[s.val*2+(digit d).val]?.getD []
def nextTable (s : Fin 9) (d : ℕ) : Finset (Fin 9) := (nextList s d).toFinset
def slot (s : Fin 9) (d : ℕ) (t : Fin 9) : ℕ := if t=(nextList s d).getD 0 0 then 0 else 1
def W (s : Fin 9) (d : ℕ) (t : Fin 9) : ℤ := (weightData[s.val]?.getD #[])[(digit d).val*2+slot s d t]?.getD 0
def source (p : Fin 106) : Fin 9 := sourceData[p.val]?.getD 0
def carry (p : Fin 106) : ℕ := carryData[p.val]?.getD 0
def endsList (p : Fin 106) : List (Fin 9) := endData[p.val]?.getD []
def ends (p : Fin 106) : Finset (Fin 9) := (endsList p).toFinset
def eslot (p : Fin 106) (t : Fin 9) : ℕ := if t=(endsList p).getD 0 0 then 0 else 1
def H (p : Fin 106) (t : Fin 9) : ℤ := (hData[p.val]?.getD #[])[eslot p t]?.getD 0
def index (p : Fin 106) (d cp : ℕ) (sp : Fin 9) : ℕ := ((digit d).val*2+cp%2)*2+slot (source p) d sp
def target (p : Fin 106) (d cp : ℕ) (sp : Fin 9) : Fin 106 := (destData[p.val]?.getD #[])[index p d cp sp]?.getD 0
def parent (p : Fin 106) (d cp : ℕ) (sp tp : Fin 9) : Fin 9 :=
  (parentData[p.val]?.getD #[])[(index p d cp sp)*2+eslot (target p d cp sp) tp]?.getD 0
def finish (p : Fin 106) : Fin 9 := finishData[p.val]?.getD 0
def J (s : Fin 9) : ℤ := jData[s.val]?.getD 0
def F (s : Fin 9) : Prop := s.val ∉ []
instance (s : Fin 9) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 9) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/8

def R (s : Fin 9) (p : Fin 106) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 9) (p : Fin 106) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_relation_0 : R 0 0 0 := by decide +kernel
lemma seed_ends_0 : ∀ t ∈ ends 0, t=(0:Fin 9) := by decide +kernel
lemma seed_bound_0 : (0:ℤ) ≤ H 0 0 := by decide +kernel
lemma seed_runs_0 : ∀ t ∈ ends 0, ∃ v,
    Run D D.start (Nat.digits 2 0).reverse t v ∧ v ≤ (H 0 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_0 t ht
  refine ⟨((0:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 0).reverse = [] := by decide +kernel
    rw [he]
    have hr := (Run.nil (D:=D) (0:Fin 9))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((0:ℤ):ℝ) ≤ H 0 0 := by exact_mod_cast seed_bound_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_1_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_relation_1 : R 0 1 1 := by decide +kernel
lemma seed_ends_1 : ∀ t ∈ ends 1, t=(1:Fin 9) := by decide +kernel
lemma seed_bound_1 : (W 0 1 1:ℤ) ≤ H 1 1 := by decide +kernel
lemma seed_runs_1 : ∀ t ∈ ends 1, ∃ v,
    Run D D.start (Nat.digits 2 1).reverse t v ∧ v ≤ (H 1 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_1 t ht
  refine ⟨((W 0 1 1:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 1).reverse = [1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_1_0 (Run.nil (D:=D) (1:Fin 9)))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1:ℤ):ℝ) ≤ H 1 1 := by exact_mod_cast seed_bound_1
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_2_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_2_1 : (2:Fin 9) ∈ D.next 1 0 := by decide +kernel
lemma seed_relation_2 : R 0 2 2 := by decide +kernel
lemma seed_ends_2 : ∀ t ∈ ends 2, t=(2:Fin 9) := by decide +kernel
lemma seed_bound_2 : (W 0 1 1 + W 1 0 2:ℤ) ≤ H 2 2 := by decide +kernel
lemma seed_runs_2 : ∀ t ∈ ends 2, ∃ v,
    Run D D.start (Nat.digits 2 2).reverse t v ∧ v ≤ (H 2 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_2 t ht
  refine ⟨((W 0 1 1 + W 1 0 2:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 2).reverse = [1,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_2_0 (Run.cons seed_edge_2_1 (Run.nil (D:=D) (2:Fin 9))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2:ℤ):ℝ) ≤ H 2 2 := by exact_mod_cast seed_bound_2
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_3_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_3_1 : (3:Fin 9) ∈ D.next 1 1 := by decide +kernel
lemma seed_relation_3 : R 0 3 3 := by decide +kernel
lemma seed_ends_3 : ∀ t ∈ ends 3, t=(3:Fin 9) := by decide +kernel
lemma seed_bound_3 : (W 0 1 1 + W 1 1 3:ℤ) ≤ H 3 3 := by decide +kernel
lemma seed_runs_3 : ∀ t ∈ ends 3, ∃ v,
    Run D D.start (Nat.digits 2 3).reverse t v ∧ v ≤ (H 3 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_3 t ht
  refine ⟨((W 0 1 1 + W 1 1 3:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 3).reverse = [1,1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_3_0 (Run.cons seed_edge_3_1 (Run.nil (D:=D) (3:Fin 9))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 1 3:ℤ):ℝ) ≤ H 3 3 := by exact_mod_cast seed_bound_3
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_4_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_4_1 : (2:Fin 9) ∈ D.next 1 0 := by decide +kernel
lemma seed_edge_4_2 : (4:Fin 9) ∈ D.next 2 0 := by decide +kernel
lemma seed_relation_4 : R 0 4 4 := by decide +kernel
lemma seed_ends_4 : ∀ t ∈ ends 4, t=(4:Fin 9) := by decide +kernel
lemma seed_bound_4 : (W 0 1 1 + W 1 0 2 + W 2 0 4:ℤ) ≤ H 4 4 := by decide +kernel
lemma seed_runs_4 : ∀ t ∈ ends 4, ∃ v,
    Run D D.start (Nat.digits 2 4).reverse t v ∧ v ≤ (H 4 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_4 t ht
  refine ⟨((W 0 1 1 + W 1 0 2 + W 2 0 4:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 4).reverse = [1,0,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_4_0 (Run.cons seed_edge_4_1 (Run.cons seed_edge_4_2 (Run.nil (D:=D) (4:Fin 9)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2 + W 2 0 4:ℤ):ℝ) ≤ H 4 4 := by exact_mod_cast seed_bound_4
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_5_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_5_1 : (2:Fin 9) ∈ D.next 1 0 := by decide +kernel
lemma seed_edge_5_2 : (5:Fin 9) ∈ D.next 2 1 := by decide +kernel
lemma seed_relation_5 : R 0 5 5 := by decide +kernel
lemma seed_ends_5 : ∀ t ∈ ends 5, t=(5:Fin 9) := by decide +kernel
lemma seed_bound_5 : (W 0 1 1 + W 1 0 2 + W 2 1 5:ℤ) ≤ H 5 5 := by decide +kernel
lemma seed_runs_5 : ∀ t ∈ ends 5, ∃ v,
    Run D D.start (Nat.digits 2 5).reverse t v ∧ v ≤ (H 5 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_5 t ht
  refine ⟨((W 0 1 1 + W 1 0 2 + W 2 1 5:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 5).reverse = [1,0,1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_5_0 (Run.cons seed_edge_5_1 (Run.cons seed_edge_5_2 (Run.nil (D:=D) (5:Fin 9)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2 + W 2 1 5:ℤ):ℝ) ≤ H 5 5 := by exact_mod_cast seed_bound_5
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_6_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_6_1 : (3:Fin 9) ∈ D.next 1 1 := by decide +kernel
lemma seed_edge_6_2 : (6:Fin 9) ∈ D.next 3 0 := by decide +kernel
lemma seed_relation_6 : R 0 6 6 := by decide +kernel
lemma seed_ends_6 : ∀ t ∈ ends 6, t=(6:Fin 9) := by decide +kernel
lemma seed_bound_6 : (W 0 1 1 + W 1 1 3 + W 3 0 6:ℤ) ≤ H 6 6 := by decide +kernel
lemma seed_runs_6 : ∀ t ∈ ends 6, ∃ v,
    Run D D.start (Nat.digits 2 6).reverse t v ∧ v ≤ (H 6 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_6 t ht
  refine ⟨((W 0 1 1 + W 1 1 3 + W 3 0 6:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 6).reverse = [1,1,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_6_0 (Run.cons seed_edge_6_1 (Run.cons seed_edge_6_2 (Run.nil (D:=D) (6:Fin 9)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 1 3 + W 3 0 6:ℤ):ℝ) ≤ H 6 6 := by exact_mod_cast seed_bound_6
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_7_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_7_1 : (3:Fin 9) ∈ D.next 1 1 := by decide +kernel
lemma seed_edge_7_2 : (6:Fin 9) ∈ D.next 3 1 := by decide +kernel
lemma seed_relation_7 : R 0 7 7 := by decide +kernel
lemma seed_ends_7 : ∀ t ∈ ends 7, t=(6:Fin 9) := by decide +kernel
lemma seed_bound_7 : (W 0 1 1 + W 1 1 3 + W 3 1 6:ℤ) ≤ H 7 6 := by decide +kernel
lemma seed_runs_7 : ∀ t ∈ ends 7, ∃ v,
    Run D D.start (Nat.digits 2 7).reverse t v ∧ v ≤ (H 7 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_7 t ht
  refine ⟨((W 0 1 1 + W 1 1 3 + W 3 1 6:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 7).reverse = [1,1,1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_7_0 (Run.cons seed_edge_7_1 (Run.cons seed_edge_7_2 (Run.nil (D:=D) (6:Fin 9)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 1 3 + W 3 1 6:ℤ):ℝ) ≤ H 7 6 := by exact_mod_cast seed_bound_7
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_edge_8_0 : (1:Fin 9) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_8_1 : (2:Fin 9) ∈ D.next 1 0 := by decide +kernel
lemma seed_edge_8_2 : (4:Fin 9) ∈ D.next 2 0 := by decide +kernel
lemma seed_edge_8_3 : (6:Fin 9) ∈ D.next 4 0 := by decide +kernel
lemma seed_relation_8 : R 0 8 8 := by decide +kernel
lemma seed_ends_8 : ∀ t ∈ ends 8, t=(6:Fin 9) := by decide +kernel
lemma seed_bound_8 : (W 0 1 1 + W 1 0 2 + W 2 0 4 + W 4 0 6:ℤ) ≤ H 8 6 := by decide +kernel
lemma seed_runs_8 : ∀ t ∈ ends 8, ∃ v,
    Run D D.start (Nat.digits 2 8).reverse t v ∧ v ≤ (H 8 t:ℝ)/8 := by
  intro t ht
  obtain rfl := seed_ends_8 t ht
  refine ⟨((W 0 1 1 + W 1 0 2 + W 2 0 4 + W 4 0 6:ℤ):ℝ)/8,?_,?_⟩
  · have he : (Nat.digits 2 8).reverse = [1,0,0,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_8_0 (Run.cons seed_edge_8_1 (Run.cons seed_edge_8_2 (Run.cons seed_edge_8_3 (Run.nil (D:=D) (6:Fin 9))))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2 + W 2 0 4 + W 4 0 6:ℤ):ℝ) ≤ H 8 6 := by exact_mod_cast seed_bound_8
    exact div_le_div_of_nonneg_right hh (by norm_num)

def StepRow (p : Fin 106) : Prop := ∀ (d e : Fin 2) (cp : Fin 9),
    9*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp

def stepCheck (p : Fin 106) : Bool :=
  ([0,1] : List ℕ).all fun d => ([0,1] : List ℕ).all fun e =>
    let cp := 2*carry p+e-9*d
    if 9*d ≤ 2*carry p+e ∧ cp < 9 then
      (nextList (source p) d).all fun sp =>
        decide (R sp (target p d cp sp) cp) &&
          (endsList (target p d cp sp)).all fun tp =>
            decide (parent p d cp sp tp ∈ ends p ∧
              tp ∈ D.next (parent p d cp sp tp) e ∧
              H p (parent p d cp sp tp)+W (parent p d cp sp tp) e tp-
                W (source p) d sp ≤ H (target p d cp sp) tp)
    else true

lemma step_check_all : ∀ p : Fin 106, stepCheck p = true := by decide +kernel

lemma step_checks : ∀ (p : Fin 106) (d e : Fin 2) (cp : Fin 9),
    9*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp := by
  intro p d e cp har sp hsp
  have hd : d.val ∈ ([0,1] : List ℕ) := by
    have := d.isLt
    simp only [List.mem_cons, List.mem_singleton]
    omega
  have he : e.val ∈ ([0,1] : List ℕ) := by
    have := e.isLt
    simp only [List.mem_cons, List.mem_singleton]
    omega
  have ha : 9*d.val ≤ 2*carry p+e.val := by omega
  have hc : 2*carry p+e.val-9*d.val = cp.val := by omega
  have hb : 2*carry p+e.val-9*d.val < 9 := by rw [hc]; exact cp.isLt
  have hh := step_check_all p
  unfold stepCheck at hh
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hh d.val hd) e.val he
  dsimp only at hh
  rw [if_pos ⟨ha,hb⟩, hc] at hh
  have hs : sp ∈ nextList (source p) d.val := by
    exact List.mem_toFinset.mp hsp
  have hz := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh sp hs)
  refine ⟨of_decide_eq_true hz.1, ?_⟩
  intro tp htp
  exact of_decide_eq_true (List.all_eq_true.mp hz.2 tp (List.mem_toFinset.mp htp))

lemma finish_checks : ∀ p : Fin 106, carry p ∈ ([0,1,3,4] : List ℕ) → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 16 := by decide +kernel

def construction : Erdos406BinaryGroupedProfile.Construction 2 D F (Fin 106) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/8
  seed := by
    intro c hc
    interval_cases c
    · exact ⟨0,seed_relation_0,seed_runs_0⟩
    · exact ⟨1,seed_relation_1,seed_runs_1⟩
    · exact ⟨2,seed_relation_2,seed_runs_2⟩
    · exact ⟨3,seed_relation_3,seed_runs_3⟩
    · exact ⟨4,seed_relation_4,seed_runs_4⟩
    · exact ⟨5,seed_relation_5,seed_runs_5⟩
    · exact ⟨6,seed_relation_6,seed_runs_6⟩
    · exact ⟨7,seed_relation_7,seed_runs_7⟩
    · exact ⟨8,seed_relation_8,seed_runs_8⟩
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
    obtain ⟨ht,hf',hh⟩ := finish_checks p ((Erdos406GroupedCertificate.goodBlock_two_iff (carry p)).mp hc) hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 16 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/8 ≤ 2
    linarith

def G (s : Fin 9) : Prop := s.val ∈ [1,2,4,6]
def Z (s : Fin 9) : Prop := s.val ∉ []
instance (s : Fin 9) : Decidable (G s) := by unfold G; infer_instance
instance (s : Fin 9) : Decidable (Z s) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, G t) ∧
    (∀ t, F t → Z t) ∧
    (∀ s, ∀ t ∈ D.next s 0, Z t → Z s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, Z t → 5+J t-J s ≤ W s 0 t) ∧
    (∀ s ∈ D.next D.start 1, ∀ t, G t → F t → Z s → -8 ≤ W D.start 1 s+J t-J s) := by decide +kernel

def powerBound : PowerBound D F where
  a := 5/8
  B := 1
  G := G
  Z := Z
  J s := (J s:ℝ)/8
  start := power_checks.1
  forward := by intro s t hs ht; exact power_checks.2.1 s hs t ht
  accepting := power_checks.2.2.1
  backward := by intro s t ht he; exact power_checks.2.2.2.1 s t he ht
  lower_step := by
    intro s t hs hz he
    have hh : (5:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s hs t he hz
    change (5/8:ℝ)+(J t:ℝ)/8-(J s:ℝ)/8 ≤ (W s 0 t:ℝ)/8
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-8:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2.2.2 s hs t ht hf hz
    change -(1:ℝ) ≤ (W D.start 1 s:ℝ)/8+(J t:ℝ)/8-(J s:ℝ)/8
    linarith

lemma start_accepts : F D.start := by decide +kernel
lemma good_run_bound (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t ∧
      v ≤ (2:ℝ)*(Nat.digits 9 n).length :=
  Erdos406BinaryGroupedProfile.Construction.exists_good_run construction (by decide) start_accepts n hg
lemma accepted_power_lower (k : ℕ) {t v}
    (hr : Run D D.start (Nat.digits 2 (2^k)).reverse t v) (hF : F t) :
    (5/8:ℝ)*k-1 ≤ v := by
  have hword : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  exact powerBound.power_run_lower k (hword ▸ hr) hF

lemma not_supercritical : ¬ Real.log 2 < (5/8:ℝ)*Real.log 3 := by
  have hn : (3:ℕ)^5 ≤ 2^8 := by decide +kernel
  have hh : (3:ℝ)^5 ≤ (2:ℝ)^8 := by exact_mod_cast hn
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^5) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos406BinaryGroupedBooleanPairControl
