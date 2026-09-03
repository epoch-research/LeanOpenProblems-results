import Submission.BinaryGroupedProfileCertificates

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryGroupedFreePairControl
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
lemma step_row_0 : StepRow 0 := by
  intro d e cp har sp hsp
  have hc : carry 0 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 0) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 0 0 0 0) at htp
      have hn : ends (target 0 0 0 0) = {0} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 0) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 0 0 1 0) at htp
      have hn : ends (target 0 0 1 0) = {1} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_1 : StepRow 1 := by
  intro d e cp har sp hsp
  have hc : carry 1 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 1) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 1 0 2 0) at htp
      have hn : ends (target 1 0 2 0) = {2} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 1) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 1 0 3 0) at htp
      have hn : ends (target 1 0 3 0) = {3} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_2 : StepRow 2 := by
  intro d e cp har sp hsp
  have hc : carry 2 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 2) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 2 0 4 0) at htp
      have hn : ends (target 2 0 4 0) = {4} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 2) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 2 0 5 0) at htp
      have hn : ends (target 2 0 5 0) = {5} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_3 : StepRow 3 := by
  intro d e cp har sp hsp
  have hc : carry 3 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 3) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 3 0 6 0) at htp
      have hn : ends (target 3 0 6 0) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 3) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 3 0 7 0) at htp
      have hn : ends (target 3 0 7 0) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_4 : StepRow 4 := by
  intro d e cp har sp hsp
  have hc : carry 4 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 4) 0 = {0} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 4 0 8 0) at htp
      have hn : ends (target 4 0 8 0) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 4) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 4 1 0 1) at htp
      have hn : ends (target 4 1 0 1) = {7} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
lemma step_row_5 : StepRow 5 := by
  intro d e cp har sp hsp
  have hc : carry 5 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 5) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 5 1 1 1) at htp
      have hn : ends (target 5 1 1 1) = {3} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 5) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 5 1 2 1) at htp
      have hn : ends (target 5 1 2 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_6 : StepRow 6 := by
  intro d e cp har sp hsp
  have hc : carry 6 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 6) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 6 1 3 1) at htp
      have hn : ends (target 6 1 3 1) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 6) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 6 1 4 1) at htp
      have hn : ends (target 6 1 4 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_7 : StepRow 7 := by
  intro d e cp har sp hsp
  have hc : carry 7 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 7) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 7 1 5 1) at htp
      have hn : ends (target 7 1 5 1) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 7) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 7 1 6 1) at htp
      have hn : ends (target 7 1 6 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_8 : StepRow 8 := by
  intro d e cp har sp hsp
  have hc : carry 8 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 8) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 8 1 7 1) at htp
      have hn : ends (target 8 1 7 1) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 8) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 8 1 8 1) at htp
      have hn : ends (target 8 1 8 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_9 : StepRow 9 := by
  intro d e cp har sp hsp
  have hc : carry 9 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 9) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 9 1 3 1) at htp
      have hn : ends (target 9 1 3 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 9) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 9 1 4 1) at htp
      have hn : ends (target 9 1 4 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_10 : StepRow 10 := by
  intro d e cp har sp hsp
  have hc : carry 10 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 10) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 10 1 5 1) at htp
      have hn : ends (target 10 1 5 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 10) 1 = {1} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 10 1 6 1) at htp
      have hn : ends (target 10 1 6 1) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_11 : StepRow 11 := by
  intro d e cp har sp hsp
  have hc : carry 11 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 11) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 11 0 0 2) at htp
      have hn : ends (target 11 0 0 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 11) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 11 0 1 2) at htp
      have hn : ends (target 11 0 1 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_12 : StepRow 12 := by
  intro d e cp har sp hsp
  have hc : carry 12 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 12) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 12 0 2 2) at htp
      have hn : ends (target 12 0 2 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 12) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 12 0 3 2) at htp
      have hn : ends (target 12 0 3 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_13 : StepRow 13 := by
  intro d e cp har sp hsp
  have hc : carry 13 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 13) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 13 0 4 2) at htp
      have hn : ends (target 13 0 4 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 13) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 13 0 5 2) at htp
      have hn : ends (target 13 0 5 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_14 : StepRow 14 := by
  intro d e cp har sp hsp
  have hc : carry 14 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 14) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 14 0 6 2) at htp
      have hn : ends (target 14 0 6 2) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 14) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 14 0 7 2) at htp
      have hn : ends (target 14 0 7 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_15 : StepRow 15 := by
  intro d e cp har sp hsp
  have hc : carry 15 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 15) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 15 0 8 2) at htp
      have hn : ends (target 15 0 8 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 15) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 15 1 0 3) at htp
      have hn : ends (target 15 1 0 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_16 : StepRow 16 := by
  intro d e cp har sp hsp
  have hc : carry 16 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 16) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 16 0 6 2) at htp
      have hn : ends (target 16 0 6 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 16) 0 = {2} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 16 0 7 2) at htp
      have hn : ends (target 16 0 7 2) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_17 : StepRow 17 := by
  intro d e cp har sp hsp
  have hc : carry 17 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 17) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 17 1 1 3) at htp
      have hn : ends (target 17 1 1 3) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 17) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 17 1 2 3) at htp
      have hn : ends (target 17 1 2 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_18 : StepRow 18 := by
  intro d e cp har sp hsp
  have hc : carry 18 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 18) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 18 1 3 3) at htp
      have hn : ends (target 18 1 3 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 18) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 18 1 4 3) at htp
      have hn : ends (target 18 1 4 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_19 : StepRow 19 := by
  intro d e cp har sp hsp
  have hc : carry 19 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 19) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 19 1 1 3) at htp
      have hn : ends (target 19 1 1 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 19) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 19 1 2 3) at htp
      have hn : ends (target 19 1 2 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_20 : StepRow 20 := by
  intro d e cp har sp hsp
  have hc : carry 20 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 20) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 20 1 5 3) at htp
      have hn : ends (target 20 1 5 3) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 20) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 20 1 6 3) at htp
      have hn : ends (target 20 1 6 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_21 : StepRow 21 := by
  intro d e cp har sp hsp
  have hc : carry 21 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 21) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 21 1 7 3) at htp
      have hn : ends (target 21 1 7 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 21) 1 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 21 1 8 3) at htp
      have hn : ends (target 21 1 8 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_22 : StepRow 22 := by
  intro d e cp har sp hsp
  have hc : carry 22 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 22) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 22 0 0 4) at htp
      have hn : ends (target 22 0 0 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 22) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 22 0 1 4) at htp
      have hn : ends (target 22 0 1 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_23 : StepRow 23 := by
  intro d e cp har sp hsp
  have hc : carry 23 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 23) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 23 0 2 4) at htp
      have hn : ends (target 23 0 2 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 23) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 23 0 3 4) at htp
      have hn : ends (target 23 0 3 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_24 : StepRow 24 := by
  intro d e cp har sp hsp
  have hc : carry 24 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 24) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 24 0 4 4) at htp
      have hn : ends (target 24 0 4 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 24) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 24 0 5 4) at htp
      have hn : ends (target 24 0 5 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_25 : StepRow 25 := by
  intro d e cp har sp hsp
  have hc : carry 25 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 25) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 25 0 6 4) at htp
      have hn : ends (target 25 0 6 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 25) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 25 0 7 4) at htp
      have hn : ends (target 25 0 7 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_26 : StepRow 26 := by
  intro d e cp har sp hsp
  have hc : carry 26 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 26) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 26 1 1 5) at htp
      have hn : ends (target 26 1 1 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 26) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 26 1 2 5) at htp
      have hn : ends (target 26 1 2 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_27 : StepRow 27 := by
  intro d e cp har sp hsp
  have hc : carry 27 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 27) 0 = {4} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 27 0 8 4) at htp
      have hn : ends (target 27 0 8 4) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 27) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 27 1 0 5) at htp
      have hn : ends (target 27 1 0 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_28 : StepRow 28 := by
  intro d e cp har sp hsp
  have hc : carry 28 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 28) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 28 1 3 5) at htp
      have hn : ends (target 28 1 3 5) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 28) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 28 1 4 5) at htp
      have hn : ends (target 28 1 4 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_29 : StepRow 29 := by
  intro d e cp har sp hsp
  have hc : carry 29 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 29) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 29 1 5 5) at htp
      have hn : ends (target 29 1 5 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 29) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 29 1 6 5) at htp
      have hn : ends (target 29 1 6 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_30 : StepRow 30 := by
  intro d e cp har sp hsp
  have hc : carry 30 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 30) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 30 0 0 6) at htp
        have hn : ends (target 30 0 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 30 0 0 8) at htp
        have hn : ends (target 30 0 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 30) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 30 0 1 6) at htp
        have hn : ends (target 30 0 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 30 0 1 8) at htp
        have hn : ends (target 30 0 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_31 : StepRow 31 := by
  intro d e cp har sp hsp
  have hc : carry 31 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 31) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 31 1 7 5) at htp
      have hn : ends (target 31 1 7 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 31) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 31 1 8 5) at htp
      have hn : ends (target 31 1 8 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_32 : StepRow 32 := by
  intro d e cp har sp hsp
  have hc : carry 32 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 32) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 32 1 3 5) at htp
      have hn : ends (target 32 1 3 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 32) 1 = {5} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 32 1 4 5) at htp
      have hn : ends (target 32 1 4 5) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_33 : StepRow 33 := by
  intro d e cp har sp hsp
  have hc : carry 33 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 33) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 33 0 2 6) at htp
        have hn : ends (target 33 0 2 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 33 0 2 8) at htp
        have hn : ends (target 33 0 2 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 33) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 33 0 3 6) at htp
        have hn : ends (target 33 0 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 33 0 3 8) at htp
        have hn : ends (target 33 0 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_34 : StepRow 34 := by
  intro d e cp har sp hsp
  have hc : carry 34 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 34) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 34 0 4 6) at htp
        have hn : ends (target 34 0 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 34 0 4 8) at htp
        have hn : ends (target 34 0 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 34) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 34 0 5 6) at htp
        have hn : ends (target 34 0 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 34 0 5 8) at htp
        have hn : ends (target 34 0 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_35 : StepRow 35 := by
  intro d e cp har sp hsp
  have hc : carry 35 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 35) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 35 0 8 6) at htp
        have hn : ends (target 35 0 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 35 0 8 8) at htp
        have hn : ends (target 35 0 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 35) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 35 1 0 6) at htp
        have hn : ends (target 35 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 35 1 0 8) at htp
        have hn : ends (target 35 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_36 : StepRow 36 := by
  intro d e cp har sp hsp
  have hc : carry 36 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 36) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 36 0 6 6) at htp
        have hn : ends (target 36 0 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 36 0 6 8) at htp
        have hn : ends (target 36 0 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 36) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 36 0 7 6) at htp
        have hn : ends (target 36 0 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 36 0 7 8) at htp
        have hn : ends (target 36 0 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_37 : StepRow 37 := by
  intro d e cp har sp hsp
  have hc : carry 37 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 37) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 37 0 2 6) at htp
        have hn : ends (target 37 0 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 37 0 2 8) at htp
        have hn : ends (target 37 0 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 37) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 37 0 3 6) at htp
        have hn : ends (target 37 0 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 37 0 3 8) at htp
        have hn : ends (target 37 0 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_38 : StepRow 38 := by
  intro d e cp har sp hsp
  have hc : carry 38 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 38) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 38 1 1 6) at htp
        have hn : ends (target 38 1 1 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 38 1 1 8) at htp
        have hn : ends (target 38 1 1 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 38) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 38 1 2 6) at htp
        have hn : ends (target 38 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 38 1 2 8) at htp
        have hn : ends (target 38 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_39 : StepRow 39 := by
  intro d e cp har sp hsp
  have hc : carry 39 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 39) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 39 1 3 6) at htp
        have hn : ends (target 39 1 3 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 39 1 3 8) at htp
        have hn : ends (target 39 1 3 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 39) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 39 1 4 6) at htp
        have hn : ends (target 39 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 39 1 4 8) at htp
        have hn : ends (target 39 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_40 : StepRow 40 := by
  intro d e cp har sp hsp
  have hc : carry 40 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 40) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 40 1 3 6) at htp
        have hn : ends (target 40 1 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 40 1 3 8) at htp
        have hn : ends (target 40 1 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 40) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 40 1 4 6) at htp
        have hn : ends (target 40 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 40 1 4 8) at htp
        have hn : ends (target 40 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_41 : StepRow 41 := by
  intro d e cp har sp hsp
  have hc : carry 41 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 41) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 41 1 7 6) at htp
        have hn : ends (target 41 1 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 41 1 7 8) at htp
        have hn : ends (target 41 1 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 41) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 41 1 8 6) at htp
        have hn : ends (target 41 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 41 1 8 8) at htp
        have hn : ends (target 41 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_42 : StepRow 42 := by
  intro d e cp har sp hsp
  have hc : carry 42 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 42) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 42 1 5 6) at htp
        have hn : ends (target 42 1 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 42 1 5 8) at htp
        have hn : ends (target 42 1 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 42) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 42 1 6 6) at htp
        have hn : ends (target 42 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 42 1 6 8) at htp
        have hn : ends (target 42 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_43 : StepRow 43 := by
  intro d e cp har sp hsp
  have hc : carry 43 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 43) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 43 0 2 6) at htp
      have hn : ends (target 43 0 2 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 43) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 43 0 3 6) at htp
      have hn : ends (target 43 0 3 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_44 : StepRow 44 := by
  intro d e cp har sp hsp
  have hc : carry 44 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 44) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 44 0 0 6) at htp
      have hn : ends (target 44 0 0 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 44) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 44 0 1 6) at htp
      have hn : ends (target 44 0 1 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_45 : StepRow 45 := by
  intro d e cp har sp hsp
  have hc : carry 45 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 45) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 45 0 6 6) at htp
      have hn : ends (target 45 0 6 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 45) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 45 0 7 6) at htp
      have hn : ends (target 45 0 7 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_46 : StepRow 46 := by
  intro d e cp har sp hsp
  have hc : carry 46 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 46) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 46 0 4 6) at htp
      have hn : ends (target 46 0 4 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 46) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 46 0 5 6) at htp
      have hn : ends (target 46 0 5 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_47 : StepRow 47 := by
  intro d e cp har sp hsp
  have hc : carry 47 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 47) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 47 1 1 7) at htp
      have hn : ends (target 47 1 1 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 47) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 47 1 2 7) at htp
      have hn : ends (target 47 1 2 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_48 : StepRow 48 := by
  intro d e cp har sp hsp
  have hc : carry 48 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 48) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 48 0 8 6) at htp
      have hn : ends (target 48 0 8 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 48) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 48 1 0 7) at htp
      have hn : ends (target 48 1 0 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_49 : StepRow 49 := by
  intro d e cp har sp hsp
  have hc : carry 49 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 49) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 49 1 5 7) at htp
      have hn : ends (target 49 1 5 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 49) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 49 1 6 7) at htp
      have hn : ends (target 49 1 6 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_50 : StepRow 50 := by
  intro d e cp har sp hsp
  have hc : carry 50 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 50) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 50 1 3 7) at htp
      have hn : ends (target 50 1 3 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 50) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 50 1 4 7) at htp
      have hn : ends (target 50 1 4 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_51 : StepRow 51 := by
  intro d e cp har sp hsp
  have hc : carry 51 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 51) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 51 0 0 3) at htp
      have hn : ends (target 51 0 0 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 51) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 51 0 1 3) at htp
      have hn : ends (target 51 0 1 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_52 : StepRow 52 := by
  intro d e cp har sp hsp
  have hc : carry 52 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 52) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 52 0 4 3) at htp
      have hn : ends (target 52 0 4 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 52) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 52 0 5 3) at htp
      have hn : ends (target 52 0 5 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_53 : StepRow 53 := by
  intro d e cp har sp hsp
  have hc : carry 53 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 53) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 53 0 2 3) at htp
      have hn : ends (target 53 0 2 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 53) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 53 0 3 3) at htp
      have hn : ends (target 53 0 3 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_54 : StepRow 54 := by
  intro d e cp har sp hsp
  have hc : carry 54 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 54) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 54 1 7 7) at htp
      have hn : ends (target 54 1 7 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 54) 1 = {7} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 54 1 8 7) at htp
      have hn : ends (target 54 1 8 7) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_55 : StepRow 55 := by
  intro d e cp har sp hsp
  have hc : carry 55 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 55) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 55 0 6 3) at htp
      have hn : ends (target 55 0 6 3) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 55) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 55 0 7 3) at htp
      have hn : ends (target 55 0 7 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_56 : StepRow 56 := by
  intro d e cp har sp hsp
  have hc : carry 56 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 56) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 56 0 8 3) at htp
      have hn : ends (target 56 0 8 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 56) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 56 1 0 6) at htp
        have hn : ends (target 56 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 56 1 0 8) at htp
        have hn : ends (target 56 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_57 : StepRow 57 := by
  intro d e cp har sp hsp
  have hc : carry 57 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 57) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 57 1 3 6) at htp
        have hn : ends (target 57 1 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 57 1 3 8) at htp
        have hn : ends (target 57 1 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 57) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 57 1 4 6) at htp
        have hn : ends (target 57 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 57 1 4 8) at htp
        have hn : ends (target 57 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_58 : StepRow 58 := by
  intro d e cp har sp hsp
  have hc : carry 58 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 58) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 58 1 1 6) at htp
        have hn : ends (target 58 1 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 58 1 1 8) at htp
        have hn : ends (target 58 1 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 58) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 58 1 2 6) at htp
        have hn : ends (target 58 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 58 1 2 8) at htp
        have hn : ends (target 58 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_59 : StepRow 59 := by
  intro d e cp har sp hsp
  have hc : carry 59 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 59) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 59 1 7 6) at htp
        have hn : ends (target 59 1 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 59 1 7 8) at htp
        have hn : ends (target 59 1 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 59) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 59 1 8 6) at htp
        have hn : ends (target 59 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 59 1 8 8) at htp
        have hn : ends (target 59 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_60 : StepRow 60 := by
  intro d e cp har sp hsp
  have hc : carry 60 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 60) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 60 0 2 6) at htp
      have hn : ends (target 60 0 2 6) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 60) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 60 0 3 6) at htp
      have hn : ends (target 60 0 3 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_61 : StepRow 61 := by
  intro d e cp har sp hsp
  have hc : carry 61 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 61) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 61 0 2 6) at htp
      have hn : ends (target 61 0 2 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 61) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 61 0 3 6) at htp
      have hn : ends (target 61 0 3 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_62 : StepRow 62 := by
  intro d e cp har sp hsp
  have hc : carry 62 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 62) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 62 0 2 6) at htp
        have hn : ends (target 62 0 2 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 62 0 2 8) at htp
        have hn : ends (target 62 0 2 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 62) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 62 0 3 6) at htp
        have hn : ends (target 62 0 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 62 0 3 8) at htp
        have hn : ends (target 62 0 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_63 : StepRow 63 := by
  intro d e cp har sp hsp
  have hc : carry 63 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 63) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 63 0 2 6) at htp
        have hn : ends (target 63 0 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 63 0 2 8) at htp
        have hn : ends (target 63 0 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 63) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 63 0 3 6) at htp
        have hn : ends (target 63 0 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 63 0 3 8) at htp
        have hn : ends (target 63 0 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_64 : StepRow 64 := by
  intro d e cp har sp hsp
  have hc : carry 64 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 64) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 64 0 0 6) at htp
      have hn : ends (target 64 0 0 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 64) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 64 0 1 6) at htp
      have hn : ends (target 64 0 1 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_65 : StepRow 65 := by
  intro d e cp har sp hsp
  have hc : carry 65 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 65) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 65 0 0 6) at htp
        have hn : ends (target 65 0 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 65 0 0 8) at htp
        have hn : ends (target 65 0 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 65) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 65 0 1 6) at htp
        have hn : ends (target 65 0 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 65 0 1 8) at htp
        have hn : ends (target 65 0 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_66 : StepRow 66 := by
  intro d e cp har sp hsp
  have hc : carry 66 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 66) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 66 1 5 6) at htp
        have hn : ends (target 66 1 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 66 1 5 8) at htp
        have hn : ends (target 66 1 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 66) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 66 1 6 6) at htp
        have hn : ends (target 66 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 66 1 6 8) at htp
        have hn : ends (target 66 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_67 : StepRow 67 := by
  intro d e cp har sp hsp
  have hc : carry 67 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 67) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 67 0 6 3) at htp
      have hn : ends (target 67 0 6 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 67) 0 = {3} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 67 0 7 3) at htp
      have hn : ends (target 67 0 7 3) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_68 : StepRow 68 := by
  intro d e cp har sp hsp
  have hc : carry 68 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 68) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 68 0 4 6) at htp
      have hn : ends (target 68 0 4 6) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 68) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 68 0 5 6) at htp
      have hn : ends (target 68 0 5 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_69 : StepRow 69 := by
  intro d e cp har sp hsp
  have hc : carry 69 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 69) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 69 0 4 6) at htp
        have hn : ends (target 69 0 4 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 69 0 4 8) at htp
        have hn : ends (target 69 0 4 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 69) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 69 0 5 6) at htp
        have hn : ends (target 69 0 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 69 0 5 8) at htp
        have hn : ends (target 69 0 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_70 : StepRow 70 := by
  intro d e cp har sp hsp
  have hc : carry 70 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 70) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 70 0 6 6) at htp
      have hn : ends (target 70 0 6 6) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 70) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 70 0 7 6) at htp
      have hn : ends (target 70 0 7 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_71 : StepRow 71 := by
  intro d e cp har sp hsp
  have hc : carry 71 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 71) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 71 0 6 6) at htp
      have hn : ends (target 71 0 6 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 71) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 71 0 7 6) at htp
      have hn : ends (target 71 0 7 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_72 : StepRow 72 := by
  intro d e cp har sp hsp
  have hc : carry 72 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 72) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 72 0 6 6) at htp
        have hn : ends (target 72 0 6 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 72 0 6 8) at htp
        have hn : ends (target 72 0 6 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 72) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 72 0 7 6) at htp
        have hn : ends (target 72 0 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 72 0 7 8) at htp
        have hn : ends (target 72 0 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_73 : StepRow 73 := by
  intro d e cp har sp hsp
  have hc : carry 73 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 73) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 73 0 6 6) at htp
        have hn : ends (target 73 0 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 73 0 6 8) at htp
        have hn : ends (target 73 0 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 73) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 73 0 7 6) at htp
        have hn : ends (target 73 0 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 73 0 7 8) at htp
        have hn : ends (target 73 0 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_74 : StepRow 74 := by
  intro d e cp har sp hsp
  have hc : carry 74 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 74) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 74 0 8 6) at htp
      have hn : ends (target 74 0 8 6) = {6} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      subst tp
      decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 74) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 74 1 0 6) at htp
        have hn : ends (target 74 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 74 1 0 8) at htp
        have hn : ends (target 74 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_75 : StepRow 75 := by
  intro d e cp har sp hsp
  have hc : carry 75 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 75) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 75 0 8 6) at htp
        have hn : ends (target 75 0 8 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 75 0 8 8) at htp
        have hn : ends (target 75 0 8 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 75) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 75 1 0 6) at htp
        have hn : ends (target 75 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 75 1 0 8) at htp
        have hn : ends (target 75 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_76 : StepRow 76 := by
  intro d e cp har sp hsp
  have hc : carry 76 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 76) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 76 1 1 6) at htp
        have hn : ends (target 76 1 1 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 76 1 1 8) at htp
        have hn : ends (target 76 1 1 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 76) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 76 1 2 6) at htp
        have hn : ends (target 76 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 76 1 2 8) at htp
        have hn : ends (target 76 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_77 : StepRow 77 := by
  intro d e cp har sp hsp
  have hc : carry 77 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 77) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 77 1 1 6) at htp
        have hn : ends (target 77 1 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 77 1 1 8) at htp
        have hn : ends (target 77 1 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 77) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 77 1 2 6) at htp
        have hn : ends (target 77 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 77 1 2 8) at htp
        have hn : ends (target 77 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_78 : StepRow 78 := by
  intro d e cp har sp hsp
  have hc : carry 78 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 78) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 78 1 1 6) at htp
        have hn : ends (target 78 1 1 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 78 1 1 8) at htp
        have hn : ends (target 78 1 1 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 78) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 78 1 2 6) at htp
        have hn : ends (target 78 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 78 1 2 8) at htp
        have hn : ends (target 78 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_79 : StepRow 79 := by
  intro d e cp har sp hsp
  have hc : carry 79 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 79) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 79 1 1 6) at htp
        have hn : ends (target 79 1 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 79 1 1 8) at htp
        have hn : ends (target 79 1 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 79) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 79 1 2 6) at htp
        have hn : ends (target 79 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 79 1 2 8) at htp
        have hn : ends (target 79 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_80 : StepRow 80 := by
  intro d e cp har sp hsp
  have hc : carry 80 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 80) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 80 0 8 6) at htp
      have hn : ends (target 80 0 8 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 80) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 80 1 0 6) at htp
        have hn : ends (target 80 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 80 1 0 8) at htp
        have hn : ends (target 80 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_81 : StepRow 81 := by
  intro d e cp har sp hsp
  have hc : carry 81 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 81) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 81 0 8 6) at htp
        have hn : ends (target 81 0 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 81 0 8 8) at htp
        have hn : ends (target 81 0 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 81) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 81 1 0 6) at htp
        have hn : ends (target 81 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 81 1 0 8) at htp
        have hn : ends (target 81 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_82 : StepRow 82 := by
  intro d e cp har sp hsp
  have hc : carry 82 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 82) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 82 1 3 6) at htp
        have hn : ends (target 82 1 3 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 82 1 3 8) at htp
        have hn : ends (target 82 1 3 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 82) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 82 1 4 6) at htp
        have hn : ends (target 82 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 82 1 4 8) at htp
        have hn : ends (target 82 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_83 : StepRow 83 := by
  intro d e cp har sp hsp
  have hc : carry 83 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 83) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 83 1 3 6) at htp
        have hn : ends (target 83 1 3 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 83 1 3 8) at htp
        have hn : ends (target 83 1 3 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 83) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 83 1 4 6) at htp
        have hn : ends (target 83 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 83 1 4 8) at htp
        have hn : ends (target 83 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_84 : StepRow 84 := by
  intro d e cp har sp hsp
  have hc : carry 84 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 84) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 84 1 5 6) at htp
        have hn : ends (target 84 1 5 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 84 1 5 8) at htp
        have hn : ends (target 84 1 5 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 84) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 84 1 6 6) at htp
        have hn : ends (target 84 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 84 1 6 8) at htp
        have hn : ends (target 84 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_85 : StepRow 85 := by
  intro d e cp har sp hsp
  have hc : carry 85 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 85) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 85 1 5 6) at htp
        have hn : ends (target 85 1 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 85 1 5 8) at htp
        have hn : ends (target 85 1 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 85) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 85 1 6 6) at htp
        have hn : ends (target 85 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 85 1 6 8) at htp
        have hn : ends (target 85 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_86 : StepRow 86 := by
  intro d e cp har sp hsp
  have hc : carry 86 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 86) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 86 1 5 6) at htp
        have hn : ends (target 86 1 5 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 86 1 5 8) at htp
        have hn : ends (target 86 1 5 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 86) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 86 1 6 6) at htp
        have hn : ends (target 86 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 86 1 6 8) at htp
        have hn : ends (target 86 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_87 : StepRow 87 := by
  intro d e cp har sp hsp
  have hc : carry 87 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 87) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 87 1 5 6) at htp
        have hn : ends (target 87 1 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 87 1 5 8) at htp
        have hn : ends (target 87 1 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 87) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 87 1 6 6) at htp
        have hn : ends (target 87 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 87 1 6 8) at htp
        have hn : ends (target 87 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_88 : StepRow 88 := by
  intro d e cp har sp hsp
  have hc : carry 88 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 88) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 88 1 7 6) at htp
        have hn : ends (target 88 1 7 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 88 1 7 8) at htp
        have hn : ends (target 88 1 7 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 88) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 88 1 8 6) at htp
        have hn : ends (target 88 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 88 1 8 8) at htp
        have hn : ends (target 88 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_89 : StepRow 89 := by
  intro d e cp har sp hsp
  have hc : carry 89 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 89) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 89 1 7 6) at htp
        have hn : ends (target 89 1 7 6) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 89 1 7 8) at htp
        have hn : ends (target 89 1 7 8) = {6} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        subst tp
        decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 89) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 89 1 8 6) at htp
        have hn : ends (target 89 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 89 1 8 8) at htp
        have hn : ends (target 89 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_90 : StepRow 90 := by
  intro d e cp har sp hsp
  have hc : carry 90 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 90) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 90 1 7 6) at htp
        have hn : ends (target 90 1 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 90 1 7 8) at htp
        have hn : ends (target 90 1 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 90) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 90 1 8 6) at htp
        have hn : ends (target 90 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 90 1 8 8) at htp
        have hn : ends (target 90 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_91 : StepRow 91 := by
  intro d e cp har sp hsp
  have hc : carry 91 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 91) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 91 1 7 6) at htp
        have hn : ends (target 91 1 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 91 1 7 8) at htp
        have hn : ends (target 91 1 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 91) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 91 1 8 6) at htp
        have hn : ends (target 91 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 91 1 8 8) at htp
        have hn : ends (target 91 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_92 : StepRow 92 := by
  intro d e cp har sp hsp
  have hc : carry 92 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 92) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 92 1 3 6) at htp
        have hn : ends (target 92 1 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 92 1 3 8) at htp
        have hn : ends (target 92 1 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 92) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 92 1 4 6) at htp
        have hn : ends (target 92 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 92 1 4 8) at htp
        have hn : ends (target 92 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_93 : StepRow 93 := by
  intro d e cp har sp hsp
  have hc : carry 93 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 93) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 93 1 3 6) at htp
        have hn : ends (target 93 1 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 93 1 3 8) at htp
        have hn : ends (target 93 1 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 93) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 93 1 4 6) at htp
        have hn : ends (target 93 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 93 1 4 8) at htp
        have hn : ends (target 93 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_94 : StepRow 94 := by
  intro d e cp har sp hsp
  have hc : carry 94 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 94) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 94 0 4 6) at htp
      have hn : ends (target 94 0 4 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 94) 0 = {6} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    subst sp
    refine ⟨?_,?_⟩
    · unfold R; decide +kernel
    · intro tp htp
      change tp ∈ ends (target 94 0 5 6) at htp
      have hn : ends (target 94 0 5 6) = {6,8} := by decide +kernel
      rw [hn] at htp
      simp only [Finset.mem_insert,Finset.mem_singleton] at htp
      rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_95 : StepRow 95 := by
  intro d e cp har sp hsp
  have hc : carry 95 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 95) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 95 0 4 6) at htp
        have hn : ends (target 95 0 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 95 0 4 8) at htp
        have hn : ends (target 95 0 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 95) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 95 0 5 6) at htp
        have hn : ends (target 95 0 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 95 0 5 8) at htp
        have hn : ends (target 95 0 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_96 : StepRow 96 := by
  intro d e cp har sp hsp
  have hc : carry 96 = 0 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*0+0 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 96) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 96 0 0 6) at htp
        have hn : ends (target 96 0 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 96 0 0 8) at htp
        have hn : ends (target 96 0 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*0+1 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 96) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 96 0 1 6) at htp
        have hn : ends (target 96 0 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 96 0 1 8) at htp
        have hn : ends (target 96 0 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*0+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*0+1 at har
    have hb := cp.isLt
    omega
lemma step_row_97 : StepRow 97 := by
  intro d e cp har sp hsp
  have hc : carry 97 = 2 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*2+0 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 97) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 97 0 4 6) at htp
        have hn : ends (target 97 0 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 97 0 4 8) at htp
        have hn : ends (target 97 0 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*2+1 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 97) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 97 0 5 6) at htp
        have hn : ends (target 97 0 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 97 0 5 8) at htp
        have hn : ends (target 97 0 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*2+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*2+1 at har
    have hb := cp.isLt
    omega
lemma step_row_98 : StepRow 98 := by
  intro d e cp har sp hsp
  have hc : carry 98 = 1 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*1+0 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 98) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 98 0 2 6) at htp
        have hn : ends (target 98 0 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 98 0 2 8) at htp
        have hn : ends (target 98 0 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*1+1 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 98) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 98 0 3 6) at htp
        have hn : ends (target 98 0 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 98 0 3 8) at htp
        have hn : ends (target 98 0 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*1+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*1+1 at har
    have hb := cp.isLt
    omega
lemma step_row_99 : StepRow 99 := by
  intro d e cp har sp hsp
  have hc : carry 99 = 4 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*4+0 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 99) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 99 0 8 6) at htp
        have hn : ends (target 99 0 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 99 0 8 8) at htp
        have hn : ends (target 99 0 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*4+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*4+1 at har
    have he : cp = (0:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 99) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 99 1 0 6) at htp
        have hn : ends (target 99 1 0 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 99 1 0 8) at htp
        have hn : ends (target 99 1 0 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_100 : StepRow 100 := by
  intro d e cp har sp hsp
  have hc : carry 100 = 6 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*6+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*6+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*6+0 at har
    have he : cp = (3:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 100) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 100 1 3 6) at htp
        have hn : ends (target 100 1 3 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 100 1 3 8) at htp
        have hn : ends (target 100 1 3 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*6+1 at har
    have he : cp = (4:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 100) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 100 1 4 6) at htp
        have hn : ends (target 100 1 4 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 100 1 4 8) at htp
        have hn : ends (target 100 1 4 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_101 : StepRow 101 := by
  intro d e cp har sp hsp
  have hc : carry 101 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 101) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 101 1 1 6) at htp
        have hn : ends (target 101 1 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 101 1 1 8) at htp
        have hn : ends (target 101 1 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 101) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 101 1 2 6) at htp
        have hn : ends (target 101 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 101 1 2 8) at htp
        have hn : ends (target 101 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_102 : StepRow 102 := by
  intro d e cp har sp hsp
  have hc : carry 102 = 3 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*3+0 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 102) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 102 0 6 6) at htp
        have hn : ends (target 102 0 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 102 0 6 8) at htp
        have hn : ends (target 102 0 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*0+cp.val = 2*3+1 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 102) 0 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 102 0 7 6) at htp
        have hn : ends (target 102 0 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 102 0 7 8) at htp
        have hn : ends (target 102 0 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*3+0 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*3+1 at har
    have hb := cp.isLt
    omega
lemma step_row_103 : StepRow 103 := by
  intro d e cp har sp hsp
  have hc : carry 103 = 8 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*8+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*8+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*8+0 at har
    have he : cp = (7:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 103) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 103 1 7 6) at htp
        have hn : ends (target 103 1 7 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 103 1 7 8) at htp
        have hn : ends (target 103 1 7 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*8+1 at har
    have he : cp = (8:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 103) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 103 1 8 6) at htp
        have hn : ends (target 103 1 8 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 103 1 8 8) at htp
        have hn : ends (target 103 1 8 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_104 : StepRow 104 := by
  intro d e cp har sp hsp
  have hc : carry 104 = 5 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*5+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*5+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*5+0 at har
    have he : cp = (1:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 104) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 104 1 1 6) at htp
        have hn : ends (target 104 1 1 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 104 1 1 8) at htp
        have hn : ends (target 104 1 1 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*5+1 at har
    have he : cp = (2:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 104) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 104 1 2 6) at htp
        have hn : ends (target 104 1 2 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 104 1 2 8) at htp
        have hn : ends (target 104 1 2 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
lemma step_row_105 : StepRow 105 := by
  intro d e cp har sp hsp
  have hc : carry 105 = 7 := by decide +kernel
  rw [hc] at har
  fin_cases d <;> fin_cases e
  · change 9*0+cp.val = 2*7+0 at har
    have hb := cp.isLt
    omega
  · change 9*0+cp.val = 2*7+1 at har
    have hb := cp.isLt
    omega
  · change 9*1+cp.val = 2*7+0 at har
    have he : cp = (5:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 105) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 105 1 5 6) at htp
        have hn : ends (target 105 1 5 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 105 1 5 8) at htp
        have hn : ends (target 105 1 5 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
  · change 9*1+cp.val = 2*7+1 at har
    have he : cp = (6:Fin 9) := by
      apply Fin.ext
      omega
    subst cp
    have hn : D.next (source 105) 1 = {6,8} := by decide +kernel
    rw [hn] at hsp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsp
    rcases hsp with rfl | rfl
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 105 1 6 6) at htp
        have hn : ends (target 105 1 6 6) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel
    · refine ⟨?_,?_⟩
      · unfold R; decide +kernel
      · intro tp htp
        change tp ∈ ends (target 105 1 6 8) at htp
        have hn : ends (target 105 1 6 8) = {6,8} := by decide +kernel
        rw [hn] at htp
        simp only [Finset.mem_insert,Finset.mem_singleton] at htp
        rcases htp with rfl | rfl <;> decide +kernel

lemma step_checks : ∀ p : Fin 106, StepRow p := by
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
  · exact step_row_54
  · exact step_row_55
  · exact step_row_56
  · exact step_row_57
  · exact step_row_58
  · exact step_row_59
  · exact step_row_60
  · exact step_row_61
  · exact step_row_62
  · exact step_row_63
  · exact step_row_64
  · exact step_row_65
  · exact step_row_66
  · exact step_row_67
  · exact step_row_68
  · exact step_row_69
  · exact step_row_70
  · exact step_row_71
  · exact step_row_72
  · exact step_row_73
  · exact step_row_74
  · exact step_row_75
  · exact step_row_76
  · exact step_row_77
  · exact step_row_78
  · exact step_row_79
  · exact step_row_80
  · exact step_row_81
  · exact step_row_82
  · exact step_row_83
  · exact step_row_84
  · exact step_row_85
  · exact step_row_86
  · exact step_row_87
  · exact step_row_88
  · exact step_row_89
  · exact step_row_90
  · exact step_row_91
  · exact step_row_92
  · exact step_row_93
  · exact step_row_94
  · exact step_row_95
  · exact step_row_96
  · exact step_row_97
  · exact step_row_98
  · exact step_row_99
  · exact step_row_100
  · exact step_row_101
  · exact step_row_102
  · exact step_row_103
  · exact step_row_104
  · exact step_row_105

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
end Erdos406BinaryGroupedFreePairControl
