import Submission.APModularTransfer
import Submission.PaleyObstruction

/-!
An unconditional finite obstruction to rational arithmetic-progression labels,
with arbitrary choices of midpoint. This is not a settlement of Erdos 595.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
open SimpleGraph Set
open scoped BigOperators Matrix
namespace Erdos595PaleyAPObstruction
open Erdos595Paley Erdos595ArithmeticProgression

def triEdges : Fin 68 → Fin 3 → Fin 68 := ![
  ![0,1,8],
  ![0,4,11],
  ![0,7,14],
  ![1,2,16],
  ![1,6,20],
  ![2,3,29],
  ![2,5,31],
  ![3,4,47],
  ![3,7,50],
  ![4,5,53],
  ![5,6,64],
  ![6,7,67],
  ![8,9,15],
  ![8,12,18],
  ![9,10,22],
  ![9,14,26],
  ![10,11,34],
  ![10,13,36],
  ![11,12,51],
  ![12,13,56],
  ![13,14,66],
  ![15,16,21],
  ![15,19,24],
  ![16,17,28],
  ![17,18,39],
  ![17,20,41],
  ![18,19,54],
  ![19,20,59],
  ![21,22,27],
  ![21,25,30],
  ![22,23,33],
  ![23,24,44],
  ![23,26,46],
  ![24,25,57],
  ![25,26,62],
  ![27,28,32],
  ![27,31,35],
  ![28,29,38],
  ![29,30,49],
  ![30,31,60],
  ![32,33,37],
  ![32,36,40],
  ![33,34,43],
  ![34,35,53],
  ![35,36,63],
  ![37,38,42],
  ![37,41,45],
  ![38,39,48],
  ![39,40,56],
  ![40,41,65],
  ![42,43,47],
  ![42,46,50],
  ![43,44,52],
  ![44,45,59],
  ![45,46,67],
  ![47,48,51],
  ![48,49,55],
  ![49,50,62],
  ![51,52,54],
  ![52,53,58],
  ![54,55,57],
  ![55,56,61],
  ![57,58,60],
  ![58,59,64],
  ![60,61,63],
  ![61,62,66],
  ![63,64,65],
  ![65,66,67]
]

def incidence : Matrix (Fin 67) (Fin 67) (ZMod 3) := fun i j =>
  ∑ k : Fin 3, if j.succ = triEdges i.castSucc k then 1 else 0

/-- Base-three row encoding keeps the exact kernel checks small. -/
def inverseRows : Fin 67 → ℕ := ![74280910912146073060674194530469,62594551752495930905361602289673,62592964414756443120286010007857,31317766086563838591020059063425,789774103447686582594976297158,85626609449749918989907256960451,44134602966003191465361517808949,54312144358897907756836248921023,75453739419061114810129439904885,62594551752824037732356748193476,62592963691046540969110368319071,11730518575259409435586213836481,61390222888043420136140472302465,84453742176343543108164779432001,2303265855226612203898886542936,85628140726156299478983605627598,62594551832554057890066062673309,62593313339766825436355152718928,32452907102600183608945108828664,62596083028902311394406569365824,44137743051798620502176583091874,84455312218913150833871329914300,62594571206912421829379853985431,62588260023321766405566067341036,21946787719586508928489262920048,62596121795393645526693814805826,328557202429268318440,74280910832088096170699045125548,62596139099095753498982071038615,62678618977364628324565439791770,31689866253642233884905707720633,54312144199328648693363049754778,75453719964936257922620292232530,62596137659882673616560312526734,62220863524624509538276248795720,15079420080978847270254094737658,2303285256222520495342598541598,85626553468477992273500465117148,62596313521425363784465377399345,69672636932212923372482058215592,62593020396027469269916594823396,44134600818230557926326754373694,84453743612358354823003862750742,62586710870672994263943519954129,32448185487535134281759823758208,62592962255141150508205240834740,1438884973055426655657478,74281259783979727226169396766854,62638164055246854605460201783609,21903175416834234437760280256014,54312494007946449191474813095082,75449022829063141774651406493666,61807960260051749969825155339608,2312849131620616552835503949818,85712399721663424944975733160292,66324973680054384831725210374569,44228102005841471440315577161328,84102059028252574205625509799360,2314324524945031366876723930641,830205234086831949650067080392,81021628399609328343346262521086,44220233745989030365028758854266,61806308763623939886864809792522,43377756689702860786723733048310,66323498685562185385383197058172,24082562924389364508682232478868,2303401537946287191696625072758]

def inverseCertificate : Matrix (Fin 67) (Fin 67) (ZMod 3) :=
  fun i j => ((inverseRows i / 3^j.val) % 3 : ℕ)

def columnRows : Fin 67 → Fin 3 → Fin 68 := ![
  ![0,3,4],
  ![3,5,6],
  ![5,7,8],
  ![1,7,9],
  ![6,9,10],
  ![4,10,11],
  ![2,8,11],
  ![0,12,13],
  ![12,14,15],
  ![14,16,17],
  ![1,16,18],
  ![13,18,19],
  ![17,19,20],
  ![2,15,20],
  ![12,21,22],
  ![3,21,23],
  ![23,24,25],
  ![13,24,26],
  ![22,26,27],
  ![4,25,27],
  ![21,28,29],
  ![14,28,30],
  ![30,31,32],
  ![22,31,33],
  ![29,33,34],
  ![15,32,34],
  ![28,35,36],
  ![23,35,37],
  ![5,37,38],
  ![29,38,39],
  ![6,36,39],
  ![35,40,41],
  ![30,40,42],
  ![16,42,43],
  ![36,43,44],
  ![17,41,44],
  ![40,45,46],
  ![37,45,47],
  ![24,47,48],
  ![41,48,49],
  ![25,46,49],
  ![45,50,51],
  ![42,50,52],
  ![31,52,53],
  ![46,53,54],
  ![32,51,54],
  ![7,50,55],
  ![47,55,56],
  ![38,56,57],
  ![8,51,57],
  ![18,55,58],
  ![52,58,59],
  ![9,43,59],
  ![26,58,60],
  ![56,60,61],
  ![19,48,61],
  ![33,60,62],
  ![59,62,63],
  ![27,53,63],
  ![39,62,64],
  ![61,64,65],
  ![34,57,65],
  ![44,64,66],
  ![10,63,66],
  ![49,66,67],
  ![20,65,67],
  ![11,54,67]
]

def paddedRow (i : Fin 67) : Fin 68 → ZMod 3 :=
  Fin.lastCases 0 (inverseCertificate i)

def indices : List (Fin 67) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66]

private lemma indices_mem : ∀ i : Fin 67, i ∈ indices := by decide +kernel

private lemma incidence_columns_0 : indices.all (fun j => decide ((if j.succ = triEdges 0 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 0 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 0 2 then (1 : ZMod 3) else 0) = (if (0 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (0 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (0 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_1 : indices.all (fun j => decide ((if j.succ = triEdges 1 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 1 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 1 2 then (1 : ZMod 3) else 0) = (if (1 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (1 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (1 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_2 : indices.all (fun j => decide ((if j.succ = triEdges 2 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 2 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 2 2 then (1 : ZMod 3) else 0) = (if (2 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (2 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (2 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_3 : indices.all (fun j => decide ((if j.succ = triEdges 3 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 3 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 3 2 then (1 : ZMod 3) else 0) = (if (3 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (3 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (3 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_4 : indices.all (fun j => decide ((if j.succ = triEdges 4 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 4 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 4 2 then (1 : ZMod 3) else 0) = (if (4 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (4 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (4 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_5 : indices.all (fun j => decide ((if j.succ = triEdges 5 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 5 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 5 2 then (1 : ZMod 3) else 0) = (if (5 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (5 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (5 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_6 : indices.all (fun j => decide ((if j.succ = triEdges 6 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 6 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 6 2 then (1 : ZMod 3) else 0) = (if (6 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (6 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (6 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_7 : indices.all (fun j => decide ((if j.succ = triEdges 7 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 7 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 7 2 then (1 : ZMod 3) else 0) = (if (7 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (7 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (7 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_8 : indices.all (fun j => decide ((if j.succ = triEdges 8 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 8 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 8 2 then (1 : ZMod 3) else 0) = (if (8 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (8 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (8 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_9 : indices.all (fun j => decide ((if j.succ = triEdges 9 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 9 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 9 2 then (1 : ZMod 3) else 0) = (if (9 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (9 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (9 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_10 : indices.all (fun j => decide ((if j.succ = triEdges 10 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 10 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 10 2 then (1 : ZMod 3) else 0) = (if (10 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (10 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (10 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_11 : indices.all (fun j => decide ((if j.succ = triEdges 11 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 11 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 11 2 then (1 : ZMod 3) else 0) = (if (11 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (11 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (11 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_12 : indices.all (fun j => decide ((if j.succ = triEdges 12 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 12 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 12 2 then (1 : ZMod 3) else 0) = (if (12 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (12 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (12 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_13 : indices.all (fun j => decide ((if j.succ = triEdges 13 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 13 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 13 2 then (1 : ZMod 3) else 0) = (if (13 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (13 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (13 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_14 : indices.all (fun j => decide ((if j.succ = triEdges 14 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 14 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 14 2 then (1 : ZMod 3) else 0) = (if (14 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (14 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (14 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_15 : indices.all (fun j => decide ((if j.succ = triEdges 15 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 15 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 15 2 then (1 : ZMod 3) else 0) = (if (15 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (15 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (15 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_16 : indices.all (fun j => decide ((if j.succ = triEdges 16 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 16 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 16 2 then (1 : ZMod 3) else 0) = (if (16 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (16 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (16 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_17 : indices.all (fun j => decide ((if j.succ = triEdges 17 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 17 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 17 2 then (1 : ZMod 3) else 0) = (if (17 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (17 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (17 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_18 : indices.all (fun j => decide ((if j.succ = triEdges 18 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 18 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 18 2 then (1 : ZMod 3) else 0) = (if (18 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (18 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (18 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_19 : indices.all (fun j => decide ((if j.succ = triEdges 19 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 19 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 19 2 then (1 : ZMod 3) else 0) = (if (19 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (19 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (19 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_20 : indices.all (fun j => decide ((if j.succ = triEdges 20 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 20 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 20 2 then (1 : ZMod 3) else 0) = (if (20 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (20 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (20 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_21 : indices.all (fun j => decide ((if j.succ = triEdges 21 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 21 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 21 2 then (1 : ZMod 3) else 0) = (if (21 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (21 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (21 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_22 : indices.all (fun j => decide ((if j.succ = triEdges 22 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 22 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 22 2 then (1 : ZMod 3) else 0) = (if (22 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (22 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (22 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_23 : indices.all (fun j => decide ((if j.succ = triEdges 23 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 23 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 23 2 then (1 : ZMod 3) else 0) = (if (23 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (23 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (23 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_24 : indices.all (fun j => decide ((if j.succ = triEdges 24 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 24 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 24 2 then (1 : ZMod 3) else 0) = (if (24 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (24 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (24 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_25 : indices.all (fun j => decide ((if j.succ = triEdges 25 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 25 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 25 2 then (1 : ZMod 3) else 0) = (if (25 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (25 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (25 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_26 : indices.all (fun j => decide ((if j.succ = triEdges 26 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 26 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 26 2 then (1 : ZMod 3) else 0) = (if (26 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (26 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (26 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_27 : indices.all (fun j => decide ((if j.succ = triEdges 27 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 27 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 27 2 then (1 : ZMod 3) else 0) = (if (27 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (27 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (27 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_28 : indices.all (fun j => decide ((if j.succ = triEdges 28 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 28 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 28 2 then (1 : ZMod 3) else 0) = (if (28 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (28 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (28 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_29 : indices.all (fun j => decide ((if j.succ = triEdges 29 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 29 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 29 2 then (1 : ZMod 3) else 0) = (if (29 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (29 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (29 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_30 : indices.all (fun j => decide ((if j.succ = triEdges 30 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 30 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 30 2 then (1 : ZMod 3) else 0) = (if (30 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (30 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (30 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_31 : indices.all (fun j => decide ((if j.succ = triEdges 31 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 31 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 31 2 then (1 : ZMod 3) else 0) = (if (31 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (31 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (31 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_32 : indices.all (fun j => decide ((if j.succ = triEdges 32 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 32 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 32 2 then (1 : ZMod 3) else 0) = (if (32 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (32 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (32 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_33 : indices.all (fun j => decide ((if j.succ = triEdges 33 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 33 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 33 2 then (1 : ZMod 3) else 0) = (if (33 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (33 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (33 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_34 : indices.all (fun j => decide ((if j.succ = triEdges 34 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 34 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 34 2 then (1 : ZMod 3) else 0) = (if (34 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (34 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (34 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_35 : indices.all (fun j => decide ((if j.succ = triEdges 35 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 35 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 35 2 then (1 : ZMod 3) else 0) = (if (35 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (35 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (35 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_36 : indices.all (fun j => decide ((if j.succ = triEdges 36 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 36 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 36 2 then (1 : ZMod 3) else 0) = (if (36 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (36 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (36 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_37 : indices.all (fun j => decide ((if j.succ = triEdges 37 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 37 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 37 2 then (1 : ZMod 3) else 0) = (if (37 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (37 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (37 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_38 : indices.all (fun j => decide ((if j.succ = triEdges 38 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 38 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 38 2 then (1 : ZMod 3) else 0) = (if (38 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (38 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (38 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_39 : indices.all (fun j => decide ((if j.succ = triEdges 39 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 39 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 39 2 then (1 : ZMod 3) else 0) = (if (39 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (39 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (39 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_40 : indices.all (fun j => decide ((if j.succ = triEdges 40 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 40 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 40 2 then (1 : ZMod 3) else 0) = (if (40 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (40 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (40 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_41 : indices.all (fun j => decide ((if j.succ = triEdges 41 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 41 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 41 2 then (1 : ZMod 3) else 0) = (if (41 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (41 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (41 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_42 : indices.all (fun j => decide ((if j.succ = triEdges 42 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 42 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 42 2 then (1 : ZMod 3) else 0) = (if (42 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (42 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (42 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_43 : indices.all (fun j => decide ((if j.succ = triEdges 43 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 43 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 43 2 then (1 : ZMod 3) else 0) = (if (43 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (43 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (43 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_44 : indices.all (fun j => decide ((if j.succ = triEdges 44 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 44 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 44 2 then (1 : ZMod 3) else 0) = (if (44 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (44 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (44 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_45 : indices.all (fun j => decide ((if j.succ = triEdges 45 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 45 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 45 2 then (1 : ZMod 3) else 0) = (if (45 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (45 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (45 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_46 : indices.all (fun j => decide ((if j.succ = triEdges 46 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 46 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 46 2 then (1 : ZMod 3) else 0) = (if (46 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (46 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (46 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_47 : indices.all (fun j => decide ((if j.succ = triEdges 47 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 47 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 47 2 then (1 : ZMod 3) else 0) = (if (47 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (47 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (47 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_48 : indices.all (fun j => decide ((if j.succ = triEdges 48 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 48 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 48 2 then (1 : ZMod 3) else 0) = (if (48 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (48 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (48 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_49 : indices.all (fun j => decide ((if j.succ = triEdges 49 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 49 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 49 2 then (1 : ZMod 3) else 0) = (if (49 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (49 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (49 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_50 : indices.all (fun j => decide ((if j.succ = triEdges 50 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 50 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 50 2 then (1 : ZMod 3) else 0) = (if (50 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (50 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (50 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_51 : indices.all (fun j => decide ((if j.succ = triEdges 51 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 51 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 51 2 then (1 : ZMod 3) else 0) = (if (51 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (51 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (51 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_52 : indices.all (fun j => decide ((if j.succ = triEdges 52 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 52 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 52 2 then (1 : ZMod 3) else 0) = (if (52 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (52 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (52 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_53 : indices.all (fun j => decide ((if j.succ = triEdges 53 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 53 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 53 2 then (1 : ZMod 3) else 0) = (if (53 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (53 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (53 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_54 : indices.all (fun j => decide ((if j.succ = triEdges 54 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 54 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 54 2 then (1 : ZMod 3) else 0) = (if (54 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (54 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (54 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_55 : indices.all (fun j => decide ((if j.succ = triEdges 55 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 55 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 55 2 then (1 : ZMod 3) else 0) = (if (55 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (55 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (55 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_56 : indices.all (fun j => decide ((if j.succ = triEdges 56 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 56 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 56 2 then (1 : ZMod 3) else 0) = (if (56 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (56 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (56 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_57 : indices.all (fun j => decide ((if j.succ = triEdges 57 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 57 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 57 2 then (1 : ZMod 3) else 0) = (if (57 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (57 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (57 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_58 : indices.all (fun j => decide ((if j.succ = triEdges 58 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 58 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 58 2 then (1 : ZMod 3) else 0) = (if (58 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (58 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (58 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_59 : indices.all (fun j => decide ((if j.succ = triEdges 59 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 59 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 59 2 then (1 : ZMod 3) else 0) = (if (59 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (59 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (59 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_60 : indices.all (fun j => decide ((if j.succ = triEdges 60 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 60 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 60 2 then (1 : ZMod 3) else 0) = (if (60 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (60 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (60 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_61 : indices.all (fun j => decide ((if j.succ = triEdges 61 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 61 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 61 2 then (1 : ZMod 3) else 0) = (if (61 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (61 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (61 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_62 : indices.all (fun j => decide ((if j.succ = triEdges 62 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 62 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 62 2 then (1 : ZMod 3) else 0) = (if (62 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (62 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (62 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_63 : indices.all (fun j => decide ((if j.succ = triEdges 63 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 63 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 63 2 then (1 : ZMod 3) else 0) = (if (63 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (63 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (63 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_64 : indices.all (fun j => decide ((if j.succ = triEdges 64 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 64 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 64 2 then (1 : ZMod 3) else 0) = (if (64 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (64 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (64 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_65 : indices.all (fun j => decide ((if j.succ = triEdges 65 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 65 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 65 2 then (1 : ZMod 3) else 0) = (if (65 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (65 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (65 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

private lemma incidence_columns_66 : indices.all (fun j => decide ((if j.succ = triEdges 66 0 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 66 1 then (1 : ZMod 3) else 0) + (if j.succ = triEdges 66 2 then (1 : ZMod 3) else 0) = (if (66 : Fin 68) = columnRows j 0 then (1 : ZMod 3) else 0) + (if (66 : Fin 68) = columnRows j 1 then (1 : ZMod 3) else 0) + (if (66 : Fin 68) = columnRows j 2 then (1 : ZMod 3) else 0))) = true := by
  decide +kernel

lemma incidence_columns : ∀ i j : Fin 67, incidence i j =
    ∑ k : Fin 3, if i.castSucc = columnRows j k then 1 else 0 := by
  intro i j
  simp only [incidence, Fin.sum_univ_three]
  fin_cases i
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_0 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_1 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_2 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_3 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_4 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_5 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_6 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_7 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_8 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_9 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_10 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_11 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_12 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_13 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_14 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_15 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_16 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_17 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_18 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_19 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_20 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_21 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_22 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_23 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_24 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_25 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_26 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_27 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_28 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_29 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_30 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_31 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_32 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_33 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_34 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_35 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_36 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_37 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_38 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_39 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_40 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_41 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_42 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_43 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_44 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_45 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_46 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_47 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_48 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_49 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_50 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_51 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_52 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_53 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_54 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_55 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_56 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_57 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_58 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_59 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_60 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_61 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_62 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_63 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_64 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_65 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp incidence_columns_66 j (indices_mem j))

private lemma sparse_certificate_0 : indices.all (fun j => decide (paddedRow 0 (columnRows j 0) + paddedRow 0 (columnRows j 1) + paddedRow 0 (columnRows j 2) = if (0 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_1 : indices.all (fun j => decide (paddedRow 1 (columnRows j 0) + paddedRow 1 (columnRows j 1) + paddedRow 1 (columnRows j 2) = if (1 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_2 : indices.all (fun j => decide (paddedRow 2 (columnRows j 0) + paddedRow 2 (columnRows j 1) + paddedRow 2 (columnRows j 2) = if (2 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_3 : indices.all (fun j => decide (paddedRow 3 (columnRows j 0) + paddedRow 3 (columnRows j 1) + paddedRow 3 (columnRows j 2) = if (3 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_4 : indices.all (fun j => decide (paddedRow 4 (columnRows j 0) + paddedRow 4 (columnRows j 1) + paddedRow 4 (columnRows j 2) = if (4 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_5 : indices.all (fun j => decide (paddedRow 5 (columnRows j 0) + paddedRow 5 (columnRows j 1) + paddedRow 5 (columnRows j 2) = if (5 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_6 : indices.all (fun j => decide (paddedRow 6 (columnRows j 0) + paddedRow 6 (columnRows j 1) + paddedRow 6 (columnRows j 2) = if (6 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_7 : indices.all (fun j => decide (paddedRow 7 (columnRows j 0) + paddedRow 7 (columnRows j 1) + paddedRow 7 (columnRows j 2) = if (7 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_8 : indices.all (fun j => decide (paddedRow 8 (columnRows j 0) + paddedRow 8 (columnRows j 1) + paddedRow 8 (columnRows j 2) = if (8 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_9 : indices.all (fun j => decide (paddedRow 9 (columnRows j 0) + paddedRow 9 (columnRows j 1) + paddedRow 9 (columnRows j 2) = if (9 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_10 : indices.all (fun j => decide (paddedRow 10 (columnRows j 0) + paddedRow 10 (columnRows j 1) + paddedRow 10 (columnRows j 2) = if (10 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_11 : indices.all (fun j => decide (paddedRow 11 (columnRows j 0) + paddedRow 11 (columnRows j 1) + paddedRow 11 (columnRows j 2) = if (11 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_12 : indices.all (fun j => decide (paddedRow 12 (columnRows j 0) + paddedRow 12 (columnRows j 1) + paddedRow 12 (columnRows j 2) = if (12 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_13 : indices.all (fun j => decide (paddedRow 13 (columnRows j 0) + paddedRow 13 (columnRows j 1) + paddedRow 13 (columnRows j 2) = if (13 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_14 : indices.all (fun j => decide (paddedRow 14 (columnRows j 0) + paddedRow 14 (columnRows j 1) + paddedRow 14 (columnRows j 2) = if (14 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_15 : indices.all (fun j => decide (paddedRow 15 (columnRows j 0) + paddedRow 15 (columnRows j 1) + paddedRow 15 (columnRows j 2) = if (15 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_16 : indices.all (fun j => decide (paddedRow 16 (columnRows j 0) + paddedRow 16 (columnRows j 1) + paddedRow 16 (columnRows j 2) = if (16 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_17 : indices.all (fun j => decide (paddedRow 17 (columnRows j 0) + paddedRow 17 (columnRows j 1) + paddedRow 17 (columnRows j 2) = if (17 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_18 : indices.all (fun j => decide (paddedRow 18 (columnRows j 0) + paddedRow 18 (columnRows j 1) + paddedRow 18 (columnRows j 2) = if (18 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_19 : indices.all (fun j => decide (paddedRow 19 (columnRows j 0) + paddedRow 19 (columnRows j 1) + paddedRow 19 (columnRows j 2) = if (19 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_20 : indices.all (fun j => decide (paddedRow 20 (columnRows j 0) + paddedRow 20 (columnRows j 1) + paddedRow 20 (columnRows j 2) = if (20 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_21 : indices.all (fun j => decide (paddedRow 21 (columnRows j 0) + paddedRow 21 (columnRows j 1) + paddedRow 21 (columnRows j 2) = if (21 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_22 : indices.all (fun j => decide (paddedRow 22 (columnRows j 0) + paddedRow 22 (columnRows j 1) + paddedRow 22 (columnRows j 2) = if (22 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_23 : indices.all (fun j => decide (paddedRow 23 (columnRows j 0) + paddedRow 23 (columnRows j 1) + paddedRow 23 (columnRows j 2) = if (23 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_24 : indices.all (fun j => decide (paddedRow 24 (columnRows j 0) + paddedRow 24 (columnRows j 1) + paddedRow 24 (columnRows j 2) = if (24 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_25 : indices.all (fun j => decide (paddedRow 25 (columnRows j 0) + paddedRow 25 (columnRows j 1) + paddedRow 25 (columnRows j 2) = if (25 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_26 : indices.all (fun j => decide (paddedRow 26 (columnRows j 0) + paddedRow 26 (columnRows j 1) + paddedRow 26 (columnRows j 2) = if (26 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_27 : indices.all (fun j => decide (paddedRow 27 (columnRows j 0) + paddedRow 27 (columnRows j 1) + paddedRow 27 (columnRows j 2) = if (27 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_28 : indices.all (fun j => decide (paddedRow 28 (columnRows j 0) + paddedRow 28 (columnRows j 1) + paddedRow 28 (columnRows j 2) = if (28 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_29 : indices.all (fun j => decide (paddedRow 29 (columnRows j 0) + paddedRow 29 (columnRows j 1) + paddedRow 29 (columnRows j 2) = if (29 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_30 : indices.all (fun j => decide (paddedRow 30 (columnRows j 0) + paddedRow 30 (columnRows j 1) + paddedRow 30 (columnRows j 2) = if (30 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_31 : indices.all (fun j => decide (paddedRow 31 (columnRows j 0) + paddedRow 31 (columnRows j 1) + paddedRow 31 (columnRows j 2) = if (31 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_32 : indices.all (fun j => decide (paddedRow 32 (columnRows j 0) + paddedRow 32 (columnRows j 1) + paddedRow 32 (columnRows j 2) = if (32 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_33 : indices.all (fun j => decide (paddedRow 33 (columnRows j 0) + paddedRow 33 (columnRows j 1) + paddedRow 33 (columnRows j 2) = if (33 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_34 : indices.all (fun j => decide (paddedRow 34 (columnRows j 0) + paddedRow 34 (columnRows j 1) + paddedRow 34 (columnRows j 2) = if (34 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_35 : indices.all (fun j => decide (paddedRow 35 (columnRows j 0) + paddedRow 35 (columnRows j 1) + paddedRow 35 (columnRows j 2) = if (35 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_36 : indices.all (fun j => decide (paddedRow 36 (columnRows j 0) + paddedRow 36 (columnRows j 1) + paddedRow 36 (columnRows j 2) = if (36 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_37 : indices.all (fun j => decide (paddedRow 37 (columnRows j 0) + paddedRow 37 (columnRows j 1) + paddedRow 37 (columnRows j 2) = if (37 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_38 : indices.all (fun j => decide (paddedRow 38 (columnRows j 0) + paddedRow 38 (columnRows j 1) + paddedRow 38 (columnRows j 2) = if (38 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_39 : indices.all (fun j => decide (paddedRow 39 (columnRows j 0) + paddedRow 39 (columnRows j 1) + paddedRow 39 (columnRows j 2) = if (39 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_40 : indices.all (fun j => decide (paddedRow 40 (columnRows j 0) + paddedRow 40 (columnRows j 1) + paddedRow 40 (columnRows j 2) = if (40 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_41 : indices.all (fun j => decide (paddedRow 41 (columnRows j 0) + paddedRow 41 (columnRows j 1) + paddedRow 41 (columnRows j 2) = if (41 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_42 : indices.all (fun j => decide (paddedRow 42 (columnRows j 0) + paddedRow 42 (columnRows j 1) + paddedRow 42 (columnRows j 2) = if (42 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_43 : indices.all (fun j => decide (paddedRow 43 (columnRows j 0) + paddedRow 43 (columnRows j 1) + paddedRow 43 (columnRows j 2) = if (43 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_44 : indices.all (fun j => decide (paddedRow 44 (columnRows j 0) + paddedRow 44 (columnRows j 1) + paddedRow 44 (columnRows j 2) = if (44 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_45 : indices.all (fun j => decide (paddedRow 45 (columnRows j 0) + paddedRow 45 (columnRows j 1) + paddedRow 45 (columnRows j 2) = if (45 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_46 : indices.all (fun j => decide (paddedRow 46 (columnRows j 0) + paddedRow 46 (columnRows j 1) + paddedRow 46 (columnRows j 2) = if (46 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_47 : indices.all (fun j => decide (paddedRow 47 (columnRows j 0) + paddedRow 47 (columnRows j 1) + paddedRow 47 (columnRows j 2) = if (47 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_48 : indices.all (fun j => decide (paddedRow 48 (columnRows j 0) + paddedRow 48 (columnRows j 1) + paddedRow 48 (columnRows j 2) = if (48 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_49 : indices.all (fun j => decide (paddedRow 49 (columnRows j 0) + paddedRow 49 (columnRows j 1) + paddedRow 49 (columnRows j 2) = if (49 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_50 : indices.all (fun j => decide (paddedRow 50 (columnRows j 0) + paddedRow 50 (columnRows j 1) + paddedRow 50 (columnRows j 2) = if (50 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_51 : indices.all (fun j => decide (paddedRow 51 (columnRows j 0) + paddedRow 51 (columnRows j 1) + paddedRow 51 (columnRows j 2) = if (51 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_52 : indices.all (fun j => decide (paddedRow 52 (columnRows j 0) + paddedRow 52 (columnRows j 1) + paddedRow 52 (columnRows j 2) = if (52 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_53 : indices.all (fun j => decide (paddedRow 53 (columnRows j 0) + paddedRow 53 (columnRows j 1) + paddedRow 53 (columnRows j 2) = if (53 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_54 : indices.all (fun j => decide (paddedRow 54 (columnRows j 0) + paddedRow 54 (columnRows j 1) + paddedRow 54 (columnRows j 2) = if (54 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_55 : indices.all (fun j => decide (paddedRow 55 (columnRows j 0) + paddedRow 55 (columnRows j 1) + paddedRow 55 (columnRows j 2) = if (55 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_56 : indices.all (fun j => decide (paddedRow 56 (columnRows j 0) + paddedRow 56 (columnRows j 1) + paddedRow 56 (columnRows j 2) = if (56 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_57 : indices.all (fun j => decide (paddedRow 57 (columnRows j 0) + paddedRow 57 (columnRows j 1) + paddedRow 57 (columnRows j 2) = if (57 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_58 : indices.all (fun j => decide (paddedRow 58 (columnRows j 0) + paddedRow 58 (columnRows j 1) + paddedRow 58 (columnRows j 2) = if (58 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_59 : indices.all (fun j => decide (paddedRow 59 (columnRows j 0) + paddedRow 59 (columnRows j 1) + paddedRow 59 (columnRows j 2) = if (59 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_60 : indices.all (fun j => decide (paddedRow 60 (columnRows j 0) + paddedRow 60 (columnRows j 1) + paddedRow 60 (columnRows j 2) = if (60 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_61 : indices.all (fun j => decide (paddedRow 61 (columnRows j 0) + paddedRow 61 (columnRows j 1) + paddedRow 61 (columnRows j 2) = if (61 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_62 : indices.all (fun j => decide (paddedRow 62 (columnRows j 0) + paddedRow 62 (columnRows j 1) + paddedRow 62 (columnRows j 2) = if (62 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_63 : indices.all (fun j => decide (paddedRow 63 (columnRows j 0) + paddedRow 63 (columnRows j 1) + paddedRow 63 (columnRows j 2) = if (63 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_64 : indices.all (fun j => decide (paddedRow 64 (columnRows j 0) + paddedRow 64 (columnRows j 1) + paddedRow 64 (columnRows j 2) = if (64 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_65 : indices.all (fun j => decide (paddedRow 65 (columnRows j 0) + paddedRow 65 (columnRows j 1) + paddedRow 65 (columnRows j 2) = if (65 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

private lemma sparse_certificate_66 : indices.all (fun j => decide (paddedRow 66 (columnRows j 0) + paddedRow 66 (columnRows j 1) + paddedRow 66 (columnRows j 2) = if (66 : Fin 67) = j then 1 else 0)) = true := by
  decide +kernel

lemma sparse_certificate : ∀ i j : Fin 67,
    (∑ k : Fin 3, paddedRow i (columnRows j k)) = if i = j then 1 else 0 := by
  intro i j
  simp only [Fin.sum_univ_three]
  fin_cases i
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_0 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_1 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_2 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_3 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_4 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_5 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_6 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_7 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_8 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_9 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_10 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_11 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_12 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_13 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_14 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_15 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_16 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_17 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_18 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_19 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_20 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_21 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_22 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_23 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_24 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_25 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_26 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_27 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_28 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_29 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_30 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_31 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_32 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_33 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_34 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_35 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_36 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_37 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_38 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_39 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_40 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_41 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_42 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_43 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_44 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_45 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_46 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_47 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_48 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_49 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_50 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_51 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_52 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_53 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_54 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_55 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_56 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_57 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_58 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_59 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_60 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_61 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_62 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_63 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_64 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_65 j (indices_mem j))
  · exact of_decide_eq_true (List.all_eq_true.mp sparse_certificate_66 j (indices_mem j))

lemma padded_sum (i : Fin 67) (a : Fin 68) :
    (∑ r : Fin 67, inverseCertificate i r * (if r.castSucc = a then 1 else 0)) =
      paddedRow i a := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [paddedRow, Fin.lastCases_last, Fin.castSucc_ne_last, if_false,
      mul_zero, Finset.sum_const_zero]
  · simp [paddedRow]

theorem certificate : inverseCertificate * incidence = 1 := by
  ext i j
  change (∑ r : Fin 67, inverseCertificate i r * incidence r j) = _
  simp_rw [incidence_columns,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [padded_sum]
  exact sparse_certificate i j

#print axioms certificate
end Erdos595PaleyAPObstruction
