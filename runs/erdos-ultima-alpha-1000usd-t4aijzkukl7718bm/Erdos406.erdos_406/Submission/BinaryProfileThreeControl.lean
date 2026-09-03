import Submission.BinaryProfileMinplusCertificates
import Submission.BinaryAcceptingMinplusCoverage

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryProfileThreeControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def nextData : Array (List (Fin 8)) := #[[0],[1],[7],[4,6],[2,3],[3],[5],[6],[4],[2,4],[6],[6],[6],[6],[4],[3,4]]
private def weightData : Array (Array (ℤ)) := #[#[0,0,-640,-640],#[1,1,-640,640],#[3,3,3,3],#[3,3,3,3],#[3,3,3,3],#[3,3,3,3],#[3,3,3,3],#[-640,-640,640,-639]]
private def sourceData : Array (Fin 8) := #[0,0,0,1,1,1,7,7,7,4,6,4,6,4,6,3,3,3,6,2,4,6,6,2,2,6,6,5,5,5,6,3,2,3,4,6,3,6,6,6,6,6,6,6,6,6,6,5,5,2,3,3,5,4,2,4,6,6,6,6,6,6,6,3,3,5,2,4,2,4,3,2,3,6,5,3,3,3,3,5,2,3,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]
private def carryData : Array ℕ := #[0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,1,2,1,0,0,2,0,1,2,1,2,0,1,2,0,0,1,1,1,1,2,2,0,1,2,0,2,0,2,0,1,0,1,2,2,0,2,2,0,0,1,2,1,0,1,2,2,1,2,0,1,1,2,2,0,1,1,1,2,2,0,1,2,0,2,2,2,0,1,2,0,1,2,0,2,1,1,0,2,0,1,2,0,2,1]
private def endData : Array (List (Fin 8)) := #[[0],[1],[7],[4],[4],[4],[4],[4],[4],[4],[4],[4],[4],[4],[2,4],[2],[4],[4],[2,4],[2],[2,4],[4],[2],[4],[4],[3,4],[3,4],[2],[3],[4],[2,3],[3],[3],[3],[3,4],[3],[2],[4,5],[2,6],[4,5],[4,6],[3],[5],[6],[2],[2,5],[3,6],[5],[6],[5],[5],[6],[5],[4,5],[2,6],[4,6],[2],[3],[4,6],[5],[6],[6],[5,6],[6],[6],[6],[4,6],[4,6],[4,6],[4,6],[3,6],[3,6],[3,6],[5],[6],[4,6],[2,6],[4,6],[2,6],[5,6],[5,6],[5,6],[5,6],[2,6],[3,6],[4,6],[4,6],[2,6],[3,6],[3,6],[2,6],[2,4,6],[5,6],[5,6],[2,4,6],[2,3,6],[3,4,6],[3,4,6],[2,5,6],[4,5,6],[4,5,6]]
private def hData : Array (Array (ℤ)) := #[#[0,0,0],#[-640,-640,-640],#[-639,-639,-639],#[-640,-640,-640],#[-639,-639,-639],#[-638,-638,-638],#[-638,-638,-638],#[-638,-638,-638],#[-637,-637,-637],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,1280,1280],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,1280,1280],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,1280,1280],#[5,1280,1280],#[5,1280,1280],#[5,1280,1280],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,5,5],#[5,1280,1280],#[5,5,5],#[5,5,5],#[5,1280,1280],#[5,1280,1280],#[5,5,5],#[5,5,1280],#[5,5,1280],#[5,5,5],#[5,5,1280],#[5,5,1280],#[5,5,1280]]
private def destData : Array (Array (Fin 101)) := #[#[0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,0,0,2,0,3,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,0,5,0],#[6,0,7,0,0,0,0,0,0,0,0,0],#[0,0,0,0,8,0,9,10,0,0,0,0],#[0,0,0,0,0,0,0,0,11,12,13,14],#[9,0,11,0,0,0,0,0,0,0,0,0],#[0,0,0,0,13,0,15,9,0,0,0,0],#[0,0,0,0,0,0,0,0,16,11,17,13],#[9,0,11,0,0,0,0,0,0,0,0,0],#[10,0,18,0,0,0,0,0,0,0,0,0],#[0,0,0,0,13,0,19,20,0,0,0,0],#[0,0,0,0,21,0,22,0,0,0,0,0],#[0,0,0,0,0,0,0,0,23,11,24,13],#[0,0,0,0,0,0,0,0,25,0,26,0],#[27,0,28,0,0,0,0,0,0,0,0,0],#[0,0,0,0,29,0,10,0,0,0,0,0],#[0,0,0,0,0,0,0,0,12,0,21,0],#[0,0,0,0,14,0,30,0,0,0,0,0],#[19,31,32,33,0,0,0,0,0,0,0,0],#[20,0,34,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,12,0,21,0],#[22,0,35,0,0,0,0,0,0,0,0,0],#[0,0,0,0,24,17,15,0,0,0,0,0],#[0,0,0,0,0,0,0,0,16,0,36,0],#[0,0,0,0,37,0,38,0,0,0,0,0],#[0,0,0,0,0,0,0,0,39,0,40,0],#[41,0,35,0,0,0,0,0,0,0,0,0],#[0,0,0,0,42,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,12,0,44,0],#[45,0,46,0,0,0,0,0,0,0,0,0],#[47,0,48,0,0,0,0,0,0,0,0,0],#[0,0,0,0,49,50,51,0,0,0,0,0],#[0,0,0,0,52,0,43,0,0,0,0,0],#[0,0,0,0,53,0,54,55,0,0,0,0],#[0,0,0,0,42,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,56,0,57,0],#[0,0,0,0,0,0,0,0,58,0,40,0],#[38,0,46,0,0,0,0,0,0,0,0,0],#[0,0,0,0,40,0,38,0,0,0,0,0],#[0,0,0,0,0,0,0,0,58,0,40,0],#[59,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[43,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,35,0,57,0],#[38,0,46,0,0,0,0,0,0,0,0,0],#[0,0,0,0,62,0,43,0,0,0,0,0],#[43,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,61,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,63,0,64,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[65,0,48,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[0,0,0,0,0,0,0,0,66,67,68,69],#[54,70,71,72,0,0,0,0,0,0,0,0],#[55,0,67,0,0,0,0,0,0,0,0,0],#[0,0,0,0,44,0,41,0,0,0,0,0],#[0,0,0,0,0,0,0,0,73,0,61,0],#[0,0,0,0,40,0,38,0,0,0,0,0],#[43,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,61,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[0,0,0,0,74,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[43,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,68,75,76,0,0,0,0,0],#[0,0,0,0,69,0,54,55,0,0,0,0],#[0,0,0,0,0,0,0,0,77,0,78,0],#[0,0,0,0,0,0,0,0,66,67,68,69],#[79,0,48,0,0,0,0,0,0,0,0,0],#[0,0,0,0,80,81,51,0,0,0,0,0],#[0,0,0,0,82,0,43,0,0,0,0,0],#[0,0,0,0,61,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[0,0,0,0,0,0,0,0,58,0,40,0],#[83,0,84,0,0,0,0,0,0,0,0,0],#[0,0,0,0,85,0,86,0,0,0,0,0],#[0,0,0,0,0,0,0,0,87,0,88,0],#[43,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,63,0,64,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[0,0,0,0,0,0,0,0,60,0,61,0],#[89,0,46,0,0,0,0,0,0,0,0,0],#[0,0,0,0,62,0,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,58,0,90,0],#[86,0,91,0,0,0,0,0,0,0,0,0],#[0,0,0,0,90,0,89,0,0,0,0,0],#[0,0,0,0,0,0,0,0,92,0,61,0],#[93,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,46,0,88,0],#[0,0,0,0,94,0,95,0,0,0,0,0],#[0,0,0,0,61,0,43,0,0,0,0,0],#[43,0,60,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,96,0,97,0],#[98,0,46,0,0,0,0,0,0,0,0,0],#[0,0,0,0,99,0,38,0,0,0,0,0],#[0,0,0,0,0,0,0,0,100,0,40,0],#[38,0,46,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,58,0,40,0],#[0,0,0,0,40,0,38,0,0,0,0,0]]
private def parentData : Array (Array (Fin 8)) := #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,0,0,0,7,7,7,0,0,0],#[4,4,4,0,0,0,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4],#[4,4,4,0,0,0,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4],#[4,4,4,0,0,0,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[4,4,4,0,0,0,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,4,4,0,0,0,2,4,4,0,0,0],#[2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,2,4,4,0,0,0,4,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[2,2,2,2,2,2,2,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[2,4,4,0,0,0,2,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,0,0,0],#[2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,3,3,0,0,0,4,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,3,3,0,0,0,4,3,3,0,0,0],#[2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,0,0,0,4,4,4,0,0,0],#[2,3,3,0,0,0,2,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[3,3,3,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,3,3,3,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,3,3,0,0,0,4,3,3,4,3,3,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,0,0,0,2,2,2,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,5,0,0,0,4,5,5,0,0,0],#[2,6,6,0,0,0,2,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,5,5,0,0,0,4,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,0,0,0],#[3,3,3,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[6,6,6,0,0,0,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,0,0,0,2,2,2,0,0,0],#[2,5,5,0,0,0,2,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,6,6,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[5,5,5,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,0,0,0,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[6,6,6,0,0,0,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,5,4,5,5,4,5,5,4,5,5],#[2,6,6,2,6,6,2,6,6,2,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[4,6,6,0,0,0,4,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,0,0,0,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,0,0,0,3,3,3,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[5,5,5,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,0,0,0,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,0,0,0,6,6,6,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,0,0,0,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,0,0,0,6,6,6,0,0,0],#[6,6,6,0,0,0,6,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,4,6,6,4,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,4,6,6,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,4,6,6,4,6,6,4,6,6],#[3,6,6,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,6,6,3,6,6,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,6,6,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,6,0,0,0,6,6,6,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,0,0,0],#[2,6,6,0,0,0,2,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,6,6,0,0,0,2,6,6,0,0,0],#[5,5,5,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0],#[2,6,6,0,0,0,2,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,3,6,6,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,6,6,0,0,0,4,6,6,0,0,0],#[4,6,6,0,0,0,4,4,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,2,6,6,0,0,0,2,6,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,6,6,0,0,0,3,3,3,0,0,0],#[3,6,6,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,6,6,0,0,0,2,6,6,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,2,4,6,0,0,0,4,2,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[5,5,5,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,4,6,0,0,0,2,4,6,0,0,0],#[2,3,6,0,0,0,2,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,3,6,0,0,0,4,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,3,6,0,0,0,4,3,3,0,0,0],#[2,5,5,0,0,0,2,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,5,0,0,0,4,5,5,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,4,5,5,0,0,0,4,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def finishData : Array (Fin 8) := #[0,1,0,4,4,0,4,4,0,4,4,4,4,0,0,2,4,0,2,2,2,0,2,4,0,3,0,2,3,0,2,3,3,3,3,3,0,0,2,4,0,3,0,6,0,2,3,5,6,0,0,6,0,0,2,4,2,0,4,5,6,0,0,6,0,6,4,4,0,0,3,3,3,5,0,0,2,4,0,5,0,0,0,2,3,0,4,2,0,3,0,2,5,5,0,2,3,0,2,0,4]
private def jData : Array ℤ := #[0,640,0,0,-640,0,0,3]
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 8) (d : ℕ) : List (Fin 8) := nextData[s.val*2+(digit d).val]?.getD []
def nextTable (s : Fin 8) (d : ℕ) : Finset (Fin 8) := (nextList s d).toFinset
def slot (s : Fin 8) (d : ℕ) (t : Fin 8) : ℕ := if t=(nextList s d).getD 0 0 then 0 else 1
def W (s : Fin 8) (d : ℕ) (t : Fin 8) : ℤ := (weightData[s.val]?.getD #[])[(digit d).val*2+slot s d t]?.getD 0
def source (p : Fin 101) : Fin 8 := sourceData[p.val]?.getD 0
def carry (p : Fin 101) : ℕ := carryData[p.val]?.getD 0
def endsList (p : Fin 101) : List (Fin 8) := endData[p.val]?.getD []
def ends (p : Fin 101) : Finset (Fin 8) := (endsList p).toFinset
def eslot (p : Fin 101) (t : Fin 8) : ℕ := (endsList p).idxOf t
def H (p : Fin 101) (t : Fin 8) : ℤ := (hData[p.val]?.getD #[])[eslot p t]?.getD 0
def index (p : Fin 101) (d cp : ℕ) (sp : Fin 8) : ℕ := ((digit d).val*3+cp)*2+slot (source p) d sp
def target (p : Fin 101) (d cp : ℕ) (sp : Fin 8) : Fin 101 := (destData[p.val]?.getD #[])[index p d cp sp]?.getD 0
def parent (p : Fin 101) (d cp : ℕ) (sp tp : Fin 8) : Fin 8 :=
  (parentData[p.val]?.getD #[])[(index p d cp sp)*3+eslot (target p d cp sp) tp]?.getD 0
def finish (p : Fin 101) : Fin 8 := finishData[p.val]?.getD 0
def J (s : Fin 8) : ℤ := jData[s.val]?.getD 0
def F (s : Fin 8) : Prop := s.val ∉ []
instance (s : Fin 8) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 8) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/5

private def familyData : Array (Finset (Fin 8)) := #[{0},{1},{2,3,4},{2,3,4,5},{2,3,4,5,6},{2,3,4,6},{2,4},{2,4,6},{3,4},{4},{4,5},{4,6},{7}]
def memberSet (i : Fin 13) : Finset (Fin 8) := familyData[i.val]?.getD ∅
private def covDestData : Array (Fin 13) := #[0,1,12,11,3,5,4,5,4,5,4,5,2,2,5,5,10,7,9,6,11,7,11,7,9,8]
def covDest (i : Fin 13) (d : Fin 2) : Fin 13 := covDestData[i.val*2+d.val]?.getD 0
def family : Finset (Finset (Fin 8)) := Finset.univ.image memberSet
lemma coverage_steps : ∀ i (d : Fin 2), nextSet D (memberSet i) d.val=memberSet (covDest i d) := by decide +kernel
private def covAcceptData : Array (Fin 8) := #[0,1,2,2,2,2,2,2,3,4,4,4,7]
def covAccept (i : Fin 13) : Fin 8 := covAcceptData[i.val]?.getD 0
lemma coverage_accepting : ∀ i : Fin 13, covAccept i ∈ memberSet i ∧ F (covAccept i) := by decide +kernel

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

def R (s : Fin 8) (p : Fin 101) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 8) (p : Fin 101) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_profiles : R 0 0 0 ∧ R 0 1 1 ∧ R 0 2 2 := by decide +kernel
lemma seed_zero : ∀ t ∈ ends 0, t=0 ∧ 0 ≤ H 0 t := by decide +kernel
lemma seed_one : ∀ t ∈ ends 1, t=1 ∧ W 0 1 1 ≤ H 1 t := by decide +kernel
lemma seed_two : ∀ t ∈ ends 2, t ∈ D.next 1 0 ∧ W 0 1 1+W 1 0 t ≤ H 2 t := by decide +kernel
lemma first_one : (1:Fin 8) ∈ D.next D.start 1 := by decide +kernel

def StepRow (p : Fin 101) : Prop := ∀ (d e : Fin 2) (cp : Fin 3),
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
lemma step_row_54 : StepRow 54 := by
  unfold StepRow R
  decide +kernel
lemma step_row_55 : StepRow 55 := by
  unfold StepRow R
  decide +kernel
lemma step_row_56 : StepRow 56 := by
  unfold StepRow R
  decide +kernel
lemma step_row_57 : StepRow 57 := by
  unfold StepRow R
  decide +kernel
lemma step_row_58 : StepRow 58 := by
  unfold StepRow R
  decide +kernel
lemma step_row_59 : StepRow 59 := by
  unfold StepRow R
  decide +kernel
lemma step_row_60 : StepRow 60 := by
  unfold StepRow R
  decide +kernel
lemma step_row_61 : StepRow 61 := by
  unfold StepRow R
  decide +kernel
lemma step_row_62 : StepRow 62 := by
  unfold StepRow R
  decide +kernel
lemma step_row_63 : StepRow 63 := by
  unfold StepRow R
  decide +kernel
lemma step_row_64 : StepRow 64 := by
  unfold StepRow R
  decide +kernel
lemma step_row_65 : StepRow 65 := by
  unfold StepRow R
  decide +kernel
lemma step_row_66 : StepRow 66 := by
  unfold StepRow R
  decide +kernel
lemma step_row_67 : StepRow 67 := by
  unfold StepRow R
  decide +kernel
lemma step_row_68 : StepRow 68 := by
  unfold StepRow R
  decide +kernel
lemma step_row_69 : StepRow 69 := by
  unfold StepRow R
  decide +kernel
lemma step_row_70 : StepRow 70 := by
  unfold StepRow R
  decide +kernel
lemma step_row_71 : StepRow 71 := by
  unfold StepRow R
  decide +kernel
lemma step_row_72 : StepRow 72 := by
  unfold StepRow R
  decide +kernel
lemma step_row_73 : StepRow 73 := by
  unfold StepRow R
  decide +kernel
lemma step_row_74 : StepRow 74 := by
  unfold StepRow R
  decide +kernel
lemma step_row_75 : StepRow 75 := by
  unfold StepRow R
  decide +kernel
lemma step_row_76 : StepRow 76 := by
  unfold StepRow R
  decide +kernel
lemma step_row_77 : StepRow 77 := by
  unfold StepRow R
  decide +kernel
lemma step_row_78 : StepRow 78 := by
  unfold StepRow R
  decide +kernel
lemma step_row_79 : StepRow 79 := by
  unfold StepRow R
  decide +kernel
lemma step_row_80 : StepRow 80 := by
  unfold StepRow R
  decide +kernel
lemma step_row_81 : StepRow 81 := by
  unfold StepRow R
  decide +kernel
lemma step_row_82 : StepRow 82 := by
  unfold StepRow R
  decide +kernel
lemma step_row_83 : StepRow 83 := by
  unfold StepRow R
  decide +kernel
lemma step_row_84 : StepRow 84 := by
  unfold StepRow R
  decide +kernel
lemma step_row_85 : StepRow 85 := by
  unfold StepRow R
  decide +kernel
lemma step_row_86 : StepRow 86 := by
  unfold StepRow R
  decide +kernel
lemma step_row_87 : StepRow 87 := by
  unfold StepRow R
  decide +kernel
lemma step_row_88 : StepRow 88 := by
  unfold StepRow R
  decide +kernel
lemma step_row_89 : StepRow 89 := by
  unfold StepRow R
  decide +kernel
lemma step_row_90 : StepRow 90 := by
  unfold StepRow R
  decide +kernel
lemma step_row_91 : StepRow 91 := by
  unfold StepRow R
  decide +kernel
lemma step_row_92 : StepRow 92 := by
  unfold StepRow R
  decide +kernel
lemma step_row_93 : StepRow 93 := by
  unfold StepRow R
  decide +kernel
lemma step_row_94 : StepRow 94 := by
  unfold StepRow R
  decide +kernel
lemma step_row_95 : StepRow 95 := by
  unfold StepRow R
  decide +kernel
lemma step_row_96 : StepRow 96 := by
  unfold StepRow R
  decide +kernel
lemma step_row_97 : StepRow 97 := by
  unfold StepRow R
  decide +kernel
lemma step_row_98 : StepRow 98 := by
  unfold StepRow R
  decide +kernel
lemma step_row_99 : StepRow 99 := by
  unfold StepRow R
  decide +kernel
lemma step_row_100 : StepRow 100 := by
  unfold StepRow R
  decide +kernel
lemma step_checks : ∀ p : Fin 101, StepRow p := by
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

lemma finish_checks : ∀ p : Fin 101, carry p < 2 → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 5 := by decide +kernel

def construction : Erdos406BinaryProfileMinplus.Construction D F (Fin 101) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/5
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
      refine ⟨(W 0 1 1:ℝ)/5,?_,?_⟩
      · have hr := Run.cons first_one (Run.nil (D:=D) 1)
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ) ≤ H 1 1 := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/5 ≤ (H 1 1:ℝ)/5
        linarith
    · refine ⟨2,seed_profiles.2.2,?_⟩
      intro t ht
      obtain ⟨he,hh⟩ := seed_two t ht
      refine ⟨(W 0 1 1:ℝ)/5+(W 1 0 t:ℝ)/5,?_,?_⟩
      · have hr := Run.cons first_one (Run.cons he (Run.nil (D:=D) t))
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ)+W 1 0 t ≤ H 2 t := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/5+(W 1 0 t:ℝ)/5 ≤ (H 2 t:ℝ)/5
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
    change (H p (parent p d cp sp tp):ℝ)/5+(W (parent p d cp sp tp) e tp:ℝ)/5-
      (W (source p) d sp:ℝ)/5 ≤ (H (target p d cp sp) tp:ℝ)/5
    linarith
  finish := by
    intro s p c hc hr hf
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨ht,hf',hh⟩ := finish_checks p hc hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 5 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/5 ≤ 1
    linarith

def G (s : Fin 8) : Prop := s.val ∈ [1,4,7]
def Z (s : Fin 8) : Prop := s.val ∉ []
instance (s : Fin 8) : Decidable (G s) := by unfold G; infer_instance
instance (s : Fin 8) : Decidable (Z s) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, G t) ∧
    (∀ t, F t → Z t) ∧
    (∀ s, ∀ t ∈ D.next s 0, Z t → Z s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, Z t → 3+J t-J s ≤ W s 0 t) ∧
    (∀ s ∈ D.next D.start 1, ∀ t, G t → F t → Z s → -1920 ≤ W D.start 1 s+J t-J s) := by decide +kernel

def powerBound : PowerBound D F where
  a := 3/5
  B := 384
  G := G
  Z := Z
  J s := (J s:ℝ)/5
  start := power_checks.1
  forward := by intro s t hs ht; exact power_checks.2.1 s hs t ht
  accepting := power_checks.2.2.1
  backward := by intro s t ht he; exact power_checks.2.2.2.1 s t he ht
  lower_step := by
    intro s t hs hz he
    have hh : (3:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s hs t he hz
    change (3/5:ℝ)+(J t:ℝ)/5-(J s:ℝ)/5 ≤ (W s 0 t:ℝ)/5
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-1920:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2.2.2 s hs t ht hf hz
    change -(384:ℝ) ≤ (W D.start 1 s:ℝ)/5+(J t:ℝ)/5-(J s:ℝ)/5
    linarith

def V (n : ℕ) : ℝ := value D F total n
lemma construction_bound (n d : ℕ) (hd : d<2) : V (3*n+d) ≤ V n+1 := construction.construction_bound total n d hd
lemma power_lower (k : ℕ) : (3/5:ℝ)*k-384 ≤ V (2^k) := powerBound.power_lower total k

lemma not_supercritical : ¬ Real.log 2 < (3/5:ℝ)*Real.log 3 := by
  have hh : (3:ℝ)^3 ≤ (2:ℝ)^5 := by norm_num
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^3) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos406BinaryProfileThreeControl
