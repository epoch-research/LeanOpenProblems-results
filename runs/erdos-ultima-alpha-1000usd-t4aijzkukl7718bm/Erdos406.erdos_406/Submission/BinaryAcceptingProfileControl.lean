import Submission.BinaryProfileMinplusCertificates
import Submission.BinaryAcceptingMinplusCoverage

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406BinaryAcceptingProfileControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def nextData : Array (List (Fin 16)) := #[[0],[1],[2],[3],[3,13],[5,6],[2,7],[7],[5],[9,14],[9],[4],[3],[7,8],[4,7],[7,8],[8,11],[12],[9],[5],[9,11],[15],[12,15],[9,15],[10],[11],[3,14],[6],[10],[14],[4,12],[5]]
private def weightData : Array (Array (ℤ)) := #[#[0,0,-3072,-3072],#[15,15,-3033,-3033],#[-3042,3072,3072,-3036],#[3072,-3072,-3069,-3069],#[1016,1016,1016,3072],#[1016,1016,1016,1016],#[12,12,-3072,3072],#[1963,15,15,3072],#[3072,3072,1016,1016],#[1016,1016,1016,1016],#[1016,-1040,-1040,-1040],#[3072,1016,1016,1016],#[1016,1016,-1040,-1040],#[3072,3072,3072,3072],#[3072,3072,3072,3072],#[-1040,3072,-1040,-1040]]
private def sourceData : Array (Fin 16) := #[0,0,0,1,1,1,2,2,2,3,3,3,13,3,13,13,5,6,5,6,5,6,7,7,7,14,14,14,9,9,9,4,8,4,4,8,8,4,4,10,10,10,9,5,11,8,11,11,12,12,12,5,5,9,14,9,14,11,11,11,15,15,15,9,9,12,15,12,15,8,11,12,12,15,9,15,15,9,9,4,10,14,5,14,14,12,15,15,10,10,12,4,12,10,11,12,12,15,9,15,10,10,11,11,5,5,9,9,4,4,4,12,5,9,5,15,15,10,4,14,14,11,11,4,12,11,5,11,12,15,12,10,11,11,11,4,5,5,15,4,9,5,5,11,4,11,10,10,15,15,12,12,10,10,14,9,4,14,5]
private def carryData : Array ℕ := #[0,1,2,0,1,2,0,1,2,0,1,2,0,1,1,2,0,0,1,1,2,2,0,1,2,0,1,2,0,1,2,0,0,1,2,1,2,0,2,0,1,2,0,0,0,1,1,2,0,1,2,0,1,1,1,2,2,0,1,2,0,1,2,0,1,0,0,1,1,2,2,0,2,2,0,0,1,0,1,0,2,0,2,1,2,2,1,2,0,1,0,1,1,2,0,1,2,1,2,2,0,1,1,2,1,2,0,1,0,1,2,2,0,2,1,1,2,0,1,0,2,1,2,2,2,1,2,0,0,0,1,2,0,1,2,2,0,1,0,1,2,1,2,1,0,0,0,1,0,2,0,1,1,2,1,2,0,0,1]
private def endData : Array (List (Fin 16)) := #[[0],[1],[2],[3],[3],[6],[7],[7],[7],[7],[3],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[7],[8],[7],[7],[7],[7],[4],[4],[7],[7],[7],[4],[4],[11],[12],[12],[7],[7],[7],[7],[5],[9],[5],[5],[9],[9],[7],[7],[4],[7],[7],[7],[5],[9],[12],[15],[15],[15],[10],[10],[11],[10],[10],[11],[11],[4],[9],[4],[5],[9],[4],[5],[9],[5],[4],[5],[9],[10],[11],[4],[5],[5],[4],[5],[11],[15],[11],[15],[15],[15],[9],[11],[15],[11],[15],[15],[15],[15],[15],[5],[5],[9],[5],[4],[9],[5],[5],[9],[5],[4],[5],[9],[9],[9],[15],[9],[4],[9],[9],[4],[15],[15],[4],[5],[15],[15],[12],[5],[4],[4],[5],[4],[9],[9],[9],[9],[4],[4],[4],[5],[9],[5],[5],[4],[10],[11],[9],[15]]
private def hData : Array (Array (ℤ)) := #[#[0,0],#[-3072,-3072],#[-3057,-3057],#[-3033,-3033],#[-3027,-3027],#[-3021,-3021],#[-6120,-6120],#[-6117,-6117],#[-6114,-6114],#[-3063,-3063],#[24,24],#[-3060,-3060],#[-6144,-6144],#[-3063,-3063],#[-6144,-6144],#[-6144,-6144],#[-2925,-2925],#[-3066,-3066],#[-2925,-2925],#[-3063,-3063],#[-2925,-2925],#[-3063,-3063],#[24,24],#[24,24],#[24,24],#[-4981,-4981],#[-5982,-5982],#[-5982,-5982],#[-2925,-2925],#[-3926,-3926],#[-3926,-3926],#[-2925,-2925],#[24,24],#[-1924,-1924],#[-2925,-2925],#[-3033,-3033],#[-3033,-3033],#[24,24],#[24,24],#[-5035,-5035],#[-5035,-5035],#[-5035,-5035],#[24,24],#[24,24],#[24,24],#[-2032,-2032],#[-2032,-2032],#[-2979,-2979],#[-4034,-4034],#[-4034,-4034],#[-4034,-4034],#[24,24],#[24,24],#[24,24],#[-2032,-2032],#[24,24],#[-2032,-2032],#[-2979,-2979],#[-2979,-2979],#[-2032,-2032],#[-3980,-3980],#[-3980,-3980],#[-3980,-3980],#[24,24],#[24,24],#[24,24],#[24,24],#[-2032,-2032],#[24,24],#[-4088,-4088],#[-4088,-4088],#[-4088,-4088],#[-4088,-4088],#[-2032,-2032],#[-4088,-4088],#[-4088,-4088],#[-2032,-2032],#[24,24],#[24,24],#[24,24],#[-4088,-4088],#[-2032,-2032],#[24,24],#[-2032,-2032],#[-2032,-2032],#[-4088,-4088],#[-2032,-2032],#[-2032,-2032],#[24,24],#[-2032,-2032],#[-4088,-4088],#[24,24],#[-4088,-4088],#[-4088,-4088],#[-2032,-2032],#[-6144,-6144],#[-6144,-6144],#[-6144,-6144],#[-2032,-2032],#[-4088,-4088],#[-4088,-4088],#[-4088,-4088],#[-4088,-4088],#[24,24],#[-2032,-2032],#[-2032,-2032],#[-4088,-4088],#[-2032,-2032],#[-2032,-2032],#[-2032,-2032],#[24,24],#[-4088,-4088],#[24,24],#[24,24],#[24,24],#[-2032,-2032],#[-2032,-2032],#[-4088,-4088],#[24,24],#[-2032,-2032],#[-2032,-2032],#[-2032,-2032],#[-2032,-2032],#[24,24],#[-4088,-4088],#[24,24],#[24,24],#[-2032,-2032],#[-4088,-4088],#[-2032,-2032],#[-4088,-4088],#[-6144,-6144],#[-4088,-4088],#[-2032,-2032],#[-2032,-2032],#[-4088,-4088],#[-2032,-2032],#[24,24],#[-2032,-2032],#[24,24],#[24,24],#[24,24],#[24,24],#[-2032,-2032],#[24,24],#[-2032,-2032],#[-4088,-4088],#[-4088,-4088],#[-2032,-2032],#[-2032,-2032],#[-4088,-4088],#[-4088,-4088],#[-4088,-4088],#[-4088,-4088],#[-6144,-6144],#[24,24],#[-2032,-2032],#[-2032,-2032],#[-2032,-2032]]
private def destData : Array (Array (Fin 159)) := #[#[0,0,1,0,0,0,0,0,0,0,0,0],#[0,0,0,0,2,0,3,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,0,5,0],#[6,0,7,0,0,0,0,0,0,0,0,0],#[0,0,0,0,8,0,9,0,0,0,0,0],#[0,0,0,0,0,0,0,0,10,0,11,0],#[9,12,13,14,0,0,0,0,0,0,0,0],#[0,0,0,0,11,15,16,17,0,0,0,0],#[0,0,0,0,0,0,0,0,18,19,20,21],#[6,22,7,23,0,0,0,0,0,0,0,0],#[0,0,0,0,8,24,22,0,0,0,0,0],#[0,0,0,0,0,0,0,0,23,0,24,0],#[9,25,13,26,0,0,0,0,0,0,0,0],#[0,0,0,0,8,24,22,0,0,0,0,0],#[0,0,0,0,11,27,17,0,0,0,0,0],#[0,0,0,0,0,0,0,0,19,0,21,0],#[28,0,29,0,0,0,0,0,0,0,0,0],#[9,0,13,0,0,0,0,0,0,0,0,0],#[0,0,0,0,30,0,31,0,0,0,0,0],#[0,0,0,0,11,0,22,32,0,0,0,0],#[0,0,0,0,0,0,0,0,33,0,34,0],#[0,0,0,0,0,0,0,0,23,35,24,36],#[37,22,33,23,0,0,0,0,0,0,0,0],#[0,0,0,0,38,24,22,32,0,0,0,0],#[0,0,0,0,0,0,0,0,23,35,24,36],#[39,0,40,0,0,0,0,0,0,0,0,0],#[0,0,0,0,41,0,25,0,0,0,0,0],#[0,0,0,0,0,0,0,0,26,0,27,0],#[42,0,29,0,0,0,0,0,0,0,0,0],#[0,0,0,0,30,0,16,0,0,0,0,0],#[0,0,0,0,0,0,0,0,18,0,20,0],#[43,0,18,0,0,0,0,0,0,0,0,0],#[32,44,45,46,0,0,0,0,0,0,0,0],#[0,0,0,0,20,0,28,25,0,0,0,0],#[0,0,0,0,0,0,0,0,29,26,30,27],#[0,0,0,0,36,47,48,0,0,0,0,0],#[0,0,0,0,0,0,0,0,49,0,50,0],#[51,0,52,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,53,54,55,56],#[28,57,29,58,0,0,0,0,0,0,0,0],#[0,0,0,0,30,59,60,0,0,0,0,0],#[0,0,0,0,0,0,0,0,61,0,62,0],#[63,0,64,0,0,0,0,0,0,0,0,0],#[63,0,64,0,0,0,0,0,0,0,0,0],#[65,66,67,68,0,0,0,0,0,0,0,0],#[0,0,0,0,69,70,71,0,0,0,0,0],#[0,0,0,0,72,73,74,75,0,0,0,0],#[0,0,0,0,0,0,0,0,29,76,30,62],#[39,0,40,0,0,0,0,0,0,0,0,0],#[0,0,0,0,41,0,57,0,0,0,0,0],#[0,0,0,0,0,0,0,0,58,0,47,0],#[77,0,78,0,0,0,0,0,0,0,0,0],#[0,0,0,0,55,0,79,0,0,0,0,0],#[0,0,0,0,55,0,43,0,0,0,0,0],#[0,0,0,0,80,0,81,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,82,0],#[0,0,0,0,0,0,0,0,83,0,84,0],#[48,60,49,61,0,0,0,0,0,0,0,0],#[0,0,0,0,85,62,28,60,0,0,0,0],#[0,0,0,0,0,0,0,0,53,86,55,87],#[31,48,33,49,0,0,0,0,0,0,0,0],#[0,0,0,0,34,50,16,0,0,0,0,0],#[0,0,0,0,0,0,0,0,18,0,20,0],#[77,0,78,0,0,0,0,0,0,0,0,0],#[0,0,0,0,55,0,51,0,0,0,0,0],#[88,0,89,0,0,0,0,0,0,0,0,0],#[37,90,91,92,0,0,0,0,0,0,0,0],#[0,0,0,0,93,0,94,0,0,0,0,0],#[0,0,0,0,38,85,51,0,0,0,0,0],#[0,0,0,0,0,0,0,0,95,0,96,0],#[0,0,0,0,0,0,0,0,64,97,98,99],#[100,0,101,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,102,0,103,0],#[0,0,0,0,0,0,0,0,104,0,105,0],#[106,0,107,0,0,0,0,0,0,0,0,0],#[108,65,109,67,0,0,0,0,0,0,0,0],#[0,0,0,0,110,111,112,0,0,0,0,0],#[77,0,53,0,0,0,0,0,0,0,0,0],#[0,0,0,0,113,0,112,0,0,0,0,0],#[112,0,114,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,115,0,116,0],#[117,0,101,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,118,0,38,0],#[0,0,0,0,80,0,119,0,0,0,0,0],#[0,0,0,0,0,0,0,0,83,0,120,0],#[0,0,0,0,0,0,0,0,121,0,122,0],#[0,0,0,0,123,124,43,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,82,0],#[77,44,107,125,0,0,0,0,0,0,0,0],#[0,0,0,0,98,103,66,0,0,0,0,0],#[117,0,101,0,0,0,0,0,0,0,0,0],#[0,0,0,0,126,0,42,81,0,0,0,0],#[0,0,0,0,80,0,127,0,0,0,0,0],#[0,0,0,0,0,0,0,0,86,0,87,0],#[128,129,130,76,0,0,0,0,0,0,0,0],#[0,0,0,0,131,0,132,0,0,0,0,0],#[0,0,0,0,0,0,0,0,133,0,134,0],#[0,0,0,0,135,96,136,0,0,0,0,0],#[0,0,0,0,0,0,0,0,137,0,82,0],#[0,0,0,0,0,0,0,0,114,0,82,0],#[42,127,53,121,0,0,0,0,0,0,0,0],#[0,0,0,0,55,122,138,0,0,0,0,0],#[0,0,0,0,96,99,77,66,0,0,0,0],#[0,0,0,0,0,0,0,0,78,76,113,116],#[0,0,0,0,98,0,108,0,0,0,0,0],#[0,0,0,0,0,0,0,0,139,0,110,0],#[42,0,53,0,0,0,0,0,0,0,0,0],#[0,0,0,0,140,0,51,0,0,0,0,0],#[43,0,141,0,0,0,0,0,0,0,0,0],#[0,0,0,0,142,0,63,119,0,0,0,0],#[0,0,0,0,0,0,0,0,64,83,140,120],#[0,0,0,0,0,0,0,0,143,0,59,0],#[77,0,53,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,142,0],#[0,0,0,0,113,0,144,0,0,0,0,0],#[0,0,0,0,123,124,51,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,142,0],#[77,145,78,133,0,0,0,0,0,0,0,0],#[0,0,0,0,126,0,63,119,0,0,0,0],#[146,0,147,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,54,0,56,0],#[0,0,0,0,124,87,42,148,0,0,0,0],#[0,0,0,0,0,0,0,0,64,115,113,116],#[0,0,0,0,0,0,0,0,64,83,113,84],#[0,0,0,0,0,0,0,0,143,0,134,0],#[0,0,0,0,85,149,63,138,0,0,0,0],#[0,0,0,0,0,0,0,0,118,0,110,0],#[150,138,151,115,0,0,0,0,0,0,0,0],#[146,0,152,0,0,0,0,0,0,0,0,0],#[144,128,91,92,0,0,0,0,0,0,0,0],#[0,0,0,0,153,0,145,0,0,0,0,0],#[0,0,0,0,0,0,0,0,76,0,116,0],#[90,148,92,86,0,0,0,0,0,0,0,0],#[0,0,0,0,111,116,77,129,0,0,0,0],#[0,0,0,0,0,0,0,0,64,115,140,149],#[0,0,0,0,0,0,0,0,78,154,113,84],#[42,0,53,0,0,0,0,0,0,0,0,0],#[0,0,0,0,155,0,156,0,0,0,0,0],#[144,128,139,130,0,0,0,0,0,0,0,0],#[0,0,0,0,82,0,77,157,0,0,0,0],#[0,0,0,0,0,0,0,0,141,0,126,0],#[0,0,0,0,55,0,37,0,0,0,0,0],#[0,0,0,0,0,0,0,0,91,0,123,0],#[0,0,0,0,124,87,63,138,0,0,0,0],#[112,0,141,0,0,0,0,0,0,0,0,0],#[128,129,92,86,0,0,0,0,0,0,0,0],#[77,145,53,121,0,0,0,0,0,0,0,0],#[0,0,0,0,113,134,129,0,0,0,0,0],#[79,150,118,151,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,141,0,126,0],#[146,0,147,0,0,0,0,0,0,0,0,0],#[0,0,0,0,80,0,94,0,0,0,0,0],#[0,0,0,0,55,122,148,0,0,0,0,0],#[0,0,0,0,0,0,0,0,115,0,149,0],#[0,0,0,0,153,0,157,0,0,0,0,0],#[0,0,0,0,0,0,0,0,52,0,105,0],#[136,0,158,0,0,0,0,0,0,0,0,0],#[146,0,152,0,0,0,0,0,0,0,0,0],#[0,0,0,0,140,0,79,0,0,0,0,0]]
private def parentData : Array (Array (Fin 16)) := #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0],#[3,3,0,0,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,3,3,0,0,3,3,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,6,6,0,0],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,3,3,3,3,3,3,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,0,0,7,7,7,7,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[8,8,8,8,8,8,8,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,0,0,7,7,7,7,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[11,11,11,11,11,11,11,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,12,12,12,12,12,12,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,12,12,12,12,12,12,12,12,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7],#[7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4],#[7,7,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,7,7,7,7,7,7,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,7,7,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0],#[12,12,0,0,12,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[15,15,15,15,15,15,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,15,15,15,15,15,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,10,0,0,10,10,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,10,10,10,10,10,10,10],#[11,11,0,0,11,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,10,0,0,10,10,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,10,0,0,10,10,0,0],#[11,11,0,0,11,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[11,11,11,11,11,11,11,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0],#[9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0],#[4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0],#[0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0],#[10,10,10,10,10,10,10,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,11,11,11,11,11,11,0,0,0,0,0,0,0,0,0,0],#[4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,5,5,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0],#[5,5,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,11,11,0,0,11,11,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0],#[0,0,0,0,0,0,0,0,11,11,11,11,11,11,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0],#[15,15,15,15,15,15,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,9,9,9,9,9,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,11,11,11,11,11,11,11,11,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,15,15,15,15,15,15],#[0,0,0,0,0,0,0,0,11,11,0,0,11,11,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0],#[15,15,0,0,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0,0,0,0,0,0,0,0,0],#[15,15,0,0,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,15,0,0,15,15,15,15,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,9,9,9,9,9,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[5,5,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,9,9,0,0,9,9,9,9,0,0,0,0,0,0,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0],#[0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,9,9,9,9,9,9],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,9,9,9,9,9,9],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0],#[0,0,0,0,0,0,0,0,15,15,15,15,15,15,15,15,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0],#[4,4,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[9,9,9,9,9,9,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0],#[15,15,15,15,15,15,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,5,5],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,15,15,15,15,15,15,15],#[15,15,0,0,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,12,12,0,0,12,12,0,0,0,0,0,0,0,0,0,0],#[5,5,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,4,0,0,4,4,4,4,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0],#[0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0],#[0,0,0,0,0,0,0,0,9,9,9,9,9,9,9,9,0,0,0,0,0,0,0,0],#[9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[9,9,9,9,9,9,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[9,9,9,9,9,9,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0],#[4,4,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0],#[5,5,0,0,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,5,5,5,5,5,5,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,5,0,0],#[0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,10,0,0,10,10,0,0],#[11,11,0,0,11,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[9,9,0,0,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,15,15,0,0,15,15,0,0,0,0,0,0,0,0,0,0]]
private def finishData : Array (Fin 16) := #[0,1,0,3,3,0,7,7,0,7,3,0,7,7,7,0,7,7,7,7,0,0,7,7,0,7,7,0,7,7,0,7,0,7,0,0,0,4,0,0,0,0,4,4,11,0,12,0,7,7,0,5,9,5,5,0,0,7,7,0,7,7,0,5,9,12,15,15,15,0,0,11,0,0,11,11,4,9,4,5,0,4,0,9,0,0,5,0,0,0,4,5,5,0,5,11,0,11,0,0,0,0,11,0,11,0,15,15,15,15,0,0,9,0,4,9,0,0,9,5,0,5,0,0,0,15,0,4,9,9,4,0,15,4,0,0,15,12,5,4,0,5,0,9,9,9,0,0,4,0,5,9,0,0,4,0,11,9,15]
private def jData : Array ℤ := #[0,3072,3072,15,-3072,-3072,0,-3072,0,-3072,-1963,-3018,-2964,-3042,-3072,-2017]
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 16) (d : ℕ) : List (Fin 16) := nextData[s.val*2+(digit d).val]?.getD []
def nextTable (s : Fin 16) (d : ℕ) : Finset (Fin 16) := (nextList s d).toFinset
def slot (s : Fin 16) (d : ℕ) (t : Fin 16) : ℕ := if t=(nextList s d).getD 0 0 then 0 else 1
def W (s : Fin 16) (d : ℕ) (t : Fin 16) : ℤ := (weightData[s.val]?.getD #[])[(digit d).val*2+slot s d t]?.getD 0
def source (p : Fin 159) : Fin 16 := sourceData[p.val]?.getD 0
def carry (p : Fin 159) : ℕ := carryData[p.val]?.getD 0
def endsList (p : Fin 159) : List (Fin 16) := endData[p.val]?.getD []
def ends (p : Fin 159) : Finset (Fin 16) := (endsList p).toFinset
def eslot (p : Fin 159) (t : Fin 16) : ℕ := if t=(endsList p).getD 0 0 then 0 else 1
def H (p : Fin 159) (t : Fin 16) : ℤ := (hData[p.val]?.getD #[])[eslot p t]?.getD 0
def index (p : Fin 159) (d cp : ℕ) (sp : Fin 16) : ℕ := ((digit d).val*3+cp)*2+slot (source p) d sp
def target (p : Fin 159) (d cp : ℕ) (sp : Fin 16) : Fin 159 := (destData[p.val]?.getD #[])[index p d cp sp]?.getD 0
def parent (p : Fin 159) (d cp : ℕ) (sp tp : Fin 16) : Fin 16 :=
  (parentData[p.val]?.getD #[])[(index p d cp sp)*2+eslot (target p d cp sp) tp]?.getD 0
def finish (p : Fin 159) : Fin 16 := finishData[p.val]?.getD 0
def J (s : Fin 16) : ℤ := jData[s.val]?.getD 0
def F (s : Fin 16) : Prop := s.val ∈ [0,1,2,3,4,5,6,7,9,11,12,13,14,15]
instance (s : Fin 16) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 16) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/24

private def familyData : Array (Finset (Fin 16)) := #[{0},{1},{2},{2,3,4,5,7,8,9,10,11,12,13,14,15},{2,3,4,5,7,8,9,10,11,12,13,15},{2,3,4,5,7,8,9,10,11,12,14,15},{2,3,4,5,7,9,10,11,12,13,14},{2,3,4,5,7,9,10,11,12,13,14,15},{2,3,4,5,7,9,10,12,13,14,15},{2,3,4,5,7,9,10,13},{2,3,4,5,7,9,11,13,14},{2,3,4,5,7,9,14},{2,3,4,5,7,14},{2,3,4,7,10,13},{2,3,7,14},{2,4,5,7},{2,4,5,7,8,9,10,11,12,15},{2,4,5,7,8,9,11,12,15},{2,7},{2,7,9},{3},{3,4,5,7,8,9,10,11},{3,4,5,7,8,9,10,11,12},{3,4,5,7,8,9,10,11,12,13,15},{3,4,5,7,8,9,10,11,12,15},{3,4,5,7,9,13},{3,4,7},{3,4,7,8,9,10,11},{3,4,7,8,9,10,11,12},{3,4,7,8,9,11},{3,4,7,9,13},{3,4,7,13},{3,9},{3,13},{4,5,6,7,8,9,11,12,14,15},{4,5,6,7,8,9,11,14,15},{4,5,6,7,8,9,14},{4,5,6,7,8,9,14,15},{4,5,7},{4,5,7,8,9,10,11},{4,5,7,8,9,10,11,12},{4,5,7,8,9,10,11,12,15},{4,5,7,8,9,11,12,14},{4,5,7,8,9,11,12,14,15},{4,5,7,8,9,11,12,15},{4,5,7,8,9,12,14},{4,5,7,8,9,12,14,15},{4,5,7,8,9,14},{4,5,7,8,10,11},{4,5,7,8,10,11,12,15},{4,5,7,8,11},{4,5,7,8,11,12,14},{4,5,7,8,11,12,15},{4,5,7,8,12,14},{4,5,7,9},{4,7},{4,7,8},{4,7,8,9,10,11},{4,7,8,9,10,11,12},{4,7,8,9,10,11,12,15},{4,7,8,9,11,12,14},{4,7,8,9,11,12,14,15},{4,7,8,9,12,14,15},{4,7,8,9,14},{4,7,8,10,11},{4,7,8,10,11,12,15},{4,7,8,11},{4,7,8,11,12,14},{4,7,8,12},{4,7,8,12,14},{4,7,9},{5,6},{5,6,7,8},{5,6,7,8,9,14},{5,6,7,8,9,14,15},{5,6,7,8,14},{5,7},{5,7,8,9,11,12,14},{5,7,8,9,11,12,14,15},{5,7,8,9,11,12,15},{5,7,8,9,12,14},{5,7,8,9,12,14,15},{5,7,8,9,14},{5,7,8,11,12,14},{5,7,8,12,14},{6,7},{6,7,8,9,14},{7},{7,8},{7,8,9,11,12,14},{7,8,9,11,12,14,15},{7,8,9,11,12,15},{7,8,9,12,14},{7,8,9,12,14,15},{7,8,9,14},{7,8,11,12},{7,8,12}]
def memberSet (i : Fin 97) : Finset (Fin 16) := familyData[i.val]?.getD ∅
private def covDestData : Array (Fin 97) := #[0,1,2,20,33,71,3,34,3,34,4,34,7,35,7,35,6,35,10,37,8,37,9,36,9,36,10,74,13,75,25,36,23,34,23,34,31,72,30,72,18,87,17,46,16,43,5,34,16,43,11,36,15,94,17,81,16,78,17,81,11,73,12,86,19,76,14,85,24,43,24,46,21,45,22,45,54,63,44,46,41,43,41,43,41,43,41,43,41,43,39,42,40,42,39,45,44,62,41,43,44,62,41,61,41,43,39,60,54,47,38,94,50,92,44,81,41,78,41,78,41,78,41,78,40,77,39,80,44,93,41,78,52,93,49,90,48,89,48,89,54,82,32,56,29,68,27,53,28,53,27,69,70,56,59,43,59,43,59,44,57,51,58,51,57,53,59,61,57,67,26,88,27,84,55,88,66,96,59,78,59,78,59,79,57,83,58,83,57,84,65,91,64,95]
def covDest (i : Fin 97) (d : Fin 2) : Fin 97 := covDestData[i.val*2+d.val]?.getD 0
def family : Finset (Finset (Fin 16)) := Finset.univ.image memberSet
lemma coverage_steps : ∀ i (d : Fin 2), nextSet D (memberSet i) d.val=memberSet (covDest i d) := by decide +kernel
lemma coverage_accepting : ∀ i : Fin 97, ∃ t, t ∈ memberSet i ∧ F t := by decide +kernel

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

def R (s : Fin 16) (p : Fin 159) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 16) (p : Fin 159) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_profiles : R 0 0 0 ∧ R 0 1 1 ∧ R 0 2 2 := by decide +kernel
lemma seed_zero : ∀ t ∈ ends 0, t=0 ∧ 0 ≤ H 0 t := by decide +kernel
lemma seed_one : ∀ t ∈ ends 1, t=1 ∧ W 0 1 1 ≤ H 1 t := by decide +kernel
lemma seed_two : ∀ t ∈ ends 2, t ∈ D.next 1 0 ∧ W 0 1 1+W 1 0 t ≤ H 2 t := by decide +kernel
lemma first_one : (1:Fin 16) ∈ D.next D.start 1 := by decide +kernel

def StepRow (p : Fin 159) : Prop := ∀ (d e : Fin 2) (cp : Fin 3),
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
lemma step_row_101 : StepRow 101 := by
  unfold StepRow R
  decide +kernel
lemma step_row_102 : StepRow 102 := by
  unfold StepRow R
  decide +kernel
lemma step_row_103 : StepRow 103 := by
  unfold StepRow R
  decide +kernel
lemma step_row_104 : StepRow 104 := by
  unfold StepRow R
  decide +kernel
lemma step_row_105 : StepRow 105 := by
  unfold StepRow R
  decide +kernel
lemma step_row_106 : StepRow 106 := by
  unfold StepRow R
  decide +kernel
lemma step_row_107 : StepRow 107 := by
  unfold StepRow R
  decide +kernel
lemma step_row_108 : StepRow 108 := by
  unfold StepRow R
  decide +kernel
lemma step_row_109 : StepRow 109 := by
  unfold StepRow R
  decide +kernel
lemma step_row_110 : StepRow 110 := by
  unfold StepRow R
  decide +kernel
lemma step_row_111 : StepRow 111 := by
  unfold StepRow R
  decide +kernel
lemma step_row_112 : StepRow 112 := by
  unfold StepRow R
  decide +kernel
lemma step_row_113 : StepRow 113 := by
  unfold StepRow R
  decide +kernel
lemma step_row_114 : StepRow 114 := by
  unfold StepRow R
  decide +kernel
lemma step_row_115 : StepRow 115 := by
  unfold StepRow R
  decide +kernel
lemma step_row_116 : StepRow 116 := by
  unfold StepRow R
  decide +kernel
lemma step_row_117 : StepRow 117 := by
  unfold StepRow R
  decide +kernel
lemma step_row_118 : StepRow 118 := by
  unfold StepRow R
  decide +kernel
lemma step_row_119 : StepRow 119 := by
  unfold StepRow R
  decide +kernel
lemma step_row_120 : StepRow 120 := by
  unfold StepRow R
  decide +kernel
lemma step_row_121 : StepRow 121 := by
  unfold StepRow R
  decide +kernel
lemma step_row_122 : StepRow 122 := by
  unfold StepRow R
  decide +kernel
lemma step_row_123 : StepRow 123 := by
  unfold StepRow R
  decide +kernel
lemma step_row_124 : StepRow 124 := by
  unfold StepRow R
  decide +kernel
lemma step_row_125 : StepRow 125 := by
  unfold StepRow R
  decide +kernel
lemma step_row_126 : StepRow 126 := by
  unfold StepRow R
  decide +kernel
lemma step_row_127 : StepRow 127 := by
  unfold StepRow R
  decide +kernel
lemma step_row_128 : StepRow 128 := by
  unfold StepRow R
  decide +kernel
lemma step_row_129 : StepRow 129 := by
  unfold StepRow R
  decide +kernel
lemma step_row_130 : StepRow 130 := by
  unfold StepRow R
  decide +kernel
lemma step_row_131 : StepRow 131 := by
  unfold StepRow R
  decide +kernel
lemma step_row_132 : StepRow 132 := by
  unfold StepRow R
  decide +kernel
lemma step_row_133 : StepRow 133 := by
  unfold StepRow R
  decide +kernel
lemma step_row_134 : StepRow 134 := by
  unfold StepRow R
  decide +kernel
lemma step_row_135 : StepRow 135 := by
  unfold StepRow R
  decide +kernel
lemma step_row_136 : StepRow 136 := by
  unfold StepRow R
  decide +kernel
lemma step_row_137 : StepRow 137 := by
  unfold StepRow R
  decide +kernel
lemma step_row_138 : StepRow 138 := by
  unfold StepRow R
  decide +kernel
lemma step_row_139 : StepRow 139 := by
  unfold StepRow R
  decide +kernel
lemma step_row_140 : StepRow 140 := by
  unfold StepRow R
  decide +kernel
lemma step_row_141 : StepRow 141 := by
  unfold StepRow R
  decide +kernel
lemma step_row_142 : StepRow 142 := by
  unfold StepRow R
  decide +kernel
lemma step_row_143 : StepRow 143 := by
  unfold StepRow R
  decide +kernel
lemma step_row_144 : StepRow 144 := by
  unfold StepRow R
  decide +kernel
lemma step_row_145 : StepRow 145 := by
  unfold StepRow R
  decide +kernel
lemma step_row_146 : StepRow 146 := by
  unfold StepRow R
  decide +kernel
lemma step_row_147 : StepRow 147 := by
  unfold StepRow R
  decide +kernel
lemma step_row_148 : StepRow 148 := by
  unfold StepRow R
  decide +kernel
lemma step_row_149 : StepRow 149 := by
  unfold StepRow R
  decide +kernel
lemma step_row_150 : StepRow 150 := by
  unfold StepRow R
  decide +kernel
lemma step_row_151 : StepRow 151 := by
  unfold StepRow R
  decide +kernel
lemma step_row_152 : StepRow 152 := by
  unfold StepRow R
  decide +kernel
lemma step_row_153 : StepRow 153 := by
  unfold StepRow R
  decide +kernel
lemma step_row_154 : StepRow 154 := by
  unfold StepRow R
  decide +kernel
lemma step_row_155 : StepRow 155 := by
  unfold StepRow R
  decide +kernel
lemma step_row_156 : StepRow 156 := by
  unfold StepRow R
  decide +kernel
lemma step_row_157 : StepRow 157 := by
  unfold StepRow R
  decide +kernel
lemma step_row_158 : StepRow 158 := by
  unfold StepRow R
  decide +kernel
lemma step_checks : ∀ p : Fin 159, StepRow p := by
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
  · exact step_row_106
  · exact step_row_107
  · exact step_row_108
  · exact step_row_109
  · exact step_row_110
  · exact step_row_111
  · exact step_row_112
  · exact step_row_113
  · exact step_row_114
  · exact step_row_115
  · exact step_row_116
  · exact step_row_117
  · exact step_row_118
  · exact step_row_119
  · exact step_row_120
  · exact step_row_121
  · exact step_row_122
  · exact step_row_123
  · exact step_row_124
  · exact step_row_125
  · exact step_row_126
  · exact step_row_127
  · exact step_row_128
  · exact step_row_129
  · exact step_row_130
  · exact step_row_131
  · exact step_row_132
  · exact step_row_133
  · exact step_row_134
  · exact step_row_135
  · exact step_row_136
  · exact step_row_137
  · exact step_row_138
  · exact step_row_139
  · exact step_row_140
  · exact step_row_141
  · exact step_row_142
  · exact step_row_143
  · exact step_row_144
  · exact step_row_145
  · exact step_row_146
  · exact step_row_147
  · exact step_row_148
  · exact step_row_149
  · exact step_row_150
  · exact step_row_151
  · exact step_row_152
  · exact step_row_153
  · exact step_row_154
  · exact step_row_155
  · exact step_row_156
  · exact step_row_157
  · exact step_row_158

lemma finish_checks : ∀ p : Fin 159, carry p < 2 → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 24 := by decide +kernel

def construction : Erdos406BinaryProfileMinplus.Construction D F (Fin 159) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/24
  seed := by
    intro c hc
    interval_cases c
    · refine ⟨0,seed_profiles.1,?_⟩
      intro t ht
      obtain ⟨rfl,hh⟩ := seed_zero t ht
      refine ⟨0,?_,?_⟩
      · simpa [D] using Run.nil (D:=D) (0:Fin 16)
      · have hR : (0:ℝ) ≤ H 0 0 := by exact_mod_cast hh
        exact div_nonneg hR (by norm_num)
    · refine ⟨1,seed_profiles.2.1,?_⟩
      intro t ht
      obtain ⟨rfl,hh⟩ := seed_one t ht
      refine ⟨(W 0 1 1:ℝ)/24,?_,?_⟩
      · have hr := Run.cons first_one (Run.nil (D:=D) 1)
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ) ≤ H 1 1 := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/24 ≤ (H 1 1:ℝ)/24
        linarith
    · refine ⟨2,seed_profiles.2.2,?_⟩
      intro t ht
      obtain ⟨he,hh⟩ := seed_two t ht
      refine ⟨(W 0 1 1:ℝ)/24+(W 1 0 t:ℝ)/24,?_,?_⟩
      · have hr := Run.cons first_one (Run.cons he (Run.nil (D:=D) t))
        simpa [D,Nat.digits_of_two_le_of_pos] using hr
      · have hR : (W 0 1 1:ℝ)+W 1 0 t ≤ H 2 t := by exact_mod_cast hh
        change (W 0 1 1:ℝ)/24+(W 1 0 t:ℝ)/24 ≤ (H 2 t:ℝ)/24
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
    change (H p (parent p d cp sp tp):ℝ)/24+(W (parent p d cp sp tp) e tp:ℝ)/24-
      (W (source p) d sp:ℝ)/24 ≤ (H (target p d cp sp) tp:ℝ)/24
    linarith
  finish := by
    intro s p c hc hr hf
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨ht,hf',hh⟩ := finish_checks p hc hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 24 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/24 ≤ 1
    linarith

def G (s : Fin 16) : Prop := s.val ∈ [1,2,3,4,5,7,9,10,11,12,13,14,15]
def Z (s : Fin 16) : Prop := s.val ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
instance (s : Fin 16) : Decidable (G s) := by unfold G; infer_instance
instance (s : Fin 16) : Decidable (Z s) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s t, G s → t ∈ D.next s 0 → G t) ∧
    (∀ t, F t → Z t) ∧
    (∀ s t, Z t → t ∈ D.next s 0 → Z s) ∧
    (∀ s t, G s → Z t → t ∈ D.next s 0 → 15+J t-J s ≤ W s 0 t) ∧
    (∀ s t, s ∈ D.next D.start 1 → G t → F t → Z s → -9216 ≤ W D.start 1 s+J t-J s) := by decide +kernel

def powerBound : PowerBound D F where
  a := 15/24
  B := 384
  G := G
  Z := Z
  J s := (J s:ℝ)/24
  start := power_checks.1
  forward := power_checks.2.1
  accepting := power_checks.2.2.1
  backward := power_checks.2.2.2.1
  lower_step := by
    intro s t hs hz he
    have hh : (15:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s t hs hz he
    change (15/24:ℝ)+(J t:ℝ)/24-(J s:ℝ)/24 ≤ (W s 0 t:ℝ)/24
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-9216:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2.2.2 s t hs ht hf hz
    change -(384:ℝ) ≤ (W D.start 1 s:ℝ)/24+(J t:ℝ)/24-(J s:ℝ)/24
    linarith

def V (n : ℕ) : ℝ := value D F total n
lemma construction_bound (n d : ℕ) (hd : d<2) : V (3*n+d) ≤ V n+1 := construction.construction_bound total n d hd
lemma power_lower (k : ℕ) : (15/24:ℝ)*k-384 ≤ V (2^k) := powerBound.power_lower total k

lemma not_supercritical : ¬ Real.log 2 < (15/24:ℝ)*Real.log 3 := by
  have hh : (3:ℝ)^5 ≤ (2:ℝ)^8 := by norm_num
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^5) hh
  rw [Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos406BinaryAcceptingProfileControl
