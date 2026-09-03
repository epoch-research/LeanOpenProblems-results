import Submission.FiveKernel3

/-! Explicit relabellings of the surviving five-color words to orbit representatives.
Coverage is tied to the independently checked good-key catalogue. -/
open scoped Classical
namespace Erdos184Work.FiveWordOrbits3
open LabelKernel Erdos184Serial CanonicalThreeReduction
open FiveRows3
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

abbrev Cases := Fin 24
abbrev Representatives := Fin 2
def caseKey : Cases → Fin 62208 := ![35235,35236,35237,35373,35374,35375,40851,40852,40853,40989,40990,40991,49530,49531,49532,49590,49591,49592,55146,55147,55148,55206,55207,55208]
def repKey : Representatives → Fin 62208 := ![35235,35237]
def orbit : Cases → Representatives := ![0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1]
def inputSource (i : Cases) : E → W := srcAt (digit0 (caseKey i).val) (digit1 (caseKey i).val) (digit2 (caseKey i).val) (digit3 (caseKey i).val) (digit4 (caseKey i).val)
def inputTarget (i : Cases) : E → W := dstAt (digit0 (caseKey i).val) (digit1 (caseKey i).val) (digit2 (caseKey i).val) (digit3 (caseKey i).val) (digit4 (caseKey i).val)
def repSrc0 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def repDst0 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def repSrc1 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def repDst1 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def representativeSource : Representatives → E → W := ![repSrc0,repSrc1]
def representativeTarget : Representatives → E → W := ![repDst0,repDst1]
def edge0 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def edgeInv0 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def vertex0 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv0 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color0 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge1 : E → E := ![12,11,10,14,13,18,17,16,15,19,5,9,8,7,6,0,4,3,2,1,22,23,20,21]
def edgeInv1 : E → E := ![15,19,18,17,16,10,14,13,12,11,2,1,0,4,3,8,7,6,5,9,22,23,20,21]
def vertex1 : W → W := ![0,1,27,26,14,5,4,7,28,9,10,11,12,13,16,15,6,17,38,19,20,21,22,23,24,25,2,3,18,29,30,31,32,33,34,35,36,37,8,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv1 : W → W := ![0,1,26,27,6,5,16,7,38,9,10,11,12,13,4,15,14,17,28,19,20,21,22,23,24,25,3,2,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color1 : Fin 5 → Fin 5 := ![2,3,1,0,4]
def edge2 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def edgeInv2 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def vertex2 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv2 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color2 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge3 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def edgeInv3 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def vertex3 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv3 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color3 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge4 : E → E := ![12,11,10,14,13,18,17,16,15,19,5,9,8,7,6,1,2,3,4,0,22,23,20,21]
def edgeInv4 : E → E := ![19,15,16,17,18,10,14,13,12,11,2,1,0,4,3,8,7,6,5,9,22,23,20,21]
def vertex4 : W → W := ![0,1,27,26,14,5,4,7,28,9,10,11,12,13,16,15,6,17,38,19,20,21,22,23,24,25,3,2,18,29,30,31,32,33,34,35,36,37,8,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv4 : W → W := ![0,1,27,26,6,5,16,7,38,9,10,11,12,13,4,15,14,17,28,19,20,21,22,23,24,25,3,2,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color4 : Fin 5 → Fin 5 := ![2,3,1,0,4]
def edge5 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def edgeInv5 : E → E := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def vertex5 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv5 : W → W := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color5 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge6 : E → E := ![1,0,4,3,2,8,9,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def edgeInv6 : E → E := ![1,0,4,3,2,7,8,9,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def vertex6 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv6 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color6 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge7 : E → E := ![11,12,13,14,10,15,19,18,17,16,5,9,8,7,6,0,4,3,2,1,22,23,20,21]
def edgeInv7 : E → E := ![15,19,18,17,16,10,14,13,12,11,4,0,1,2,3,5,9,8,7,6,22,23,20,21]
def vertex7 : W → W := ![0,1,26,27,14,5,4,7,28,9,10,11,12,13,16,15,6,17,38,19,20,21,22,23,24,25,2,3,18,29,30,31,32,33,34,35,36,37,8,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv7 : W → W := ![0,1,26,27,6,5,16,7,38,9,10,11,12,13,4,15,14,17,28,19,20,21,22,23,24,25,2,3,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color7 : Fin 5 → Fin 5 := ![2,3,1,0,4]
def edge8 : E → E := ![1,0,4,3,2,8,9,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def edgeInv8 : E → E := ![1,0,4,3,2,7,8,9,5,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def vertex8 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv8 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color8 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge9 : E → E := ![1,0,4,3,2,8,9,5,6,7,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def edgeInv9 : E → E := ![1,0,4,3,2,7,8,9,5,6,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def vertex9 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv9 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color9 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge10 : E → E := ![11,12,13,14,10,15,19,18,17,16,5,9,8,7,6,1,2,3,4,0,22,23,20,21]
def edgeInv10 : E → E := ![19,15,16,17,18,10,14,13,12,11,4,0,1,2,3,5,9,8,7,6,22,23,20,21]
def vertex10 : W → W := ![0,1,26,27,14,5,4,7,28,9,10,11,12,13,16,15,6,17,38,19,20,21,22,23,24,25,3,2,18,29,30,31,32,33,34,35,36,37,8,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv10 : W → W := ![0,1,27,26,6,5,16,7,38,9,10,11,12,13,4,15,14,17,28,19,20,21,22,23,24,25,2,3,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color10 : Fin 5 → Fin 5 := ![2,3,1,0,4]
def edge11 : E → E := ![1,0,4,3,2,8,9,5,6,7,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def edgeInv11 : E → E := ![1,0,4,3,2,7,8,9,5,6,10,11,12,13,14,19,18,17,16,15,20,21,22,23]
def vertex11 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv11 : W → W := ![0,1,3,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def color11 : Fin 5 → Fin 5 := ![0,1,2,3,4]
def edge12 : E → E := ![10,14,13,12,11,15,19,18,17,16,1,2,3,4,0,5,9,8,7,6,22,23,20,21]
def edgeInv12 : E → E := ![14,10,11,12,13,15,19,18,17,16,0,4,3,2,1,5,9,8,7,6,22,23,20,21]
def vertex12 : W → W := ![0,1,26,27,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,3,2,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv12 : W → W := ![0,1,27,26,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,2,3,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color12 : Fin 5 → Fin 5 := ![2,3,0,1,4]
def edge13 : E → E := ![2,3,4,0,1,8,9,5,6,7,19,18,17,16,15,10,11,12,13,14,20,21,22,23]
def edgeInv13 : E → E := ![3,4,0,1,2,7,8,9,5,6,15,16,17,18,19,14,13,12,11,10,20,21,22,23]
def vertex13 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv13 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color13 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge14 : E → E := ![2,3,4,0,1,8,9,5,6,7,19,18,17,16,15,10,11,12,13,14,23,22,21,20]
def edgeInv14 : E → E := ![3,4,0,1,2,7,8,9,5,6,15,16,17,18,19,14,13,12,11,10,23,22,21,20]
def vertex14 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv14 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color14 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge15 : E → E := ![10,14,13,12,11,15,19,18,17,16,0,4,3,2,1,5,9,8,7,6,22,23,20,21]
def edgeInv15 : E → E := ![10,14,13,12,11,15,19,18,17,16,0,4,3,2,1,5,9,8,7,6,22,23,20,21]
def vertex15 : W → W := ![0,1,26,27,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,2,3,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv15 : W → W := ![0,1,26,27,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,2,3,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color15 : Fin 5 → Fin 5 := ![2,3,0,1,4]
def edge16 : E → E := ![2,3,4,0,1,8,9,5,6,7,15,16,17,18,19,10,11,12,13,14,20,21,22,23]
def edgeInv16 : E → E := ![3,4,0,1,2,7,8,9,5,6,15,16,17,18,19,10,11,12,13,14,20,21,22,23]
def vertex16 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv16 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color16 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge17 : E → E := ![2,3,4,0,1,8,9,5,6,7,15,16,17,18,19,10,11,12,13,14,23,22,21,20]
def edgeInv17 : E → E := ![3,4,0,1,2,7,8,9,5,6,15,16,17,18,19,10,11,12,13,14,23,22,21,20]
def vertex17 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv17 : W → W := ![0,1,3,2,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color17 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge18 : E → E := ![12,11,10,14,13,19,15,16,17,18,1,2,3,4,0,5,9,8,7,6,22,23,20,21]
def edgeInv18 : E → E := ![14,10,11,12,13,15,19,18,17,16,2,1,0,4,3,6,7,8,9,5,22,23,20,21]
def vertex18 : W → W := ![0,1,27,26,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,3,2,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv18 : W → W := ![0,1,27,26,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,3,2,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color18 : Fin 5 → Fin 5 := ![2,3,0,1,4]
def edge19 : E → E := ![0,1,2,3,4,9,8,7,6,5,19,18,17,16,15,10,11,12,13,14,20,21,22,23]
def edgeInv19 : E → E := ![0,1,2,3,4,9,8,7,6,5,15,16,17,18,19,14,13,12,11,10,20,21,22,23]
def vertex19 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv19 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color19 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge20 : E → E := ![0,1,2,3,4,9,8,7,6,5,19,18,17,16,15,10,11,12,13,14,23,22,21,20]
def edgeInv20 : E → E := ![0,1,2,3,4,9,8,7,6,5,15,16,17,18,19,14,13,12,11,10,23,22,21,20]
def vertex20 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv20 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,27,26,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color20 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge21 : E → E := ![12,11,10,14,13,19,15,16,17,18,0,4,3,2,1,5,9,8,7,6,22,23,20,21]
def edgeInv21 : E → E := ![10,14,13,12,11,15,19,18,17,16,2,1,0,4,3,6,7,8,9,5,22,23,20,21]
def vertex21 : W → W := ![0,1,27,26,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,2,3,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv21 : W → W := ![0,1,26,27,4,5,14,7,28,9,10,11,12,13,6,15,16,17,38,19,20,21,22,23,24,25,3,2,8,29,30,31,32,33,34,35,36,37,18,39,40,41,42,43,44,45,46,47,48,49]
def color21 : Fin 5 → Fin 5 := ![2,3,0,1,4]
def edge22 : E → E := ![0,1,2,3,4,9,8,7,6,5,15,16,17,18,19,10,11,12,13,14,20,21,22,23]
def edgeInv22 : E → E := ![0,1,2,3,4,9,8,7,6,5,15,16,17,18,19,10,11,12,13,14,20,21,22,23]
def vertex22 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv22 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color22 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edge23 : E → E := ![0,1,2,3,4,9,8,7,6,5,15,16,17,18,19,10,11,12,13,14,23,22,21,20]
def edgeInv23 : E → E := ![0,1,2,3,4,9,8,7,6,5,15,16,17,18,19,10,11,12,13,14,23,22,21,20]
def vertex23 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def vertexInv23 : W → W := ![0,1,2,3,6,5,4,7,8,9,10,11,12,13,16,15,14,17,18,19,20,21,22,23,24,25,26,27,38,29,30,31,32,33,34,35,36,37,28,39,40,41,42,43,44,45,46,47,48,49]
def color23 : Fin 5 → Fin 5 := ![0,1,3,2,4]
def edgeMap (i : Cases) : E → E := (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then edge0 else (if i.val < 2 then edge1 else edge2)) else (if i.val < 4 then edge3 else (if i.val < 5 then edge4 else edge5))) else (if i.val < 9 then (if i.val < 7 then edge6 else (if i.val < 8 then edge7 else edge8)) else (if i.val < 10 then edge9 else (if i.val < 11 then edge10 else edge11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then edge12 else (if i.val < 14 then edge13 else edge14)) else (if i.val < 16 then edge15 else (if i.val < 17 then edge16 else edge17))) else (if i.val < 21 then (if i.val < 19 then edge18 else (if i.val < 20 then edge19 else edge20)) else (if i.val < 22 then edge21 else (if i.val < 23 then edge22 else edge23)))))
def edgeInverse (i : Cases) : E → E := (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then edgeInv0 else (if i.val < 2 then edgeInv1 else edgeInv2)) else (if i.val < 4 then edgeInv3 else (if i.val < 5 then edgeInv4 else edgeInv5))) else (if i.val < 9 then (if i.val < 7 then edgeInv6 else (if i.val < 8 then edgeInv7 else edgeInv8)) else (if i.val < 10 then edgeInv9 else (if i.val < 11 then edgeInv10 else edgeInv11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then edgeInv12 else (if i.val < 14 then edgeInv13 else edgeInv14)) else (if i.val < 16 then edgeInv15 else (if i.val < 17 then edgeInv16 else edgeInv17))) else (if i.val < 21 then (if i.val < 19 then edgeInv18 else (if i.val < 20 then edgeInv19 else edgeInv20)) else (if i.val < 22 then edgeInv21 else (if i.val < 23 then edgeInv22 else edgeInv23)))))
def vertexMap (i : Cases) : W → W := (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then vertex0 else (if i.val < 2 then vertex1 else vertex2)) else (if i.val < 4 then vertex3 else (if i.val < 5 then vertex4 else vertex5))) else (if i.val < 9 then (if i.val < 7 then vertex6 else (if i.val < 8 then vertex7 else vertex8)) else (if i.val < 10 then vertex9 else (if i.val < 11 then vertex10 else vertex11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then vertex12 else (if i.val < 14 then vertex13 else vertex14)) else (if i.val < 16 then vertex15 else (if i.val < 17 then vertex16 else vertex17))) else (if i.val < 21 then (if i.val < 19 then vertex18 else (if i.val < 20 then vertex19 else vertex20)) else (if i.val < 22 then vertex21 else (if i.val < 23 then vertex22 else vertex23)))))
def vertexInverse (i : Cases) : W → W := (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then vertexInv0 else (if i.val < 2 then vertexInv1 else vertexInv2)) else (if i.val < 4 then vertexInv3 else (if i.val < 5 then vertexInv4 else vertexInv5))) else (if i.val < 9 then (if i.val < 7 then vertexInv6 else (if i.val < 8 then vertexInv7 else vertexInv8)) else (if i.val < 10 then vertexInv9 else (if i.val < 11 then vertexInv10 else vertexInv11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then vertexInv12 else (if i.val < 14 then vertexInv13 else vertexInv14)) else (if i.val < 16 then vertexInv15 else (if i.val < 17 then vertexInv16 else vertexInv17))) else (if i.val < 21 then (if i.val < 19 then vertexInv18 else (if i.val < 20 then vertexInv19 else vertexInv20)) else (if i.val < 22 then vertexInv21 else (if i.val < 23 then vertexInv22 else vertexInv23)))))
def colorMap (i : Cases) : Fin 5 → Fin 5 := (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then color0 else (if i.val < 2 then color1 else color2)) else (if i.val < 4 then color3 else (if i.val < 5 then color4 else color5))) else (if i.val < 9 then (if i.val < 7 then color6 else (if i.val < 8 then color7 else color8)) else (if i.val < 10 then color9 else (if i.val < 11 then color10 else color11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then color12 else (if i.val < 14 then color13 else color14)) else (if i.val < 16 then color15 else (if i.val < 17 then color16 else color17))) else (if i.val < 21 then (if i.val < 19 then color18 else (if i.val < 20 then color19 else color20)) else (if i.val < 22 then color21 else (if i.val < 23 then color22 else color23)))))

lemma good_eq : FiveRows3.good = Finset.univ.image caseKey := by decide +kernel
lemma edge_left : ∀ (i : Cases) (e : E), edgeInverse i (edgeMap i e) = e := by decide +kernel
lemma edge_right : ∀ (i : Cases) (e : E), edgeMap i (edgeInverse i e) = e := by decide +kernel
lemma vertex_left : ∀ (i : Cases) (v : W), vertexInverse i (vertexMap i v) = v := by decide +kernel
lemma endpoints_valid : ∀ (i : Cases) (e : E),
    s(vertexMap i (inputSource i e),vertexMap i (inputTarget i e)) =
      s(representativeSource (orbit i) (edgeMap i e),representativeTarget (orbit i) (edgeMap i e)) := by
  decide +kernel
lemma color_map : ∀ (i : Cases) (e : E),
    FlatCanonicalKernel.color b (edgeMap i e) = colorMap i (FlatCanonicalKernel.color b e) := by decide +kernel
lemma representative_src_row : ∀ (r : Representatives) (e : E),
    representativeSource r e = srcAt (digit0 (repKey r).val) (digit1 (repKey r).val) (digit2 (repKey r).val) (digit3 (repKey r).val) (digit4 (repKey r).val) e := by decide +kernel
lemma representative_dst_row : ∀ (r : Representatives) (e : E),
    representativeTarget r e = dstAt (digit0 (repKey r).val) (digit1 (repKey r).val) (digit2 (repKey r).val) (digit3 (repKey r).val) (digit4 (repKey r).val) e := by decide +kernel

def edgeEquiv (i : Cases) : E ≃ E where
  toFun := edgeMap i
  invFun := edgeInverse i
  left_inv := edge_left i
  right_inv := edge_right i

def caseEmbedding (i : Cases) : Embedding (inputSource i) (inputTarget i)
    (representativeSource (orbit i)) (representativeTarget (orbit i)) where
  edge := (edgeEquiv i).toEmbedding
  vertex := ⟨vertexMap i,Function.LeftInverse.injective (vertex_left i)⟩
  endpoints := endpoints_valid i

lemma exists_case (o : Orders) (h : LocalBounds b hb o) :
    ∃ i : Cases, caseKey i = ⟨key o,key_lt o⟩ := by
  have hg := FiveRows3.catalogue o h
  rw [good_eq] at hg
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hg
  exact ⟨i,hi⟩
noncomputable def index (o : Orders) (h : LocalBounds b hb o) : Cases := (exists_case o h).choose
lemma index_key (o : Orders) (h : LocalBounds b hb o) :
    caseKey (index o h) = ⟨key o,key_lt o⟩ := (exists_case o h).choose_spec
lemma inputSource_eq (o : Orders) (h : LocalBounds b hb o) :
    inputSource (index o h) = FlatCanonicalKernel.src b hb o := by
  funext e
  unfold inputSource
  rw [index_key]
  simp only [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
  exact (flat_src o h e).symm
lemma inputTarget_eq (o : Orders) (h : LocalBounds b hb o) :
    inputTarget (index o h) = FlatCanonicalKernel.dst b hb o := by
  funext e
  unfold inputTarget
  rw [index_key]
  simp only [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
  exact (flat_dst o h e).symm

noncomputable def embedding (o : Orders) (h : LocalBounds b hb o) :
    Embedding (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o)
      (representativeSource (orbit (index o h))) (representativeTarget (orbit (index o h))) where
  edge := (edgeEquiv (index o h)).toEmbedding
  vertex := ⟨vertexMap (index o h),Function.LeftInverse.injective (vertex_left (index o h))⟩
  endpoints e := by
    rw [← inputSource_eq o h,← inputTarget_eq o h]
    exact endpoints_valid (index o h) e
lemma map_univ (o : Orders) (h : LocalBounds b hb o) :
    (Finset.univ : Finset E).map (embedding o h).edge = Finset.univ :=
  Finset.map_univ_equiv (edgeEquiv (index o h))
lemma embedding_colors (o : Orders) (h : LocalBounds b hb o) (e : E) :
    FlatCanonicalKernel.color b ((embedding o h).edge e) =
      colorMap (index o h) (FlatCanonicalKernel.color b e) := color_map (index o h) e
lemma exists_representative (o : Orders) (h : LocalBounds b hb o) :
    ∃ r : Representatives, Nonempty (Embedding (FlatCanonicalKernel.src b hb o)
      (FlatCanonicalKernel.dst b hb o) (representativeSource r) (representativeTarget r)) :=
  ⟨orbit (index o h),⟨embedding o h⟩⟩

#print axioms good_eq
#print axioms endpoints_valid
#print axioms exists_representative
#print axioms map_univ
#print axioms embedding_colors
end Erdos184Work.FiveWordOrbits3
