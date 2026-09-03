import Submission.SortedDisjointCertificate

/-!
An exact finite certificate for doubled Petersen cycle partitions.
The connection to all cycles of the subdivided simple graph is not yet
formalized here. This does not settle Erdos 184.
-/
open scoped BigOperators
namespace Erdos184
namespace DoubledPetersenCertificate

def code : Fin 72 → ℕ :=
  ![269488145,
    4802735779090689,
    72058762538520833,
    17596482064641,
    72076358751096849,
    4785147619577873,
    76843772449657089,
    1099528409345,
    18696277856273,
    4803835038011409,
    72057662774186001,
    72075259523633409,
    76842673222193169,
    76860260844835073,
    282578801197313,
    72339142046973969,
    281479540178961,
    72340241809211649,
    299067162820865,
    300166960709649,
    72357829431853073,
    4503668346912785,
    4504768144802049,
    4521265096360193,
    76561193951625233,
    76578790164201729,
    76562293176992001,
    76579889926438929,
    299067432309008,
    76562293446480144,
    1099797889296,
    76860261114315024,
    17596749447440,
    282579068588304,
    76843772717039888,
    4521264828977424,
    4504767875322128,
    4786247147979024,
    4802735509602576,
    72356729937006864,
    72075259256242448,
    72058762269032720,
    4503668616400896,
    72357829701341184,
    76579889659056128,
    281479272796160,
    4522364624769024,
    300166691229696,
    72339142314364928,
    76561193682145280,
    4803835307491328,
    72057663043665920,
    18696010465280,
    76842672954802176,
    4785147886960640,
    72076359018479616,
    76861360339681280,
    2,
    32,
    512,
    8192,
    131072,
    2097152,
    33554432,
    536870912,
    8589934592,
    137438953472,
    2199023255552,
    35184372088832,
    562949953421312,
    9007199254740992,
    144115188075855872]

def extension : Fin 72 → List (Fin 72) :=
  ![[0,11,37,61,56],
    [1,4,34,61,63],
    [2,9,31,61,65],
    [3,9,34,61,51],
    [4,1,34,61,63],
    [5,11,31,61,67],
    [6,9,40,61,64],
    [7,4,31,61,54],
    [8,1,37,61,71],
    [9,6,40,61,64],
    [10,1,34,61,52],
    [11,6,58,61,50],
    [12,1,40,61,67],
    [13,4,37,61,64],
    [14,1,58,46,71],
    [15,1,32,49,67],
    [16,1,36,52,71],
    [17,1,58,44,63],
    [18,4,29,63,54],
    [19,1,36,65,71],
    [20,1,29,63,65],
    [21,1,33,52,71],
    [22,4,32,49,69],
    [23,4,29,63,69],
    [24,1,39,65,67],
    [25,1,58,48,67],
    [26,1,58,48,52],
    [27,1,41,45,63],
    [28,4,17,63,70],
    [29,1,20,63,65],
    [30,1,20,49,65],
    [31,4,7,61,54],
    [32,1,15,49,67],
    [33,1,21,52,71],
    [34,1,4,61,63],
    [35,6,20,63,64],
    [36,1,19,65,71],
    [37,1,8,61,71],
    [38,4,14,49,64],
    [39,1,24,65,67],
    [40,1,12,61,67],
    [41,1,12,61,52],
    [42,4,18,34,63],
    [43,6,23,58,63],
    [44,1,17,58,63],
    [45,1,27,41,63],
    [46,1,14,58,71],
    [47,1,24,41,65],
    [48,1,25,58,67],
    [49,1,15,32,67],
    [50,4,12,59,61],
    [51,4,18,33,70],
    [52,1,12,41,61],
    [53,1,8,41,61],
    [54,4,19,59,49],
    [55,1,14,58,49],
    [56,11,22,58,45],
    [57,29,37,48,68],
    [58,1,17,44,63],
    [59,4,12,61,50],
    [60,15,22,34,68],
    [61,1,4,34,63],
    [62,9,11,34,61],
    [63,1,4,34,61],
    [64,4,25,36,69],
    [65,1,19,36,71],
    [66,6,19,32,49],
    [67,1,12,40,61],
    [68,6,15,36,64],
    [69,4,22,32,49],
    [70,4,17,28,63],
    [71,1,19,36,65]]

def fullCode : ℕ := 153722867280912930

def digit (i : Fin 72) (e : Fin 15) : ℕ := code i / 16 ^ e.val % 16

def IsPartition (D : List (Fin 72)) : Prop :=
  ∀ e : Fin 15, (D.map (fun i => digit i e)).sum = 2

lemma code_expand (i : Fin 72) : code i = ∑ e : Fin 15, digit i e * 16 ^ e.val := by
  revert i; decide

lemma full_expand : fullCode = ∑ e : Fin 15, 2 * 16 ^ e.val := by decide

set_option maxRecDepth 10000 in
lemma extension_partition (i : Fin 72) : IsPartition (extension i) := by
  unfold IsPartition
  revert i; decide

lemma extension_length (i : Fin 72) : (extension i).length = 5 := by
  revert i; decide

lemma mem_extension (i : Fin 72) : i ∈ extension i := by
  revert i; decide

lemma partition_code (D : List (Fin 72)) (hD : IsPartition D) :
    (D.map code).sum = fullCode := by
  have hs : ∀ E : List (Fin 72), (E.map code).sum =
      ∑ e : Fin 15, (E.map (fun i => digit i e)).sum * 16 ^ e.val := by
    intro E
    induction E with
    | nil => simp
    | cons i E ih =>
      simp only [List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib]
      rw [ih,code_expand i]
  rw [hs,full_expand]
  apply Finset.sum_congr rfl
  intro e _
  rw [hD e]

def allCodes : List ℕ := 0 :: List.ofFn code

def pairSums : List ℕ := allCodes.flatMap (fun a => allCodes.map (a + ·))

def leftSums : List ℕ := SortedDisjointCertificate.sorted pairSums
def rightSums : List ℕ := SortedDisjointCertificate.sorted
  ((pairSums.filter (fun x => decide (x ≤ fullCode))).map (fullCode - ·))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
lemma checked_separation : SortedDisjointCertificate.check 11000 leftSums rightSums = true := by
  decide +kernel


end DoubledPetersenCertificate
end Erdos184
