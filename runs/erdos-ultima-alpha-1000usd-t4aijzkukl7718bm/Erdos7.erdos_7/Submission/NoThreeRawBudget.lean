import Submission.ArithmeticReduction

/-! A stronger uniform raw budget for primes at least five. -/
namespace Erdos7NoThreeRawBudget
open Erdos7No23Sieve
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000

def fixedPrimes : List ℕ := (List.range 40000).filter (fun p =>
  decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p))

def rounded : ℕ × ℕ := fixedPrimes.foldl roundedStep (1000000,0)

def chunk (lo : ℕ) : List ℕ := (List.range' lo 1000).filter (fun p =>
  decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p))

lemma chunk_0 : (chunk 0).foldl roundedStep (1000000,0) = (160681849,779751374) := by
  decide +kernel

lemma chunk_1000 : (chunk 1000).foldl roundedStep (160681849,779751374) = (228892975,800021834) := by
  decide +kernel

lemma chunk_2000 : (chunk 2000).foldl roundedStep (228892975,800021834) = (277755577,808353307) := by
  decide +kernel

lemma chunk_3000 : (chunk 3000).foldl roundedStep (277755577,808353307) = (316155790,812974409) := by
  decide +kernel

lemma chunk_4000 : (chunk 4000).foldl roundedStep (316155790,812974409) = (349324668,816072447) := by
  decide +kernel

lemma chunk_5000 : (chunk 5000).foldl roundedStep (349324668,816072447) = (377655260,818229175) := by
  decide +kernel

lemma chunk_6000 : (chunk 6000).foldl roundedStep (377655260,818229175) = (404074231,819927831) := by
  decide +kernel

lemma chunk_7000 : (chunk 7000).foldl roundedStep (404074231,819927831) = (426295223,821164254) := by
  decide +kernel

lemma chunk_8000 : (chunk 8000).foldl roundedStep (426295223,821164254) = (447512157,822206007) := by
  decide +kernel

lemma chunk_9000 : (chunk 9000).foldl roundedStep (447512157,822206007) = (467786023,823097714) := by
  decide +kernel

lemma chunk_10000 : (chunk 10000).foldl roundedStep (467786023,823097714) = (485861664,823816476) := by
  decide +kernel

lemma chunk_11000 : (chunk 11000).foldl roundedStep (485861664,823816476) = (502448988,824417482) := by
  decide +kernel

lemma chunk_12000 : (chunk 12000).foldl roundedStep (502448988,824417482) = (519155939,824974797) := by
  decide +kernel

lemma chunk_13000 : (chunk 13000).foldl roundedStep (519155939,824974797) = (534529271,825449745) := by
  decide +kernel

lemma chunk_14000 : (chunk 14000).foldl roundedStep (534529271,825449745) = (548799383,825859450) := by
  decide +kernel

lemma chunk_15000 : (chunk 15000).foldl roundedStep (548799383,825859450) = (563336693,826250610) := by
  decide +kernel

lemma chunk_16000 : (chunk 16000).foldl roundedStep (563336693,826250610) = (576027674,826571283) := by
  decide +kernel

lemma chunk_17000 : (chunk 17000).foldl roundedStep (576027674,826571283) = (589007277,826880397) := by
  decide +kernel

lemma chunk_18000 : (chunk 18000).foldl roundedStep (589007277,826880397) = (600366131,827136951) := by
  decide +kernel

lemma chunk_19000 : (chunk 19000).foldl roundedStep (600366131,827136951) = (612492348,827396111) := by
  decide +kernel

lemma chunk_20000 : (chunk 20000).foldl roundedStep (612492348,827396111) = (623581399,827621788) := by
  decide +kernel

lemma chunk_21000 : (chunk 21000).foldl roundedStep (623581399,827621788) = (635004423,827843405) := by
  decide +kernel

lemma chunk_22000 : (chunk 22000).foldl roundedStep (635004423,827843405) = (645688371,828041546) := by
  decide +kernel

lemma chunk_23000 : (chunk 23000).foldl roundedStep (645688371,828041546) = (656498381,828233376) := by
  decide +kernel

lemma chunk_24000 : (chunk 24000).foldl roundedStep (656498381,828233376) = (666022132,828395580) := by
  decide +kernel

lemma chunk_25000 : (chunk 25000).foldl roundedStep (666022132,828395580) = (675686844,828553514) := by
  decide +kernel

lemma chunk_26000 : (chunk 26000).foldl roundedStep (675686844,828553514) = (685410248,828706414) := by
  decide +kernel

lemma chunk_27000 : (chunk 27000).foldl roundedStep (685410248,828706414) = (694245171,828840231) := by
  decide +kernel

lemma chunk_28000 : (chunk 28000).foldl roundedStep (694245171,828840231) = (703254435,828971992) := by
  decide +kernel

lemma chunk_29000 : (chunk 29000).foldl roundedStep (703254435,828971992) = (711536051,829089140) := by
  decide +kernel

lemma chunk_30000 : (chunk 30000).foldl roundedStep (711536051,829089140) = (719897589,829203451) := by
  decide +kernel

lemma chunk_31000 : (chunk 31000).foldl roundedStep (719897589,829203451) = (727835540,829308634) := by
  decide +kernel

lemma chunk_32000 : (chunk 32000).foldl roundedStep (727835540,829308634) = (736794977,829423593) := by
  decide +kernel

lemma chunk_33000 : (chunk 33000).foldl roundedStep (736794977,829423593) = (745088999,829526806) := by
  decide +kernel

lemma chunk_34000 : (chunk 34000).foldl roundedStep (745088999,829526806) = (752741182,829619286) := by
  decide +kernel

lemma chunk_35000 : (chunk 35000).foldl roundedStep (752741182,829619286) = (760092838,829705633) := by
  decide +kernel

lemma chunk_36000 : (chunk 36000).foldl roundedStep (760092838,829705633) = (767859774,829794306) := by
  decide +kernel

lemma chunk_37000 : (chunk 37000).foldl roundedStep (767859774,829794306) = (775111938,829874940) := by
  decide +kernel

lemma chunk_38000 : (chunk 38000).foldl roundedStep (775111938,829874940) = (781932368,829948754) := by
  decide +kernel

lemma chunk_39000 : (chunk 39000).foldl roundedStep (781932368,829948754) = (789092232,830024338) := by
  decide +kernel

lemma fixedPrimes_split : fixedPrimes = chunk 0 ++ chunk 1000 ++ chunk 2000 ++ chunk 3000 ++ chunk 4000 ++ chunk 5000 ++ chunk 6000 ++ chunk 7000 ++ chunk 8000 ++ chunk 9000 ++ chunk 10000 ++ chunk 11000 ++ chunk 12000 ++ chunk 13000 ++ chunk 14000 ++ chunk 15000 ++ chunk 16000 ++ chunk 17000 ++ chunk 18000 ++ chunk 19000 ++ chunk 20000 ++ chunk 21000 ++ chunk 22000 ++ chunk 23000 ++ chunk 24000 ++ chunk 25000 ++ chunk 26000 ++ chunk 27000 ++ chunk 28000 ++ chunk 29000 ++ chunk 30000 ++ chunk 31000 ++ chunk 32000 ++ chunk 33000 ++ chunk 34000 ++ chunk 35000 ++ chunk 36000 ++ chunk 37000 ++ chunk 38000 ++ chunk 39000 := by
  have h1000 : List.range' 0 1000 = List.range' 0 1000 := rfl
  have h2000 : List.range' 0 1000 ++ List.range' 1000 1000 = List.range' 0 2000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 1000 1000) h1000).trans (@List.range'_append_1 0 1000 1000)
  have h3000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 = List.range' 0 3000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 2000 1000) h2000).trans (@List.range'_append_1 0 2000 1000)
  have h4000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 = List.range' 0 4000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 3000 1000) h3000).trans (@List.range'_append_1 0 3000 1000)
  have h5000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 = List.range' 0 5000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 4000 1000) h4000).trans (@List.range'_append_1 0 4000 1000)
  have h6000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 = List.range' 0 6000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 5000 1000) h5000).trans (@List.range'_append_1 0 5000 1000)
  have h7000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 = List.range' 0 7000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 6000 1000) h6000).trans (@List.range'_append_1 0 6000 1000)
  have h8000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 = List.range' 0 8000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 7000 1000) h7000).trans (@List.range'_append_1 0 7000 1000)
  have h9000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 = List.range' 0 9000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 8000 1000) h8000).trans (@List.range'_append_1 0 8000 1000)
  have h10000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 = List.range' 0 10000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 9000 1000) h9000).trans (@List.range'_append_1 0 9000 1000)
  have h11000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 = List.range' 0 11000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 10000 1000) h10000).trans (@List.range'_append_1 0 10000 1000)
  have h12000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 = List.range' 0 12000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 11000 1000) h11000).trans (@List.range'_append_1 0 11000 1000)
  have h13000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 = List.range' 0 13000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 12000 1000) h12000).trans (@List.range'_append_1 0 12000 1000)
  have h14000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 = List.range' 0 14000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 13000 1000) h13000).trans (@List.range'_append_1 0 13000 1000)
  have h15000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 = List.range' 0 15000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 14000 1000) h14000).trans (@List.range'_append_1 0 14000 1000)
  have h16000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 = List.range' 0 16000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 15000 1000) h15000).trans (@List.range'_append_1 0 15000 1000)
  have h17000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 = List.range' 0 17000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 16000 1000) h16000).trans (@List.range'_append_1 0 16000 1000)
  have h18000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 = List.range' 0 18000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 17000 1000) h17000).trans (@List.range'_append_1 0 17000 1000)
  have h19000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 = List.range' 0 19000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 18000 1000) h18000).trans (@List.range'_append_1 0 18000 1000)
  have h20000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 = List.range' 0 20000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 19000 1000) h19000).trans (@List.range'_append_1 0 19000 1000)
  have h21000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 = List.range' 0 21000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 20000 1000) h20000).trans (@List.range'_append_1 0 20000 1000)
  have h22000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 = List.range' 0 22000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 21000 1000) h21000).trans (@List.range'_append_1 0 21000 1000)
  have h23000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 = List.range' 0 23000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 22000 1000) h22000).trans (@List.range'_append_1 0 22000 1000)
  have h24000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 = List.range' 0 24000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 23000 1000) h23000).trans (@List.range'_append_1 0 23000 1000)
  have h25000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 = List.range' 0 25000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 24000 1000) h24000).trans (@List.range'_append_1 0 24000 1000)
  have h26000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 = List.range' 0 26000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 25000 1000) h25000).trans (@List.range'_append_1 0 25000 1000)
  have h27000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 = List.range' 0 27000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 26000 1000) h26000).trans (@List.range'_append_1 0 26000 1000)
  have h28000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 = List.range' 0 28000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 27000 1000) h27000).trans (@List.range'_append_1 0 27000 1000)
  have h29000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 = List.range' 0 29000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 28000 1000) h28000).trans (@List.range'_append_1 0 28000 1000)
  have h30000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 = List.range' 0 30000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 29000 1000) h29000).trans (@List.range'_append_1 0 29000 1000)
  have h31000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 = List.range' 0 31000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 30000 1000) h30000).trans (@List.range'_append_1 0 30000 1000)
  have h32000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 = List.range' 0 32000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 31000 1000) h31000).trans (@List.range'_append_1 0 31000 1000)
  have h33000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 = List.range' 0 33000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 32000 1000) h32000).trans (@List.range'_append_1 0 32000 1000)
  have h34000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 = List.range' 0 34000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 33000 1000) h33000).trans (@List.range'_append_1 0 33000 1000)
  have h35000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 = List.range' 0 35000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 34000 1000) h34000).trans (@List.range'_append_1 0 34000 1000)
  have h36000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 ++ List.range' 35000 1000 = List.range' 0 36000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 35000 1000) h35000).trans (@List.range'_append_1 0 35000 1000)
  have h37000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 ++ List.range' 35000 1000 ++ List.range' 36000 1000 = List.range' 0 37000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 36000 1000) h36000).trans (@List.range'_append_1 0 36000 1000)
  have h38000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 ++ List.range' 35000 1000 ++ List.range' 36000 1000 ++ List.range' 37000 1000 = List.range' 0 38000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 37000 1000) h37000).trans (@List.range'_append_1 0 37000 1000)
  have h39000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 ++ List.range' 35000 1000 ++ List.range' 36000 1000 ++ List.range' 37000 1000 ++ List.range' 38000 1000 = List.range' 0 39000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 38000 1000) h38000).trans (@List.range'_append_1 0 38000 1000)
  have h40000 : List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 ++ List.range' 35000 1000 ++ List.range' 36000 1000 ++ List.range' 37000 1000 ++ List.range' 38000 1000 ++ List.range' 39000 1000 = List.range' 0 40000 :=
    (congrArg (fun L : List ℕ => L ++ List.range' 39000 1000) h39000).trans (@List.range'_append_1 0 39000 1000)
  calc
    fixedPrimes = List.filter (fun p => decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p)) (List.range' 0 40000) :=
      congrArg (List.filter _) List.range_eq_range'
    _ = List.filter (fun p => decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p)) (List.range' 0 1000 ++ List.range' 1000 1000 ++ List.range' 2000 1000 ++ List.range' 3000 1000 ++ List.range' 4000 1000 ++ List.range' 5000 1000 ++ List.range' 6000 1000 ++ List.range' 7000 1000 ++ List.range' 8000 1000 ++ List.range' 9000 1000 ++ List.range' 10000 1000 ++ List.range' 11000 1000 ++ List.range' 12000 1000 ++ List.range' 13000 1000 ++ List.range' 14000 1000 ++ List.range' 15000 1000 ++ List.range' 16000 1000 ++ List.range' 17000 1000 ++ List.range' 18000 1000 ++ List.range' 19000 1000 ++ List.range' 20000 1000 ++ List.range' 21000 1000 ++ List.range' 22000 1000 ++ List.range' 23000 1000 ++ List.range' 24000 1000 ++ List.range' 25000 1000 ++ List.range' 26000 1000 ++ List.range' 27000 1000 ++ List.range' 28000 1000 ++ List.range' 29000 1000 ++ List.range' 30000 1000 ++ List.range' 31000 1000 ++ List.range' 32000 1000 ++ List.range' 33000 1000 ++ List.range' 34000 1000 ++ List.range' 35000 1000 ++ List.range' 36000 1000 ++ List.range' 37000 1000 ++ List.range' 38000 1000 ++ List.range' 39000 1000) :=
      congrArg (List.filter _) h40000.symm
    _ = _ := by simp only [List.filter_append,chunk]

lemma rounded_certificate : rounded = (789092232,830024338) := by
  unfold rounded
  rw [fixedPrimes_split]
  simp only [List.foldl_append]
  rw [chunk_0, chunk_1000, chunk_2000, chunk_3000, chunk_4000, chunk_5000, chunk_6000, chunk_7000, chunk_8000, chunk_9000, chunk_10000, chunk_11000, chunk_12000, chunk_13000, chunk_14000, chunk_15000, chunk_16000, chunk_17000, chunk_18000, chunk_19000, chunk_20000, chunk_21000, chunk_22000, chunk_23000, chunk_24000, chunk_25000, chunk_26000, chunk_27000, chunk_28000, chunk_29000, chunk_30000, chunk_31000, chunk_32000, chunk_33000, chunk_34000, chunk_35000, chunk_36000, chunk_37000, chunk_38000, chunk_39000]

lemma mem_prefix (p : ℕ) : p ∈ fixedPrimes ↔ p.Prime ∧ 5 ≤ p ∧ p < 40000 := by
  simp only [fixedPrimes,List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
  tauto

lemma prefix_ge_five : ∀ p ∈ fixedPrimes.toFinset, 5 ≤ p := by
  intro p hp
  exact ((mem_prefix p).mp (List.mem_toFinset.mp hp)).2.1

lemma prefix_pairwise : fixedPrimes.Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma prefix_budget_bound :
    budgetCost fixedPrimes.toFinset + (16/5 : ℚ)*budgetProduct fixedPrimes.toFinset/40000 < 9/10 := by
  have hL : ∀ p ∈ fixedPrimes, 5 ≤ p := fun p hp => ((mem_prefix p).mp hp).2.1
  have hd := roundedFold_dominates fixedPrimes hL (1000000,0) (1,0)
    (by norm_num [Dominates])
  change Dominates rounded (fixedPrimes.foldl rationalStep (1,0)) at hd
  rw [rounded_certificate,rationalFold_eq fixedPrimes prefix_pairwise 1 0] at hd
  simp only [Dominates,one_mul,zero_add] at hd
  norm_num at hd
  nlinarith [hd.1,hd.2]

/-- The finite fixedPrimes and the uniform tail bound cover every finite prime set. -/
theorem budgetCost_lt_nine_tenths (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) : budgetCost S < 9/10 := by
  let A := S.filter (· < 40000)
  let B := S.filter (fun p => ¬p < 40000)
  have hSAB : S = A ∪ B := (Finset.filter_union_filter_not_eq _ _).symm
  have hA : A ⊆ fixedPrimes.toFinset := by
    intro p hp
    obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr ((mem_prefix p).mpr ⟨(hS p hp).1,(hS p hp).2,hlo⟩)
  have hB (p : ℕ) (hp : p ∈ B) : p.Prime ∧ 40000 ≤ p := by
    obtain ⟨hp,hhi⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hp).1,by omega⟩
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    exact (Finset.mem_filter.mp ha).2.trans_le (hB b hb).2
  have hPA := budgetProduct_mono hA prefix_ge_five
  have hCA := budgetCost_mono hA prefix_ge_five
  have hCB := tail_cost_bound 40000 (by omega) B hB
  have hPA0 := budgetProduct_nonneg A (fun p hp => prefix_ge_five p (hA hp))
  have hterm : budgetProduct A * budgetCost B ≤
      budgetProduct fixedPrimes.toFinset * ((16/5 : ℚ)/40000) := by
    exact (mul_le_mul_of_nonneg_left hCB hPA0).trans
      (mul_le_mul_of_nonneg_right hPA (by norm_num))
  rw [hSAB,budgetCost_union hAB]
  apply (add_le_add hCA hterm).trans_lt
  convert prefix_budget_bound using 1 <;> ring

#print axioms rounded_certificate
#print axioms budgetCost_lt_nine_tenths
end Erdos7NoThreeRawBudget
