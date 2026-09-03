import Submission.MixedSevenData
/-! Alternate direct-kernel check of the finite packing certificate. -/
namespace Erdos184.MixedSevenFinite
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Quantify only over the (at most two) chosen pieces, rather than all 103
cycle indices. This changes the decision procedure, not the proposition. -/
def FastValid (S : Finset E) : Prop :=
  (∀ i : pack S, cyc i.val ⊆ S) ∧
  (∀ i j : pack S, i.val ≠ j.val → Disjoint (cyc i.val) (cyc j.val)) ∧
  S.card ≤ 6 + ∑ i ∈ pack S, ((cyc i).card-1)

instance fastValidDecidable (S : Finset E) : Decidable (FastValid S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma fastValid_iff (S : Finset E) : FastValid S ↔ Valid S := by
  constructor
  · rintro ⟨hs,hd,hc⟩
    exact ⟨fun i hi => hs ⟨i,hi⟩,
      fun i hi j hj hij => hd ⟨i,hi⟩ ⟨j,hj⟩ hij,hc⟩
  · rintro ⟨hs,hd,hc⟩
    exact ⟨fun i => hs i.val i.property,
      fun i j hij => hd i.val i.property j.val j.property hij,hc⟩

instance (priority := 2000) fastDecidableValid (S : Finset E) : Decidable (Valid S) :=
  decidable_of_iff (FastValid S) (fastValid_iff S)

def lowBase : Finset E := Finset.univ.filter (fun e => e.val < 8)
def highBase : Finset E := Finset.univ.filter (fun e => 8 ≤ e.val)
abbrev Small := lowBase.powerset
abbrev High := highBase.powerset

def highSet (b : Fin 128) : Finset E :=
  highBase.filter (fun e => Nat.testBit b.val (e.val - 8))

lemma high_complete : ∀ U : High, ∃ b, highSet b = U.val := by decide +kernel

def extend (T : Small) (b : Fin 128) : Finset E := T.val ∪ highSet b

lemma represented (S : Finset E) : ∃ (T : Small) (b : Fin 128), extend T b = S := by
  have hs : S \ highBase ⊆ lowBase := by
    intro i hi
    fin_cases i <;> simp_all [lowBase,highBase]
  let T : Small := ⟨S \ highBase,Finset.mem_powerset.mpr hs⟩
  let U : High := ⟨S ∩ highBase,Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  obtain ⟨b,hb⟩ := high_complete U
  refine ⟨T,b,?_⟩
  rw [extend,hb]
  change (S \ highBase) ∪ (S ∩ highBase) = S
  ext i
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto

lemma check0 : ∀ T : Small, extend T 0 ≠ Finset.univ → Valid (extend T 0) := by decide +kernel
#eval IO.eprintln "Completed check0"
lemma check1 : ∀ T : Small, extend T 1 ≠ Finset.univ → Valid (extend T 1) := by decide +kernel
#eval IO.eprintln "Completed check1"
lemma check2 : ∀ T : Small, extend T 2 ≠ Finset.univ → Valid (extend T 2) := by decide +kernel
#eval IO.eprintln "Completed check2"
lemma check3 : ∀ T : Small, extend T 3 ≠ Finset.univ → Valid (extend T 3) := by decide +kernel
#eval IO.eprintln "Completed check3"
lemma check4 : ∀ T : Small, extend T 4 ≠ Finset.univ → Valid (extend T 4) := by decide +kernel
#eval IO.eprintln "Completed check4"
lemma check5 : ∀ T : Small, extend T 5 ≠ Finset.univ → Valid (extend T 5) := by decide +kernel
#eval IO.eprintln "Completed check5"
lemma check6 : ∀ T : Small, extend T 6 ≠ Finset.univ → Valid (extend T 6) := by decide +kernel
#eval IO.eprintln "Completed check6"
lemma check7 : ∀ T : Small, extend T 7 ≠ Finset.univ → Valid (extend T 7) := by decide +kernel
#eval IO.eprintln "Completed check7"
lemma check8 : ∀ T : Small, extend T 8 ≠ Finset.univ → Valid (extend T 8) := by decide +kernel
#eval IO.eprintln "Completed check8"
lemma check9 : ∀ T : Small, extend T 9 ≠ Finset.univ → Valid (extend T 9) := by decide +kernel
#eval IO.eprintln "Completed check9"
lemma check10 : ∀ T : Small, extend T 10 ≠ Finset.univ → Valid (extend T 10) := by decide +kernel
#eval IO.eprintln "Completed check10"
lemma check11 : ∀ T : Small, extend T 11 ≠ Finset.univ → Valid (extend T 11) := by decide +kernel
#eval IO.eprintln "Completed check11"
lemma check12 : ∀ T : Small, extend T 12 ≠ Finset.univ → Valid (extend T 12) := by decide +kernel
#eval IO.eprintln "Completed check12"
lemma check13 : ∀ T : Small, extend T 13 ≠ Finset.univ → Valid (extend T 13) := by decide +kernel
#eval IO.eprintln "Completed check13"
lemma check14 : ∀ T : Small, extend T 14 ≠ Finset.univ → Valid (extend T 14) := by decide +kernel
#eval IO.eprintln "Completed check14"
lemma check15 : ∀ T : Small, extend T 15 ≠ Finset.univ → Valid (extend T 15) := by decide +kernel
#eval IO.eprintln "Completed check15"
lemma check16 : ∀ T : Small, extend T 16 ≠ Finset.univ → Valid (extend T 16) := by decide +kernel
#eval IO.eprintln "Completed check16"
lemma check17 : ∀ T : Small, extend T 17 ≠ Finset.univ → Valid (extend T 17) := by decide +kernel
#eval IO.eprintln "Completed check17"
lemma check18 : ∀ T : Small, extend T 18 ≠ Finset.univ → Valid (extend T 18) := by decide +kernel
#eval IO.eprintln "Completed check18"
lemma check19 : ∀ T : Small, extend T 19 ≠ Finset.univ → Valid (extend T 19) := by decide +kernel
#eval IO.eprintln "Completed check19"
lemma check20 : ∀ T : Small, extend T 20 ≠ Finset.univ → Valid (extend T 20) := by decide +kernel
#eval IO.eprintln "Completed check20"
lemma check21 : ∀ T : Small, extend T 21 ≠ Finset.univ → Valid (extend T 21) := by decide +kernel
#eval IO.eprintln "Completed check21"
lemma check22 : ∀ T : Small, extend T 22 ≠ Finset.univ → Valid (extend T 22) := by decide +kernel
#eval IO.eprintln "Completed check22"
lemma check23 : ∀ T : Small, extend T 23 ≠ Finset.univ → Valid (extend T 23) := by decide +kernel
#eval IO.eprintln "Completed check23"
lemma check24 : ∀ T : Small, extend T 24 ≠ Finset.univ → Valid (extend T 24) := by decide +kernel
#eval IO.eprintln "Completed check24"
lemma check25 : ∀ T : Small, extend T 25 ≠ Finset.univ → Valid (extend T 25) := by decide +kernel
#eval IO.eprintln "Completed check25"
lemma check26 : ∀ T : Small, extend T 26 ≠ Finset.univ → Valid (extend T 26) := by decide +kernel
#eval IO.eprintln "Completed check26"
lemma check27 : ∀ T : Small, extend T 27 ≠ Finset.univ → Valid (extend T 27) := by decide +kernel
#eval IO.eprintln "Completed check27"
lemma check28 : ∀ T : Small, extend T 28 ≠ Finset.univ → Valid (extend T 28) := by decide +kernel
#eval IO.eprintln "Completed check28"
lemma check29 : ∀ T : Small, extend T 29 ≠ Finset.univ → Valid (extend T 29) := by decide +kernel
#eval IO.eprintln "Completed check29"
lemma check30 : ∀ T : Small, extend T 30 ≠ Finset.univ → Valid (extend T 30) := by decide +kernel
#eval IO.eprintln "Completed check30"
lemma check31 : ∀ T : Small, extend T 31 ≠ Finset.univ → Valid (extend T 31) := by decide +kernel
#eval IO.eprintln "Completed check31"
lemma check32 : ∀ T : Small, extend T 32 ≠ Finset.univ → Valid (extend T 32) := by decide +kernel
#eval IO.eprintln "Completed check32"
lemma check33 : ∀ T : Small, extend T 33 ≠ Finset.univ → Valid (extend T 33) := by decide +kernel
#eval IO.eprintln "Completed check33"
lemma check34 : ∀ T : Small, extend T 34 ≠ Finset.univ → Valid (extend T 34) := by decide +kernel
#eval IO.eprintln "Completed check34"
lemma check35 : ∀ T : Small, extend T 35 ≠ Finset.univ → Valid (extend T 35) := by decide +kernel
#eval IO.eprintln "Completed check35"
lemma check36 : ∀ T : Small, extend T 36 ≠ Finset.univ → Valid (extend T 36) := by decide +kernel
#eval IO.eprintln "Completed check36"
lemma check37 : ∀ T : Small, extend T 37 ≠ Finset.univ → Valid (extend T 37) := by decide +kernel
#eval IO.eprintln "Completed check37"
lemma check38 : ∀ T : Small, extend T 38 ≠ Finset.univ → Valid (extend T 38) := by decide +kernel
#eval IO.eprintln "Completed check38"
lemma check39 : ∀ T : Small, extend T 39 ≠ Finset.univ → Valid (extend T 39) := by decide +kernel
#eval IO.eprintln "Completed check39"
lemma check40 : ∀ T : Small, extend T 40 ≠ Finset.univ → Valid (extend T 40) := by decide +kernel
#eval IO.eprintln "Completed check40"
lemma check41 : ∀ T : Small, extend T 41 ≠ Finset.univ → Valid (extend T 41) := by decide +kernel
#eval IO.eprintln "Completed check41"
lemma check42 : ∀ T : Small, extend T 42 ≠ Finset.univ → Valid (extend T 42) := by decide +kernel
#eval IO.eprintln "Completed check42"
lemma check43 : ∀ T : Small, extend T 43 ≠ Finset.univ → Valid (extend T 43) := by decide +kernel
#eval IO.eprintln "Completed check43"
lemma check44 : ∀ T : Small, extend T 44 ≠ Finset.univ → Valid (extend T 44) := by decide +kernel
#eval IO.eprintln "Completed check44"
lemma check45 : ∀ T : Small, extend T 45 ≠ Finset.univ → Valid (extend T 45) := by decide +kernel
#eval IO.eprintln "Completed check45"
lemma check46 : ∀ T : Small, extend T 46 ≠ Finset.univ → Valid (extend T 46) := by decide +kernel
#eval IO.eprintln "Completed check46"
lemma check47 : ∀ T : Small, extend T 47 ≠ Finset.univ → Valid (extend T 47) := by decide +kernel
#eval IO.eprintln "Completed check47"
lemma check48 : ∀ T : Small, extend T 48 ≠ Finset.univ → Valid (extend T 48) := by decide +kernel
#eval IO.eprintln "Completed check48"
lemma check49 : ∀ T : Small, extend T 49 ≠ Finset.univ → Valid (extend T 49) := by decide +kernel
#eval IO.eprintln "Completed check49"
lemma check50 : ∀ T : Small, extend T 50 ≠ Finset.univ → Valid (extend T 50) := by decide +kernel
#eval IO.eprintln "Completed check50"
lemma check51 : ∀ T : Small, extend T 51 ≠ Finset.univ → Valid (extend T 51) := by decide +kernel
#eval IO.eprintln "Completed check51"
lemma check52 : ∀ T : Small, extend T 52 ≠ Finset.univ → Valid (extend T 52) := by decide +kernel
#eval IO.eprintln "Completed check52"
lemma check53 : ∀ T : Small, extend T 53 ≠ Finset.univ → Valid (extend T 53) := by decide +kernel
#eval IO.eprintln "Completed check53"
lemma check54 : ∀ T : Small, extend T 54 ≠ Finset.univ → Valid (extend T 54) := by decide +kernel
#eval IO.eprintln "Completed check54"
lemma check55 : ∀ T : Small, extend T 55 ≠ Finset.univ → Valid (extend T 55) := by decide +kernel
#eval IO.eprintln "Completed check55"
lemma check56 : ∀ T : Small, extend T 56 ≠ Finset.univ → Valid (extend T 56) := by decide +kernel
#eval IO.eprintln "Completed check56"
lemma check57 : ∀ T : Small, extend T 57 ≠ Finset.univ → Valid (extend T 57) := by decide +kernel
#eval IO.eprintln "Completed check57"
lemma check58 : ∀ T : Small, extend T 58 ≠ Finset.univ → Valid (extend T 58) := by decide +kernel
#eval IO.eprintln "Completed check58"
lemma check59 : ∀ T : Small, extend T 59 ≠ Finset.univ → Valid (extend T 59) := by decide +kernel
#eval IO.eprintln "Completed check59"
lemma check60 : ∀ T : Small, extend T 60 ≠ Finset.univ → Valid (extend T 60) := by decide +kernel
#eval IO.eprintln "Completed check60"
lemma check61 : ∀ T : Small, extend T 61 ≠ Finset.univ → Valid (extend T 61) := by decide +kernel
#eval IO.eprintln "Completed check61"
lemma check62 : ∀ T : Small, extend T 62 ≠ Finset.univ → Valid (extend T 62) := by decide +kernel
#eval IO.eprintln "Completed check62"
lemma check63 : ∀ T : Small, extend T 63 ≠ Finset.univ → Valid (extend T 63) := by decide +kernel
#eval IO.eprintln "Completed check63"
lemma check64 : ∀ T : Small, extend T 64 ≠ Finset.univ → Valid (extend T 64) := by decide +kernel
#eval IO.eprintln "Completed check64"
lemma check65 : ∀ T : Small, extend T 65 ≠ Finset.univ → Valid (extend T 65) := by decide +kernel
#eval IO.eprintln "Completed check65"
lemma check66 : ∀ T : Small, extend T 66 ≠ Finset.univ → Valid (extend T 66) := by decide +kernel
#eval IO.eprintln "Completed check66"
lemma check67 : ∀ T : Small, extend T 67 ≠ Finset.univ → Valid (extend T 67) := by decide +kernel
#eval IO.eprintln "Completed check67"
lemma check68 : ∀ T : Small, extend T 68 ≠ Finset.univ → Valid (extend T 68) := by decide +kernel
#eval IO.eprintln "Completed check68"
lemma check69 : ∀ T : Small, extend T 69 ≠ Finset.univ → Valid (extend T 69) := by decide +kernel
#eval IO.eprintln "Completed check69"
lemma check70 : ∀ T : Small, extend T 70 ≠ Finset.univ → Valid (extend T 70) := by decide +kernel
#eval IO.eprintln "Completed check70"
lemma check71 : ∀ T : Small, extend T 71 ≠ Finset.univ → Valid (extend T 71) := by decide +kernel
#eval IO.eprintln "Completed check71"
lemma check72 : ∀ T : Small, extend T 72 ≠ Finset.univ → Valid (extend T 72) := by decide +kernel
#eval IO.eprintln "Completed check72"
lemma check73 : ∀ T : Small, extend T 73 ≠ Finset.univ → Valid (extend T 73) := by decide +kernel
#eval IO.eprintln "Completed check73"
lemma check74 : ∀ T : Small, extend T 74 ≠ Finset.univ → Valid (extend T 74) := by decide +kernel
#eval IO.eprintln "Completed check74"
lemma check75 : ∀ T : Small, extend T 75 ≠ Finset.univ → Valid (extend T 75) := by decide +kernel
#eval IO.eprintln "Completed check75"
lemma check76 : ∀ T : Small, extend T 76 ≠ Finset.univ → Valid (extend T 76) := by decide +kernel
#eval IO.eprintln "Completed check76"
lemma check77 : ∀ T : Small, extend T 77 ≠ Finset.univ → Valid (extend T 77) := by decide +kernel
#eval IO.eprintln "Completed check77"
lemma check78 : ∀ T : Small, extend T 78 ≠ Finset.univ → Valid (extend T 78) := by decide +kernel
#eval IO.eprintln "Completed check78"
lemma check79 : ∀ T : Small, extend T 79 ≠ Finset.univ → Valid (extend T 79) := by decide +kernel
#eval IO.eprintln "Completed check79"
lemma check80 : ∀ T : Small, extend T 80 ≠ Finset.univ → Valid (extend T 80) := by decide +kernel
#eval IO.eprintln "Completed check80"
lemma check81 : ∀ T : Small, extend T 81 ≠ Finset.univ → Valid (extend T 81) := by decide +kernel
#eval IO.eprintln "Completed check81"
lemma check82 : ∀ T : Small, extend T 82 ≠ Finset.univ → Valid (extend T 82) := by decide +kernel
#eval IO.eprintln "Completed check82"
lemma check83 : ∀ T : Small, extend T 83 ≠ Finset.univ → Valid (extend T 83) := by decide +kernel
#eval IO.eprintln "Completed check83"
lemma check84 : ∀ T : Small, extend T 84 ≠ Finset.univ → Valid (extend T 84) := by decide +kernel
#eval IO.eprintln "Completed check84"
lemma check85 : ∀ T : Small, extend T 85 ≠ Finset.univ → Valid (extend T 85) := by decide +kernel
#eval IO.eprintln "Completed check85"
lemma check86 : ∀ T : Small, extend T 86 ≠ Finset.univ → Valid (extend T 86) := by decide +kernel
#eval IO.eprintln "Completed check86"
lemma check87 : ∀ T : Small, extend T 87 ≠ Finset.univ → Valid (extend T 87) := by decide +kernel
#eval IO.eprintln "Completed check87"
lemma check88 : ∀ T : Small, extend T 88 ≠ Finset.univ → Valid (extend T 88) := by decide +kernel
#eval IO.eprintln "Completed check88"
lemma check89 : ∀ T : Small, extend T 89 ≠ Finset.univ → Valid (extend T 89) := by decide +kernel
#eval IO.eprintln "Completed check89"
lemma check90 : ∀ T : Small, extend T 90 ≠ Finset.univ → Valid (extend T 90) := by decide +kernel
#eval IO.eprintln "Completed check90"
lemma check91 : ∀ T : Small, extend T 91 ≠ Finset.univ → Valid (extend T 91) := by decide +kernel
#eval IO.eprintln "Completed check91"
lemma check92 : ∀ T : Small, extend T 92 ≠ Finset.univ → Valid (extend T 92) := by decide +kernel
#eval IO.eprintln "Completed check92"
lemma check93 : ∀ T : Small, extend T 93 ≠ Finset.univ → Valid (extend T 93) := by decide +kernel
#eval IO.eprintln "Completed check93"
lemma check94 : ∀ T : Small, extend T 94 ≠ Finset.univ → Valid (extend T 94) := by decide +kernel
#eval IO.eprintln "Completed check94"
lemma check95 : ∀ T : Small, extend T 95 ≠ Finset.univ → Valid (extend T 95) := by decide +kernel
#eval IO.eprintln "Completed check95"
lemma check96 : ∀ T : Small, extend T 96 ≠ Finset.univ → Valid (extend T 96) := by decide +kernel
#eval IO.eprintln "Completed check96"
lemma check97 : ∀ T : Small, extend T 97 ≠ Finset.univ → Valid (extend T 97) := by decide +kernel
#eval IO.eprintln "Completed check97"
lemma check98 : ∀ T : Small, extend T 98 ≠ Finset.univ → Valid (extend T 98) := by decide +kernel
#eval IO.eprintln "Completed check98"
lemma check99 : ∀ T : Small, extend T 99 ≠ Finset.univ → Valid (extend T 99) := by decide +kernel
#eval IO.eprintln "Completed check99"
lemma check100 : ∀ T : Small, extend T 100 ≠ Finset.univ → Valid (extend T 100) := by decide +kernel
#eval IO.eprintln "Completed check100"
lemma check101 : ∀ T : Small, extend T 101 ≠ Finset.univ → Valid (extend T 101) := by decide +kernel
#eval IO.eprintln "Completed check101"
lemma check102 : ∀ T : Small, extend T 102 ≠ Finset.univ → Valid (extend T 102) := by decide +kernel
#eval IO.eprintln "Completed check102"
lemma check103 : ∀ T : Small, extend T 103 ≠ Finset.univ → Valid (extend T 103) := by decide +kernel
#eval IO.eprintln "Completed check103"
lemma check104 : ∀ T : Small, extend T 104 ≠ Finset.univ → Valid (extend T 104) := by decide +kernel
#eval IO.eprintln "Completed check104"
lemma check105 : ∀ T : Small, extend T 105 ≠ Finset.univ → Valid (extend T 105) := by decide +kernel
#eval IO.eprintln "Completed check105"
lemma check106 : ∀ T : Small, extend T 106 ≠ Finset.univ → Valid (extend T 106) := by decide +kernel
#eval IO.eprintln "Completed check106"
lemma check107 : ∀ T : Small, extend T 107 ≠ Finset.univ → Valid (extend T 107) := by decide +kernel
#eval IO.eprintln "Completed check107"
lemma check108 : ∀ T : Small, extend T 108 ≠ Finset.univ → Valid (extend T 108) := by decide +kernel
#eval IO.eprintln "Completed check108"
lemma check109 : ∀ T : Small, extend T 109 ≠ Finset.univ → Valid (extend T 109) := by decide +kernel
#eval IO.eprintln "Completed check109"
lemma check110 : ∀ T : Small, extend T 110 ≠ Finset.univ → Valid (extend T 110) := by decide +kernel
#eval IO.eprintln "Completed check110"
lemma check111 : ∀ T : Small, extend T 111 ≠ Finset.univ → Valid (extend T 111) := by decide +kernel
#eval IO.eprintln "Completed check111"
lemma check112 : ∀ T : Small, extend T 112 ≠ Finset.univ → Valid (extend T 112) := by decide +kernel
#eval IO.eprintln "Completed check112"
lemma check113 : ∀ T : Small, extend T 113 ≠ Finset.univ → Valid (extend T 113) := by decide +kernel
#eval IO.eprintln "Completed check113"
lemma check114 : ∀ T : Small, extend T 114 ≠ Finset.univ → Valid (extend T 114) := by decide +kernel
#eval IO.eprintln "Completed check114"
lemma check115 : ∀ T : Small, extend T 115 ≠ Finset.univ → Valid (extend T 115) := by decide +kernel
#eval IO.eprintln "Completed check115"
lemma check116 : ∀ T : Small, extend T 116 ≠ Finset.univ → Valid (extend T 116) := by decide +kernel
#eval IO.eprintln "Completed check116"
lemma check117 : ∀ T : Small, extend T 117 ≠ Finset.univ → Valid (extend T 117) := by decide +kernel
#eval IO.eprintln "Completed check117"
lemma check118 : ∀ T : Small, extend T 118 ≠ Finset.univ → Valid (extend T 118) := by decide +kernel
#eval IO.eprintln "Completed check118"
lemma check119 : ∀ T : Small, extend T 119 ≠ Finset.univ → Valid (extend T 119) := by decide +kernel
#eval IO.eprintln "Completed check119"
lemma check120 : ∀ T : Small, extend T 120 ≠ Finset.univ → Valid (extend T 120) := by decide +kernel
#eval IO.eprintln "Completed check120"
lemma check121 : ∀ T : Small, extend T 121 ≠ Finset.univ → Valid (extend T 121) := by decide +kernel
#eval IO.eprintln "Completed check121"
lemma check122 : ∀ T : Small, extend T 122 ≠ Finset.univ → Valid (extend T 122) := by decide +kernel
#eval IO.eprintln "Completed check122"
lemma check123 : ∀ T : Small, extend T 123 ≠ Finset.univ → Valid (extend T 123) := by decide +kernel
#eval IO.eprintln "Completed check123"
lemma check124 : ∀ T : Small, extend T 124 ≠ Finset.univ → Valid (extend T 124) := by decide +kernel
#eval IO.eprintln "Completed check124"
lemma check125 : ∀ T : Small, extend T 125 ≠ Finset.univ → Valid (extend T 125) := by decide +kernel
#eval IO.eprintln "Completed check125"
lemma check126 : ∀ T : Small, extend T 126 ≠ Finset.univ → Valid (extend T 126) := by decide +kernel
#eval IO.eprintln "Completed check126"
lemma check127 : ∀ T : Small, extend T 127 ≠ Finset.univ → Valid (extend T 127) := by decide +kernel
#eval IO.eprintln "Completed check127"

lemma certificate : ∀ S : Finset E, S ≠ Finset.univ → Valid S := by
  intro S hS
  obtain ⟨T,b,rfl⟩ := represented S
  fin_cases b
  · exact check0 T hS
  · exact check1 T hS
  · exact check2 T hS
  · exact check3 T hS
  · exact check4 T hS
  · exact check5 T hS
  · exact check6 T hS
  · exact check7 T hS
  · exact check8 T hS
  · exact check9 T hS
  · exact check10 T hS
  · exact check11 T hS
  · exact check12 T hS
  · exact check13 T hS
  · exact check14 T hS
  · exact check15 T hS
  · exact check16 T hS
  · exact check17 T hS
  · exact check18 T hS
  · exact check19 T hS
  · exact check20 T hS
  · exact check21 T hS
  · exact check22 T hS
  · exact check23 T hS
  · exact check24 T hS
  · exact check25 T hS
  · exact check26 T hS
  · exact check27 T hS
  · exact check28 T hS
  · exact check29 T hS
  · exact check30 T hS
  · exact check31 T hS
  · exact check32 T hS
  · exact check33 T hS
  · exact check34 T hS
  · exact check35 T hS
  · exact check36 T hS
  · exact check37 T hS
  · exact check38 T hS
  · exact check39 T hS
  · exact check40 T hS
  · exact check41 T hS
  · exact check42 T hS
  · exact check43 T hS
  · exact check44 T hS
  · exact check45 T hS
  · exact check46 T hS
  · exact check47 T hS
  · exact check48 T hS
  · exact check49 T hS
  · exact check50 T hS
  · exact check51 T hS
  · exact check52 T hS
  · exact check53 T hS
  · exact check54 T hS
  · exact check55 T hS
  · exact check56 T hS
  · exact check57 T hS
  · exact check58 T hS
  · exact check59 T hS
  · exact check60 T hS
  · exact check61 T hS
  · exact check62 T hS
  · exact check63 T hS
  · exact check64 T hS
  · exact check65 T hS
  · exact check66 T hS
  · exact check67 T hS
  · exact check68 T hS
  · exact check69 T hS
  · exact check70 T hS
  · exact check71 T hS
  · exact check72 T hS
  · exact check73 T hS
  · exact check74 T hS
  · exact check75 T hS
  · exact check76 T hS
  · exact check77 T hS
  · exact check78 T hS
  · exact check79 T hS
  · exact check80 T hS
  · exact check81 T hS
  · exact check82 T hS
  · exact check83 T hS
  · exact check84 T hS
  · exact check85 T hS
  · exact check86 T hS
  · exact check87 T hS
  · exact check88 T hS
  · exact check89 T hS
  · exact check90 T hS
  · exact check91 T hS
  · exact check92 T hS
  · exact check93 T hS
  · exact check94 T hS
  · exact check95 T hS
  · exact check96 T hS
  · exact check97 T hS
  · exact check98 T hS
  · exact check99 T hS
  · exact check100 T hS
  · exact check101 T hS
  · exact check102 T hS
  · exact check103 T hS
  · exact check104 T hS
  · exact check105 T hS
  · exact check106 T hS
  · exact check107 T hS
  · exact check108 T hS
  · exact check109 T hS
  · exact check110 T hS
  · exact check111 T hS
  · exact check112 T hS
  · exact check113 T hS
  · exact check114 T hS
  · exact check115 T hS
  · exact check116 T hS
  · exact check117 T hS
  · exact check118 T hS
  · exact check119 T hS
  · exact check120 T hS
  · exact check121 T hS
  · exact check122 T hS
  · exact check123 T hS
  · exact check124 T hS
  · exact check125 T hS
  · exact check126 T hS
  · exact check127 T hS
end Erdos184.MixedSevenFinite
