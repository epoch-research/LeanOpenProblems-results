import Submission.Sieve729Data
import Submission.Sieve729Masks

/-! Kernel-checked closure identities for a block of barrier rows. -/
namespace Erdos952Investigation.Sieve729
open BitsetBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

lemma start_checked : bits 0 ||| rows 0 = rows 0 := by
  decide +kernel

lemma row_checked_0 :
    (dilate period (rowNeighbors rows 0) &&& bits 0) ||| rows 0 = rows 0 := by
  decide +kernel

lemma row_checked_1 :
    (dilate period (rowNeighbors rows 1) &&& bits 1) ||| rows 1 = rows 1 := by
  decide +kernel

lemma row_checked_2 :
    (dilate period (rowNeighbors rows 2) &&& bits 2) ||| rows 2 = rows 2 := by
  decide +kernel

lemma row_checked_3 :
    (dilate period (rowNeighbors rows 3) &&& bits 3) ||| rows 3 = rows 3 := by
  decide +kernel

lemma row_checked_4 :
    (dilate period (rowNeighbors rows 4) &&& bits 4) ||| rows 4 = rows 4 := by
  decide +kernel

lemma row_checked_5 :
    (dilate period (rowNeighbors rows 5) &&& bits 5) ||| rows 5 = rows 5 := by
  decide +kernel

lemma row_checked_6 :
    (dilate period (rowNeighbors rows 6) &&& bits 6) ||| rows 6 = rows 6 := by
  decide +kernel

lemma row_checked_7 :
    (dilate period (rowNeighbors rows 7) &&& bits 7) ||| rows 7 = rows 7 := by
  decide +kernel

lemma row_checked_8 :
    (dilate period (rowNeighbors rows 8) &&& bits 8) ||| rows 8 = rows 8 := by
  decide +kernel

lemma row_checked_9 :
    (dilate period (rowNeighbors rows 9) &&& bits 9) ||| rows 9 = rows 9 := by
  decide +kernel

lemma row_checked_10 :
    (dilate period (rowNeighbors rows 10) &&& bits 10) ||| rows 10 = rows 10 := by
  decide +kernel

lemma row_checked_11 :
    (dilate period (rowNeighbors rows 11) &&& bits 11) ||| rows 11 = rows 11 := by
  decide +kernel

lemma row_checked_12 :
    (dilate period (rowNeighbors rows 12) &&& bits 12) ||| rows 12 = rows 12 := by
  decide +kernel

lemma row_checked_13 :
    (dilate period (rowNeighbors rows 13) &&& bits 13) ||| rows 13 = rows 13 := by
  decide +kernel

lemma row_checked_14 :
    (dilate period (rowNeighbors rows 14) &&& bits 14) ||| rows 14 = rows 14 := by
  decide +kernel

lemma row_checked_15 :
    (dilate period (rowNeighbors rows 15) &&& bits 15) ||| rows 15 = rows 15 := by
  decide +kernel

lemma row_checked_16 :
    (dilate period (rowNeighbors rows 16) &&& bits 16) ||| rows 16 = rows 16 := by
  decide +kernel

lemma row_checked_17 :
    (dilate period (rowNeighbors rows 17) &&& bits 17) ||| rows 17 = rows 17 := by
  decide +kernel

lemma row_checked_18 :
    (dilate period (rowNeighbors rows 18) &&& bits 18) ||| rows 18 = rows 18 := by
  decide +kernel

lemma row_checked_19 :
    (dilate period (rowNeighbors rows 19) &&& bits 19) ||| rows 19 = rows 19 := by
  decide +kernel

lemma row_checked_20 :
    (dilate period (rowNeighbors rows 20) &&& bits 20) ||| rows 20 = rows 20 := by
  decide +kernel

lemma row_checked_21 :
    (dilate period (rowNeighbors rows 21) &&& bits 21) ||| rows 21 = rows 21 := by
  decide +kernel

lemma row_checked_22 :
    (dilate period (rowNeighbors rows 22) &&& bits 22) ||| rows 22 = rows 22 := by
  decide +kernel

lemma row_checked_23 :
    (dilate period (rowNeighbors rows 23) &&& bits 23) ||| rows 23 = rows 23 := by
  decide +kernel

lemma row_checked_24 :
    (dilate period (rowNeighbors rows 24) &&& bits 24) ||| rows 24 = rows 24 := by
  decide +kernel

lemma row_checked_25 :
    (dilate period (rowNeighbors rows 25) &&& bits 25) ||| rows 25 = rows 25 := by
  decide +kernel

lemma row_checked_26 :
    (dilate period (rowNeighbors rows 26) &&& bits 26) ||| rows 26 = rows 26 := by
  decide +kernel

lemma row_checked_27 :
    (dilate period (rowNeighbors rows 27) &&& bits 27) ||| rows 27 = rows 27 := by
  decide +kernel

lemma row_checked_28 :
    (dilate period (rowNeighbors rows 28) &&& bits 28) ||| rows 28 = rows 28 := by
  decide +kernel

lemma row_checked_29 :
    (dilate period (rowNeighbors rows 29) &&& bits 29) ||| rows 29 = rows 29 := by
  decide +kernel

lemma row_checked_30 :
    (dilate period (rowNeighbors rows 30) &&& bits 30) ||| rows 30 = rows 30 := by
  decide +kernel

lemma row_checked_31 :
    (dilate period (rowNeighbors rows 31) &&& bits 31) ||| rows 31 = rows 31 := by
  decide +kernel

lemma row_checked_32 :
    (dilate period (rowNeighbors rows 32) &&& bits 32) ||| rows 32 = rows 32 := by
  decide +kernel

lemma row_checked_33 :
    (dilate period (rowNeighbors rows 33) &&& bits 33) ||| rows 33 = rows 33 := by
  decide +kernel

lemma row_checked_34 :
    (dilate period (rowNeighbors rows 34) &&& bits 34) ||| rows 34 = rows 34 := by
  decide +kernel

lemma row_checked_35 :
    (dilate period (rowNeighbors rows 35) &&& bits 35) ||| rows 35 = rows 35 := by
  decide +kernel

lemma row_checked_36 :
    (dilate period (rowNeighbors rows 36) &&& bits 36) ||| rows 36 = rows 36 := by
  decide +kernel

lemma row_checked_37 :
    (dilate period (rowNeighbors rows 37) &&& bits 37) ||| rows 37 = rows 37 := by
  decide +kernel

lemma row_checked_38 :
    (dilate period (rowNeighbors rows 38) &&& bits 38) ||| rows 38 = rows 38 := by
  decide +kernel

lemma row_checked_39 :
    (dilate period (rowNeighbors rows 39) &&& bits 39) ||| rows 39 = rows 39 := by
  decide +kernel

lemma row_checked_40 :
    (dilate period (rowNeighbors rows 40) &&& bits 40) ||| rows 40 = rows 40 := by
  decide +kernel

lemma row_checked_41 :
    (dilate period (rowNeighbors rows 41) &&& bits 41) ||| rows 41 = rows 41 := by
  decide +kernel

lemma row_checked_42 :
    (dilate period (rowNeighbors rows 42) &&& bits 42) ||| rows 42 = rows 42 := by
  decide +kernel

lemma row_checked_43 :
    (dilate period (rowNeighbors rows 43) &&& bits 43) ||| rows 43 = rows 43 := by
  decide +kernel

lemma row_checked_44 :
    (dilate period (rowNeighbors rows 44) &&& bits 44) ||| rows 44 = rows 44 := by
  decide +kernel

lemma row_checked_45 :
    (dilate period (rowNeighbors rows 45) &&& bits 45) ||| rows 45 = rows 45 := by
  decide +kernel

lemma row_checked_46 :
    (dilate period (rowNeighbors rows 46) &&& bits 46) ||| rows 46 = rows 46 := by
  decide +kernel

lemma row_checked_47 :
    (dilate period (rowNeighbors rows 47) &&& bits 47) ||| rows 47 = rows 47 := by
  decide +kernel

lemma row_checked_48 :
    (dilate period (rowNeighbors rows 48) &&& bits 48) ||| rows 48 = rows 48 := by
  decide +kernel

lemma row_checked_49 :
    (dilate period (rowNeighbors rows 49) &&& bits 49) ||| rows 49 = rows 49 := by
  decide +kernel

lemma row_checked_50 :
    (dilate period (rowNeighbors rows 50) &&& bits 50) ||| rows 50 = rows 50 := by
  decide +kernel

lemma row_checked_51 :
    (dilate period (rowNeighbors rows 51) &&& bits 51) ||| rows 51 = rows 51 := by
  decide +kernel

lemma row_checked_52 :
    (dilate period (rowNeighbors rows 52) &&& bits 52) ||| rows 52 = rows 52 := by
  decide +kernel

lemma row_checked_53 :
    (dilate period (rowNeighbors rows 53) &&& bits 53) ||| rows 53 = rows 53 := by
  decide +kernel

lemma row_checked_54 :
    (dilate period (rowNeighbors rows 54) &&& bits 54) ||| rows 54 = rows 54 := by
  decide +kernel

lemma row_checked_55 :
    (dilate period (rowNeighbors rows 55) &&& bits 55) ||| rows 55 = rows 55 := by
  decide +kernel

lemma row_checked_56 :
    (dilate period (rowNeighbors rows 56) &&& bits 56) ||| rows 56 = rows 56 := by
  decide +kernel

lemma row_checked_57 :
    (dilate period (rowNeighbors rows 57) &&& bits 57) ||| rows 57 = rows 57 := by
  decide +kernel

lemma row_checked_58 :
    (dilate period (rowNeighbors rows 58) &&& bits 58) ||| rows 58 = rows 58 := by
  decide +kernel

lemma row_checked_59 :
    (dilate period (rowNeighbors rows 59) &&& bits 59) ||| rows 59 = rows 59 := by
  decide +kernel

lemma row_checked_60 :
    (dilate period (rowNeighbors rows 60) &&& bits 60) ||| rows 60 = rows 60 := by
  decide +kernel

lemma row_checked_61 :
    (dilate period (rowNeighbors rows 61) &&& bits 61) ||| rows 61 = rows 61 := by
  decide +kernel

lemma row_checked_62 :
    (dilate period (rowNeighbors rows 62) &&& bits 62) ||| rows 62 = rows 62 := by
  decide +kernel

lemma row_checked_63 :
    (dilate period (rowNeighbors rows 63) &&& bits 63) ||| rows 63 = rows 63 := by
  decide +kernel

lemma row_checked_64 :
    (dilate period (rowNeighbors rows 64) &&& bits 64) ||| rows 64 = rows 64 := by
  decide +kernel

lemma row_checked_65 :
    (dilate period (rowNeighbors rows 65) &&& bits 65) ||| rows 65 = rows 65 := by
  decide +kernel

lemma row_checked_66 :
    (dilate period (rowNeighbors rows 66) &&& bits 66) ||| rows 66 = rows 66 := by
  decide +kernel

lemma row_checked_67 :
    (dilate period (rowNeighbors rows 67) &&& bits 67) ||| rows 67 = rows 67 := by
  decide +kernel

lemma row_checked_68 :
    (dilate period (rowNeighbors rows 68) &&& bits 68) ||| rows 68 = rows 68 := by
  decide +kernel

lemma row_checked_69 :
    (dilate period (rowNeighbors rows 69) &&& bits 69) ||| rows 69 = rows 69 := by
  decide +kernel

lemma row_checked_70 :
    (dilate period (rowNeighbors rows 70) &&& bits 70) ||| rows 70 = rows 70 := by
  decide +kernel

lemma row_checked_71 :
    (dilate period (rowNeighbors rows 71) &&& bits 71) ||| rows 71 = rows 71 := by
  decide +kernel

lemma row_checked_72 :
    (dilate period (rowNeighbors rows 72) &&& bits 72) ||| rows 72 = rows 72 := by
  decide +kernel

lemma row_checked_73 :
    (dilate period (rowNeighbors rows 73) &&& bits 73) ||| rows 73 = rows 73 := by
  decide +kernel

lemma row_checked_74 :
    (dilate period (rowNeighbors rows 74) &&& bits 74) ||| rows 74 = rows 74 := by
  decide +kernel

lemma row_checked_75 :
    (dilate period (rowNeighbors rows 75) &&& bits 75) ||| rows 75 = rows 75 := by
  decide +kernel

lemma row_checked_76 :
    (dilate period (rowNeighbors rows 76) &&& bits 76) ||| rows 76 = rows 76 := by
  decide +kernel

lemma row_checked_77 :
    (dilate period (rowNeighbors rows 77) &&& bits 77) ||| rows 77 = rows 77 := by
  decide +kernel

lemma row_checked_78 :
    (dilate period (rowNeighbors rows 78) &&& bits 78) ||| rows 78 = rows 78 := by
  decide +kernel

lemma row_checked_79 :
    (dilate period (rowNeighbors rows 79) &&& bits 79) ||| rows 79 = rows 79 := by
  decide +kernel

lemma row_checked_80 :
    (dilate period (rowNeighbors rows 80) &&& bits 80) ||| rows 80 = rows 80 := by
  decide +kernel

lemma row_checked_81 :
    (dilate period (rowNeighbors rows 81) &&& bits 81) ||| rows 81 = rows 81 := by
  decide +kernel

lemma row_checked_82 :
    (dilate period (rowNeighbors rows 82) &&& bits 82) ||| rows 82 = rows 82 := by
  decide +kernel

lemma row_checked_83 :
    (dilate period (rowNeighbors rows 83) &&& bits 83) ||| rows 83 = rows 83 := by
  decide +kernel

lemma row_checked_84 :
    (dilate period (rowNeighbors rows 84) &&& bits 84) ||| rows 84 = rows 84 := by
  decide +kernel

lemma row_checked_85 :
    (dilate period (rowNeighbors rows 85) &&& bits 85) ||| rows 85 = rows 85 := by
  decide +kernel

lemma row_checked_86 :
    (dilate period (rowNeighbors rows 86) &&& bits 86) ||| rows 86 = rows 86 := by
  decide +kernel

lemma row_checked_87 :
    (dilate period (rowNeighbors rows 87) &&& bits 87) ||| rows 87 = rows 87 := by
  decide +kernel

lemma row_checked_88 :
    (dilate period (rowNeighbors rows 88) &&& bits 88) ||| rows 88 = rows 88 := by
  decide +kernel

lemma row_checked_89 :
    (dilate period (rowNeighbors rows 89) &&& bits 89) ||| rows 89 = rows 89 := by
  decide +kernel

lemma row_checked_90 :
    (dilate period (rowNeighbors rows 90) &&& bits 90) ||| rows 90 = rows 90 := by
  decide +kernel

lemma row_checked_91 :
    (dilate period (rowNeighbors rows 91) &&& bits 91) ||| rows 91 = rows 91 := by
  decide +kernel

lemma row_checked_92 :
    (dilate period (rowNeighbors rows 92) &&& bits 92) ||| rows 92 = rows 92 := by
  decide +kernel

lemma row_checked_93 :
    (dilate period (rowNeighbors rows 93) &&& bits 93) ||| rows 93 = rows 93 := by
  decide +kernel

lemma row_checked_94 :
    (dilate period (rowNeighbors rows 94) &&& bits 94) ||| rows 94 = rows 94 := by
  decide +kernel

lemma row_checked_95 :
    (dilate period (rowNeighbors rows 95) &&& bits 95) ||| rows 95 = rows 95 := by
  decide +kernel

lemma row_checked_96 :
    (dilate period (rowNeighbors rows 96) &&& bits 96) ||| rows 96 = rows 96 := by
  decide +kernel

lemma row_checked_97 :
    (dilate period (rowNeighbors rows 97) &&& bits 97) ||| rows 97 = rows 97 := by
  decide +kernel

lemma row_checked_98 :
    (dilate period (rowNeighbors rows 98) &&& bits 98) ||| rows 98 = rows 98 := by
  decide +kernel

lemma row_checked_99 :
    (dilate period (rowNeighbors rows 99) &&& bits 99) ||| rows 99 = rows 99 := by
  decide +kernel

lemma block_checked_0 (i : Fin 100) :
    (dilate period (rowNeighbors rows (0 + i.val)) &&& bits (0 + i.val)) |||
      rows (0 + i.val) = rows (0 + i.val) := by
  fin_cases i
  · exact row_checked_0
  · exact row_checked_1
  · exact row_checked_2
  · exact row_checked_3
  · exact row_checked_4
  · exact row_checked_5
  · exact row_checked_6
  · exact row_checked_7
  · exact row_checked_8
  · exact row_checked_9
  · exact row_checked_10
  · exact row_checked_11
  · exact row_checked_12
  · exact row_checked_13
  · exact row_checked_14
  · exact row_checked_15
  · exact row_checked_16
  · exact row_checked_17
  · exact row_checked_18
  · exact row_checked_19
  · exact row_checked_20
  · exact row_checked_21
  · exact row_checked_22
  · exact row_checked_23
  · exact row_checked_24
  · exact row_checked_25
  · exact row_checked_26
  · exact row_checked_27
  · exact row_checked_28
  · exact row_checked_29
  · exact row_checked_30
  · exact row_checked_31
  · exact row_checked_32
  · exact row_checked_33
  · exact row_checked_34
  · exact row_checked_35
  · exact row_checked_36
  · exact row_checked_37
  · exact row_checked_38
  · exact row_checked_39
  · exact row_checked_40
  · exact row_checked_41
  · exact row_checked_42
  · exact row_checked_43
  · exact row_checked_44
  · exact row_checked_45
  · exact row_checked_46
  · exact row_checked_47
  · exact row_checked_48
  · exact row_checked_49
  · exact row_checked_50
  · exact row_checked_51
  · exact row_checked_52
  · exact row_checked_53
  · exact row_checked_54
  · exact row_checked_55
  · exact row_checked_56
  · exact row_checked_57
  · exact row_checked_58
  · exact row_checked_59
  · exact row_checked_60
  · exact row_checked_61
  · exact row_checked_62
  · exact row_checked_63
  · exact row_checked_64
  · exact row_checked_65
  · exact row_checked_66
  · exact row_checked_67
  · exact row_checked_68
  · exact row_checked_69
  · exact row_checked_70
  · exact row_checked_71
  · exact row_checked_72
  · exact row_checked_73
  · exact row_checked_74
  · exact row_checked_75
  · exact row_checked_76
  · exact row_checked_77
  · exact row_checked_78
  · exact row_checked_79
  · exact row_checked_80
  · exact row_checked_81
  · exact row_checked_82
  · exact row_checked_83
  · exact row_checked_84
  · exact row_checked_85
  · exact row_checked_86
  · exact row_checked_87
  · exact row_checked_88
  · exact row_checked_89
  · exact row_checked_90
  · exact row_checked_91
  · exact row_checked_92
  · exact row_checked_93
  · exact row_checked_94
  · exact row_checked_95
  · exact row_checked_96
  · exact row_checked_97
  · exact row_checked_98
  · exact row_checked_99

#print axioms row_checked_99

end Erdos952Investigation.Sieve729
