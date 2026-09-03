import FormalConjecturesUtil

namespace Erdos406BalancedAssemblyTest
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def stepCheck (_ : Fin 397) := true
def finishCheck (_ : Fin 397) := true
lemma step_check_chunk_0 (p : Fin 397) (hl : 0 ≤ p.val) (hh : p.val < 4) : stepCheck p = true := by rfl
lemma step_check_chunk_1 (p : Fin 397) (hl : 4 ≤ p.val) (hh : p.val < 8) : stepCheck p = true := by rfl
lemma step_check_chunk_2 (p : Fin 397) (hl : 8 ≤ p.val) (hh : p.val < 12) : stepCheck p = true := by rfl
lemma step_check_chunk_3 (p : Fin 397) (hl : 12 ≤ p.val) (hh : p.val < 16) : stepCheck p = true := by rfl
lemma step_check_chunk_4 (p : Fin 397) (hl : 16 ≤ p.val) (hh : p.val < 20) : stepCheck p = true := by rfl
lemma step_check_chunk_5 (p : Fin 397) (hl : 20 ≤ p.val) (hh : p.val < 24) : stepCheck p = true := by rfl
lemma step_check_chunk_6 (p : Fin 397) (hl : 24 ≤ p.val) (hh : p.val < 28) : stepCheck p = true := by rfl
lemma step_check_chunk_7 (p : Fin 397) (hl : 28 ≤ p.val) (hh : p.val < 32) : stepCheck p = true := by rfl
lemma step_check_chunk_8 (p : Fin 397) (hl : 32 ≤ p.val) (hh : p.val < 36) : stepCheck p = true := by rfl
lemma step_check_chunk_9 (p : Fin 397) (hl : 36 ≤ p.val) (hh : p.val < 40) : stepCheck p = true := by rfl
lemma step_check_chunk_10 (p : Fin 397) (hl : 40 ≤ p.val) (hh : p.val < 44) : stepCheck p = true := by rfl
lemma step_check_chunk_11 (p : Fin 397) (hl : 44 ≤ p.val) (hh : p.val < 48) : stepCheck p = true := by rfl
lemma step_check_chunk_12 (p : Fin 397) (hl : 48 ≤ p.val) (hh : p.val < 52) : stepCheck p = true := by rfl
lemma step_check_chunk_13 (p : Fin 397) (hl : 52 ≤ p.val) (hh : p.val < 56) : stepCheck p = true := by rfl
lemma step_check_chunk_14 (p : Fin 397) (hl : 56 ≤ p.val) (hh : p.val < 60) : stepCheck p = true := by rfl
lemma step_check_chunk_15 (p : Fin 397) (hl : 60 ≤ p.val) (hh : p.val < 64) : stepCheck p = true := by rfl
lemma step_check_chunk_16 (p : Fin 397) (hl : 64 ≤ p.val) (hh : p.val < 68) : stepCheck p = true := by rfl
lemma step_check_chunk_17 (p : Fin 397) (hl : 68 ≤ p.val) (hh : p.val < 72) : stepCheck p = true := by rfl
lemma step_check_chunk_18 (p : Fin 397) (hl : 72 ≤ p.val) (hh : p.val < 76) : stepCheck p = true := by rfl
lemma step_check_chunk_19 (p : Fin 397) (hl : 76 ≤ p.val) (hh : p.val < 80) : stepCheck p = true := by rfl
lemma step_check_chunk_20 (p : Fin 397) (hl : 80 ≤ p.val) (hh : p.val < 84) : stepCheck p = true := by rfl
lemma step_check_chunk_21 (p : Fin 397) (hl : 84 ≤ p.val) (hh : p.val < 88) : stepCheck p = true := by rfl
lemma step_check_chunk_22 (p : Fin 397) (hl : 88 ≤ p.val) (hh : p.val < 92) : stepCheck p = true := by rfl
lemma step_check_chunk_23 (p : Fin 397) (hl : 92 ≤ p.val) (hh : p.val < 96) : stepCheck p = true := by rfl
lemma step_check_chunk_24 (p : Fin 397) (hl : 96 ≤ p.val) (hh : p.val < 100) : stepCheck p = true := by rfl
lemma step_check_chunk_25 (p : Fin 397) (hl : 100 ≤ p.val) (hh : p.val < 104) : stepCheck p = true := by rfl
lemma step_check_chunk_26 (p : Fin 397) (hl : 104 ≤ p.val) (hh : p.val < 108) : stepCheck p = true := by rfl
lemma step_check_chunk_27 (p : Fin 397) (hl : 108 ≤ p.val) (hh : p.val < 112) : stepCheck p = true := by rfl
lemma step_check_chunk_28 (p : Fin 397) (hl : 112 ≤ p.val) (hh : p.val < 116) : stepCheck p = true := by rfl
lemma step_check_chunk_29 (p : Fin 397) (hl : 116 ≤ p.val) (hh : p.val < 120) : stepCheck p = true := by rfl
lemma step_check_chunk_30 (p : Fin 397) (hl : 120 ≤ p.val) (hh : p.val < 124) : stepCheck p = true := by rfl
lemma step_check_chunk_31 (p : Fin 397) (hl : 124 ≤ p.val) (hh : p.val < 128) : stepCheck p = true := by rfl
lemma step_check_chunk_32 (p : Fin 397) (hl : 128 ≤ p.val) (hh : p.val < 132) : stepCheck p = true := by rfl
lemma step_check_chunk_33 (p : Fin 397) (hl : 132 ≤ p.val) (hh : p.val < 136) : stepCheck p = true := by rfl
lemma step_check_chunk_34 (p : Fin 397) (hl : 136 ≤ p.val) (hh : p.val < 140) : stepCheck p = true := by rfl
lemma step_check_chunk_35 (p : Fin 397) (hl : 140 ≤ p.val) (hh : p.val < 144) : stepCheck p = true := by rfl
lemma step_check_chunk_36 (p : Fin 397) (hl : 144 ≤ p.val) (hh : p.val < 148) : stepCheck p = true := by rfl
lemma step_check_chunk_37 (p : Fin 397) (hl : 148 ≤ p.val) (hh : p.val < 152) : stepCheck p = true := by rfl
lemma step_check_chunk_38 (p : Fin 397) (hl : 152 ≤ p.val) (hh : p.val < 156) : stepCheck p = true := by rfl
lemma step_check_chunk_39 (p : Fin 397) (hl : 156 ≤ p.val) (hh : p.val < 160) : stepCheck p = true := by rfl
lemma step_check_chunk_40 (p : Fin 397) (hl : 160 ≤ p.val) (hh : p.val < 164) : stepCheck p = true := by rfl
lemma step_check_chunk_41 (p : Fin 397) (hl : 164 ≤ p.val) (hh : p.val < 168) : stepCheck p = true := by rfl
lemma step_check_chunk_42 (p : Fin 397) (hl : 168 ≤ p.val) (hh : p.val < 172) : stepCheck p = true := by rfl
lemma step_check_chunk_43 (p : Fin 397) (hl : 172 ≤ p.val) (hh : p.val < 176) : stepCheck p = true := by rfl
lemma step_check_chunk_44 (p : Fin 397) (hl : 176 ≤ p.val) (hh : p.val < 180) : stepCheck p = true := by rfl
lemma step_check_chunk_45 (p : Fin 397) (hl : 180 ≤ p.val) (hh : p.val < 184) : stepCheck p = true := by rfl
lemma step_check_chunk_46 (p : Fin 397) (hl : 184 ≤ p.val) (hh : p.val < 188) : stepCheck p = true := by rfl
lemma step_check_chunk_47 (p : Fin 397) (hl : 188 ≤ p.val) (hh : p.val < 192) : stepCheck p = true := by rfl
lemma step_check_chunk_48 (p : Fin 397) (hl : 192 ≤ p.val) (hh : p.val < 196) : stepCheck p = true := by rfl
lemma step_check_chunk_49 (p : Fin 397) (hl : 196 ≤ p.val) (hh : p.val < 200) : stepCheck p = true := by rfl
lemma step_check_chunk_50 (p : Fin 397) (hl : 200 ≤ p.val) (hh : p.val < 204) : stepCheck p = true := by rfl
lemma step_check_chunk_51 (p : Fin 397) (hl : 204 ≤ p.val) (hh : p.val < 208) : stepCheck p = true := by rfl
lemma step_check_chunk_52 (p : Fin 397) (hl : 208 ≤ p.val) (hh : p.val < 212) : stepCheck p = true := by rfl
lemma step_check_chunk_53 (p : Fin 397) (hl : 212 ≤ p.val) (hh : p.val < 216) : stepCheck p = true := by rfl
lemma step_check_chunk_54 (p : Fin 397) (hl : 216 ≤ p.val) (hh : p.val < 220) : stepCheck p = true := by rfl
lemma step_check_chunk_55 (p : Fin 397) (hl : 220 ≤ p.val) (hh : p.val < 224) : stepCheck p = true := by rfl
lemma step_check_chunk_56 (p : Fin 397) (hl : 224 ≤ p.val) (hh : p.val < 228) : stepCheck p = true := by rfl
lemma step_check_chunk_57 (p : Fin 397) (hl : 228 ≤ p.val) (hh : p.val < 232) : stepCheck p = true := by rfl
lemma step_check_chunk_58 (p : Fin 397) (hl : 232 ≤ p.val) (hh : p.val < 236) : stepCheck p = true := by rfl
lemma step_check_chunk_59 (p : Fin 397) (hl : 236 ≤ p.val) (hh : p.val < 240) : stepCheck p = true := by rfl
lemma step_check_chunk_60 (p : Fin 397) (hl : 240 ≤ p.val) (hh : p.val < 244) : stepCheck p = true := by rfl
lemma step_check_chunk_61 (p : Fin 397) (hl : 244 ≤ p.val) (hh : p.val < 248) : stepCheck p = true := by rfl
lemma step_check_chunk_62 (p : Fin 397) (hl : 248 ≤ p.val) (hh : p.val < 252) : stepCheck p = true := by rfl
lemma step_check_chunk_63 (p : Fin 397) (hl : 252 ≤ p.val) (hh : p.val < 256) : stepCheck p = true := by rfl
lemma step_check_chunk_64 (p : Fin 397) (hl : 256 ≤ p.val) (hh : p.val < 260) : stepCheck p = true := by rfl
lemma step_check_chunk_65 (p : Fin 397) (hl : 260 ≤ p.val) (hh : p.val < 264) : stepCheck p = true := by rfl
lemma step_check_chunk_66 (p : Fin 397) (hl : 264 ≤ p.val) (hh : p.val < 268) : stepCheck p = true := by rfl
lemma step_check_chunk_67 (p : Fin 397) (hl : 268 ≤ p.val) (hh : p.val < 272) : stepCheck p = true := by rfl
lemma step_check_chunk_68 (p : Fin 397) (hl : 272 ≤ p.val) (hh : p.val < 276) : stepCheck p = true := by rfl
lemma step_check_chunk_69 (p : Fin 397) (hl : 276 ≤ p.val) (hh : p.val < 280) : stepCheck p = true := by rfl
lemma step_check_chunk_70 (p : Fin 397) (hl : 280 ≤ p.val) (hh : p.val < 284) : stepCheck p = true := by rfl
lemma step_check_chunk_71 (p : Fin 397) (hl : 284 ≤ p.val) (hh : p.val < 288) : stepCheck p = true := by rfl
lemma step_check_chunk_72 (p : Fin 397) (hl : 288 ≤ p.val) (hh : p.val < 292) : stepCheck p = true := by rfl
lemma step_check_chunk_73 (p : Fin 397) (hl : 292 ≤ p.val) (hh : p.val < 296) : stepCheck p = true := by rfl
lemma step_check_chunk_74 (p : Fin 397) (hl : 296 ≤ p.val) (hh : p.val < 300) : stepCheck p = true := by rfl
lemma step_check_chunk_75 (p : Fin 397) (hl : 300 ≤ p.val) (hh : p.val < 304) : stepCheck p = true := by rfl
lemma step_check_chunk_76 (p : Fin 397) (hl : 304 ≤ p.val) (hh : p.val < 308) : stepCheck p = true := by rfl
lemma step_check_chunk_77 (p : Fin 397) (hl : 308 ≤ p.val) (hh : p.val < 312) : stepCheck p = true := by rfl
lemma step_check_chunk_78 (p : Fin 397) (hl : 312 ≤ p.val) (hh : p.val < 316) : stepCheck p = true := by rfl
lemma step_check_chunk_79 (p : Fin 397) (hl : 316 ≤ p.val) (hh : p.val < 320) : stepCheck p = true := by rfl
lemma step_check_chunk_80 (p : Fin 397) (hl : 320 ≤ p.val) (hh : p.val < 324) : stepCheck p = true := by rfl
lemma step_check_chunk_81 (p : Fin 397) (hl : 324 ≤ p.val) (hh : p.val < 328) : stepCheck p = true := by rfl
lemma step_check_chunk_82 (p : Fin 397) (hl : 328 ≤ p.val) (hh : p.val < 332) : stepCheck p = true := by rfl
lemma step_check_chunk_83 (p : Fin 397) (hl : 332 ≤ p.val) (hh : p.val < 336) : stepCheck p = true := by rfl
lemma step_check_chunk_84 (p : Fin 397) (hl : 336 ≤ p.val) (hh : p.val < 340) : stepCheck p = true := by rfl
lemma step_check_chunk_85 (p : Fin 397) (hl : 340 ≤ p.val) (hh : p.val < 344) : stepCheck p = true := by rfl
lemma step_check_chunk_86 (p : Fin 397) (hl : 344 ≤ p.val) (hh : p.val < 348) : stepCheck p = true := by rfl
lemma step_check_chunk_87 (p : Fin 397) (hl : 348 ≤ p.val) (hh : p.val < 352) : stepCheck p = true := by rfl
lemma step_check_chunk_88 (p : Fin 397) (hl : 352 ≤ p.val) (hh : p.val < 356) : stepCheck p = true := by rfl
lemma step_check_chunk_89 (p : Fin 397) (hl : 356 ≤ p.val) (hh : p.val < 360) : stepCheck p = true := by rfl
lemma step_check_chunk_90 (p : Fin 397) (hl : 360 ≤ p.val) (hh : p.val < 364) : stepCheck p = true := by rfl
lemma step_check_chunk_91 (p : Fin 397) (hl : 364 ≤ p.val) (hh : p.val < 368) : stepCheck p = true := by rfl
lemma step_check_chunk_92 (p : Fin 397) (hl : 368 ≤ p.val) (hh : p.val < 372) : stepCheck p = true := by rfl
lemma step_check_chunk_93 (p : Fin 397) (hl : 372 ≤ p.val) (hh : p.val < 376) : stepCheck p = true := by rfl
lemma step_check_chunk_94 (p : Fin 397) (hl : 376 ≤ p.val) (hh : p.val < 380) : stepCheck p = true := by rfl
lemma step_check_chunk_95 (p : Fin 397) (hl : 380 ≤ p.val) (hh : p.val < 384) : stepCheck p = true := by rfl
lemma step_check_chunk_96 (p : Fin 397) (hl : 384 ≤ p.val) (hh : p.val < 388) : stepCheck p = true := by rfl
lemma step_check_chunk_97 (p : Fin 397) (hl : 388 ≤ p.val) (hh : p.val < 392) : stepCheck p = true := by rfl
lemma step_check_chunk_98 (p : Fin 397) (hl : 392 ≤ p.val) (hh : p.val < 396) : stepCheck p = true := by rfl
lemma step_check_chunk_99 (p : Fin 397) (hl : 396 ≤ p.val) (hh : p.val < 397) : stepCheck p = true := by rfl
lemma step_check_all (p : Fin 397) : stepCheck p = true := by
  have hlo_root : 0 ≤ p.val := Nat.zero_le _
  have hhi_root : p.val < 397 := p.isLt
  by_cases hmid_0_100 : p.val < 200
  · by_cases hmid_0_50 : p.val < 100
    · by_cases hmid_0_25 : p.val < 48
      · by_cases hmid_0_12 : p.val < 24
        · by_cases hmid_0_6 : p.val < 12
          · by_cases hmid_0_3 : p.val < 4
            · exact step_check_chunk_0 p hlo_root hmid_0_3
            · have hlo_1_3 : 4 ≤ p.val := Nat.le_of_not_gt hmid_0_3
              by_cases hmid_1_3 : p.val < 8
              · exact step_check_chunk_1 p hlo_1_3 hmid_1_3
              · have hlo_2_3 : 8 ≤ p.val := Nat.le_of_not_gt hmid_1_3
                exact step_check_chunk_2 p hlo_2_3 hmid_0_6
          · have hlo_3_6 : 12 ≤ p.val := Nat.le_of_not_gt hmid_0_6
            by_cases hmid_3_6 : p.val < 16
            · exact step_check_chunk_3 p hlo_3_6 hmid_3_6
            · have hlo_4_6 : 16 ≤ p.val := Nat.le_of_not_gt hmid_3_6
              by_cases hmid_4_6 : p.val < 20
              · exact step_check_chunk_4 p hlo_4_6 hmid_4_6
              · have hlo_5_6 : 20 ≤ p.val := Nat.le_of_not_gt hmid_4_6
                exact step_check_chunk_5 p hlo_5_6 hmid_0_12
        · have hlo_6_12 : 24 ≤ p.val := Nat.le_of_not_gt hmid_0_12
          by_cases hmid_6_12 : p.val < 36
          · by_cases hmid_6_9 : p.val < 28
            · exact step_check_chunk_6 p hlo_6_12 hmid_6_9
            · have hlo_7_9 : 28 ≤ p.val := Nat.le_of_not_gt hmid_6_9
              by_cases hmid_7_9 : p.val < 32
              · exact step_check_chunk_7 p hlo_7_9 hmid_7_9
              · have hlo_8_9 : 32 ≤ p.val := Nat.le_of_not_gt hmid_7_9
                exact step_check_chunk_8 p hlo_8_9 hmid_6_12
          · have hlo_9_12 : 36 ≤ p.val := Nat.le_of_not_gt hmid_6_12
            by_cases hmid_9_12 : p.val < 40
            · exact step_check_chunk_9 p hlo_9_12 hmid_9_12
            · have hlo_10_12 : 40 ≤ p.val := Nat.le_of_not_gt hmid_9_12
              by_cases hmid_10_12 : p.val < 44
              · exact step_check_chunk_10 p hlo_10_12 hmid_10_12
              · have hlo_11_12 : 44 ≤ p.val := Nat.le_of_not_gt hmid_10_12
                exact step_check_chunk_11 p hlo_11_12 hmid_0_25
      · have hlo_12_25 : 48 ≤ p.val := Nat.le_of_not_gt hmid_0_25
        by_cases hmid_12_25 : p.val < 72
        · by_cases hmid_12_18 : p.val < 60
          · by_cases hmid_12_15 : p.val < 52
            · exact step_check_chunk_12 p hlo_12_25 hmid_12_15
            · have hlo_13_15 : 52 ≤ p.val := Nat.le_of_not_gt hmid_12_15
              by_cases hmid_13_15 : p.val < 56
              · exact step_check_chunk_13 p hlo_13_15 hmid_13_15
              · have hlo_14_15 : 56 ≤ p.val := Nat.le_of_not_gt hmid_13_15
                exact step_check_chunk_14 p hlo_14_15 hmid_12_18
          · have hlo_15_18 : 60 ≤ p.val := Nat.le_of_not_gt hmid_12_18
            by_cases hmid_15_18 : p.val < 64
            · exact step_check_chunk_15 p hlo_15_18 hmid_15_18
            · have hlo_16_18 : 64 ≤ p.val := Nat.le_of_not_gt hmid_15_18
              by_cases hmid_16_18 : p.val < 68
              · exact step_check_chunk_16 p hlo_16_18 hmid_16_18
              · have hlo_17_18 : 68 ≤ p.val := Nat.le_of_not_gt hmid_16_18
                exact step_check_chunk_17 p hlo_17_18 hmid_12_25
        · have hlo_18_25 : 72 ≤ p.val := Nat.le_of_not_gt hmid_12_25
          by_cases hmid_18_25 : p.val < 84
          · by_cases hmid_18_21 : p.val < 76
            · exact step_check_chunk_18 p hlo_18_25 hmid_18_21
            · have hlo_19_21 : 76 ≤ p.val := Nat.le_of_not_gt hmid_18_21
              by_cases hmid_19_21 : p.val < 80
              · exact step_check_chunk_19 p hlo_19_21 hmid_19_21
              · have hlo_20_21 : 80 ≤ p.val := Nat.le_of_not_gt hmid_19_21
                exact step_check_chunk_20 p hlo_20_21 hmid_18_25
          · have hlo_21_25 : 84 ≤ p.val := Nat.le_of_not_gt hmid_18_25
            by_cases hmid_21_25 : p.val < 92
            · by_cases hmid_21_23 : p.val < 88
              · exact step_check_chunk_21 p hlo_21_25 hmid_21_23
              · have hlo_22_23 : 88 ≤ p.val := Nat.le_of_not_gt hmid_21_23
                exact step_check_chunk_22 p hlo_22_23 hmid_21_25
            · have hlo_23_25 : 92 ≤ p.val := Nat.le_of_not_gt hmid_21_25
              by_cases hmid_23_25 : p.val < 96
              · exact step_check_chunk_23 p hlo_23_25 hmid_23_25
              · have hlo_24_25 : 96 ≤ p.val := Nat.le_of_not_gt hmid_23_25
                exact step_check_chunk_24 p hlo_24_25 hmid_0_50
    · have hlo_25_50 : 100 ≤ p.val := Nat.le_of_not_gt hmid_0_50
      by_cases hmid_25_50 : p.val < 148
      · by_cases hmid_25_37 : p.val < 124
        · by_cases hmid_25_31 : p.val < 112
          · by_cases hmid_25_28 : p.val < 104
            · exact step_check_chunk_25 p hlo_25_50 hmid_25_28
            · have hlo_26_28 : 104 ≤ p.val := Nat.le_of_not_gt hmid_25_28
              by_cases hmid_26_28 : p.val < 108
              · exact step_check_chunk_26 p hlo_26_28 hmid_26_28
              · have hlo_27_28 : 108 ≤ p.val := Nat.le_of_not_gt hmid_26_28
                exact step_check_chunk_27 p hlo_27_28 hmid_25_31
          · have hlo_28_31 : 112 ≤ p.val := Nat.le_of_not_gt hmid_25_31
            by_cases hmid_28_31 : p.val < 116
            · exact step_check_chunk_28 p hlo_28_31 hmid_28_31
            · have hlo_29_31 : 116 ≤ p.val := Nat.le_of_not_gt hmid_28_31
              by_cases hmid_29_31 : p.val < 120
              · exact step_check_chunk_29 p hlo_29_31 hmid_29_31
              · have hlo_30_31 : 120 ≤ p.val := Nat.le_of_not_gt hmid_29_31
                exact step_check_chunk_30 p hlo_30_31 hmid_25_37
        · have hlo_31_37 : 124 ≤ p.val := Nat.le_of_not_gt hmid_25_37
          by_cases hmid_31_37 : p.val < 136
          · by_cases hmid_31_34 : p.val < 128
            · exact step_check_chunk_31 p hlo_31_37 hmid_31_34
            · have hlo_32_34 : 128 ≤ p.val := Nat.le_of_not_gt hmid_31_34
              by_cases hmid_32_34 : p.val < 132
              · exact step_check_chunk_32 p hlo_32_34 hmid_32_34
              · have hlo_33_34 : 132 ≤ p.val := Nat.le_of_not_gt hmid_32_34
                exact step_check_chunk_33 p hlo_33_34 hmid_31_37
          · have hlo_34_37 : 136 ≤ p.val := Nat.le_of_not_gt hmid_31_37
            by_cases hmid_34_37 : p.val < 140
            · exact step_check_chunk_34 p hlo_34_37 hmid_34_37
            · have hlo_35_37 : 140 ≤ p.val := Nat.le_of_not_gt hmid_34_37
              by_cases hmid_35_37 : p.val < 144
              · exact step_check_chunk_35 p hlo_35_37 hmid_35_37
              · have hlo_36_37 : 144 ≤ p.val := Nat.le_of_not_gt hmid_35_37
                exact step_check_chunk_36 p hlo_36_37 hmid_25_50
      · have hlo_37_50 : 148 ≤ p.val := Nat.le_of_not_gt hmid_25_50
        by_cases hmid_37_50 : p.val < 172
        · by_cases hmid_37_43 : p.val < 160
          · by_cases hmid_37_40 : p.val < 152
            · exact step_check_chunk_37 p hlo_37_50 hmid_37_40
            · have hlo_38_40 : 152 ≤ p.val := Nat.le_of_not_gt hmid_37_40
              by_cases hmid_38_40 : p.val < 156
              · exact step_check_chunk_38 p hlo_38_40 hmid_38_40
              · have hlo_39_40 : 156 ≤ p.val := Nat.le_of_not_gt hmid_38_40
                exact step_check_chunk_39 p hlo_39_40 hmid_37_43
          · have hlo_40_43 : 160 ≤ p.val := Nat.le_of_not_gt hmid_37_43
            by_cases hmid_40_43 : p.val < 164
            · exact step_check_chunk_40 p hlo_40_43 hmid_40_43
            · have hlo_41_43 : 164 ≤ p.val := Nat.le_of_not_gt hmid_40_43
              by_cases hmid_41_43 : p.val < 168
              · exact step_check_chunk_41 p hlo_41_43 hmid_41_43
              · have hlo_42_43 : 168 ≤ p.val := Nat.le_of_not_gt hmid_41_43
                exact step_check_chunk_42 p hlo_42_43 hmid_37_50
        · have hlo_43_50 : 172 ≤ p.val := Nat.le_of_not_gt hmid_37_50
          by_cases hmid_43_50 : p.val < 184
          · by_cases hmid_43_46 : p.val < 176
            · exact step_check_chunk_43 p hlo_43_50 hmid_43_46
            · have hlo_44_46 : 176 ≤ p.val := Nat.le_of_not_gt hmid_43_46
              by_cases hmid_44_46 : p.val < 180
              · exact step_check_chunk_44 p hlo_44_46 hmid_44_46
              · have hlo_45_46 : 180 ≤ p.val := Nat.le_of_not_gt hmid_44_46
                exact step_check_chunk_45 p hlo_45_46 hmid_43_50
          · have hlo_46_50 : 184 ≤ p.val := Nat.le_of_not_gt hmid_43_50
            by_cases hmid_46_50 : p.val < 192
            · by_cases hmid_46_48 : p.val < 188
              · exact step_check_chunk_46 p hlo_46_50 hmid_46_48
              · have hlo_47_48 : 188 ≤ p.val := Nat.le_of_not_gt hmid_46_48
                exact step_check_chunk_47 p hlo_47_48 hmid_46_50
            · have hlo_48_50 : 192 ≤ p.val := Nat.le_of_not_gt hmid_46_50
              by_cases hmid_48_50 : p.val < 196
              · exact step_check_chunk_48 p hlo_48_50 hmid_48_50
              · have hlo_49_50 : 196 ≤ p.val := Nat.le_of_not_gt hmid_48_50
                exact step_check_chunk_49 p hlo_49_50 hmid_0_100
  · have hlo_50_100 : 200 ≤ p.val := Nat.le_of_not_gt hmid_0_100
    by_cases hmid_50_100 : p.val < 300
    · by_cases hmid_50_75 : p.val < 248
      · by_cases hmid_50_62 : p.val < 224
        · by_cases hmid_50_56 : p.val < 212
          · by_cases hmid_50_53 : p.val < 204
            · exact step_check_chunk_50 p hlo_50_100 hmid_50_53
            · have hlo_51_53 : 204 ≤ p.val := Nat.le_of_not_gt hmid_50_53
              by_cases hmid_51_53 : p.val < 208
              · exact step_check_chunk_51 p hlo_51_53 hmid_51_53
              · have hlo_52_53 : 208 ≤ p.val := Nat.le_of_not_gt hmid_51_53
                exact step_check_chunk_52 p hlo_52_53 hmid_50_56
          · have hlo_53_56 : 212 ≤ p.val := Nat.le_of_not_gt hmid_50_56
            by_cases hmid_53_56 : p.val < 216
            · exact step_check_chunk_53 p hlo_53_56 hmid_53_56
            · have hlo_54_56 : 216 ≤ p.val := Nat.le_of_not_gt hmid_53_56
              by_cases hmid_54_56 : p.val < 220
              · exact step_check_chunk_54 p hlo_54_56 hmid_54_56
              · have hlo_55_56 : 220 ≤ p.val := Nat.le_of_not_gt hmid_54_56
                exact step_check_chunk_55 p hlo_55_56 hmid_50_62
        · have hlo_56_62 : 224 ≤ p.val := Nat.le_of_not_gt hmid_50_62
          by_cases hmid_56_62 : p.val < 236
          · by_cases hmid_56_59 : p.val < 228
            · exact step_check_chunk_56 p hlo_56_62 hmid_56_59
            · have hlo_57_59 : 228 ≤ p.val := Nat.le_of_not_gt hmid_56_59
              by_cases hmid_57_59 : p.val < 232
              · exact step_check_chunk_57 p hlo_57_59 hmid_57_59
              · have hlo_58_59 : 232 ≤ p.val := Nat.le_of_not_gt hmid_57_59
                exact step_check_chunk_58 p hlo_58_59 hmid_56_62
          · have hlo_59_62 : 236 ≤ p.val := Nat.le_of_not_gt hmid_56_62
            by_cases hmid_59_62 : p.val < 240
            · exact step_check_chunk_59 p hlo_59_62 hmid_59_62
            · have hlo_60_62 : 240 ≤ p.val := Nat.le_of_not_gt hmid_59_62
              by_cases hmid_60_62 : p.val < 244
              · exact step_check_chunk_60 p hlo_60_62 hmid_60_62
              · have hlo_61_62 : 244 ≤ p.val := Nat.le_of_not_gt hmid_60_62
                exact step_check_chunk_61 p hlo_61_62 hmid_50_75
      · have hlo_62_75 : 248 ≤ p.val := Nat.le_of_not_gt hmid_50_75
        by_cases hmid_62_75 : p.val < 272
        · by_cases hmid_62_68 : p.val < 260
          · by_cases hmid_62_65 : p.val < 252
            · exact step_check_chunk_62 p hlo_62_75 hmid_62_65
            · have hlo_63_65 : 252 ≤ p.val := Nat.le_of_not_gt hmid_62_65
              by_cases hmid_63_65 : p.val < 256
              · exact step_check_chunk_63 p hlo_63_65 hmid_63_65
              · have hlo_64_65 : 256 ≤ p.val := Nat.le_of_not_gt hmid_63_65
                exact step_check_chunk_64 p hlo_64_65 hmid_62_68
          · have hlo_65_68 : 260 ≤ p.val := Nat.le_of_not_gt hmid_62_68
            by_cases hmid_65_68 : p.val < 264
            · exact step_check_chunk_65 p hlo_65_68 hmid_65_68
            · have hlo_66_68 : 264 ≤ p.val := Nat.le_of_not_gt hmid_65_68
              by_cases hmid_66_68 : p.val < 268
              · exact step_check_chunk_66 p hlo_66_68 hmid_66_68
              · have hlo_67_68 : 268 ≤ p.val := Nat.le_of_not_gt hmid_66_68
                exact step_check_chunk_67 p hlo_67_68 hmid_62_75
        · have hlo_68_75 : 272 ≤ p.val := Nat.le_of_not_gt hmid_62_75
          by_cases hmid_68_75 : p.val < 284
          · by_cases hmid_68_71 : p.val < 276
            · exact step_check_chunk_68 p hlo_68_75 hmid_68_71
            · have hlo_69_71 : 276 ≤ p.val := Nat.le_of_not_gt hmid_68_71
              by_cases hmid_69_71 : p.val < 280
              · exact step_check_chunk_69 p hlo_69_71 hmid_69_71
              · have hlo_70_71 : 280 ≤ p.val := Nat.le_of_not_gt hmid_69_71
                exact step_check_chunk_70 p hlo_70_71 hmid_68_75
          · have hlo_71_75 : 284 ≤ p.val := Nat.le_of_not_gt hmid_68_75
            by_cases hmid_71_75 : p.val < 292
            · by_cases hmid_71_73 : p.val < 288
              · exact step_check_chunk_71 p hlo_71_75 hmid_71_73
              · have hlo_72_73 : 288 ≤ p.val := Nat.le_of_not_gt hmid_71_73
                exact step_check_chunk_72 p hlo_72_73 hmid_71_75
            · have hlo_73_75 : 292 ≤ p.val := Nat.le_of_not_gt hmid_71_75
              by_cases hmid_73_75 : p.val < 296
              · exact step_check_chunk_73 p hlo_73_75 hmid_73_75
              · have hlo_74_75 : 296 ≤ p.val := Nat.le_of_not_gt hmid_73_75
                exact step_check_chunk_74 p hlo_74_75 hmid_50_100
    · have hlo_75_100 : 300 ≤ p.val := Nat.le_of_not_gt hmid_50_100
      by_cases hmid_75_100 : p.val < 348
      · by_cases hmid_75_87 : p.val < 324
        · by_cases hmid_75_81 : p.val < 312
          · by_cases hmid_75_78 : p.val < 304
            · exact step_check_chunk_75 p hlo_75_100 hmid_75_78
            · have hlo_76_78 : 304 ≤ p.val := Nat.le_of_not_gt hmid_75_78
              by_cases hmid_76_78 : p.val < 308
              · exact step_check_chunk_76 p hlo_76_78 hmid_76_78
              · have hlo_77_78 : 308 ≤ p.val := Nat.le_of_not_gt hmid_76_78
                exact step_check_chunk_77 p hlo_77_78 hmid_75_81
          · have hlo_78_81 : 312 ≤ p.val := Nat.le_of_not_gt hmid_75_81
            by_cases hmid_78_81 : p.val < 316
            · exact step_check_chunk_78 p hlo_78_81 hmid_78_81
            · have hlo_79_81 : 316 ≤ p.val := Nat.le_of_not_gt hmid_78_81
              by_cases hmid_79_81 : p.val < 320
              · exact step_check_chunk_79 p hlo_79_81 hmid_79_81
              · have hlo_80_81 : 320 ≤ p.val := Nat.le_of_not_gt hmid_79_81
                exact step_check_chunk_80 p hlo_80_81 hmid_75_87
        · have hlo_81_87 : 324 ≤ p.val := Nat.le_of_not_gt hmid_75_87
          by_cases hmid_81_87 : p.val < 336
          · by_cases hmid_81_84 : p.val < 328
            · exact step_check_chunk_81 p hlo_81_87 hmid_81_84
            · have hlo_82_84 : 328 ≤ p.val := Nat.le_of_not_gt hmid_81_84
              by_cases hmid_82_84 : p.val < 332
              · exact step_check_chunk_82 p hlo_82_84 hmid_82_84
              · have hlo_83_84 : 332 ≤ p.val := Nat.le_of_not_gt hmid_82_84
                exact step_check_chunk_83 p hlo_83_84 hmid_81_87
          · have hlo_84_87 : 336 ≤ p.val := Nat.le_of_not_gt hmid_81_87
            by_cases hmid_84_87 : p.val < 340
            · exact step_check_chunk_84 p hlo_84_87 hmid_84_87
            · have hlo_85_87 : 340 ≤ p.val := Nat.le_of_not_gt hmid_84_87
              by_cases hmid_85_87 : p.val < 344
              · exact step_check_chunk_85 p hlo_85_87 hmid_85_87
              · have hlo_86_87 : 344 ≤ p.val := Nat.le_of_not_gt hmid_85_87
                exact step_check_chunk_86 p hlo_86_87 hmid_75_100
      · have hlo_87_100 : 348 ≤ p.val := Nat.le_of_not_gt hmid_75_100
        by_cases hmid_87_100 : p.val < 372
        · by_cases hmid_87_93 : p.val < 360
          · by_cases hmid_87_90 : p.val < 352
            · exact step_check_chunk_87 p hlo_87_100 hmid_87_90
            · have hlo_88_90 : 352 ≤ p.val := Nat.le_of_not_gt hmid_87_90
              by_cases hmid_88_90 : p.val < 356
              · exact step_check_chunk_88 p hlo_88_90 hmid_88_90
              · have hlo_89_90 : 356 ≤ p.val := Nat.le_of_not_gt hmid_88_90
                exact step_check_chunk_89 p hlo_89_90 hmid_87_93
          · have hlo_90_93 : 360 ≤ p.val := Nat.le_of_not_gt hmid_87_93
            by_cases hmid_90_93 : p.val < 364
            · exact step_check_chunk_90 p hlo_90_93 hmid_90_93
            · have hlo_91_93 : 364 ≤ p.val := Nat.le_of_not_gt hmid_90_93
              by_cases hmid_91_93 : p.val < 368
              · exact step_check_chunk_91 p hlo_91_93 hmid_91_93
              · have hlo_92_93 : 368 ≤ p.val := Nat.le_of_not_gt hmid_91_93
                exact step_check_chunk_92 p hlo_92_93 hmid_87_100
        · have hlo_93_100 : 372 ≤ p.val := Nat.le_of_not_gt hmid_87_100
          by_cases hmid_93_100 : p.val < 384
          · by_cases hmid_93_96 : p.val < 376
            · exact step_check_chunk_93 p hlo_93_100 hmid_93_96
            · have hlo_94_96 : 376 ≤ p.val := Nat.le_of_not_gt hmid_93_96
              by_cases hmid_94_96 : p.val < 380
              · exact step_check_chunk_94 p hlo_94_96 hmid_94_96
              · have hlo_95_96 : 380 ≤ p.val := Nat.le_of_not_gt hmid_94_96
                exact step_check_chunk_95 p hlo_95_96 hmid_93_100
          · have hlo_96_100 : 384 ≤ p.val := Nat.le_of_not_gt hmid_93_100
            by_cases hmid_96_100 : p.val < 392
            · by_cases hmid_96_98 : p.val < 388
              · exact step_check_chunk_96 p hlo_96_100 hmid_96_98
              · have hlo_97_98 : 388 ≤ p.val := Nat.le_of_not_gt hmid_96_98
                exact step_check_chunk_97 p hlo_97_98 hmid_96_100
            · have hlo_98_100 : 392 ≤ p.val := Nat.le_of_not_gt hmid_96_100
              by_cases hmid_98_100 : p.val < 396
              · exact step_check_chunk_98 p hlo_98_100 hmid_98_100
              · have hlo_99_100 : 396 ≤ p.val := Nat.le_of_not_gt hmid_98_100
                exact step_check_chunk_99 p hlo_99_100 hhi_root

lemma step_checks (p : Fin 397) : stepCheck p = true := step_check_all p
lemma finish_check_chunk_0 (p : Fin 397) (hl : 0 ≤ p.val) (hh : p.val < 16) : finishCheck p = true := by rfl
lemma finish_check_chunk_1 (p : Fin 397) (hl : 16 ≤ p.val) (hh : p.val < 32) : finishCheck p = true := by rfl
lemma finish_check_chunk_2 (p : Fin 397) (hl : 32 ≤ p.val) (hh : p.val < 48) : finishCheck p = true := by rfl
lemma finish_check_chunk_3 (p : Fin 397) (hl : 48 ≤ p.val) (hh : p.val < 64) : finishCheck p = true := by rfl
lemma finish_check_chunk_4 (p : Fin 397) (hl : 64 ≤ p.val) (hh : p.val < 80) : finishCheck p = true := by rfl
lemma finish_check_chunk_5 (p : Fin 397) (hl : 80 ≤ p.val) (hh : p.val < 96) : finishCheck p = true := by rfl
lemma finish_check_chunk_6 (p : Fin 397) (hl : 96 ≤ p.val) (hh : p.val < 112) : finishCheck p = true := by rfl
lemma finish_check_chunk_7 (p : Fin 397) (hl : 112 ≤ p.val) (hh : p.val < 128) : finishCheck p = true := by rfl
lemma finish_check_chunk_8 (p : Fin 397) (hl : 128 ≤ p.val) (hh : p.val < 144) : finishCheck p = true := by rfl
lemma finish_check_chunk_9 (p : Fin 397) (hl : 144 ≤ p.val) (hh : p.val < 160) : finishCheck p = true := by rfl
lemma finish_check_chunk_10 (p : Fin 397) (hl : 160 ≤ p.val) (hh : p.val < 176) : finishCheck p = true := by rfl
lemma finish_check_chunk_11 (p : Fin 397) (hl : 176 ≤ p.val) (hh : p.val < 192) : finishCheck p = true := by rfl
lemma finish_check_chunk_12 (p : Fin 397) (hl : 192 ≤ p.val) (hh : p.val < 208) : finishCheck p = true := by rfl
lemma finish_check_chunk_13 (p : Fin 397) (hl : 208 ≤ p.val) (hh : p.val < 224) : finishCheck p = true := by rfl
lemma finish_check_chunk_14 (p : Fin 397) (hl : 224 ≤ p.val) (hh : p.val < 240) : finishCheck p = true := by rfl
lemma finish_check_chunk_15 (p : Fin 397) (hl : 240 ≤ p.val) (hh : p.val < 256) : finishCheck p = true := by rfl
lemma finish_check_chunk_16 (p : Fin 397) (hl : 256 ≤ p.val) (hh : p.val < 272) : finishCheck p = true := by rfl
lemma finish_check_chunk_17 (p : Fin 397) (hl : 272 ≤ p.val) (hh : p.val < 288) : finishCheck p = true := by rfl
lemma finish_check_chunk_18 (p : Fin 397) (hl : 288 ≤ p.val) (hh : p.val < 304) : finishCheck p = true := by rfl
lemma finish_check_chunk_19 (p : Fin 397) (hl : 304 ≤ p.val) (hh : p.val < 320) : finishCheck p = true := by rfl
lemma finish_check_chunk_20 (p : Fin 397) (hl : 320 ≤ p.val) (hh : p.val < 336) : finishCheck p = true := by rfl
lemma finish_check_chunk_21 (p : Fin 397) (hl : 336 ≤ p.val) (hh : p.val < 352) : finishCheck p = true := by rfl
lemma finish_check_chunk_22 (p : Fin 397) (hl : 352 ≤ p.val) (hh : p.val < 368) : finishCheck p = true := by rfl
lemma finish_check_chunk_23 (p : Fin 397) (hl : 368 ≤ p.val) (hh : p.val < 384) : finishCheck p = true := by rfl
lemma finish_check_chunk_24 (p : Fin 397) (hl : 384 ≤ p.val) (hh : p.val < 397) : finishCheck p = true := by rfl
lemma finish_check_all (p : Fin 397) : finishCheck p = true := by
  have hlo_root : 0 ≤ p.val := Nat.zero_le _
  have hhi_root : p.val < 397 := p.isLt
  by_cases hmid_0_25 : p.val < 192
  · by_cases hmid_0_12 : p.val < 96
    · by_cases hmid_0_6 : p.val < 48
      · by_cases hmid_0_3 : p.val < 16
        · exact finish_check_chunk_0 p hlo_root hmid_0_3
        · have hlo_1_3 : 16 ≤ p.val := Nat.le_of_not_gt hmid_0_3
          by_cases hmid_1_3 : p.val < 32
          · exact finish_check_chunk_1 p hlo_1_3 hmid_1_3
          · have hlo_2_3 : 32 ≤ p.val := Nat.le_of_not_gt hmid_1_3
            exact finish_check_chunk_2 p hlo_2_3 hmid_0_6
      · have hlo_3_6 : 48 ≤ p.val := Nat.le_of_not_gt hmid_0_6
        by_cases hmid_3_6 : p.val < 64
        · exact finish_check_chunk_3 p hlo_3_6 hmid_3_6
        · have hlo_4_6 : 64 ≤ p.val := Nat.le_of_not_gt hmid_3_6
          by_cases hmid_4_6 : p.val < 80
          · exact finish_check_chunk_4 p hlo_4_6 hmid_4_6
          · have hlo_5_6 : 80 ≤ p.val := Nat.le_of_not_gt hmid_4_6
            exact finish_check_chunk_5 p hlo_5_6 hmid_0_12
    · have hlo_6_12 : 96 ≤ p.val := Nat.le_of_not_gt hmid_0_12
      by_cases hmid_6_12 : p.val < 144
      · by_cases hmid_6_9 : p.val < 112
        · exact finish_check_chunk_6 p hlo_6_12 hmid_6_9
        · have hlo_7_9 : 112 ≤ p.val := Nat.le_of_not_gt hmid_6_9
          by_cases hmid_7_9 : p.val < 128
          · exact finish_check_chunk_7 p hlo_7_9 hmid_7_9
          · have hlo_8_9 : 128 ≤ p.val := Nat.le_of_not_gt hmid_7_9
            exact finish_check_chunk_8 p hlo_8_9 hmid_6_12
      · have hlo_9_12 : 144 ≤ p.val := Nat.le_of_not_gt hmid_6_12
        by_cases hmid_9_12 : p.val < 160
        · exact finish_check_chunk_9 p hlo_9_12 hmid_9_12
        · have hlo_10_12 : 160 ≤ p.val := Nat.le_of_not_gt hmid_9_12
          by_cases hmid_10_12 : p.val < 176
          · exact finish_check_chunk_10 p hlo_10_12 hmid_10_12
          · have hlo_11_12 : 176 ≤ p.val := Nat.le_of_not_gt hmid_10_12
            exact finish_check_chunk_11 p hlo_11_12 hmid_0_25
  · have hlo_12_25 : 192 ≤ p.val := Nat.le_of_not_gt hmid_0_25
    by_cases hmid_12_25 : p.val < 288
    · by_cases hmid_12_18 : p.val < 240
      · by_cases hmid_12_15 : p.val < 208
        · exact finish_check_chunk_12 p hlo_12_25 hmid_12_15
        · have hlo_13_15 : 208 ≤ p.val := Nat.le_of_not_gt hmid_12_15
          by_cases hmid_13_15 : p.val < 224
          · exact finish_check_chunk_13 p hlo_13_15 hmid_13_15
          · have hlo_14_15 : 224 ≤ p.val := Nat.le_of_not_gt hmid_13_15
            exact finish_check_chunk_14 p hlo_14_15 hmid_12_18
      · have hlo_15_18 : 240 ≤ p.val := Nat.le_of_not_gt hmid_12_18
        by_cases hmid_15_18 : p.val < 256
        · exact finish_check_chunk_15 p hlo_15_18 hmid_15_18
        · have hlo_16_18 : 256 ≤ p.val := Nat.le_of_not_gt hmid_15_18
          by_cases hmid_16_18 : p.val < 272
          · exact finish_check_chunk_16 p hlo_16_18 hmid_16_18
          · have hlo_17_18 : 272 ≤ p.val := Nat.le_of_not_gt hmid_16_18
            exact finish_check_chunk_17 p hlo_17_18 hmid_12_25
    · have hlo_18_25 : 288 ≤ p.val := Nat.le_of_not_gt hmid_12_25
      by_cases hmid_18_25 : p.val < 336
      · by_cases hmid_18_21 : p.val < 304
        · exact finish_check_chunk_18 p hlo_18_25 hmid_18_21
        · have hlo_19_21 : 304 ≤ p.val := Nat.le_of_not_gt hmid_18_21
          by_cases hmid_19_21 : p.val < 320
          · exact finish_check_chunk_19 p hlo_19_21 hmid_19_21
          · have hlo_20_21 : 320 ≤ p.val := Nat.le_of_not_gt hmid_19_21
            exact finish_check_chunk_20 p hlo_20_21 hmid_18_25
      · have hlo_21_25 : 336 ≤ p.val := Nat.le_of_not_gt hmid_18_25
        by_cases hmid_21_25 : p.val < 368
        · by_cases hmid_21_23 : p.val < 352
          · exact finish_check_chunk_21 p hlo_21_25 hmid_21_23
          · have hlo_22_23 : 352 ≤ p.val := Nat.le_of_not_gt hmid_21_23
            exact finish_check_chunk_22 p hlo_22_23 hmid_21_25
        · have hlo_23_25 : 368 ≤ p.val := Nat.le_of_not_gt hmid_21_25
          by_cases hmid_23_25 : p.val < 384
          · exact finish_check_chunk_23 p hlo_23_25 hmid_23_25
          · have hlo_24_25 : 384 ≤ p.val := Nat.le_of_not_gt hmid_23_25
            exact finish_check_chunk_24 p hlo_24_25 hhi_root

lemma finish_checks (p : Fin 397) : finishCheck p = true := finish_check_all p
end Erdos406BalancedAssemblyTest
#print axioms Erdos406BalancedAssemblyTest.step_checks
#print axioms Erdos406BalancedAssemblyTest.finish_checks
