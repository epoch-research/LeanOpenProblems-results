import Submission.Primes
import Submission.Spec
open Nat Finset BigOperators

theorem not_comp_3 : ¬ IsComposite (A297707 3 - Nat.prevPrime (A297707 3)) := by
  have hd : A297707 3 - Nat.prevPrime (A297707 3) = 1 := by sorry
  rw [hd]
  dsimp [IsComposite]
  intro h
  rcases h with ⟨h1, h2⟩
  revert h1
  decide

theorem not_comp_4 : ¬ IsComposite (A297707 4 - Nat.prevPrime (A297707 4)) := by
  have hd : A297707 4 - Nat.prevPrime (A297707 4) = 7 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7

theorem not_comp_5 : ¬ IsComposite (A297707 5 - Nat.prevPrime (A297707 5)) := by
  have hd : A297707 5 - Nat.prevPrime (A297707 5) = 11 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_11

theorem not_comp_6 : ¬ IsComposite (A297707 6 - Nat.prevPrime (A297707 6)) := by
  have hd : A297707 6 - Nat.prevPrime (A297707 6) = 23 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_23

theorem not_comp_7 : ¬ IsComposite (A297707 7 - Nat.prevPrime (A297707 7)) := by
  have hd : A297707 7 - Nat.prevPrime (A297707 7) = 13 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_13

theorem not_comp_8 : ¬ IsComposite (A297707 8 - Nat.prevPrime (A297707 8)) := by
  have hd : A297707 8 - Nat.prevPrime (A297707 8) = 17 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17

theorem not_comp_9 : ¬ IsComposite (A297707 9 - Nat.prevPrime (A297707 9)) := by
  have hd : A297707 9 - Nat.prevPrime (A297707 9) = 13 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_13

theorem not_comp_10 : ¬ IsComposite (A297707 10 - Nat.prevPrime (A297707 10)) := by
  have hd : A297707 10 - Nat.prevPrime (A297707 10) = 83 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_83

theorem not_comp_11 : ¬ IsComposite (A297707 11 - Nat.prevPrime (A297707 11)) := by
  have hd : A297707 11 - Nat.prevPrime (A297707 11) = 29 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_29

theorem not_comp_12 : ¬ IsComposite (A297707 12 - Nat.prevPrime (A297707 12)) := by
  have hd : A297707 12 - Nat.prevPrime (A297707 12) = 157 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_157

theorem not_comp_13 : ¬ IsComposite (A297707 13 - Nat.prevPrime (A297707 13)) := by
  have hd : A297707 13 - Nat.prevPrime (A297707 13) = 41 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_41

theorem not_comp_14 : ¬ IsComposite (A297707 14 - Nat.prevPrime (A297707 14)) := by
  have hd : A297707 14 - Nat.prevPrime (A297707 14) = 23 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_23

theorem not_comp_15 : ¬ IsComposite (A297707 15 - Nat.prevPrime (A297707 15)) := by
  have hd : A297707 15 - Nat.prevPrime (A297707 15) = 53 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_53

theorem not_comp_16 : ¬ IsComposite (A297707 16 - Nat.prevPrime (A297707 16)) := by
  have hd : A297707 16 - Nat.prevPrime (A297707 16) = 157 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_157

theorem not_comp_17 : ¬ IsComposite (A297707 17 - Nat.prevPrime (A297707 17)) := by
  have hd : A297707 17 - Nat.prevPrime (A297707 17) = 433 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_433

theorem not_comp_18 : ¬ IsComposite (A297707 18 - Nat.prevPrime (A297707 18)) := by
  have hd : A297707 18 - Nat.prevPrime (A297707 18) = 103 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_103

theorem not_comp_19 : ¬ IsComposite (A297707 19 - Nat.prevPrime (A297707 19)) := by
  have hd : A297707 19 - Nat.prevPrime (A297707 19) = 83 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_83

theorem not_comp_20 : ¬ IsComposite (A297707 20 - Nat.prevPrime (A297707 20)) := by
  have hd : A297707 20 - Nat.prevPrime (A297707 20) = 107 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_107

theorem not_comp_21 : ¬ IsComposite (A297707 21 - Nat.prevPrime (A297707 21)) := by
  have hd : A297707 21 - Nat.prevPrime (A297707 21) = 23 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_23

theorem not_comp_22 : ¬ IsComposite (A297707 22 - Nat.prevPrime (A297707 22)) := by
  have hd : A297707 22 - Nat.prevPrime (A297707 22) = 43 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_43

theorem not_comp_23 : ¬ IsComposite (A297707 23 - Nat.prevPrime (A297707 23)) := by
  have hd : A297707 23 - Nat.prevPrime (A297707 23) = 719 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_719

theorem not_comp_24 : ¬ IsComposite (A297707 24 - Nat.prevPrime (A297707 24)) := by
  have hd : A297707 24 - Nat.prevPrime (A297707 24) = 421 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_421

theorem not_comp_25 : ¬ IsComposite (A297707 25 - Nat.prevPrime (A297707 25)) := by
  have hd : A297707 25 - Nat.prevPrime (A297707 25) = 431 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_431

theorem not_comp_26 : ¬ IsComposite (A297707 26 - Nat.prevPrime (A297707 26)) := by
  have hd : A297707 26 - Nat.prevPrime (A297707 26) = 67 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_67

theorem not_comp_27 : ¬ IsComposite (A297707 27 - Nat.prevPrime (A297707 27)) := by
  have hd : A297707 27 - Nat.prevPrime (A297707 27) = 47 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_47

theorem not_comp_28 : ¬ IsComposite (A297707 28 - Nat.prevPrime (A297707 28)) := by
  have hd : A297707 28 - Nat.prevPrime (A297707 28) = 193 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_193

theorem not_comp_29 : ¬ IsComposite (A297707 29 - Nat.prevPrime (A297707 29)) := by
  have hd : A297707 29 - Nat.prevPrime (A297707 29) = 367 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_367

theorem not_comp_30 : ¬ IsComposite (A297707 30 - Nat.prevPrime (A297707 30)) := by
  have hd : A297707 30 - Nat.prevPrime (A297707 30) = 167 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_167

theorem not_comp_31 : ¬ IsComposite (A297707 31 - Nat.prevPrime (A297707 31)) := by
  have hd : A297707 31 - Nat.prevPrime (A297707 31) = 809 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_809

theorem not_comp_32 : ¬ IsComposite (A297707 32 - Nat.prevPrime (A297707 32)) := by
  have hd : A297707 32 - Nat.prevPrime (A297707 32) = 1109 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1109

theorem not_comp_33 : ¬ IsComposite (A297707 33 - Nat.prevPrime (A297707 33)) := by
  have hd : A297707 33 - Nat.prevPrime (A297707 33) = 421 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_421

theorem not_comp_34 : ¬ IsComposite (A297707 34 - Nat.prevPrime (A297707 34)) := by
  have hd : A297707 34 - Nat.prevPrime (A297707 34) = 401 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_401

theorem not_comp_35 : ¬ IsComposite (A297707 35 - Nat.prevPrime (A297707 35)) := by
  have hd : A297707 35 - Nat.prevPrime (A297707 35) = 239 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_239

theorem not_comp_36 : ¬ IsComposite (A297707 36 - Nat.prevPrime (A297707 36)) := by
  have hd : A297707 36 - Nat.prevPrime (A297707 36) = 479 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_479

theorem not_comp_37 : ¬ IsComposite (A297707 37 - Nat.prevPrime (A297707 37)) := by
  have hd : A297707 37 - Nat.prevPrime (A297707 37) = 1307 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1307

theorem not_comp_38 : ¬ IsComposite (A297707 38 - Nat.prevPrime (A297707 38)) := by
  have hd : A297707 38 - Nat.prevPrime (A297707 38) = 521 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_521

theorem not_comp_39 : ¬ IsComposite (A297707 39 - Nat.prevPrime (A297707 39)) := by
  have hd : A297707 39 - Nat.prevPrime (A297707 39) = 53 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_53

theorem not_comp_40 : ¬ IsComposite (A297707 40 - Nat.prevPrime (A297707 40)) := by
  have hd : A297707 40 - Nat.prevPrime (A297707 40) = 983 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_983

theorem not_comp_41 : ¬ IsComposite (A297707 41 - Nat.prevPrime (A297707 41)) := by
  have hd : A297707 41 - Nat.prevPrime (A297707 41) = 3413 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3413

theorem not_comp_42 : ¬ IsComposite (A297707 42 - Nat.prevPrime (A297707 42)) := by
  have hd : A297707 42 - Nat.prevPrime (A297707 42) = 1217 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1217

theorem not_comp_43 : ¬ IsComposite (A297707 43 - Nat.prevPrime (A297707 43)) := by
  have hd : A297707 43 - Nat.prevPrime (A297707 43) = 887 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_887

theorem not_comp_44 : ¬ IsComposite (A297707 44 - Nat.prevPrime (A297707 44)) := by
  have hd : A297707 44 - Nat.prevPrime (A297707 44) = 41 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_41

theorem not_comp_45 : ¬ IsComposite (A297707 45 - Nat.prevPrime (A297707 45)) := by
  have hd : A297707 45 - Nat.prevPrime (A297707 45) = 89 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_89

theorem not_comp_46 : ¬ IsComposite (A297707 46 - Nat.prevPrime (A297707 46)) := by
  have hd : A297707 46 - Nat.prevPrime (A297707 46) = 17 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17

theorem not_comp_47 : ¬ IsComposite (A297707 47 - Nat.prevPrime (A297707 47)) := by
  have hd : A297707 47 - Nat.prevPrime (A297707 47) = 181 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_181

theorem not_comp_48 : ¬ IsComposite (A297707 48 - Nat.prevPrime (A297707 48)) := by
  have hd : A297707 48 - Nat.prevPrime (A297707 48) = 1229 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1229

theorem not_comp_49 : ¬ IsComposite (A297707 49 - Nat.prevPrime (A297707 49)) := by
  have hd : A297707 49 - Nat.prevPrime (A297707 49) = 1277 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1277

theorem not_comp_50 : ¬ IsComposite (A297707 50 - Nat.prevPrime (A297707 50)) := by
  have hd : A297707 50 - Nat.prevPrime (A297707 50) = 1613 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1613

theorem not_comp_51 : ¬ IsComposite (A297707 51 - Nat.prevPrime (A297707 51)) := by
  have hd : A297707 51 - Nat.prevPrime (A297707 51) = 743 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_743

theorem not_comp_52 : ¬ IsComposite (A297707 52 - Nat.prevPrime (A297707 52)) := by
  have hd : A297707 52 - Nat.prevPrime (A297707 52) = 1997 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1997

theorem not_comp_53 : ¬ IsComposite (A297707 53 - Nat.prevPrime (A297707 53)) := by
  have hd : A297707 53 - Nat.prevPrime (A297707 53) = 2027 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2027

theorem not_comp_54 : ¬ IsComposite (A297707 54 - Nat.prevPrime (A297707 54)) := by
  have hd : A297707 54 - Nat.prevPrime (A297707 54) = 31 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_31

theorem not_comp_55 : ¬ IsComposite (A297707 55 - Nat.prevPrime (A297707 55)) := by
  have hd : A297707 55 - Nat.prevPrime (A297707 55) = 1061 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1061

theorem not_comp_56 : ¬ IsComposite (A297707 56 - Nat.prevPrime (A297707 56)) := by
  have hd : A297707 56 - Nat.prevPrime (A297707 56) = 769 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_769

theorem not_comp_57 : ¬ IsComposite (A297707 57 - Nat.prevPrime (A297707 57)) := by
  have hd : A297707 57 - Nat.prevPrime (A297707 57) = 389 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_389

theorem not_comp_58 : ¬ IsComposite (A297707 58 - Nat.prevPrime (A297707 58)) := by
  have hd : A297707 58 - Nat.prevPrime (A297707 58) = 419 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_419

theorem not_comp_59 : ¬ IsComposite (A297707 59 - Nat.prevPrime (A297707 59)) := by
  have hd : A297707 59 - Nat.prevPrime (A297707 59) = 673 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_673

theorem not_comp_60 : ¬ IsComposite (A297707 60 - Nat.prevPrime (A297707 60)) := by
  have hd : A297707 60 - Nat.prevPrime (A297707 60) = 443 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_443

theorem not_comp_61 : ¬ IsComposite (A297707 61 - Nat.prevPrime (A297707 61)) := by
  have hd : A297707 61 - Nat.prevPrime (A297707 61) = 317 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_317

theorem not_comp_62 : ¬ IsComposite (A297707 62 - Nat.prevPrime (A297707 62)) := by
  have hd : A297707 62 - Nat.prevPrime (A297707 62) = 1423 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1423

theorem not_comp_63 : ¬ IsComposite (A297707 63 - Nat.prevPrime (A297707 63)) := by
  have hd : A297707 63 - Nat.prevPrime (A297707 63) = 1109 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1109

theorem not_comp_64 : ¬ IsComposite (A297707 64 - Nat.prevPrime (A297707 64)) := by
  have hd : A297707 64 - Nat.prevPrime (A297707 64) = 311 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_311

theorem not_comp_65 : ¬ IsComposite (A297707 65 - Nat.prevPrime (A297707 65)) := by
  have hd : A297707 65 - Nat.prevPrime (A297707 65) = 3539 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3539

theorem not_comp_66 : ¬ IsComposite (A297707 66 - Nat.prevPrime (A297707 66)) := by
  have hd : A297707 66 - Nat.prevPrime (A297707 66) = 3023 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3023

theorem not_comp_67 : ¬ IsComposite (A297707 67 - Nat.prevPrime (A297707 67)) := by
  have hd : A297707 67 - Nat.prevPrime (A297707 67) = 1619 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1619

theorem not_comp_68 : ¬ IsComposite (A297707 68 - Nat.prevPrime (A297707 68)) := by
  have hd : A297707 68 - Nat.prevPrime (A297707 68) = 271 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_271

theorem not_comp_69 : ¬ IsComposite (A297707 69 - Nat.prevPrime (A297707 69)) := by
  have hd : A297707 69 - Nat.prevPrime (A297707 69) = 11 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_11

theorem not_comp_70 : ¬ IsComposite (A297707 70 - Nat.prevPrime (A297707 70)) := by
  have hd : A297707 70 - Nat.prevPrime (A297707 70) = 677 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_677

theorem not_comp_71 : ¬ IsComposite (A297707 71 - Nat.prevPrime (A297707 71)) := by
  have hd : A297707 71 - Nat.prevPrime (A297707 71) = 431 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_431

theorem not_comp_72 : ¬ IsComposite (A297707 72 - Nat.prevPrime (A297707 72)) := by
  have hd : A297707 72 - Nat.prevPrime (A297707 72) = 2423 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2423

theorem not_comp_73 : ¬ IsComposite (A297707 73 - Nat.prevPrime (A297707 73)) := by
  have hd : A297707 73 - Nat.prevPrime (A297707 73) = 1511 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1511

theorem not_comp_74 : ¬ IsComposite (A297707 74 - Nat.prevPrime (A297707 74)) := by
  have hd : A297707 74 - Nat.prevPrime (A297707 74) = 739 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_739

theorem not_comp_75 : ¬ IsComposite (A297707 75 - Nat.prevPrime (A297707 75)) := by
  have hd : A297707 75 - Nat.prevPrime (A297707 75) = 1019 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1019

theorem not_comp_76 : ¬ IsComposite (A297707 76 - Nat.prevPrime (A297707 76)) := by
  have hd : A297707 76 - Nat.prevPrime (A297707 76) = 971 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_971

theorem not_comp_77 : ¬ IsComposite (A297707 77 - Nat.prevPrime (A297707 77)) := by
  have hd : A297707 77 - Nat.prevPrime (A297707 77) = 2729 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2729

theorem not_comp_78 : ¬ IsComposite (A297707 78 - Nat.prevPrime (A297707 78)) := by
  have hd : A297707 78 - Nat.prevPrime (A297707 78) = 3779 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3779

theorem not_comp_79 : ¬ IsComposite (A297707 79 - Nat.prevPrime (A297707 79)) := by
  have hd : A297707 79 - Nat.prevPrime (A297707 79) = 563 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_563

theorem not_comp_80 : ¬ IsComposite (A297707 80 - Nat.prevPrime (A297707 80)) := by
  have hd : A297707 80 - Nat.prevPrime (A297707 80) = 373 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_373

theorem not_comp_81 : ¬ IsComposite (A297707 81 - Nat.prevPrime (A297707 81)) := by
  have hd : A297707 81 - Nat.prevPrime (A297707 81) = 2477 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2477

theorem not_comp_82 : ¬ IsComposite (A297707 82 - Nat.prevPrime (A297707 82)) := by
  have hd : A297707 82 - Nat.prevPrime (A297707 82) = 1193 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1193

theorem not_comp_83 : ¬ IsComposite (A297707 83 - Nat.prevPrime (A297707 83)) := by
  have hd : A297707 83 - Nat.prevPrime (A297707 83) = 109 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_109

theorem not_comp_84 : ¬ IsComposite (A297707 84 - Nat.prevPrime (A297707 84)) := by
  have hd : A297707 84 - Nat.prevPrime (A297707 84) = 383 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_383

theorem not_comp_85 : ¬ IsComposite (A297707 85 - Nat.prevPrime (A297707 85)) := by
  have hd : A297707 85 - Nat.prevPrime (A297707 85) = 1109 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1109

theorem not_comp_86 : ¬ IsComposite (A297707 86 - Nat.prevPrime (A297707 86)) := by
  have hd : A297707 86 - Nat.prevPrime (A297707 86) = 491 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_491

theorem not_comp_87 : ¬ IsComposite (A297707 87 - Nat.prevPrime (A297707 87)) := by
  have hd : A297707 87 - Nat.prevPrime (A297707 87) = 577 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_577

theorem not_comp_88 : ¬ IsComposite (A297707 88 - Nat.prevPrime (A297707 88)) := by
  have hd : A297707 88 - Nat.prevPrime (A297707 88) = 157 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_157

theorem not_comp_89 : ¬ IsComposite (A297707 89 - Nat.prevPrime (A297707 89)) := by
  have hd : A297707 89 - Nat.prevPrime (A297707 89) = 223 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_223

theorem not_comp_90 : ¬ IsComposite (A297707 90 - Nat.prevPrime (A297707 90)) := by
  have hd : A297707 90 - Nat.prevPrime (A297707 90) = 6733 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6733

theorem not_comp_91 : ¬ IsComposite (A297707 91 - Nat.prevPrime (A297707 91)) := by
  have hd : A297707 91 - Nat.prevPrime (A297707 91) = 853 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_853

theorem not_comp_92 : ¬ IsComposite (A297707 92 - Nat.prevPrime (A297707 92)) := by
  have hd : A297707 92 - Nat.prevPrime (A297707 92) = 1367 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1367

theorem not_comp_93 : ¬ IsComposite (A297707 93 - Nat.prevPrime (A297707 93)) := by
  have hd : A297707 93 - Nat.prevPrime (A297707 93) = 1523 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1523

theorem not_comp_94 : ¬ IsComposite (A297707 94 - Nat.prevPrime (A297707 94)) := by
  have hd : A297707 94 - Nat.prevPrime (A297707 94) = 821 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_821

theorem not_comp_95 : ¬ IsComposite (A297707 95 - Nat.prevPrime (A297707 95)) := by
  have hd : A297707 95 - Nat.prevPrime (A297707 95) = 1217 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1217

theorem not_comp_96 : ¬ IsComposite (A297707 96 - Nat.prevPrime (A297707 96)) := by
  have hd : A297707 96 - Nat.prevPrime (A297707 96) = 1319 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1319

theorem not_comp_97 : ¬ IsComposite (A297707 97 - Nat.prevPrime (A297707 97)) := by
  have hd : A297707 97 - Nat.prevPrime (A297707 97) = 103 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_103

theorem not_comp_98 : ¬ IsComposite (A297707 98 - Nat.prevPrime (A297707 98)) := by
  have hd : A297707 98 - Nat.prevPrime (A297707 98) = 751 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_751

theorem not_comp_99 : ¬ IsComposite (A297707 99 - Nat.prevPrime (A297707 99)) := by
  have hd : A297707 99 - Nat.prevPrime (A297707 99) = 1973 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1973

theorem not_comp_100 : ¬ IsComposite (A297707 100 - Nat.prevPrime (A297707 100)) := by
  have hd : A297707 100 - Nat.prevPrime (A297707 100) = 3911 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3911

theorem not_comp_101 : ¬ IsComposite (A297707 101 - Nat.prevPrime (A297707 101)) := by
  have hd : A297707 101 - Nat.prevPrime (A297707 101) = 31 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_31

theorem not_comp_102 : ¬ IsComposite (A297707 102 - Nat.prevPrime (A297707 102)) := by
  have hd : A297707 102 - Nat.prevPrime (A297707 102) = 1481 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1481

theorem not_comp_103 : ¬ IsComposite (A297707 103 - Nat.prevPrime (A297707 103)) := by
  have hd : A297707 103 - Nat.prevPrime (A297707 103) = 1289 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1289

theorem not_comp_104 : ¬ IsComposite (A297707 104 - Nat.prevPrime (A297707 104)) := by
  have hd : A297707 104 - Nat.prevPrime (A297707 104) = 37 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_37

theorem not_comp_105 : ¬ IsComposite (A297707 105 - Nat.prevPrime (A297707 105)) := by
  have hd : A297707 105 - Nat.prevPrime (A297707 105) = 6563 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6563

theorem not_comp_106 : ¬ IsComposite (A297707 106 - Nat.prevPrime (A297707 106)) := by
  have hd : A297707 106 - Nat.prevPrime (A297707 106) = 2351 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2351

theorem not_comp_107 : ¬ IsComposite (A297707 107 - Nat.prevPrime (A297707 107)) := by
  have hd : A297707 107 - Nat.prevPrime (A297707 107) = 743 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_743

theorem not_comp_108 : ¬ IsComposite (A297707 108 - Nat.prevPrime (A297707 108)) := by
  have hd : A297707 108 - Nat.prevPrime (A297707 108) = 71 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_71

theorem not_comp_109 : ¬ IsComposite (A297707 109 - Nat.prevPrime (A297707 109)) := by
  have hd : A297707 109 - Nat.prevPrime (A297707 109) = 241 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_241

theorem not_comp_110 : ¬ IsComposite (A297707 110 - Nat.prevPrime (A297707 110)) := by
  have hd : A297707 110 - Nat.prevPrime (A297707 110) = 241 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_241

theorem not_comp_111 : ¬ IsComposite (A297707 111 - Nat.prevPrime (A297707 111)) := by
  have hd : A297707 111 - Nat.prevPrime (A297707 111) = 4093 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4093

theorem not_comp_112 : ¬ IsComposite (A297707 112 - Nat.prevPrime (A297707 112)) := by
  have hd : A297707 112 - Nat.prevPrime (A297707 112) = 577 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_577

theorem not_comp_113 : ¬ IsComposite (A297707 113 - Nat.prevPrime (A297707 113)) := by
  have hd : A297707 113 - Nat.prevPrime (A297707 113) = 2311 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2311

theorem not_comp_114 : ¬ IsComposite (A297707 114 - Nat.prevPrime (A297707 114)) := by
  have hd : A297707 114 - Nat.prevPrime (A297707 114) = 677 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_677

theorem not_comp_115 : ¬ IsComposite (A297707 115 - Nat.prevPrime (A297707 115)) := by
  have hd : A297707 115 - Nat.prevPrime (A297707 115) = 41 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_41

theorem not_comp_116 : ¬ IsComposite (A297707 116 - Nat.prevPrime (A297707 116)) := by
  have hd : A297707 116 - Nat.prevPrime (A297707 116) = 6257 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6257

theorem not_comp_117 : ¬ IsComposite (A297707 117 - Nat.prevPrime (A297707 117)) := by
  have hd : A297707 117 - Nat.prevPrime (A297707 117) = 311 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_311

theorem not_comp_118 : ¬ IsComposite (A297707 118 - Nat.prevPrime (A297707 118)) := by
  have hd : A297707 118 - Nat.prevPrime (A297707 118) = 6907 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6907

theorem not_comp_119 : ¬ IsComposite (A297707 119 - Nat.prevPrime (A297707 119)) := by
  have hd : A297707 119 - Nat.prevPrime (A297707 119) = 2113 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2113

theorem not_comp_120 : ¬ IsComposite (A297707 120 - Nat.prevPrime (A297707 120)) := by
  have hd : A297707 120 - Nat.prevPrime (A297707 120) = 5413 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_5413

theorem not_comp_121 : ¬ IsComposite (A297707 121 - Nat.prevPrime (A297707 121)) := by
  have hd : A297707 121 - Nat.prevPrime (A297707 121) = 211 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_211

theorem not_comp_122 : ¬ IsComposite (A297707 122 - Nat.prevPrime (A297707 122)) := by
  have hd : A297707 122 - Nat.prevPrime (A297707 122) = 4457 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4457

theorem not_comp_123 : ¬ IsComposite (A297707 123 - Nat.prevPrime (A297707 123)) := by
  have hd : A297707 123 - Nat.prevPrime (A297707 123) = 821 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_821

theorem not_comp_124 : ¬ IsComposite (A297707 124 - Nat.prevPrime (A297707 124)) := by
  have hd : A297707 124 - Nat.prevPrime (A297707 124) = 7919 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7919

theorem not_comp_125 : ¬ IsComposite (A297707 125 - Nat.prevPrime (A297707 125)) := by
  have hd : A297707 125 - Nat.prevPrime (A297707 125) = 4679 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4679

theorem not_comp_126 : ¬ IsComposite (A297707 126 - Nat.prevPrime (A297707 126)) := by
  have hd : A297707 126 - Nat.prevPrime (A297707 126) = 4793 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4793

theorem not_comp_127 : ¬ IsComposite (A297707 127 - Nat.prevPrime (A297707 127)) := by
  have hd : A297707 127 - Nat.prevPrime (A297707 127) = 167 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_167

theorem not_comp_128 : ¬ IsComposite (A297707 128 - Nat.prevPrime (A297707 128)) := by
  have hd : A297707 128 - Nat.prevPrime (A297707 128) = 1621 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1621

theorem not_comp_129 : ¬ IsComposite (A297707 129 - Nat.prevPrime (A297707 129)) := by
  have hd : A297707 129 - Nat.prevPrime (A297707 129) = 2953 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2953

theorem not_comp_130 : ¬ IsComposite (A297707 130 - Nat.prevPrime (A297707 130)) := by
  have hd : A297707 130 - Nat.prevPrime (A297707 130) = 17387 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17387

theorem not_comp_131 : ¬ IsComposite (A297707 131 - Nat.prevPrime (A297707 131)) := by
  have hd : A297707 131 - Nat.prevPrime (A297707 131) = 7823 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7823

theorem not_comp_132 : ¬ IsComposite (A297707 132 - Nat.prevPrime (A297707 132)) := by
  have hd : A297707 132 - Nat.prevPrime (A297707 132) = 3779 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3779

theorem not_comp_133 : ¬ IsComposite (A297707 133 - Nat.prevPrime (A297707 133)) := by
  have hd : A297707 133 - Nat.prevPrime (A297707 133) = 569 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_569

theorem not_comp_134 : ¬ IsComposite (A297707 134 - Nat.prevPrime (A297707 134)) := by
  have hd : A297707 134 - Nat.prevPrime (A297707 134) = 4813 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4813

theorem not_comp_135 : ¬ IsComposite (A297707 135 - Nat.prevPrime (A297707 135)) := by
  have hd : A297707 135 - Nat.prevPrime (A297707 135) = 1511 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1511

theorem not_comp_136 : ¬ IsComposite (A297707 136 - Nat.prevPrime (A297707 136)) := by
  have hd : A297707 136 - Nat.prevPrime (A297707 136) = 4751 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4751

theorem not_comp_137 : ¬ IsComposite (A297707 137 - Nat.prevPrime (A297707 137)) := by
  have hd : A297707 137 - Nat.prevPrime (A297707 137) = 103 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_103

theorem not_comp_138 : ¬ IsComposite (A297707 138 - Nat.prevPrime (A297707 138)) := by
  have hd : A297707 138 - Nat.prevPrime (A297707 138) = 4337 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4337

theorem not_comp_139 : ¬ IsComposite (A297707 139 - Nat.prevPrime (A297707 139)) := by
  have hd : A297707 139 - Nat.prevPrime (A297707 139) = 2503 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2503

theorem not_comp_140 : ¬ IsComposite (A297707 140 - Nat.prevPrime (A297707 140)) := by
  have hd : A297707 140 - Nat.prevPrime (A297707 140) = 607 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_607

theorem not_comp_141 : ¬ IsComposite (A297707 141 - Nat.prevPrime (A297707 141)) := by
  have hd : A297707 141 - Nat.prevPrime (A297707 141) = 937 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_937

theorem not_comp_142 : ¬ IsComposite (A297707 142 - Nat.prevPrime (A297707 142)) := by
  have hd : A297707 142 - Nat.prevPrime (A297707 142) = 3761 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3761

theorem not_comp_143 : ¬ IsComposite (A297707 143 - Nat.prevPrime (A297707 143)) := by
  have hd : A297707 143 - Nat.prevPrime (A297707 143) = 7673 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7673

theorem not_comp_144 : ¬ IsComposite (A297707 144 - Nat.prevPrime (A297707 144)) := by
  have hd : A297707 144 - Nat.prevPrime (A297707 144) = 15817 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_15817

theorem not_comp_145 : ¬ IsComposite (A297707 145 - Nat.prevPrime (A297707 145)) := by
  have hd : A297707 145 - Nat.prevPrime (A297707 145) = 10259 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_10259

theorem not_comp_146 : ¬ IsComposite (A297707 146 - Nat.prevPrime (A297707 146)) := by
  have hd : A297707 146 - Nat.prevPrime (A297707 146) = 13327 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_13327

theorem not_comp_147 : ¬ IsComposite (A297707 147 - Nat.prevPrime (A297707 147)) := by
  have hd : A297707 147 - Nat.prevPrime (A297707 147) = 17827 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17827

theorem not_comp_148 : ¬ IsComposite (A297707 148 - Nat.prevPrime (A297707 148)) := by
  have hd : A297707 148 - Nat.prevPrime (A297707 148) = 859 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_859

theorem not_comp_149 : ¬ IsComposite (A297707 149 - Nat.prevPrime (A297707 149)) := by
  have hd : A297707 149 - Nat.prevPrime (A297707 149) = 2213 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2213

theorem not_comp_150 : ¬ IsComposite (A297707 150 - Nat.prevPrime (A297707 150)) := by
  have hd : A297707 150 - Nat.prevPrime (A297707 150) = 1217 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1217

theorem not_comp_151 : ¬ IsComposite (A297707 151 - Nat.prevPrime (A297707 151)) := by
  have hd : A297707 151 - Nat.prevPrime (A297707 151) = 1579 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1579

theorem not_comp_152 : ¬ IsComposite (A297707 152 - Nat.prevPrime (A297707 152)) := by
  have hd : A297707 152 - Nat.prevPrime (A297707 152) = 229 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_229

theorem not_comp_153 : ¬ IsComposite (A297707 153 - Nat.prevPrime (A297707 153)) := by
  have hd : A297707 153 - Nat.prevPrime (A297707 153) = 1657 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1657

theorem not_comp_154 : ¬ IsComposite (A297707 154 - Nat.prevPrime (A297707 154)) := by
  have hd : A297707 154 - Nat.prevPrime (A297707 154) = 2939 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2939

theorem not_comp_155 : ¬ IsComposite (A297707 155 - Nat.prevPrime (A297707 155)) := by
  have hd : A297707 155 - Nat.prevPrime (A297707 155) = 1231 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1231

theorem not_comp_156 : ¬ IsComposite (A297707 156 - Nat.prevPrime (A297707 156)) := by
  have hd : A297707 156 - Nat.prevPrime (A297707 156) = 4261 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4261

theorem not_comp_157 : ¬ IsComposite (A297707 157 - Nat.prevPrime (A297707 157)) := by
  have hd : A297707 157 - Nat.prevPrime (A297707 157) = 14081 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_14081

theorem not_comp_158 : ¬ IsComposite (A297707 158 - Nat.prevPrime (A297707 158)) := by
  have hd : A297707 158 - Nat.prevPrime (A297707 158) = 773 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_773

theorem not_comp_159 : ¬ IsComposite (A297707 159 - Nat.prevPrime (A297707 159)) := by
  have hd : A297707 159 - Nat.prevPrime (A297707 159) = 367 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_367

theorem not_comp_160 : ¬ IsComposite (A297707 160 - Nat.prevPrime (A297707 160)) := by
  have hd : A297707 160 - Nat.prevPrime (A297707 160) = 2953 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2953

theorem not_comp_161 : ¬ IsComposite (A297707 161 - Nat.prevPrime (A297707 161)) := by
  have hd : A297707 161 - Nat.prevPrime (A297707 161) = 1039 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1039

theorem not_comp_162 : ¬ IsComposite (A297707 162 - Nat.prevPrime (A297707 162)) := by
  have hd : A297707 162 - Nat.prevPrime (A297707 162) = 3581 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3581

theorem not_comp_163 : ¬ IsComposite (A297707 163 - Nat.prevPrime (A297707 163)) := by
  have hd : A297707 163 - Nat.prevPrime (A297707 163) = 6947 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6947

theorem not_comp_164 : ¬ IsComposite (A297707 164 - Nat.prevPrime (A297707 164)) := by
  have hd : A297707 164 - Nat.prevPrime (A297707 164) = 709 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_709

theorem not_comp_165 : ¬ IsComposite (A297707 165 - Nat.prevPrime (A297707 165)) := by
  have hd : A297707 165 - Nat.prevPrime (A297707 165) = 311 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_311

theorem not_comp_166 : ¬ IsComposite (A297707 166 - Nat.prevPrime (A297707 166)) := by
  have hd : A297707 166 - Nat.prevPrime (A297707 166) = 1997 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1997

theorem not_comp_167 : ¬ IsComposite (A297707 167 - Nat.prevPrime (A297707 167)) := by
  have hd : A297707 167 - Nat.prevPrime (A297707 167) = 1997 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1997

theorem not_comp_168 : ¬ IsComposite (A297707 168 - Nat.prevPrime (A297707 168)) := by
  have hd : A297707 168 - Nat.prevPrime (A297707 168) = 6971 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6971

theorem not_comp_169 : ¬ IsComposite (A297707 169 - Nat.prevPrime (A297707 169)) := by
  have hd : A297707 169 - Nat.prevPrime (A297707 169) = 2693 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2693

theorem not_comp_170 : ¬ IsComposite (A297707 170 - Nat.prevPrime (A297707 170)) := by
  have hd : A297707 170 - Nat.prevPrime (A297707 170) = 3539 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3539

theorem not_comp_171 : ¬ IsComposite (A297707 171 - Nat.prevPrime (A297707 171)) := by
  have hd : A297707 171 - Nat.prevPrime (A297707 171) = 1913 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1913

theorem not_comp_172 : ¬ IsComposite (A297707 172 - Nat.prevPrime (A297707 172)) := by
  have hd : A297707 172 - Nat.prevPrime (A297707 172) = 3727 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3727

theorem not_comp_173 : ¬ IsComposite (A297707 173 - Nat.prevPrime (A297707 173)) := by
  have hd : A297707 173 - Nat.prevPrime (A297707 173) = 277 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_277

theorem not_comp_174 : ¬ IsComposite (A297707 174 - Nat.prevPrime (A297707 174)) := by
  have hd : A297707 174 - Nat.prevPrime (A297707 174) = 4519 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4519

theorem not_comp_175 : ¬ IsComposite (A297707 175 - Nat.prevPrime (A297707 175)) := by
  have hd : A297707 175 - Nat.prevPrime (A297707 175) = 1879 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1879

theorem not_comp_176 : ¬ IsComposite (A297707 176 - Nat.prevPrime (A297707 176)) := by
  have hd : A297707 176 - Nat.prevPrime (A297707 176) = 2239 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2239

theorem not_comp_177 : ¬ IsComposite (A297707 177 - Nat.prevPrime (A297707 177)) := by
  have hd : A297707 177 - Nat.prevPrime (A297707 177) = 3469 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3469

theorem not_comp_178 : ¬ IsComposite (A297707 178 - Nat.prevPrime (A297707 178)) := by
  have hd : A297707 178 - Nat.prevPrime (A297707 178) = 15601 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_15601

theorem not_comp_179 : ¬ IsComposite (A297707 179 - Nat.prevPrime (A297707 179)) := by
  have hd : A297707 179 - Nat.prevPrime (A297707 179) = 5231 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_5231

theorem not_comp_180 : ¬ IsComposite (A297707 180 - Nat.prevPrime (A297707 180)) := by
  have hd : A297707 180 - Nat.prevPrime (A297707 180) = 421 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_421

theorem not_comp_181 : ¬ IsComposite (A297707 181 - Nat.prevPrime (A297707 181)) := by
  have hd : A297707 181 - Nat.prevPrime (A297707 181) = 2477 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2477

theorem not_comp_182 : ¬ IsComposite (A297707 182 - Nat.prevPrime (A297707 182)) := by
  have hd : A297707 182 - Nat.prevPrime (A297707 182) = 6269 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6269

theorem not_comp_183 : ¬ IsComposite (A297707 183 - Nat.prevPrime (A297707 183)) := by
  have hd : A297707 183 - Nat.prevPrime (A297707 183) = 613 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_613

theorem not_comp_184 : ¬ IsComposite (A297707 184 - Nat.prevPrime (A297707 184)) := by
  have hd : A297707 184 - Nat.prevPrime (A297707 184) = 1831 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1831

theorem not_comp_185 : ¬ IsComposite (A297707 185 - Nat.prevPrime (A297707 185)) := by
  have hd : A297707 185 - Nat.prevPrime (A297707 185) = 3001 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3001

theorem not_comp_186 : ¬ IsComposite (A297707 186 - Nat.prevPrime (A297707 186)) := by
  have hd : A297707 186 - Nat.prevPrime (A297707 186) = 757 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_757

theorem not_comp_187 : ¬ IsComposite (A297707 187 - Nat.prevPrime (A297707 187)) := by
  have hd : A297707 187 - Nat.prevPrime (A297707 187) = 5417 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_5417

theorem not_comp_188 : ¬ IsComposite (A297707 188 - Nat.prevPrime (A297707 188)) := by
  have hd : A297707 188 - Nat.prevPrime (A297707 188) = 4813 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4813

theorem not_comp_189 : ¬ IsComposite (A297707 189 - Nat.prevPrime (A297707 189)) := by
  have hd : A297707 189 - Nat.prevPrime (A297707 189) = 15913 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_15913

theorem not_comp_190 : ¬ IsComposite (A297707 190 - Nat.prevPrime (A297707 190)) := by
  have hd : A297707 190 - Nat.prevPrime (A297707 190) = 2609 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2609

theorem not_comp_191 : ¬ IsComposite (A297707 191 - Nat.prevPrime (A297707 191)) := by
  have hd : A297707 191 - Nat.prevPrime (A297707 191) = 1181 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1181

theorem not_comp_192 : ¬ IsComposite (A297707 192 - Nat.prevPrime (A297707 192)) := by
  have hd : A297707 192 - Nat.prevPrime (A297707 192) = 7253 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7253

theorem not_comp_193 : ¬ IsComposite (A297707 193 - Nat.prevPrime (A297707 193)) := by
  have hd : A297707 193 - Nat.prevPrime (A297707 193) = 18301 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_18301

theorem not_comp_194 : ¬ IsComposite (A297707 194 - Nat.prevPrime (A297707 194)) := by
  have hd : A297707 194 - Nat.prevPrime (A297707 194) = 239 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_239

theorem not_comp_195 : ¬ IsComposite (A297707 195 - Nat.prevPrime (A297707 195)) := by
  have hd : A297707 195 - Nat.prevPrime (A297707 195) = 7193 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7193

theorem not_comp_196 : ¬ IsComposite (A297707 196 - Nat.prevPrime (A297707 196)) := by
  have hd : A297707 196 - Nat.prevPrime (A297707 196) = 6661 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6661

theorem not_comp_197 : ¬ IsComposite (A297707 197 - Nat.prevPrime (A297707 197)) := by
  have hd : A297707 197 - Nat.prevPrime (A297707 197) = 10333 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_10333

theorem not_comp_198 : ¬ IsComposite (A297707 198 - Nat.prevPrime (A297707 198)) := by
  have hd : A297707 198 - Nat.prevPrime (A297707 198) = 4349 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4349

theorem not_comp_199 : ¬ IsComposite (A297707 199 - Nat.prevPrime (A297707 199)) := by
  have hd : A297707 199 - Nat.prevPrime (A297707 199) = 10949 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_10949

theorem not_comp_200 : ¬ IsComposite (A297707 200 - Nat.prevPrime (A297707 200)) := by
  have hd : A297707 200 - Nat.prevPrime (A297707 200) = 10151 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_10151

theorem not_comp_201 : ¬ IsComposite (A297707 201 - Nat.prevPrime (A297707 201)) := by
  have hd : A297707 201 - Nat.prevPrime (A297707 201) = 3637 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3637

theorem not_comp_202 : ¬ IsComposite (A297707 202 - Nat.prevPrime (A297707 202)) := by
  have hd : A297707 202 - Nat.prevPrime (A297707 202) = 347 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_347

theorem not_comp_203 : ¬ IsComposite (A297707 203 - Nat.prevPrime (A297707 203)) := by
  have hd : A297707 203 - Nat.prevPrime (A297707 203) = 2909 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2909

theorem not_comp_204 : ¬ IsComposite (A297707 204 - Nat.prevPrime (A297707 204)) := by
  have hd : A297707 204 - Nat.prevPrime (A297707 204) = 1117 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1117

theorem not_comp_205 : ¬ IsComposite (A297707 205 - Nat.prevPrime (A297707 205)) := by
  have hd : A297707 205 - Nat.prevPrime (A297707 205) = 13967 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_13967

theorem not_comp_206 : ¬ IsComposite (A297707 206 - Nat.prevPrime (A297707 206)) := by
  have hd : A297707 206 - Nat.prevPrime (A297707 206) = 18119 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_18119

theorem not_comp_207 : ¬ IsComposite (A297707 207 - Nat.prevPrime (A297707 207)) := by
  have hd : A297707 207 - Nat.prevPrime (A297707 207) = 9749 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_9749

theorem not_comp_208 : ¬ IsComposite (A297707 208 - Nat.prevPrime (A297707 208)) := by
  have hd : A297707 208 - Nat.prevPrime (A297707 208) = 283 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_283

theorem not_comp_209 : ¬ IsComposite (A297707 209 - Nat.prevPrime (A297707 209)) := by
  have hd : A297707 209 - Nat.prevPrime (A297707 209) = 5573 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_5573

theorem not_comp_210 : ¬ IsComposite (A297707 210 - Nat.prevPrime (A297707 210)) := by
  have hd : A297707 210 - Nat.prevPrime (A297707 210) = 13477 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_13477

theorem not_comp_211 : ¬ IsComposite (A297707 211 - Nat.prevPrime (A297707 211)) := by
  have hd : A297707 211 - Nat.prevPrime (A297707 211) = 883 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_883

theorem not_comp_212 : ¬ IsComposite (A297707 212 - Nat.prevPrime (A297707 212)) := by
  have hd : A297707 212 - Nat.prevPrime (A297707 212) = 2309 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2309

theorem not_comp_213 : ¬ IsComposite (A297707 213 - Nat.prevPrime (A297707 213)) := by
  have hd : A297707 213 - Nat.prevPrime (A297707 213) = 4507 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4507

theorem not_comp_214 : ¬ IsComposite (A297707 214 - Nat.prevPrime (A297707 214)) := by
  have hd : A297707 214 - Nat.prevPrime (A297707 214) = 7561 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_7561

theorem not_comp_215 : ¬ IsComposite (A297707 215 - Nat.prevPrime (A297707 215)) := by
  have hd : A297707 215 - Nat.prevPrime (A297707 215) = 1259 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1259

theorem not_comp_216 : ¬ IsComposite (A297707 216 - Nat.prevPrime (A297707 216)) := by
  have hd : A297707 216 - Nat.prevPrime (A297707 216) = 3001 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3001

theorem not_comp_217 : ¬ IsComposite (A297707 217 - Nat.prevPrime (A297707 217)) := by
  have hd : A297707 217 - Nat.prevPrime (A297707 217) = 2927 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2927

theorem not_comp_218 : ¬ IsComposite (A297707 218 - Nat.prevPrime (A297707 218)) := by
  have hd : A297707 218 - Nat.prevPrime (A297707 218) = 1789 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1789

theorem not_comp_219 : ¬ IsComposite (A297707 219 - Nat.prevPrime (A297707 219)) := by
  have hd : A297707 219 - Nat.prevPrime (A297707 219) = 877 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_877

theorem not_comp_220 : ¬ IsComposite (A297707 220 - Nat.prevPrime (A297707 220)) := by
  have hd : A297707 220 - Nat.prevPrime (A297707 220) = 1097 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1097

theorem not_comp_221 : ¬ IsComposite (A297707 221 - Nat.prevPrime (A297707 221)) := by
  have hd : A297707 221 - Nat.prevPrime (A297707 221) = 5431 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_5431

theorem not_comp_222 : ¬ IsComposite (A297707 222 - Nat.prevPrime (A297707 222)) := by
  have hd : A297707 222 - Nat.prevPrime (A297707 222) = 2221 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2221

theorem not_comp_223 : ¬ IsComposite (A297707 223 - Nat.prevPrime (A297707 223)) := by
  have hd : A297707 223 - Nat.prevPrime (A297707 223) = 2243 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2243

theorem not_comp_224 : ¬ IsComposite (A297707 224 - Nat.prevPrime (A297707 224)) := by
  have hd : A297707 224 - Nat.prevPrime (A297707 224) = 1193 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1193

theorem not_comp_225 : ¬ IsComposite (A297707 225 - Nat.prevPrime (A297707 225)) := by
  have hd : A297707 225 - Nat.prevPrime (A297707 225) = 8839 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_8839

theorem not_comp_226 : ¬ IsComposite (A297707 226 - Nat.prevPrime (A297707 226)) := by
  have hd : A297707 226 - Nat.prevPrime (A297707 226) = 877 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_877

theorem not_comp_227 : ¬ IsComposite (A297707 227 - Nat.prevPrime (A297707 227)) := by
  have hd : A297707 227 - Nat.prevPrime (A297707 227) = 853 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_853

theorem not_comp_228 : ¬ IsComposite (A297707 228 - Nat.prevPrime (A297707 228)) := by
  have hd : A297707 228 - Nat.prevPrime (A297707 228) = 4721 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4721

theorem not_comp_229 : ¬ IsComposite (A297707 229 - Nat.prevPrime (A297707 229)) := by
  have hd : A297707 229 - Nat.prevPrime (A297707 229) = 10061 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_10061

theorem not_comp_230 : ¬ IsComposite (A297707 230 - Nat.prevPrime (A297707 230)) := by
  have hd : A297707 230 - Nat.prevPrime (A297707 230) = 17729 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17729

theorem not_comp_231 : ¬ IsComposite (A297707 231 - Nat.prevPrime (A297707 231)) := by
  have hd : A297707 231 - Nat.prevPrime (A297707 231) = 17713 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17713

theorem not_comp_232 : ¬ IsComposite (A297707 232 - Nat.prevPrime (A297707 232)) := by
  have hd : A297707 232 - Nat.prevPrime (A297707 232) = 4691 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_4691

theorem not_comp_233 : ¬ IsComposite (A297707 233 - Nat.prevPrime (A297707 233)) := by
  have hd : A297707 233 - Nat.prevPrime (A297707 233) = 2083 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2083

theorem not_comp_234 : ¬ IsComposite (A297707 234 - Nat.prevPrime (A297707 234)) := by
  have hd : A297707 234 - Nat.prevPrime (A297707 234) = 11423 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_11423

theorem not_comp_235 : ¬ IsComposite (A297707 235 - Nat.prevPrime (A297707 235)) := by
  have hd : A297707 235 - Nat.prevPrime (A297707 235) = 449 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_449

theorem not_comp_236 : ¬ IsComposite (A297707 236 - Nat.prevPrime (A297707 236)) := by
  have hd : A297707 236 - Nat.prevPrime (A297707 236) = 3361 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_3361

theorem not_comp_237 : ¬ IsComposite (A297707 237 - Nat.prevPrime (A297707 237)) := by
  have hd : A297707 237 - Nat.prevPrime (A297707 237) = 1277 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1277

theorem not_comp_238 : ¬ IsComposite (A297707 238 - Nat.prevPrime (A297707 238)) := by
  have hd : A297707 238 - Nat.prevPrime (A297707 238) = 12763 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_12763

theorem not_comp_239 : ¬ IsComposite (A297707 239 - Nat.prevPrime (A297707 239)) := by
  have hd : A297707 239 - Nat.prevPrime (A297707 239) = 22469 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_22469

theorem not_comp_240 : ¬ IsComposite (A297707 240 - Nat.prevPrime (A297707 240)) := by
  have hd : A297707 240 - Nat.prevPrime (A297707 240) = 23929 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_23929

theorem not_comp_241 : ¬ IsComposite (A297707 241 - Nat.prevPrime (A297707 241)) := by
  have hd : A297707 241 - Nat.prevPrime (A297707 241) = 24359 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_24359

theorem not_comp_242 : ¬ IsComposite (A297707 242 - Nat.prevPrime (A297707 242)) := by
  have hd : A297707 242 - Nat.prevPrime (A297707 242) = 17599 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_17599

theorem not_comp_243 : ¬ IsComposite (A297707 243 - Nat.prevPrime (A297707 243)) := by
  have hd : A297707 243 - Nat.prevPrime (A297707 243) = 2633 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_2633

theorem not_comp_244 : ¬ IsComposite (A297707 244 - Nat.prevPrime (A297707 244)) := by
  have hd : A297707 244 - Nat.prevPrime (A297707 244) = 293 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_293

theorem not_comp_245 : ¬ IsComposite (A297707 245 - Nat.prevPrime (A297707 245)) := by
  have hd : A297707 245 - Nat.prevPrime (A297707 245) = 6323 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_6323

theorem not_comp_246 : ¬ IsComposite (A297707 246 - Nat.prevPrime (A297707 246)) := by
  have hd : A297707 246 - Nat.prevPrime (A297707 246) = 1663 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1663

theorem not_comp_247 : ¬ IsComposite (A297707 247 - Nat.prevPrime (A297707 247)) := by
  have hd : A297707 247 - Nat.prevPrime (A297707 247) = 1117 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1117

theorem not_comp_248 : ¬ IsComposite (A297707 248 - Nat.prevPrime (A297707 248)) := by
  have hd : A297707 248 - Nat.prevPrime (A297707 248) = 1249 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1249

theorem not_comp_249 : ¬ IsComposite (A297707 249 - Nat.prevPrime (A297707 249)) := by
  have hd : A297707 249 - Nat.prevPrime (A297707 249) = 1693 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_1693

theorem not_comp_250 : ¬ IsComposite (A297707 250 - Nat.prevPrime (A297707 250)) := by
  have hd : A297707 250 - Nat.prevPrime (A297707 250) = 9277 := by sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact prime_9277

