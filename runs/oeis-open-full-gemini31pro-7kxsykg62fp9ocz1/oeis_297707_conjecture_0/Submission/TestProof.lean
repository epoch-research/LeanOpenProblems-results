import Submission.Spec
open Nat Finset BigOperators

theorem not_composite_3 : ¬ IsComposite (A297707 3 - Nat.prevPrime (A297707 3)) := by
  have hd : A297707 3 - Nat.prevPrime (A297707 3) = 1 := sorry
  rw [hd]
  dsimp [IsComposite]
  intro h
  rcases h with ⟨h1, h2⟩
  revert h1
  decide

theorem not_composite_4 : ¬ IsComposite (A297707 4 - Nat.prevPrime (A297707 4)) := by
  have hd : A297707 4 - Nat.prevPrime (A297707 4) = 7 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_5 : ¬ IsComposite (A297707 5 - Nat.prevPrime (A297707 5)) := by
  have hd : A297707 5 - Nat.prevPrime (A297707 5) = 11 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_6 : ¬ IsComposite (A297707 6 - Nat.prevPrime (A297707 6)) := by
  have hd : A297707 6 - Nat.prevPrime (A297707 6) = 23 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_7 : ¬ IsComposite (A297707 7 - Nat.prevPrime (A297707 7)) := by
  have hd : A297707 7 - Nat.prevPrime (A297707 7) = 13 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_8 : ¬ IsComposite (A297707 8 - Nat.prevPrime (A297707 8)) := by
  have hd : A297707 8 - Nat.prevPrime (A297707 8) = 17 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_9 : ¬ IsComposite (A297707 9 - Nat.prevPrime (A297707 9)) := by
  have hd : A297707 9 - Nat.prevPrime (A297707 9) = 13 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_10 : ¬ IsComposite (A297707 10 - Nat.prevPrime (A297707 10)) := by
  have hd : A297707 10 - Nat.prevPrime (A297707 10) = 83 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_11 : ¬ IsComposite (A297707 11 - Nat.prevPrime (A297707 11)) := by
  have hd : A297707 11 - Nat.prevPrime (A297707 11) = 29 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_12 : ¬ IsComposite (A297707 12 - Nat.prevPrime (A297707 12)) := by
  have hd : A297707 12 - Nat.prevPrime (A297707 12) = 157 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_13 : ¬ IsComposite (A297707 13 - Nat.prevPrime (A297707 13)) := by
  have hd : A297707 13 - Nat.prevPrime (A297707 13) = 41 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_14 : ¬ IsComposite (A297707 14 - Nat.prevPrime (A297707 14)) := by
  have hd : A297707 14 - Nat.prevPrime (A297707 14) = 23 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_15 : ¬ IsComposite (A297707 15 - Nat.prevPrime (A297707 15)) := by
  have hd : A297707 15 - Nat.prevPrime (A297707 15) = 53 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_16 : ¬ IsComposite (A297707 16 - Nat.prevPrime (A297707 16)) := by
  have hd : A297707 16 - Nat.prevPrime (A297707 16) = 157 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_17 : ¬ IsComposite (A297707 17 - Nat.prevPrime (A297707 17)) := by
  have hd : A297707 17 - Nat.prevPrime (A297707 17) = 433 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_18 : ¬ IsComposite (A297707 18 - Nat.prevPrime (A297707 18)) := by
  have hd : A297707 18 - Nat.prevPrime (A297707 18) = 103 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_19 : ¬ IsComposite (A297707 19 - Nat.prevPrime (A297707 19)) := by
  have hd : A297707 19 - Nat.prevPrime (A297707 19) = 83 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_20 : ¬ IsComposite (A297707 20 - Nat.prevPrime (A297707 20)) := by
  have hd : A297707 20 - Nat.prevPrime (A297707 20) = 107 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_21 : ¬ IsComposite (A297707 21 - Nat.prevPrime (A297707 21)) := by
  have hd : A297707 21 - Nat.prevPrime (A297707 21) = 23 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_22 : ¬ IsComposite (A297707 22 - Nat.prevPrime (A297707 22)) := by
  have hd : A297707 22 - Nat.prevPrime (A297707 22) = 43 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_23 : ¬ IsComposite (A297707 23 - Nat.prevPrime (A297707 23)) := by
  have hd : A297707 23 - Nat.prevPrime (A297707 23) = 719 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_24 : ¬ IsComposite (A297707 24 - Nat.prevPrime (A297707 24)) := by
  have hd : A297707 24 - Nat.prevPrime (A297707 24) = 421 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_25 : ¬ IsComposite (A297707 25 - Nat.prevPrime (A297707 25)) := by
  have hd : A297707 25 - Nat.prevPrime (A297707 25) = 431 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_26 : ¬ IsComposite (A297707 26 - Nat.prevPrime (A297707 26)) := by
  have hd : A297707 26 - Nat.prevPrime (A297707 26) = 67 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_27 : ¬ IsComposite (A297707 27 - Nat.prevPrime (A297707 27)) := by
  have hd : A297707 27 - Nat.prevPrime (A297707 27) = 47 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_28 : ¬ IsComposite (A297707 28 - Nat.prevPrime (A297707 28)) := by
  have hd : A297707 28 - Nat.prevPrime (A297707 28) = 193 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_29 : ¬ IsComposite (A297707 29 - Nat.prevPrime (A297707 29)) := by
  have hd : A297707 29 - Nat.prevPrime (A297707 29) = 367 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_30 : ¬ IsComposite (A297707 30 - Nat.prevPrime (A297707 30)) := by
  have hd : A297707 30 - Nat.prevPrime (A297707 30) = 167 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_31 : ¬ IsComposite (A297707 31 - Nat.prevPrime (A297707 31)) := by
  have hd : A297707 31 - Nat.prevPrime (A297707 31) = 809 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_32 : ¬ IsComposite (A297707 32 - Nat.prevPrime (A297707 32)) := by
  have hd : A297707 32 - Nat.prevPrime (A297707 32) = 1109 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_33 : ¬ IsComposite (A297707 33 - Nat.prevPrime (A297707 33)) := by
  have hd : A297707 33 - Nat.prevPrime (A297707 33) = 421 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_34 : ¬ IsComposite (A297707 34 - Nat.prevPrime (A297707 34)) := by
  have hd : A297707 34 - Nat.prevPrime (A297707 34) = 401 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_35 : ¬ IsComposite (A297707 35 - Nat.prevPrime (A297707 35)) := by
  have hd : A297707 35 - Nat.prevPrime (A297707 35) = 239 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_36 : ¬ IsComposite (A297707 36 - Nat.prevPrime (A297707 36)) := by
  have hd : A297707 36 - Nat.prevPrime (A297707 36) = 479 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_37 : ¬ IsComposite (A297707 37 - Nat.prevPrime (A297707 37)) := by
  have hd : A297707 37 - Nat.prevPrime (A297707 37) = 1307 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_38 : ¬ IsComposite (A297707 38 - Nat.prevPrime (A297707 38)) := by
  have hd : A297707 38 - Nat.prevPrime (A297707 38) = 521 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_39 : ¬ IsComposite (A297707 39 - Nat.prevPrime (A297707 39)) := by
  have hd : A297707 39 - Nat.prevPrime (A297707 39) = 53 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_40 : ¬ IsComposite (A297707 40 - Nat.prevPrime (A297707 40)) := by
  have hd : A297707 40 - Nat.prevPrime (A297707 40) = 983 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_41 : ¬ IsComposite (A297707 41 - Nat.prevPrime (A297707 41)) := by
  have hd : A297707 41 - Nat.prevPrime (A297707 41) = 3413 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_42 : ¬ IsComposite (A297707 42 - Nat.prevPrime (A297707 42)) := by
  have hd : A297707 42 - Nat.prevPrime (A297707 42) = 1217 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_43 : ¬ IsComposite (A297707 43 - Nat.prevPrime (A297707 43)) := by
  have hd : A297707 43 - Nat.prevPrime (A297707 43) = 887 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_44 : ¬ IsComposite (A297707 44 - Nat.prevPrime (A297707 44)) := by
  have hd : A297707 44 - Nat.prevPrime (A297707 44) = 41 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_45 : ¬ IsComposite (A297707 45 - Nat.prevPrime (A297707 45)) := by
  have hd : A297707 45 - Nat.prevPrime (A297707 45) = 89 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_46 : ¬ IsComposite (A297707 46 - Nat.prevPrime (A297707 46)) := by
  have hd : A297707 46 - Nat.prevPrime (A297707 46) = 17 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_47 : ¬ IsComposite (A297707 47 - Nat.prevPrime (A297707 47)) := by
  have hd : A297707 47 - Nat.prevPrime (A297707 47) = 181 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_48 : ¬ IsComposite (A297707 48 - Nat.prevPrime (A297707 48)) := by
  have hd : A297707 48 - Nat.prevPrime (A297707 48) = 1229 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_49 : ¬ IsComposite (A297707 49 - Nat.prevPrime (A297707 49)) := by
  have hd : A297707 49 - Nat.prevPrime (A297707 49) = 1277 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_50 : ¬ IsComposite (A297707 50 - Nat.prevPrime (A297707 50)) := by
  have hd : A297707 50 - Nat.prevPrime (A297707 50) = 1613 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_51 : ¬ IsComposite (A297707 51 - Nat.prevPrime (A297707 51)) := by
  have hd : A297707 51 - Nat.prevPrime (A297707 51) = 743 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_52 : ¬ IsComposite (A297707 52 - Nat.prevPrime (A297707 52)) := by
  have hd : A297707 52 - Nat.prevPrime (A297707 52) = 1997 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_53 : ¬ IsComposite (A297707 53 - Nat.prevPrime (A297707 53)) := by
  have hd : A297707 53 - Nat.prevPrime (A297707 53) = 2027 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_54 : ¬ IsComposite (A297707 54 - Nat.prevPrime (A297707 54)) := by
  have hd : A297707 54 - Nat.prevPrime (A297707 54) = 31 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_55 : ¬ IsComposite (A297707 55 - Nat.prevPrime (A297707 55)) := by
  have hd : A297707 55 - Nat.prevPrime (A297707 55) = 1061 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_56 : ¬ IsComposite (A297707 56 - Nat.prevPrime (A297707 56)) := by
  have hd : A297707 56 - Nat.prevPrime (A297707 56) = 769 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_57 : ¬ IsComposite (A297707 57 - Nat.prevPrime (A297707 57)) := by
  have hd : A297707 57 - Nat.prevPrime (A297707 57) = 389 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_58 : ¬ IsComposite (A297707 58 - Nat.prevPrime (A297707 58)) := by
  have hd : A297707 58 - Nat.prevPrime (A297707 58) = 419 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_59 : ¬ IsComposite (A297707 59 - Nat.prevPrime (A297707 59)) := by
  have hd : A297707 59 - Nat.prevPrime (A297707 59) = 673 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_60 : ¬ IsComposite (A297707 60 - Nat.prevPrime (A297707 60)) := by
  have hd : A297707 60 - Nat.prevPrime (A297707 60) = 443 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_61 : ¬ IsComposite (A297707 61 - Nat.prevPrime (A297707 61)) := by
  have hd : A297707 61 - Nat.prevPrime (A297707 61) = 317 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_62 : ¬ IsComposite (A297707 62 - Nat.prevPrime (A297707 62)) := by
  have hd : A297707 62 - Nat.prevPrime (A297707 62) = 1423 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_63 : ¬ IsComposite (A297707 63 - Nat.prevPrime (A297707 63)) := by
  have hd : A297707 63 - Nat.prevPrime (A297707 63) = 1109 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_64 : ¬ IsComposite (A297707 64 - Nat.prevPrime (A297707 64)) := by
  have hd : A297707 64 - Nat.prevPrime (A297707 64) = 311 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_65 : ¬ IsComposite (A297707 65 - Nat.prevPrime (A297707 65)) := by
  have hd : A297707 65 - Nat.prevPrime (A297707 65) = 3539 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_66 : ¬ IsComposite (A297707 66 - Nat.prevPrime (A297707 66)) := by
  have hd : A297707 66 - Nat.prevPrime (A297707 66) = 3023 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_67 : ¬ IsComposite (A297707 67 - Nat.prevPrime (A297707 67)) := by
  have hd : A297707 67 - Nat.prevPrime (A297707 67) = 1619 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_68 : ¬ IsComposite (A297707 68 - Nat.prevPrime (A297707 68)) := by
  have hd : A297707 68 - Nat.prevPrime (A297707 68) = 271 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_69 : ¬ IsComposite (A297707 69 - Nat.prevPrime (A297707 69)) := by
  have hd : A297707 69 - Nat.prevPrime (A297707 69) = 11 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_70 : ¬ IsComposite (A297707 70 - Nat.prevPrime (A297707 70)) := by
  have hd : A297707 70 - Nat.prevPrime (A297707 70) = 677 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_71 : ¬ IsComposite (A297707 71 - Nat.prevPrime (A297707 71)) := by
  have hd : A297707 71 - Nat.prevPrime (A297707 71) = 431 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_72 : ¬ IsComposite (A297707 72 - Nat.prevPrime (A297707 72)) := by
  have hd : A297707 72 - Nat.prevPrime (A297707 72) = 2423 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_73 : ¬ IsComposite (A297707 73 - Nat.prevPrime (A297707 73)) := by
  have hd : A297707 73 - Nat.prevPrime (A297707 73) = 1511 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_74 : ¬ IsComposite (A297707 74 - Nat.prevPrime (A297707 74)) := by
  have hd : A297707 74 - Nat.prevPrime (A297707 74) = 739 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_75 : ¬ IsComposite (A297707 75 - Nat.prevPrime (A297707 75)) := by
  have hd : A297707 75 - Nat.prevPrime (A297707 75) = 1019 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_76 : ¬ IsComposite (A297707 76 - Nat.prevPrime (A297707 76)) := by
  have hd : A297707 76 - Nat.prevPrime (A297707 76) = 971 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_77 : ¬ IsComposite (A297707 77 - Nat.prevPrime (A297707 77)) := by
  have hd : A297707 77 - Nat.prevPrime (A297707 77) = 2729 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_78 : ¬ IsComposite (A297707 78 - Nat.prevPrime (A297707 78)) := by
  have hd : A297707 78 - Nat.prevPrime (A297707 78) = 3779 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_79 : ¬ IsComposite (A297707 79 - Nat.prevPrime (A297707 79)) := by
  have hd : A297707 79 - Nat.prevPrime (A297707 79) = 563 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_80 : ¬ IsComposite (A297707 80 - Nat.prevPrime (A297707 80)) := by
  have hd : A297707 80 - Nat.prevPrime (A297707 80) = 373 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_81 : ¬ IsComposite (A297707 81 - Nat.prevPrime (A297707 81)) := by
  have hd : A297707 81 - Nat.prevPrime (A297707 81) = 2477 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_82 : ¬ IsComposite (A297707 82 - Nat.prevPrime (A297707 82)) := by
  have hd : A297707 82 - Nat.prevPrime (A297707 82) = 1193 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_83 : ¬ IsComposite (A297707 83 - Nat.prevPrime (A297707 83)) := by
  have hd : A297707 83 - Nat.prevPrime (A297707 83) = 109 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_84 : ¬ IsComposite (A297707 84 - Nat.prevPrime (A297707 84)) := by
  have hd : A297707 84 - Nat.prevPrime (A297707 84) = 383 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_85 : ¬ IsComposite (A297707 85 - Nat.prevPrime (A297707 85)) := by
  have hd : A297707 85 - Nat.prevPrime (A297707 85) = 1109 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_86 : ¬ IsComposite (A297707 86 - Nat.prevPrime (A297707 86)) := by
  have hd : A297707 86 - Nat.prevPrime (A297707 86) = 491 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_87 : ¬ IsComposite (A297707 87 - Nat.prevPrime (A297707 87)) := by
  have hd : A297707 87 - Nat.prevPrime (A297707 87) = 577 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_88 : ¬ IsComposite (A297707 88 - Nat.prevPrime (A297707 88)) := by
  have hd : A297707 88 - Nat.prevPrime (A297707 88) = 157 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_89 : ¬ IsComposite (A297707 89 - Nat.prevPrime (A297707 89)) := by
  have hd : A297707 89 - Nat.prevPrime (A297707 89) = 223 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_90 : ¬ IsComposite (A297707 90 - Nat.prevPrime (A297707 90)) := by
  have hd : A297707 90 - Nat.prevPrime (A297707 90) = 6733 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_91 : ¬ IsComposite (A297707 91 - Nat.prevPrime (A297707 91)) := by
  have hd : A297707 91 - Nat.prevPrime (A297707 91) = 853 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_92 : ¬ IsComposite (A297707 92 - Nat.prevPrime (A297707 92)) := by
  have hd : A297707 92 - Nat.prevPrime (A297707 92) = 1367 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_93 : ¬ IsComposite (A297707 93 - Nat.prevPrime (A297707 93)) := by
  have hd : A297707 93 - Nat.prevPrime (A297707 93) = 1523 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_94 : ¬ IsComposite (A297707 94 - Nat.prevPrime (A297707 94)) := by
  have hd : A297707 94 - Nat.prevPrime (A297707 94) = 821 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_95 : ¬ IsComposite (A297707 95 - Nat.prevPrime (A297707 95)) := by
  have hd : A297707 95 - Nat.prevPrime (A297707 95) = 1217 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_96 : ¬ IsComposite (A297707 96 - Nat.prevPrime (A297707 96)) := by
  have hd : A297707 96 - Nat.prevPrime (A297707 96) = 1319 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_97 : ¬ IsComposite (A297707 97 - Nat.prevPrime (A297707 97)) := by
  have hd : A297707 97 - Nat.prevPrime (A297707 97) = 103 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_98 : ¬ IsComposite (A297707 98 - Nat.prevPrime (A297707 98)) := by
  have hd : A297707 98 - Nat.prevPrime (A297707 98) = 751 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_99 : ¬ IsComposite (A297707 99 - Nat.prevPrime (A297707 99)) := by
  have hd : A297707 99 - Nat.prevPrime (A297707 99) = 1973 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_100 : ¬ IsComposite (A297707 100 - Nat.prevPrime (A297707 100)) := by
  have hd : A297707 100 - Nat.prevPrime (A297707 100) = 3911 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_101 : ¬ IsComposite (A297707 101 - Nat.prevPrime (A297707 101)) := by
  have hd : A297707 101 - Nat.prevPrime (A297707 101) = 31 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_102 : ¬ IsComposite (A297707 102 - Nat.prevPrime (A297707 102)) := by
  have hd : A297707 102 - Nat.prevPrime (A297707 102) = 1481 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_103 : ¬ IsComposite (A297707 103 - Nat.prevPrime (A297707 103)) := by
  have hd : A297707 103 - Nat.prevPrime (A297707 103) = 1289 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_104 : ¬ IsComposite (A297707 104 - Nat.prevPrime (A297707 104)) := by
  have hd : A297707 104 - Nat.prevPrime (A297707 104) = 37 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_105 : ¬ IsComposite (A297707 105 - Nat.prevPrime (A297707 105)) := by
  have hd : A297707 105 - Nat.prevPrime (A297707 105) = 6563 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_106 : ¬ IsComposite (A297707 106 - Nat.prevPrime (A297707 106)) := by
  have hd : A297707 106 - Nat.prevPrime (A297707 106) = 2351 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_107 : ¬ IsComposite (A297707 107 - Nat.prevPrime (A297707 107)) := by
  have hd : A297707 107 - Nat.prevPrime (A297707 107) = 743 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_108 : ¬ IsComposite (A297707 108 - Nat.prevPrime (A297707 108)) := by
  have hd : A297707 108 - Nat.prevPrime (A297707 108) = 71 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_109 : ¬ IsComposite (A297707 109 - Nat.prevPrime (A297707 109)) := by
  have hd : A297707 109 - Nat.prevPrime (A297707 109) = 241 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_110 : ¬ IsComposite (A297707 110 - Nat.prevPrime (A297707 110)) := by
  have hd : A297707 110 - Nat.prevPrime (A297707 110) = 241 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_111 : ¬ IsComposite (A297707 111 - Nat.prevPrime (A297707 111)) := by
  have hd : A297707 111 - Nat.prevPrime (A297707 111) = 4093 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_112 : ¬ IsComposite (A297707 112 - Nat.prevPrime (A297707 112)) := by
  have hd : A297707 112 - Nat.prevPrime (A297707 112) = 577 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_113 : ¬ IsComposite (A297707 113 - Nat.prevPrime (A297707 113)) := by
  have hd : A297707 113 - Nat.prevPrime (A297707 113) = 2311 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_114 : ¬ IsComposite (A297707 114 - Nat.prevPrime (A297707 114)) := by
  have hd : A297707 114 - Nat.prevPrime (A297707 114) = 677 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_115 : ¬ IsComposite (A297707 115 - Nat.prevPrime (A297707 115)) := by
  have hd : A297707 115 - Nat.prevPrime (A297707 115) = 41 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_116 : ¬ IsComposite (A297707 116 - Nat.prevPrime (A297707 116)) := by
  have hd : A297707 116 - Nat.prevPrime (A297707 116) = 6257 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_117 : ¬ IsComposite (A297707 117 - Nat.prevPrime (A297707 117)) := by
  have hd : A297707 117 - Nat.prevPrime (A297707 117) = 311 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_118 : ¬ IsComposite (A297707 118 - Nat.prevPrime (A297707 118)) := by
  have hd : A297707 118 - Nat.prevPrime (A297707 118) = 6907 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_119 : ¬ IsComposite (A297707 119 - Nat.prevPrime (A297707 119)) := by
  have hd : A297707 119 - Nat.prevPrime (A297707 119) = 2113 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_120 : ¬ IsComposite (A297707 120 - Nat.prevPrime (A297707 120)) := by
  have hd : A297707 120 - Nat.prevPrime (A297707 120) = 5413 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_121 : ¬ IsComposite (A297707 121 - Nat.prevPrime (A297707 121)) := by
  have hd : A297707 121 - Nat.prevPrime (A297707 121) = 211 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_122 : ¬ IsComposite (A297707 122 - Nat.prevPrime (A297707 122)) := by
  have hd : A297707 122 - Nat.prevPrime (A297707 122) = 4457 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_123 : ¬ IsComposite (A297707 123 - Nat.prevPrime (A297707 123)) := by
  have hd : A297707 123 - Nat.prevPrime (A297707 123) = 821 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_124 : ¬ IsComposite (A297707 124 - Nat.prevPrime (A297707 124)) := by
  have hd : A297707 124 - Nat.prevPrime (A297707 124) = 7919 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_125 : ¬ IsComposite (A297707 125 - Nat.prevPrime (A297707 125)) := by
  have hd : A297707 125 - Nat.prevPrime (A297707 125) = 4679 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_126 : ¬ IsComposite (A297707 126 - Nat.prevPrime (A297707 126)) := by
  have hd : A297707 126 - Nat.prevPrime (A297707 126) = 4793 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_127 : ¬ IsComposite (A297707 127 - Nat.prevPrime (A297707 127)) := by
  have hd : A297707 127 - Nat.prevPrime (A297707 127) = 167 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_128 : ¬ IsComposite (A297707 128 - Nat.prevPrime (A297707 128)) := by
  have hd : A297707 128 - Nat.prevPrime (A297707 128) = 1621 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_129 : ¬ IsComposite (A297707 129 - Nat.prevPrime (A297707 129)) := by
  have hd : A297707 129 - Nat.prevPrime (A297707 129) = 2953 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_130 : ¬ IsComposite (A297707 130 - Nat.prevPrime (A297707 130)) := by
  have hd : A297707 130 - Nat.prevPrime (A297707 130) = 17387 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_131 : ¬ IsComposite (A297707 131 - Nat.prevPrime (A297707 131)) := by
  have hd : A297707 131 - Nat.prevPrime (A297707 131) = 7823 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_132 : ¬ IsComposite (A297707 132 - Nat.prevPrime (A297707 132)) := by
  have hd : A297707 132 - Nat.prevPrime (A297707 132) = 3779 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_133 : ¬ IsComposite (A297707 133 - Nat.prevPrime (A297707 133)) := by
  have hd : A297707 133 - Nat.prevPrime (A297707 133) = 569 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_134 : ¬ IsComposite (A297707 134 - Nat.prevPrime (A297707 134)) := by
  have hd : A297707 134 - Nat.prevPrime (A297707 134) = 4813 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_135 : ¬ IsComposite (A297707 135 - Nat.prevPrime (A297707 135)) := by
  have hd : A297707 135 - Nat.prevPrime (A297707 135) = 1511 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_136 : ¬ IsComposite (A297707 136 - Nat.prevPrime (A297707 136)) := by
  have hd : A297707 136 - Nat.prevPrime (A297707 136) = 4751 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_137 : ¬ IsComposite (A297707 137 - Nat.prevPrime (A297707 137)) := by
  have hd : A297707 137 - Nat.prevPrime (A297707 137) = 103 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_138 : ¬ IsComposite (A297707 138 - Nat.prevPrime (A297707 138)) := by
  have hd : A297707 138 - Nat.prevPrime (A297707 138) = 4337 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_139 : ¬ IsComposite (A297707 139 - Nat.prevPrime (A297707 139)) := by
  have hd : A297707 139 - Nat.prevPrime (A297707 139) = 2503 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_140 : ¬ IsComposite (A297707 140 - Nat.prevPrime (A297707 140)) := by
  have hd : A297707 140 - Nat.prevPrime (A297707 140) = 607 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_141 : ¬ IsComposite (A297707 141 - Nat.prevPrime (A297707 141)) := by
  have hd : A297707 141 - Nat.prevPrime (A297707 141) = 937 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_142 : ¬ IsComposite (A297707 142 - Nat.prevPrime (A297707 142)) := by
  have hd : A297707 142 - Nat.prevPrime (A297707 142) = 3761 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_143 : ¬ IsComposite (A297707 143 - Nat.prevPrime (A297707 143)) := by
  have hd : A297707 143 - Nat.prevPrime (A297707 143) = 7673 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_144 : ¬ IsComposite (A297707 144 - Nat.prevPrime (A297707 144)) := by
  have hd : A297707 144 - Nat.prevPrime (A297707 144) = 15817 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_145 : ¬ IsComposite (A297707 145 - Nat.prevPrime (A297707 145)) := by
  have hd : A297707 145 - Nat.prevPrime (A297707 145) = 10259 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_146 : ¬ IsComposite (A297707 146 - Nat.prevPrime (A297707 146)) := by
  have hd : A297707 146 - Nat.prevPrime (A297707 146) = 13327 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_147 : ¬ IsComposite (A297707 147 - Nat.prevPrime (A297707 147)) := by
  have hd : A297707 147 - Nat.prevPrime (A297707 147) = 17827 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_148 : ¬ IsComposite (A297707 148 - Nat.prevPrime (A297707 148)) := by
  have hd : A297707 148 - Nat.prevPrime (A297707 148) = 859 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_149 : ¬ IsComposite (A297707 149 - Nat.prevPrime (A297707 149)) := by
  have hd : A297707 149 - Nat.prevPrime (A297707 149) = 2213 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_150 : ¬ IsComposite (A297707 150 - Nat.prevPrime (A297707 150)) := by
  have hd : A297707 150 - Nat.prevPrime (A297707 150) = 1217 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_151 : ¬ IsComposite (A297707 151 - Nat.prevPrime (A297707 151)) := by
  have hd : A297707 151 - Nat.prevPrime (A297707 151) = 1579 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_152 : ¬ IsComposite (A297707 152 - Nat.prevPrime (A297707 152)) := by
  have hd : A297707 152 - Nat.prevPrime (A297707 152) = 229 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_153 : ¬ IsComposite (A297707 153 - Nat.prevPrime (A297707 153)) := by
  have hd : A297707 153 - Nat.prevPrime (A297707 153) = 1657 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_154 : ¬ IsComposite (A297707 154 - Nat.prevPrime (A297707 154)) := by
  have hd : A297707 154 - Nat.prevPrime (A297707 154) = 2939 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_155 : ¬ IsComposite (A297707 155 - Nat.prevPrime (A297707 155)) := by
  have hd : A297707 155 - Nat.prevPrime (A297707 155) = 1231 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_156 : ¬ IsComposite (A297707 156 - Nat.prevPrime (A297707 156)) := by
  have hd : A297707 156 - Nat.prevPrime (A297707 156) = 4261 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_157 : ¬ IsComposite (A297707 157 - Nat.prevPrime (A297707 157)) := by
  have hd : A297707 157 - Nat.prevPrime (A297707 157) = 14081 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_158 : ¬ IsComposite (A297707 158 - Nat.prevPrime (A297707 158)) := by
  have hd : A297707 158 - Nat.prevPrime (A297707 158) = 773 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_159 : ¬ IsComposite (A297707 159 - Nat.prevPrime (A297707 159)) := by
  have hd : A297707 159 - Nat.prevPrime (A297707 159) = 367 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_160 : ¬ IsComposite (A297707 160 - Nat.prevPrime (A297707 160)) := by
  have hd : A297707 160 - Nat.prevPrime (A297707 160) = 2953 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_161 : ¬ IsComposite (A297707 161 - Nat.prevPrime (A297707 161)) := by
  have hd : A297707 161 - Nat.prevPrime (A297707 161) = 1039 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_162 : ¬ IsComposite (A297707 162 - Nat.prevPrime (A297707 162)) := by
  have hd : A297707 162 - Nat.prevPrime (A297707 162) = 3581 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_163 : ¬ IsComposite (A297707 163 - Nat.prevPrime (A297707 163)) := by
  have hd : A297707 163 - Nat.prevPrime (A297707 163) = 6947 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_164 : ¬ IsComposite (A297707 164 - Nat.prevPrime (A297707 164)) := by
  have hd : A297707 164 - Nat.prevPrime (A297707 164) = 709 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_165 : ¬ IsComposite (A297707 165 - Nat.prevPrime (A297707 165)) := by
  have hd : A297707 165 - Nat.prevPrime (A297707 165) = 311 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_166 : ¬ IsComposite (A297707 166 - Nat.prevPrime (A297707 166)) := by
  have hd : A297707 166 - Nat.prevPrime (A297707 166) = 1997 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_167 : ¬ IsComposite (A297707 167 - Nat.prevPrime (A297707 167)) := by
  have hd : A297707 167 - Nat.prevPrime (A297707 167) = 1997 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_168 : ¬ IsComposite (A297707 168 - Nat.prevPrime (A297707 168)) := by
  have hd : A297707 168 - Nat.prevPrime (A297707 168) = 6971 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_169 : ¬ IsComposite (A297707 169 - Nat.prevPrime (A297707 169)) := by
  have hd : A297707 169 - Nat.prevPrime (A297707 169) = 2693 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_170 : ¬ IsComposite (A297707 170 - Nat.prevPrime (A297707 170)) := by
  have hd : A297707 170 - Nat.prevPrime (A297707 170) = 3539 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_171 : ¬ IsComposite (A297707 171 - Nat.prevPrime (A297707 171)) := by
  have hd : A297707 171 - Nat.prevPrime (A297707 171) = 1913 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_172 : ¬ IsComposite (A297707 172 - Nat.prevPrime (A297707 172)) := by
  have hd : A297707 172 - Nat.prevPrime (A297707 172) = 3727 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_173 : ¬ IsComposite (A297707 173 - Nat.prevPrime (A297707 173)) := by
  have hd : A297707 173 - Nat.prevPrime (A297707 173) = 277 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_174 : ¬ IsComposite (A297707 174 - Nat.prevPrime (A297707 174)) := by
  have hd : A297707 174 - Nat.prevPrime (A297707 174) = 4519 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_175 : ¬ IsComposite (A297707 175 - Nat.prevPrime (A297707 175)) := by
  have hd : A297707 175 - Nat.prevPrime (A297707 175) = 1879 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_176 : ¬ IsComposite (A297707 176 - Nat.prevPrime (A297707 176)) := by
  have hd : A297707 176 - Nat.prevPrime (A297707 176) = 2239 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_177 : ¬ IsComposite (A297707 177 - Nat.prevPrime (A297707 177)) := by
  have hd : A297707 177 - Nat.prevPrime (A297707 177) = 3469 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_178 : ¬ IsComposite (A297707 178 - Nat.prevPrime (A297707 178)) := by
  have hd : A297707 178 - Nat.prevPrime (A297707 178) = 15601 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_179 : ¬ IsComposite (A297707 179 - Nat.prevPrime (A297707 179)) := by
  have hd : A297707 179 - Nat.prevPrime (A297707 179) = 5231 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_180 : ¬ IsComposite (A297707 180 - Nat.prevPrime (A297707 180)) := by
  have hd : A297707 180 - Nat.prevPrime (A297707 180) = 421 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_181 : ¬ IsComposite (A297707 181 - Nat.prevPrime (A297707 181)) := by
  have hd : A297707 181 - Nat.prevPrime (A297707 181) = 2477 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_182 : ¬ IsComposite (A297707 182 - Nat.prevPrime (A297707 182)) := by
  have hd : A297707 182 - Nat.prevPrime (A297707 182) = 6269 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_183 : ¬ IsComposite (A297707 183 - Nat.prevPrime (A297707 183)) := by
  have hd : A297707 183 - Nat.prevPrime (A297707 183) = 613 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_184 : ¬ IsComposite (A297707 184 - Nat.prevPrime (A297707 184)) := by
  have hd : A297707 184 - Nat.prevPrime (A297707 184) = 1831 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_185 : ¬ IsComposite (A297707 185 - Nat.prevPrime (A297707 185)) := by
  have hd : A297707 185 - Nat.prevPrime (A297707 185) = 3001 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_186 : ¬ IsComposite (A297707 186 - Nat.prevPrime (A297707 186)) := by
  have hd : A297707 186 - Nat.prevPrime (A297707 186) = 757 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_187 : ¬ IsComposite (A297707 187 - Nat.prevPrime (A297707 187)) := by
  have hd : A297707 187 - Nat.prevPrime (A297707 187) = 5417 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_188 : ¬ IsComposite (A297707 188 - Nat.prevPrime (A297707 188)) := by
  have hd : A297707 188 - Nat.prevPrime (A297707 188) = 4813 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_189 : ¬ IsComposite (A297707 189 - Nat.prevPrime (A297707 189)) := by
  have hd : A297707 189 - Nat.prevPrime (A297707 189) = 15913 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_190 : ¬ IsComposite (A297707 190 - Nat.prevPrime (A297707 190)) := by
  have hd : A297707 190 - Nat.prevPrime (A297707 190) = 2609 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_191 : ¬ IsComposite (A297707 191 - Nat.prevPrime (A297707 191)) := by
  have hd : A297707 191 - Nat.prevPrime (A297707 191) = 1181 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_192 : ¬ IsComposite (A297707 192 - Nat.prevPrime (A297707 192)) := by
  have hd : A297707 192 - Nat.prevPrime (A297707 192) = 7253 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_193 : ¬ IsComposite (A297707 193 - Nat.prevPrime (A297707 193)) := by
  have hd : A297707 193 - Nat.prevPrime (A297707 193) = 18301 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_194 : ¬ IsComposite (A297707 194 - Nat.prevPrime (A297707 194)) := by
  have hd : A297707 194 - Nat.prevPrime (A297707 194) = 239 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_195 : ¬ IsComposite (A297707 195 - Nat.prevPrime (A297707 195)) := by
  have hd : A297707 195 - Nat.prevPrime (A297707 195) = 7193 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_196 : ¬ IsComposite (A297707 196 - Nat.prevPrime (A297707 196)) := by
  have hd : A297707 196 - Nat.prevPrime (A297707 196) = 6661 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_197 : ¬ IsComposite (A297707 197 - Nat.prevPrime (A297707 197)) := by
  have hd : A297707 197 - Nat.prevPrime (A297707 197) = 10333 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_198 : ¬ IsComposite (A297707 198 - Nat.prevPrime (A297707 198)) := by
  have hd : A297707 198 - Nat.prevPrime (A297707 198) = 4349 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_199 : ¬ IsComposite (A297707 199 - Nat.prevPrime (A297707 199)) := by
  have hd : A297707 199 - Nat.prevPrime (A297707 199) = 10949 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_200 : ¬ IsComposite (A297707 200 - Nat.prevPrime (A297707 200)) := by
  have hd : A297707 200 - Nat.prevPrime (A297707 200) = 10151 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_201 : ¬ IsComposite (A297707 201 - Nat.prevPrime (A297707 201)) := by
  have hd : A297707 201 - Nat.prevPrime (A297707 201) = 3637 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_202 : ¬ IsComposite (A297707 202 - Nat.prevPrime (A297707 202)) := by
  have hd : A297707 202 - Nat.prevPrime (A297707 202) = 347 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_203 : ¬ IsComposite (A297707 203 - Nat.prevPrime (A297707 203)) := by
  have hd : A297707 203 - Nat.prevPrime (A297707 203) = 2909 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_204 : ¬ IsComposite (A297707 204 - Nat.prevPrime (A297707 204)) := by
  have hd : A297707 204 - Nat.prevPrime (A297707 204) = 1117 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_205 : ¬ IsComposite (A297707 205 - Nat.prevPrime (A297707 205)) := by
  have hd : A297707 205 - Nat.prevPrime (A297707 205) = 13967 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_206 : ¬ IsComposite (A297707 206 - Nat.prevPrime (A297707 206)) := by
  have hd : A297707 206 - Nat.prevPrime (A297707 206) = 18119 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_207 : ¬ IsComposite (A297707 207 - Nat.prevPrime (A297707 207)) := by
  have hd : A297707 207 - Nat.prevPrime (A297707 207) = 9749 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_208 : ¬ IsComposite (A297707 208 - Nat.prevPrime (A297707 208)) := by
  have hd : A297707 208 - Nat.prevPrime (A297707 208) = 283 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_209 : ¬ IsComposite (A297707 209 - Nat.prevPrime (A297707 209)) := by
  have hd : A297707 209 - Nat.prevPrime (A297707 209) = 5573 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_210 : ¬ IsComposite (A297707 210 - Nat.prevPrime (A297707 210)) := by
  have hd : A297707 210 - Nat.prevPrime (A297707 210) = 13477 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_211 : ¬ IsComposite (A297707 211 - Nat.prevPrime (A297707 211)) := by
  have hd : A297707 211 - Nat.prevPrime (A297707 211) = 883 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_212 : ¬ IsComposite (A297707 212 - Nat.prevPrime (A297707 212)) := by
  have hd : A297707 212 - Nat.prevPrime (A297707 212) = 2309 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_213 : ¬ IsComposite (A297707 213 - Nat.prevPrime (A297707 213)) := by
  have hd : A297707 213 - Nat.prevPrime (A297707 213) = 4507 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_214 : ¬ IsComposite (A297707 214 - Nat.prevPrime (A297707 214)) := by
  have hd : A297707 214 - Nat.prevPrime (A297707 214) = 7561 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_215 : ¬ IsComposite (A297707 215 - Nat.prevPrime (A297707 215)) := by
  have hd : A297707 215 - Nat.prevPrime (A297707 215) = 1259 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_216 : ¬ IsComposite (A297707 216 - Nat.prevPrime (A297707 216)) := by
  have hd : A297707 216 - Nat.prevPrime (A297707 216) = 3001 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_217 : ¬ IsComposite (A297707 217 - Nat.prevPrime (A297707 217)) := by
  have hd : A297707 217 - Nat.prevPrime (A297707 217) = 2927 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_218 : ¬ IsComposite (A297707 218 - Nat.prevPrime (A297707 218)) := by
  have hd : A297707 218 - Nat.prevPrime (A297707 218) = 1789 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_219 : ¬ IsComposite (A297707 219 - Nat.prevPrime (A297707 219)) := by
  have hd : A297707 219 - Nat.prevPrime (A297707 219) = 877 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_220 : ¬ IsComposite (A297707 220 - Nat.prevPrime (A297707 220)) := by
  have hd : A297707 220 - Nat.prevPrime (A297707 220) = 1097 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_221 : ¬ IsComposite (A297707 221 - Nat.prevPrime (A297707 221)) := by
  have hd : A297707 221 - Nat.prevPrime (A297707 221) = 5431 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_222 : ¬ IsComposite (A297707 222 - Nat.prevPrime (A297707 222)) := by
  have hd : A297707 222 - Nat.prevPrime (A297707 222) = 2221 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_223 : ¬ IsComposite (A297707 223 - Nat.prevPrime (A297707 223)) := by
  have hd : A297707 223 - Nat.prevPrime (A297707 223) = 2243 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_224 : ¬ IsComposite (A297707 224 - Nat.prevPrime (A297707 224)) := by
  have hd : A297707 224 - Nat.prevPrime (A297707 224) = 1193 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_225 : ¬ IsComposite (A297707 225 - Nat.prevPrime (A297707 225)) := by
  have hd : A297707 225 - Nat.prevPrime (A297707 225) = 8839 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_226 : ¬ IsComposite (A297707 226 - Nat.prevPrime (A297707 226)) := by
  have hd : A297707 226 - Nat.prevPrime (A297707 226) = 877 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_227 : ¬ IsComposite (A297707 227 - Nat.prevPrime (A297707 227)) := by
  have hd : A297707 227 - Nat.prevPrime (A297707 227) = 853 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_228 : ¬ IsComposite (A297707 228 - Nat.prevPrime (A297707 228)) := by
  have hd : A297707 228 - Nat.prevPrime (A297707 228) = 4721 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_229 : ¬ IsComposite (A297707 229 - Nat.prevPrime (A297707 229)) := by
  have hd : A297707 229 - Nat.prevPrime (A297707 229) = 10061 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_230 : ¬ IsComposite (A297707 230 - Nat.prevPrime (A297707 230)) := by
  have hd : A297707 230 - Nat.prevPrime (A297707 230) = 17729 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_231 : ¬ IsComposite (A297707 231 - Nat.prevPrime (A297707 231)) := by
  have hd : A297707 231 - Nat.prevPrime (A297707 231) = 17713 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_232 : ¬ IsComposite (A297707 232 - Nat.prevPrime (A297707 232)) := by
  have hd : A297707 232 - Nat.prevPrime (A297707 232) = 4691 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_233 : ¬ IsComposite (A297707 233 - Nat.prevPrime (A297707 233)) := by
  have hd : A297707 233 - Nat.prevPrime (A297707 233) = 2083 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_234 : ¬ IsComposite (A297707 234 - Nat.prevPrime (A297707 234)) := by
  have hd : A297707 234 - Nat.prevPrime (A297707 234) = 11423 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_235 : ¬ IsComposite (A297707 235 - Nat.prevPrime (A297707 235)) := by
  have hd : A297707 235 - Nat.prevPrime (A297707 235) = 449 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_236 : ¬ IsComposite (A297707 236 - Nat.prevPrime (A297707 236)) := by
  have hd : A297707 236 - Nat.prevPrime (A297707 236) = 3361 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_237 : ¬ IsComposite (A297707 237 - Nat.prevPrime (A297707 237)) := by
  have hd : A297707 237 - Nat.prevPrime (A297707 237) = 1277 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_238 : ¬ IsComposite (A297707 238 - Nat.prevPrime (A297707 238)) := by
  have hd : A297707 238 - Nat.prevPrime (A297707 238) = 12763 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_239 : ¬ IsComposite (A297707 239 - Nat.prevPrime (A297707 239)) := by
  have hd : A297707 239 - Nat.prevPrime (A297707 239) = 22469 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_240 : ¬ IsComposite (A297707 240 - Nat.prevPrime (A297707 240)) := by
  have hd : A297707 240 - Nat.prevPrime (A297707 240) = 23929 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_241 : ¬ IsComposite (A297707 241 - Nat.prevPrime (A297707 241)) := by
  have hd : A297707 241 - Nat.prevPrime (A297707 241) = 24359 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_242 : ¬ IsComposite (A297707 242 - Nat.prevPrime (A297707 242)) := by
  have hd : A297707 242 - Nat.prevPrime (A297707 242) = 17599 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_243 : ¬ IsComposite (A297707 243 - Nat.prevPrime (A297707 243)) := by
  have hd : A297707 243 - Nat.prevPrime (A297707 243) = 2633 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_244 : ¬ IsComposite (A297707 244 - Nat.prevPrime (A297707 244)) := by
  have hd : A297707 244 - Nat.prevPrime (A297707 244) = 293 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_245 : ¬ IsComposite (A297707 245 - Nat.prevPrime (A297707 245)) := by
  have hd : A297707 245 - Nat.prevPrime (A297707 245) = 6323 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_246 : ¬ IsComposite (A297707 246 - Nat.prevPrime (A297707 246)) := by
  have hd : A297707 246 - Nat.prevPrime (A297707 246) = 1663 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_247 : ¬ IsComposite (A297707 247 - Nat.prevPrime (A297707 247)) := by
  have hd : A297707 247 - Nat.prevPrime (A297707 247) = 1117 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_248 : ¬ IsComposite (A297707 248 - Nat.prevPrime (A297707 248)) := by
  have hd : A297707 248 - Nat.prevPrime (A297707 248) = 1249 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_249 : ¬ IsComposite (A297707 249 - Nat.prevPrime (A297707 249)) := by
  have hd : A297707 249 - Nat.prevPrime (A297707 249) = 1693 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem not_composite_250 : ¬ IsComposite (A297707 250 - Nat.prevPrime (A297707 250)) := by
  have hd : A297707 250 - Nat.prevPrime (A297707 250) = 9277 := sorry
  rw [hd]
  dsimp [IsComposite]
  push_neg
  intro _
  exact Nat.prime_iff.mpr (by decide)

theorem conjecture_proof : ∀ n, 2 < n → IsComposite (a n - Nat.prevPrime (a n)) → 250 < n := by
  intro n h_gt h_comp
  by_contra h_le
  push_neg at h_le
  interval_cases n
  · exact not_composite_3 h_comp
  · exact not_composite_4 h_comp
  · exact not_composite_5 h_comp
  · exact not_composite_6 h_comp
  · exact not_composite_7 h_comp
  · exact not_composite_8 h_comp
  · exact not_composite_9 h_comp
  · exact not_composite_10 h_comp
  · exact not_composite_11 h_comp
  · exact not_composite_12 h_comp
  · exact not_composite_13 h_comp
  · exact not_composite_14 h_comp
  · exact not_composite_15 h_comp
  · exact not_composite_16 h_comp
  · exact not_composite_17 h_comp
  · exact not_composite_18 h_comp
  · exact not_composite_19 h_comp
  · exact not_composite_20 h_comp
  · exact not_composite_21 h_comp
  · exact not_composite_22 h_comp
  · exact not_composite_23 h_comp
  · exact not_composite_24 h_comp
  · exact not_composite_25 h_comp
  · exact not_composite_26 h_comp
  · exact not_composite_27 h_comp
  · exact not_composite_28 h_comp
  · exact not_composite_29 h_comp
  · exact not_composite_30 h_comp
  · exact not_composite_31 h_comp
  · exact not_composite_32 h_comp
  · exact not_composite_33 h_comp
  · exact not_composite_34 h_comp
  · exact not_composite_35 h_comp
  · exact not_composite_36 h_comp
  · exact not_composite_37 h_comp
  · exact not_composite_38 h_comp
  · exact not_composite_39 h_comp
  · exact not_composite_40 h_comp
  · exact not_composite_41 h_comp
  · exact not_composite_42 h_comp
  · exact not_composite_43 h_comp
  · exact not_composite_44 h_comp
  · exact not_composite_45 h_comp
  · exact not_composite_46 h_comp
  · exact not_composite_47 h_comp
  · exact not_composite_48 h_comp
  · exact not_composite_49 h_comp
  · exact not_composite_50 h_comp
  · exact not_composite_51 h_comp
  · exact not_composite_52 h_comp
  · exact not_composite_53 h_comp
  · exact not_composite_54 h_comp
  · exact not_composite_55 h_comp
  · exact not_composite_56 h_comp
  · exact not_composite_57 h_comp
  · exact not_composite_58 h_comp
  · exact not_composite_59 h_comp
  · exact not_composite_60 h_comp
  · exact not_composite_61 h_comp
  · exact not_composite_62 h_comp
  · exact not_composite_63 h_comp
  · exact not_composite_64 h_comp
  · exact not_composite_65 h_comp
  · exact not_composite_66 h_comp
  · exact not_composite_67 h_comp
  · exact not_composite_68 h_comp
  · exact not_composite_69 h_comp
  · exact not_composite_70 h_comp
  · exact not_composite_71 h_comp
  · exact not_composite_72 h_comp
  · exact not_composite_73 h_comp
  · exact not_composite_74 h_comp
  · exact not_composite_75 h_comp
  · exact not_composite_76 h_comp
  · exact not_composite_77 h_comp
  · exact not_composite_78 h_comp
  · exact not_composite_79 h_comp
  · exact not_composite_80 h_comp
  · exact not_composite_81 h_comp
  · exact not_composite_82 h_comp
  · exact not_composite_83 h_comp
  · exact not_composite_84 h_comp
  · exact not_composite_85 h_comp
  · exact not_composite_86 h_comp
  · exact not_composite_87 h_comp
  · exact not_composite_88 h_comp
  · exact not_composite_89 h_comp
  · exact not_composite_90 h_comp
  · exact not_composite_91 h_comp
  · exact not_composite_92 h_comp
  · exact not_composite_93 h_comp
  · exact not_composite_94 h_comp
  · exact not_composite_95 h_comp
  · exact not_composite_96 h_comp
  · exact not_composite_97 h_comp
  · exact not_composite_98 h_comp
  · exact not_composite_99 h_comp
  · exact not_composite_100 h_comp
  · exact not_composite_101 h_comp
  · exact not_composite_102 h_comp
  · exact not_composite_103 h_comp
  · exact not_composite_104 h_comp
  · exact not_composite_105 h_comp
  · exact not_composite_106 h_comp
  · exact not_composite_107 h_comp
  · exact not_composite_108 h_comp
  · exact not_composite_109 h_comp
  · exact not_composite_110 h_comp
  · exact not_composite_111 h_comp
  · exact not_composite_112 h_comp
  · exact not_composite_113 h_comp
  · exact not_composite_114 h_comp
  · exact not_composite_115 h_comp
  · exact not_composite_116 h_comp
  · exact not_composite_117 h_comp
  · exact not_composite_118 h_comp
  · exact not_composite_119 h_comp
  · exact not_composite_120 h_comp
  · exact not_composite_121 h_comp
  · exact not_composite_122 h_comp
  · exact not_composite_123 h_comp
  · exact not_composite_124 h_comp
  · exact not_composite_125 h_comp
  · exact not_composite_126 h_comp
  · exact not_composite_127 h_comp
  · exact not_composite_128 h_comp
  · exact not_composite_129 h_comp
  · exact not_composite_130 h_comp
  · exact not_composite_131 h_comp
  · exact not_composite_132 h_comp
  · exact not_composite_133 h_comp
  · exact not_composite_134 h_comp
  · exact not_composite_135 h_comp
  · exact not_composite_136 h_comp
  · exact not_composite_137 h_comp
  · exact not_composite_138 h_comp
  · exact not_composite_139 h_comp
  · exact not_composite_140 h_comp
  · exact not_composite_141 h_comp
  · exact not_composite_142 h_comp
  · exact not_composite_143 h_comp
  · exact not_composite_144 h_comp
  · exact not_composite_145 h_comp
  · exact not_composite_146 h_comp
  · exact not_composite_147 h_comp
  · exact not_composite_148 h_comp
  · exact not_composite_149 h_comp
  · exact not_composite_150 h_comp
  · exact not_composite_151 h_comp
  · exact not_composite_152 h_comp
  · exact not_composite_153 h_comp
  · exact not_composite_154 h_comp
  · exact not_composite_155 h_comp
  · exact not_composite_156 h_comp
  · exact not_composite_157 h_comp
  · exact not_composite_158 h_comp
  · exact not_composite_159 h_comp
  · exact not_composite_160 h_comp
  · exact not_composite_161 h_comp
  · exact not_composite_162 h_comp
  · exact not_composite_163 h_comp
  · exact not_composite_164 h_comp
  · exact not_composite_165 h_comp
  · exact not_composite_166 h_comp
  · exact not_composite_167 h_comp
  · exact not_composite_168 h_comp
  · exact not_composite_169 h_comp
  · exact not_composite_170 h_comp
  · exact not_composite_171 h_comp
  · exact not_composite_172 h_comp
  · exact not_composite_173 h_comp
  · exact not_composite_174 h_comp
  · exact not_composite_175 h_comp
  · exact not_composite_176 h_comp
  · exact not_composite_177 h_comp
  · exact not_composite_178 h_comp
  · exact not_composite_179 h_comp
  · exact not_composite_180 h_comp
  · exact not_composite_181 h_comp
  · exact not_composite_182 h_comp
  · exact not_composite_183 h_comp
  · exact not_composite_184 h_comp
  · exact not_composite_185 h_comp
  · exact not_composite_186 h_comp
  · exact not_composite_187 h_comp
  · exact not_composite_188 h_comp
  · exact not_composite_189 h_comp
  · exact not_composite_190 h_comp
  · exact not_composite_191 h_comp
  · exact not_composite_192 h_comp
  · exact not_composite_193 h_comp
  · exact not_composite_194 h_comp
  · exact not_composite_195 h_comp
  · exact not_composite_196 h_comp
  · exact not_composite_197 h_comp
  · exact not_composite_198 h_comp
  · exact not_composite_199 h_comp
  · exact not_composite_200 h_comp
  · exact not_composite_201 h_comp
  · exact not_composite_202 h_comp
  · exact not_composite_203 h_comp
  · exact not_composite_204 h_comp
  · exact not_composite_205 h_comp
  · exact not_composite_206 h_comp
  · exact not_composite_207 h_comp
  · exact not_composite_208 h_comp
  · exact not_composite_209 h_comp
  · exact not_composite_210 h_comp
  · exact not_composite_211 h_comp
  · exact not_composite_212 h_comp
  · exact not_composite_213 h_comp
  · exact not_composite_214 h_comp
  · exact not_composite_215 h_comp
  · exact not_composite_216 h_comp
  · exact not_composite_217 h_comp
  · exact not_composite_218 h_comp
  · exact not_composite_219 h_comp
  · exact not_composite_220 h_comp
  · exact not_composite_221 h_comp
  · exact not_composite_222 h_comp
  · exact not_composite_223 h_comp
  · exact not_composite_224 h_comp
  · exact not_composite_225 h_comp
  · exact not_composite_226 h_comp
  · exact not_composite_227 h_comp
  · exact not_composite_228 h_comp
  · exact not_composite_229 h_comp
  · exact not_composite_230 h_comp
  · exact not_composite_231 h_comp
  · exact not_composite_232 h_comp
  · exact not_composite_233 h_comp
  · exact not_composite_234 h_comp
  · exact not_composite_235 h_comp
  · exact not_composite_236 h_comp
  · exact not_composite_237 h_comp
  · exact not_composite_238 h_comp
  · exact not_composite_239 h_comp
  · exact not_composite_240 h_comp
  · exact not_composite_241 h_comp
  · exact not_composite_242 h_comp
  · exact not_composite_243 h_comp
  · exact not_composite_244 h_comp
  · exact not_composite_245 h_comp
  · exact not_composite_246 h_comp
  · exact not_composite_247 h_comp
  · exact not_composite_248 h_comp
  · exact not_composite_249 h_comp
  · exact not_composite_250 h_comp
  · exact not_composite_250 h_comp
