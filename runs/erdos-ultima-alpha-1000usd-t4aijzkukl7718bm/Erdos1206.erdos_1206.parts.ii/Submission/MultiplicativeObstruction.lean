import FormalConjecturesUtil

/-! A checked finite obstruction to Boolean completely multiplicative colorings.
This does not disprove the positive-density cube-Sidon conjecture. -/

namespace Erdos1206

private structure MultCore (c : ℕ → Bool) : Prop where
  he_0 : ¬ (((Bool.xor (c 3) (c 167))) = (c 11) ∧ ((Bool.xor (c 3) (c 167))) = ((Bool.xor (c 17) (c 31))) ∧ ((Bool.xor (c 3) (c 167))) = ((Bool.xor (c 3) (c 19))))
  he_1 : ¬ (((Bool.xor (c 5) (c 11))) = (false) ∧ ((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 2) ((Bool.xor (c 3) (c 73))))) ∧ ((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 2) (c 167))))
  he_2 : ¬ (((Bool.xor (c 3) (c 149))) = ((Bool.xor (c 3) (c 101))) ∧ ((Bool.xor (c 3) (c 149))) = ((Bool.xor (c 5) (c 97))) ∧ ((Bool.xor (c 3) (c 149))) = ((Bool.xor (c 5) (c 29))))
  he_3 : ¬ ((c 7) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 17))))) ∧ (c 7) = ((Bool.xor (c 2) ((Bool.xor (c 3) (c 79))))) ∧ (c 7) = (c 7))
  he_4 : ¬ ((c 47) = ((Bool.xor (c 3) (c 19))) ∧ (c 47) = (c 109) ∧ (c 47) = (c 167))
  he_5 : ¬ (((Bool.xor (c 2) (c 23))) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 17))))) ∧ ((Bool.xor (c 2) (c 23))) = (c 109) ∧ ((Bool.xor (c 2) (c 23))) = (c 167))
  he_6 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 73))))) = ((Bool.xor (c 2) (c 31))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 73))))) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 29))))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 73))))) = (c 5))
  he_7 : ¬ ((c 17) = (c 151) ∧ (c 17) = ((Bool.xor (c 2) (c 11))) ∧ (c 17) = (c 83))
  he_8 : ¬ (((Bool.xor (c 3) ((Bool.xor (c 7) (c 19))))) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 17))))) ∧ ((Bool.xor (c 3) ((Bool.xor (c 7) (c 19))))) = ((Bool.xor (c 7) (c 61))) ∧ ((Bool.xor (c 3) ((Bool.xor (c 7) (c 19))))) = (c 131))
  he_9 : ¬ (((Bool.xor (c 2) (c 167))) = ((Bool.xor (c 17) (c 19))) ∧ ((Bool.xor (c 2) (c 167))) = ((Bool.xor (c 2) (c 23))) ∧ ((Bool.xor (c 2) (c 167))) = (c 3))
  he_10 : ¬ (((Bool.xor (c 2) (c 47))) = ((Bool.xor (c 3) (c 79))) ∧ ((Bool.xor (c 2) (c 47))) = (c 5) ∧ ((Bool.xor (c 2) (c 47))) = ((Bool.xor (c 2) (c 17))))
  he_11 : ¬ (((Bool.xor (c 3) (c 131))) = ((Bool.xor (c 2) (c 83))) ∧ ((Bool.xor (c 3) (c 131))) = (c 337) ∧ ((Bool.xor (c 3) (c 131))) = (c 3))
  he_12 : ¬ (((Bool.xor (c 5) (c 73))) = ((Bool.xor (c 2) ((Bool.xor (c 7) (c 17))))) ∧ ((Bool.xor (c 5) (c 73))) = (c 11) ∧ ((Bool.xor (c 5) (c 73))) = ((Bool.xor (c 3) (c 7))))
  he_13 : ¬ ((false) = ((Bool.xor (c 2) (c 151))) ∧ (false) = ((Bool.xor (c 3) (c 131))) ∧ (false) = ((Bool.xor (c 5) (c 19))))
  he_14 : ¬ (((Bool.xor (c 2) (c 47))) = (c 41) ∧ ((Bool.xor (c 2) (c 47))) = ((Bool.xor (c 2) ((Bool.xor (c 11) (c 17))))) ∧ ((Bool.xor (c 2) (c 47))) = (c 97))
  he_15 : ¬ (((Bool.xor (c 3) (c 5))) = (c 17) ∧ ((Bool.xor (c 3) (c 5))) = (c 37) ∧ ((Bool.xor (c 3) (c 5))) = (c 251))
  he_16 : ¬ (((Bool.xor (c 3) ((Bool.xor (c 5) (c 19))))) = (c 11) ∧ ((Bool.xor (c 3) ((Bool.xor (c 5) (c 19))))) = ((Bool.xor (c 2) (c 19))) ∧ ((Bool.xor (c 3) ((Bool.xor (c 5) (c 19))))) = ((Bool.xor (c 2) (c 79))))
  he_17 : ¬ (((Bool.xor (c 2) (c 149))) = (c 251) ∧ ((Bool.xor (c 2) (c 149))) = ((Bool.xor (c 3) (c 29))) ∧ ((Bool.xor (c 2) (c 149))) = ((Bool.xor (c 3) (c 17))))
  he_18 : ¬ ((c 7) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 7))))) ∧ (c 7) = ((Bool.xor (c 2) (c 167))) ∧ (c 7) = (c 2))
  he_19 : ¬ (((Bool.xor (c 2) (c 43))) = ((Bool.xor (c 2) (c 43))) ∧ ((Bool.xor (c 2) (c 43))) = ((Bool.xor (c 17) (c 19))) ∧ ((Bool.xor (c 2) (c 43))) = (c 197))
  he_20 : ¬ (((Bool.xor (c 3) ((Bool.xor (c 5) (c 23))))) = ((Bool.xor (c 2) (c 29))) ∧ ((Bool.xor (c 3) ((Bool.xor (c 5) (c 23))))) = (c 337) ∧ ((Bool.xor (c 3) ((Bool.xor (c 5) (c 23))))) = (false))
  he_21 : ¬ (((Bool.xor (c 3) ((Bool.xor (c 5) (c 19))))) = (c 3) ∧ ((Bool.xor (c 3) ((Bool.xor (c 5) (c 19))))) = ((Bool.xor (c 2) (c 167))) ∧ ((Bool.xor (c 3) ((Bool.xor (c 5) (c 19))))) = ((Bool.xor (c 2) (c 31))))
  he_22 : ¬ (((Bool.xor (c 5) (c 59))) = ((Bool.xor (c 2) (c 97))) ∧ ((Bool.xor (c 5) (c 59))) = ((Bool.xor (c 11) (c 29))) ∧ ((Bool.xor (c 5) (c 59))) = (c 5))
  he_23 : ¬ ((c 7) = ((Bool.xor (c 2) (c 31))) ∧ (c 7) = ((Bool.xor (c 5) (c 7))) ∧ (c 7) = (c 5))
  he_24 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 5) (c 7))))) = ((Bool.xor (c 3) (c 7))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 5) (c 7))))) = ((Bool.xor (c 2) (c 17))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 5) (c 7))))) = (c 37))
  he_25 : ¬ (((Bool.xor (c 3) (c 101))) = ((Bool.xor (c 2) (c 3))) ∧ ((Bool.xor (c 3) (c 101))) = ((Bool.xor (c 2) ((Bool.xor (c 5) (c 29))))) ∧ ((Bool.xor (c 3) (c 101))) = (c 151))
  he_26 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 47))))) = (false) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 47))))) = ((Bool.xor (c 3) ((Bool.xor (c 7) (c 13))))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 47))))) = ((Bool.xor (c 2) ((Bool.xor (c 5) (c 13))))))
  he_27 : ¬ (((Bool.xor (c 3) (c 23))) = (c 11) ∧ ((Bool.xor (c 3) (c 23))) = ((Bool.xor (c 2) ((Bool.xor (c 5) (c 7))))) ∧ ((Bool.xor (c 3) (c 23))) = ((Bool.xor (c 5) (c 7))))
  he_28 : ¬ ((c 11) = ((Bool.xor (c 3) (c 23))) ∧ (c 11) = ((Bool.xor (c 3) (c 5))) ∧ (c 11) = ((Bool.xor (c 2) (c 97))))
  he_29 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 5))))) = (c 73) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 5))))) = (c 61) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 5))))) = ((Bool.xor (c 3) (c 59))))
  he_30 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 11))))) = (c 19) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 11))))) = ((Bool.xor (c 2) (c 131))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 11))))) = (c 3))
  he_31 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 41))))) = ((Bool.xor (c 2) (c 73))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 41))))) = ((Bool.xor (c 11) (c 19))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 41))))) = (c 23))
  he_32 : ¬ (((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 3) (c 61))) ∧ ((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 17))))) ∧ ((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 2) (c 29))))
  he_33 : ¬ ((c 59) = (c 151) ∧ (c 59) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 17))))) ∧ (c 59) = (c 2))
  he_34 : ¬ (((Bool.xor (c 5) (c 47))) = ((Bool.xor (c 3) (c 5))) ∧ ((Bool.xor (c 5) (c 47))) = ((Bool.xor (c 3) (c 83))) ∧ ((Bool.xor (c 5) (c 47))) = (false))
  he_35 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 41))))) = (c 17) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 41))))) = (c 23) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 41))))) = ((Bool.xor (c 5) (c 37))))
  he_36 : ¬ (((Bool.xor (c 2) (c 109))) = (false) ∧ ((Bool.xor (c 2) (c 109))) = (false) ∧ ((Bool.xor (c 2) (c 109))) = ((Bool.xor (c 3) (c 13))))
  he_37 : ¬ (((Bool.xor (c 3) (c 17))) = (c 19) ∧ ((Bool.xor (c 3) (c 17))) = ((Bool.xor (c 5) (c 47))) ∧ ((Bool.xor (c 3) (c 17))) = (c 5))
  he_38 : ¬ (((Bool.xor (c 2) (c 113))) = ((Bool.xor (c 2) (c 3))) ∧ ((Bool.xor (c 2) (c 113))) = (false) ∧ ((Bool.xor (c 2) (c 113))) = ((Bool.xor (c 5) (c 11))))
  he_39 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 7))))))) = (c 29) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 7))))))) = (c 197) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 7))))))) = (c 3))
  he_40 : ¬ (((Bool.xor (c 3) (c 59))) = (c 167) ∧ ((Bool.xor (c 3) (c 59))) = ((Bool.xor (c 2) (c 3))) ∧ ((Bool.xor (c 3) (c 59))) = (c 2))
  he_41 : ¬ ((c 23) = ((Bool.xor (c 2) (c 7))) ∧ (c 23) = ((Bool.xor (c 3) (c 61))) ∧ (c 23) = ((Bool.xor (c 5) (c 7))))
  he_42 : ¬ (((Bool.xor (c 2) (c 83))) = (c 149) ∧ ((Bool.xor (c 2) (c 83))) = (c 3) ∧ ((Bool.xor (c 2) (c 83))) = ((Bool.xor (c 3) (c 31))))
  he_43 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 29))))) = ((Bool.xor (c 7) (c 19))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 29))))) = (false) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 29))))) = (c 5))
  he_44 : ¬ (((Bool.xor (c 2) (c 83))) = (c 113) ∧ ((Bool.xor (c 2) (c 83))) = (c 5) ∧ ((Bool.xor (c 2) (c 83))) = ((Bool.xor (c 3) (c 19))))
  he_45 : ¬ (((Bool.xor (c 2) (c 89))) = ((Bool.xor (c 3) (c 17))) ∧ ((Bool.xor (c 2) (c 89))) = (c 2) ∧ ((Bool.xor (c 2) (c 89))) = ((Bool.xor (c 5) (c 23))))
  he_46 : ¬ ((c 41) = (false) ∧ (c 41) = (c 167) ∧ (c 41) = (false))
  he_47 : ¬ (((Bool.xor (c 2) (c 83))) = (c 2) ∧ ((Bool.xor (c 2) (c 83))) = ((Bool.xor (c 3) (c 5))) ∧ ((Bool.xor (c 2) (c 83))) = ((Bool.xor (c 3) (c 43))))
  he_48 : ¬ (((Bool.xor (c 2) (c 19))) = (false) ∧ ((Bool.xor (c 2) (c 19))) = ((Bool.xor (c 3) ((Bool.xor (c 5) (c 11))))) ∧ ((Bool.xor (c 2) (c 19))) = (c 3))
  he_49 : ¬ ((c 17) = (c 2) ∧ (c 17) = ((Bool.xor (c 2) (c 61))) ∧ (c 17) = (false))
  he_50 : ¬ (((Bool.xor (c 2) (c 3))) = (false) ∧ ((Bool.xor (c 2) (c 3))) = (false) ∧ ((Bool.xor (c 2) (c 3))) = (c 73))
  he_51 : ¬ ((c 113) = ((Bool.xor (c 5) (c 11))) ∧ (c 113) = ((Bool.xor (c 2) (c 47))) ∧ (c 113) = (c 23))
  he_52 : ¬ ((c 109) = ((Bool.xor (c 2) (c 31))) ∧ (c 109) = ((Bool.xor (c 3) (c 31))) ∧ (c 109) = ((Bool.xor (c 2) (c 5))))
  he_53 : ¬ (((Bool.xor (c 2) ((Bool.xor (c 3) (c 17))))) = (c 23) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 17))))) = ((Bool.xor (c 5) (c 19))) ∧ ((Bool.xor (c 2) ((Bool.xor (c 3) (c 17))))) = ((Bool.xor (c 3) (c 5))))
  he_54 : ¬ (((Bool.xor (c 2) (c 5))) = ((Bool.xor (c 2) ((Bool.xor (c 3) (c 11))))) ∧ ((Bool.xor (c 2) (c 5))) = (c 97) ∧ ((Bool.xor (c 2) (c 5))) = (c 47))
  he_55 : ¬ ((c 23) = ((Bool.xor (c 3) (c 5))) ∧ (c 23) = (c 11) ∧ (c 23) = (c 29))
  he_56 : ¬ ((c 2) = ((Bool.xor (c 5) (c 7))) ∧ (c 2) = (c 23) ∧ (c 2) = (c 59))
  he_57 : ¬ (((Bool.xor (c 2) (c 47))) = (c 23) ∧ ((Bool.xor (c 2) (c 47))) = ((Bool.xor (c 3) (c 7))) ∧ ((Bool.xor (c 2) (c 47))) = (c 7))
  he_58 : ¬ (((Bool.xor (c 2) (c 43))) = (c 41) ∧ ((Bool.xor (c 2) (c 43))) = (c 89) ∧ ((Bool.xor (c 2) (c 43))) = (c 2))
  he_59 : ¬ ((c 3) = (false) ∧ (c 3) = ((Bool.xor (c 2) (c 41))) ∧ (c 3) = ((Bool.xor (c 3) (c 17))))
  he_60 : ¬ ((c 73) = ((Bool.xor (c 2) (c 19))) ∧ (c 73) = (c 19) ∧ (c 73) = (c 17))
  he_61 : ¬ ((c 19) = (c 5) ∧ (c 19) = ((Bool.xor (c 3) (c 23))) ∧ (c 19) = (c 3))
  he_62 : ¬ ((c 59) = ((Bool.xor (c 2) (c 11))) ∧ (c 59) = ((Bool.xor (c 3) (c 5))) ∧ (c 59) = (c 3))
  he_63 : ¬ (((Bool.xor (c 2) (c 29))) = (false) ∧ ((Bool.xor (c 2) (c 29))) = ((Bool.xor (c 3) (c 19))) ∧ ((Bool.xor (c 2) (c 29))) = ((Bool.xor (c 2) (c 11))))
  he_64 : ¬ (((Bool.xor (c 5) (c 11))) = (c 17) ∧ ((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 2) (c 3))) ∧ ((Bool.xor (c 5) (c 11))) = ((Bool.xor (c 2) (c 3))))
  he_65 : ¬ (((Bool.xor (c 3) (c 11))) = (false) ∧ ((Bool.xor (c 3) (c 11))) = ((Bool.xor (c 2) (c 17))) ∧ ((Bool.xor (c 3) (c 11))) = (false))
  he_66 : ¬ (((Bool.xor (c 3) (c 5))) = (false) ∧ ((Bool.xor (c 3) (c 5))) = (false) ∧ ((Bool.xor (c 3) (c 5))) = (c 2))
  he_67 : ¬ (((Bool.xor (c 2) (c 5))) = (false) ∧ ((Bool.xor (c 2) (c 5))) = (c 3) ∧ ((Bool.xor (c 2) (c 5))) = (false))

private lemma cl_1 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_2 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 11 = true) → (c 17 = true) → (¬ c 19 = true) → (c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a3 a5
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_3 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 11 = true) → (¬ c 17 = true) → (c 19 = true) → (c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_4 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 11 = true) → (c 17 = true) → (c 19 = true) → (¬ c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a4
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_5 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_6 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 11 = true) → (c 17 = true) → (c 19 = true) → (c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_7 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a5
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_8 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 11 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_0
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_9 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 73 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_10 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 73 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_11 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 73 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3 a5
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_12 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (c 73 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_13 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 73 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_14 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 73 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_15 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 73 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_16 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 73 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a4
  apply h.he_1
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_17 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 29 = true) → (¬ c 97 = true) → (¬ c 101 = true) → (¬ c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_18 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (c 29 = true) → (c 97 = true) → (c 101 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_19 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (¬ c 29 = true) → (¬ c 97 = true) → (c 101 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_20 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 29 = true) → (c 97 = true) → (¬ c 101 = true) → (¬ c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a4 a5
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_21 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (¬ c 29 = true) → (¬ c 97 = true) → (c 101 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_22 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (c 29 = true) → (c 97 = true) → (¬ c 101 = true) → (¬ c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4 a5
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_23 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 29 = true) → (¬ c 97 = true) → (¬ c 101 = true) → (¬ c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a4 a5
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_24 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 29 = true) → (c 97 = true) → (c 101 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  apply h.he_2
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_25 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_26 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_27 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a3 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_28 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_29 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_30 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_31 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_32 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_33 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_34 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_35 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_36 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_37 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_38 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_39 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_40 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (c 17 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  apply h.he_3
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_41 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 19 = true) → (¬ c 47 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_4
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_42 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 19 = true) → (c 47 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0
  apply h.he_4
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_43 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 19 = true) → (c 47 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1
  apply h.he_4
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_44 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 19 = true) → (¬ c 47 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_4
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_45 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_46 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_47 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a3
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_48 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (¬ c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a4 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_49 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_50 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (¬ c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a4 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_51 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a3 a4 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_52 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_53 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a3 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_54 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (¬ c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_55 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_56 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_57 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_58 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_59 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (c 23 = true) → (¬ c 109 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a3 a5 a6
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_60 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (¬ c 23 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a4
  apply h.he_5
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_61 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 29 = true) → (¬ c 31 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_62 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 29 = true) → (c 31 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a3
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_63 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 29 = true) → (¬ c 31 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_64 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 29 = true) → (c 31 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_65 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 29 = true) → (c 31 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_66 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 29 = true) → (¬ c 31 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a4 a5
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_67 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 29 = true) → (c 31 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a5
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_68 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 29 = true) → (¬ c 31 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a4
  apply h.he_6
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_69 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 83 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_7
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_70 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 11 = true) → (c 17 = true) → (c 83 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0
  apply h.he_7
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_71 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 11 = true) → (c 17 = true) → (c 83 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1
  apply h.he_7
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_72 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 83 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_7
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_73 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_74 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (c 19 = true) → (c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_75 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (c 19 = true) → (c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a3 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_76 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_77 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (c 19 = true) → (c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_78 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a4 a5 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_79 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a3 a4 a5
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_80 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (c 17 = true) → (c 19 = true) → (c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_81 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_82 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (c 19 = true) → (¬ c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a5 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_83 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a3 a5
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_84 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 17 = true) → (¬ c 19 = true) → (c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a4 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_85 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a3 a5 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_86 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (¬ c 19 = true) → (c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a4
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_87 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (c 61 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a3 a4 a6
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_88 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 7 = true) → (c 17 = true) → (c 19 = true) → (¬ c 61 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a5
  apply h.he_8
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_89 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 23 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_90 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 17 = true) → (c 19 = true) → (¬ c 23 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_91 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 17 = true) → (c 19 = true) → (c 23 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_92 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 17 = true) → (¬ c 19 = true) → (c 23 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_93 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (c 23 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_94 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 17 = true) → (c 19 = true) → (c 23 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_95 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 23 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4 a5
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_96 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 23 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_9
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_97 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 47 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_98 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (c 47 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_99 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 47 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3 a4
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_100 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 47 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_101 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 47 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a5
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_102 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 47 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_103 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 47 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_104 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 47 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_10
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_105 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 83 = true) → (¬ c 131 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_11
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_106 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 83 = true) → (¬ c 131 = true) → (c 337 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_11
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_107 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 83 = true) → (¬ c 131 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_11
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_108 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 83 = true) → (¬ c 131 = true) → (c 337 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_11
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_109 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_110 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 11 = true) → (¬ c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a5
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_111 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a3 a4 a5
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_112 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a5 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_113 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 11 = true) → (c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_114 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 11 = true) → (c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a4 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_115 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 11 = true) → (c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a3 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_116 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 11 = true) → (c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a4
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_117 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 11 = true) → (c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a3 a4 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_118 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 11 = true) → (c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_119 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 11 = true) → (c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_120 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (c 11 = true) → (c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_121 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 11 = true) → (¬ c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a3 a5
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_122 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a4 a5 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_123 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a3 a5 a6
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_124 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a4 a5
  apply h.he_12
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_125 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (¬ c 131 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_126 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 19 = true) → (¬ c 131 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_127 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (c 131 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3 a5
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_128 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 19 = true) → (c 131 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_129 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (¬ c 131 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_130 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 19 = true) → (¬ c 131 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_131 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (c 131 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_132 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 19 = true) → (c 131 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  apply h.he_13
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_133 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 41 = true) → (¬ c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_134 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 11 = true) → (c 17 = true) → (c 41 = true) → (c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_135 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 11 = true) → (¬ c 17 = true) → (c 41 = true) → (c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_136 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 11 = true) → (c 17 = true) → (¬ c 41 = true) → (¬ c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4 a5
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_137 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (c 41 = true) → (¬ c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_138 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 11 = true) → (c 17 = true) → (¬ c 41 = true) → (c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a5
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_139 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 41 = true) → (c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a5
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_140 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 11 = true) → (c 17 = true) → (c 41 = true) → (¬ c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a4
  apply h.he_14
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_141 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 37 = true) → (¬ c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_15
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_142 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (c 37 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0
  apply h.he_15
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_143 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 37 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1
  apply h.he_15
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_144 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 37 = true) → (¬ c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_15
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_145 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_146 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 19 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_147 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4 a5
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_148 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (c 19 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_149 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 19 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_150 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 19 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4 a5
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_151 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 19 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_152 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 19 = true) → (¬ c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4 a5
  apply h.he_16
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_153 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (¬ c 149 = true) → (¬ c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_154 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 17 = true) → (c 29 = true) → (c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_155 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_156 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 17 = true) → (c 29 = true) → (¬ c 149 = true) → (¬ c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a4 a5
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_157 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (c 149 = true) → (¬ c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a5
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_158 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 17 = true) → (c 29 = true) → (¬ c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_159 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (¬ c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_160 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 17 = true) → (c 29 = true) → (c 149 = true) → (¬ c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a5
  apply h.he_17
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_161 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_18
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_162 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_18
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_163 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_18
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_164 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a4
  apply h.he_18
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_165 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 43 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_166 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 17 = true) → (c 19 = true) → (c 43 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_167 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 17 = true) → (¬ c 19 = true) → (c 43 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_168 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 17 = true) → (c 19 = true) → (¬ c 43 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_169 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (c 43 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_170 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 43 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_171 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 43 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_172 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 17 = true) → (c 19 = true) → (c 43 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a4
  apply h.he_19
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_173 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 23 = true) → (¬ c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_174 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 23 = true) → (¬ c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_175 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 23 = true) → (¬ c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_176 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 23 = true) → (¬ c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_177 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 23 = true) → (c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_178 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 23 = true) → (c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_179 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 23 = true) → (c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_180 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 23 = true) → (c 29 = true) → (¬ c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a5
  apply h.he_20
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_181 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (¬ c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_182 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 19 = true) → (¬ c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_183 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_184 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 19 = true) → (c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_185 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_186 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 19 = true) → (c 31 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_187 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (¬ c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a4 a5
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_188 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 19 = true) → (¬ c 31 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a4 a5
  apply h.he_21
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_189 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 29 = true) → (¬ c 59 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_190 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (c 11 = true) → (c 29 = true) → (¬ c 59 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_191 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 5 = true) → (¬ c 11 = true) → (c 29 = true) → (¬ c 59 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_192 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 5 = true) → (c 11 = true) → (¬ c 29 = true) → (¬ c 59 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_193 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 29 = true) → (¬ c 59 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_194 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (c 11 = true) → (c 29 = true) → (¬ c 59 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_195 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 5 = true) → (¬ c 11 = true) → (c 29 = true) → (¬ c 59 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4 a5
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_196 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 5 = true) → (c 11 = true) → (¬ c 29 = true) → (¬ c 59 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_22
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_197 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 31 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_23
  simp only [a0, a1, a2, a3]; decide

private lemma cl_198 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 31 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_23
  simp only [a0, a1, a2, a3]; decide

private lemma cl_199 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (¬ c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_200 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 17 = true) → (c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_201 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_202 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (¬ c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a4 a5
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_203 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 17 = true) → (¬ c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a5
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_204 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 17 = true) → (c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_205 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 17 = true) → (c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_206 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 17 = true) → (¬ c 37 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a5
  apply h.he_24
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_207 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 29 = true) → (¬ c 101 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_208 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 29 = true) → (¬ c 101 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_209 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 29 = true) → (¬ c 101 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_210 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 29 = true) → (¬ c 101 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_211 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 29 = true) → (c 101 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_212 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 29 = true) → (c 101 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_213 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 29 = true) → (c 101 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a5
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_214 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 29 = true) → (c 101 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a5
  apply h.he_25
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_215 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 13 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_216 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (c 13 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a5
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_217 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 13 = true) → (c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_218 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 13 = true) → (c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_219 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 13 = true) → (c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_220 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 13 = true) → (c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_221 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 13 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a5
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_222 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 13 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a4 a5
  apply h.he_26
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_223 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 11 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_224 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 11 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_225 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 11 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a3
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_226 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 11 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_227 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 11 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3 a4
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_228 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 11 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a5
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_229 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 11 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a5
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_230 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 11 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a4
  apply h.he_27
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_231 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 23 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_232 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 23 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_233 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 23 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_234 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 23 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a5
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_235 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 23 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_236 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 23 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a5
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_237 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 23 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4 a5
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_238 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 23 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3
  apply h.he_28
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_239 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 59 = true) → (¬ c 61 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_240 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 59 = true) → (c 61 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_241 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 59 = true) → (c 61 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_242 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 59 = true) → (¬ c 61 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a4 a5
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_243 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 59 = true) → (c 61 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_244 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 59 = true) → (¬ c 61 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a4 a5
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_245 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 59 = true) → (¬ c 61 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4 a5
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_246 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 59 = true) → (c 61 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3
  apply h.he_29
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_247 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_30
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_248 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 11 = true) → (c 19 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_30
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_249 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 11 = true) → (¬ c 19 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_30
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_250 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 11 = true) → (c 19 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a4
  apply h.he_30
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_251 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 23 = true) → (¬ c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_252 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (c 19 = true) → (c 23 = true) → (c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_253 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 11 = true) → (¬ c 19 = true) → (c 23 = true) → (c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a3
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_254 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 11 = true) → (c 19 = true) → (¬ c 23 = true) → (¬ c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a4 a5 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_255 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 23 = true) → (c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a3 a4 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_256 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 11 = true) → (c 19 = true) → (c 23 = true) → (¬ c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a5
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_257 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 11 = true) → (¬ c 19 = true) → (c 23 = true) → (¬ c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a3 a5
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_258 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 11 = true) → (c 19 = true) → (¬ c 23 = true) → (c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a4 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_259 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 23 = true) → (c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_260 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (c 19 = true) → (c 23 = true) → (¬ c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a5 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_261 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 11 = true) → (¬ c 19 = true) → (c 23 = true) → (¬ c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a3 a5 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_262 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 11 = true) → (c 19 = true) → (¬ c 23 = true) → (c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_263 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 23 = true) → (¬ c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a3 a4 a5
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_264 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 11 = true) → (c 19 = true) → (c 23 = true) → (c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_265 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 11 = true) → (¬ c 19 = true) → (c 23 = true) → (c 41 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a3 a6
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_266 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 11 = true) → (c 19 = true) → (¬ c 23 = true) → (¬ c 41 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a4 a5
  apply h.he_31
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_267 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_268 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 17 = true) → (c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_269 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a3 a4
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_270 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 17 = true) → (¬ c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a5 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_271 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 17 = true) → (¬ c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a3 a5
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_272 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 17 = true) → (c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a4 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_273 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 17 = true) → (c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a3 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_274 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a4 a5
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_275 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a3 a4 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_276 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 17 = true) → (¬ c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a5
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_277 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a3 a4 a5
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_278 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 17 = true) → (c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_279 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 17 = true) → (c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_280 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 17 = true) → (¬ c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a4 a5 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_281 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 17 = true) → (¬ c 29 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a3 a5 a6
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_282 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 17 = true) → (c 29 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a4
  apply h.he_32
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_283 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 59 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_284 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (¬ c 59 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_285 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (¬ c 59 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4 a5
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_286 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 59 = true) → (¬ c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4 a5
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_287 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 59 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_288 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (c 59 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_289 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (c 59 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_290 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 59 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  apply h.he_33
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_291 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 47 = true) → (¬ c 83 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_34
  simp only [a0, a1, a2, a3]; decide

private lemma cl_292 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 47 = true) → (c 83 = true) → False := by
  intro a0 a1 a2 a3
  apply h.he_34
  simp only [a0, a1, a2, a3]; decide

private lemma cl_293 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_294 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_295 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a3 a4 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_296 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a1 a5
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_297 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a3 a4 a5
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_298 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a2 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_299 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_300 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a0 a5 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_301 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a3 a4 a5
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_302 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a2 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_303 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_304 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a1 a5 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_305 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2 a3 a4 a5 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_306 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a2
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_307 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (c 37 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a3 a4 a6
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_308 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 37 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  simp only [Bool.not_eq_true] at a5
  apply h.he_35
  simp only [a0, a1, a2, a3, a4, a5, a6]; decide

private lemma cl_309 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 13 = true) → (¬ c 109 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_36
  simp only [a0, a1, a2, a3]; decide

private lemma cl_310 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 13 = true) → (¬ c 109 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_36
  simp only [a0, a1, a2, a3]; decide

private lemma cl_311 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 13 = true) → (c 109 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_36
  simp only [a0, a1, a2, a3]; decide

private lemma cl_312 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 13 = true) → (c 109 = true) → False := by
  intro a0 a1 a2 a3
  apply h.he_36
  simp only [a0, a1, a2, a3]; decide

private lemma cl_313 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_37
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_314 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (c 19 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a4
  apply h.he_37
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_315 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_37
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_316 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a4
  apply h.he_37
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_317 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_38
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_318 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a4
  apply h.he_38
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_319 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_38
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_320 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4
  apply h.he_38
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_321 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 29 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_322 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 29 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4 a5
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_323 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (c 29 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_324 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (c 29 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_325 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (¬ c 29 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a4 a5
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_326 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (¬ c 29 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a4 a5
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_327 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 29 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_328 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 29 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3
  apply h.he_39
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_329 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 59 = true) → (¬ c 167 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_40
  simp only [a0, a1, a2, a3]; decide

private lemma cl_330 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 59 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a1
  apply h.he_40
  simp only [a0, a1, a2, a3]; decide

private lemma cl_331 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 23 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_332 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 23 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_333 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 23 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3 a4
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_334 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 23 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a5
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_335 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 23 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_336 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 23 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4 a5
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_337 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 7 = true) → (c 23 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a5
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_338 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 7 = true) → (¬ c 23 = true) → (c 61 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a4
  apply h.he_41
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_339 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 31 = true) → (¬ c 83 = true) → (¬ c 149 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_42
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_340 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 31 = true) → (c 83 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_42
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_341 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 31 = true) → (c 83 = true) → (¬ c 149 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_42
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_342 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 31 = true) → (¬ c 83 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_42
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_343 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 19 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_344 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 19 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a5
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_345 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 19 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3 a4
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_346 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 19 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_347 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 19 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a4
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_348 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 19 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_349 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 19 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a4 a5
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_350 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 7 = true) → (c 19 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a5
  apply h.he_43
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_351 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (¬ c 83 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_352 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 19 = true) → (c 83 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_353 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 19 = true) → (¬ c 83 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4 a5
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_354 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 19 = true) → (c 83 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_355 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (c 83 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a5
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_356 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 19 = true) → (¬ c 83 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_357 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 19 = true) → (c 83 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a5
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_358 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 19 = true) → (¬ c 83 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4
  apply h.he_44
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_359 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_360 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a3 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_361 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (¬ c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_362 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_363 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_364 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (¬ c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_365 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a3 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_366 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 23 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_45
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_367 {c : ℕ → Bool} (h : MultCore c) : (¬ c 41 = true) → (¬ c 167 = true) → False := by
  intro a0 a1
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_46
  simp only [a0, a1]; decide

private lemma cl_368 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 43 = true) → (¬ c 83 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_47
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_369 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 43 = true) → (¬ c 83 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a4
  apply h.he_47
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_370 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 43 = true) → (¬ c 83 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_47
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_371 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 43 = true) → (¬ c 83 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_47
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_372 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 19 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_48
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_373 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 19 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a4
  apply h.he_48
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_374 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 19 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_48
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_375 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 19 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1
  apply h.he_48
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_376 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 17 = true) → (¬ c 61 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_49
  simp only [a0, a1, a2]; decide

private lemma cl_377 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_50
  simp only [a0, a1, a2]; decide

private lemma cl_378 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a2
  apply h.he_50
  simp only [a0, a1, a2]; decide

private lemma cl_379 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 23 = true) → (¬ c 47 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_380 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (c 11 = true) → (c 23 = true) → (c 47 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_381 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 5 = true) → (¬ c 11 = true) → (c 23 = true) → (c 47 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_382 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 5 = true) → (c 11 = true) → (¬ c 23 = true) → (¬ c 47 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3 a4 a5
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_383 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 23 = true) → (c 47 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3 a5
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_384 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (c 11 = true) → (c 23 = true) → (¬ c 47 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_385 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 5 = true) → (¬ c 11 = true) → (c 23 = true) → (¬ c 47 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2 a4
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_386 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 5 = true) → (c 11 = true) → (¬ c 23 = true) → (c 47 = true) → (¬ c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a5
  apply h.he_51
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_387 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 31 = true) → (¬ c 109 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_52
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_388 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 31 = true) → (c 109 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_52
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_389 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 31 = true) → (c 109 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_52
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_390 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 31 = true) → (¬ c 109 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a4
  apply h.he_52
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_391 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_392 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 17 = true) → (¬ c 19 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a4
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_393 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 17 = true) → (c 19 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a3
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_394 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (c 17 = true) → (c 19 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a5
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_395 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (¬ c 19 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a4 a5
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_396 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a3 a4
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_397 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 17 = true) → (c 19 = true) → (c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_398 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 17 = true) → (c 19 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a5
  apply h.he_53
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_399 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4 a5
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_400 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_401 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a2 a4 a5
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_402 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_403 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_404 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a1 a4 a5
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_405 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 47 = true) → (c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a2
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_406 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (¬ c 47 = true) → (¬ c 97 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  simp only [Bool.not_eq_true] at a3 a4 a5
  apply h.he_54
  simp only [a0, a1, a2, a3, a4, a5]; decide

private lemma cl_407 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 23 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_55
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_408 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (c 23 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0
  apply h.he_55
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_409 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 23 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1
  apply h.he_55
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_410 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (¬ c 23 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_55
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_411 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (¬ c 7 = true) → (¬ c 23 = true) → (¬ c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_56
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_412 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 5 = true) → (c 7 = true) → (¬ c 23 = true) → (¬ c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a3 a4
  apply h.he_56
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_413 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (c 7 = true) → (c 23 = true) → (c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1
  apply h.he_56
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_414 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 5 = true) → (¬ c 7 = true) → (c 23 = true) → (c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2
  apply h.he_56
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_415 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 7 = true) → (¬ c 23 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_57
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_416 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 7 = true) → (c 23 = true) → (c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1
  apply h.he_57
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_417 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 7 = true) → (¬ c 23 = true) → (c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2 a3
  apply h.he_57
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_418 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 7 = true) → (c 23 = true) → (¬ c 47 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a4
  apply h.he_57
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_419 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 41 = true) → (¬ c 43 = true) → (¬ c 89 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_58
  simp only [a0, a1, a2, a3]; decide

private lemma cl_420 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 41 = true) → (¬ c 43 = true) → (c 89 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a2
  apply h.he_58
  simp only [a0, a1, a2, a3]; decide

private lemma cl_421 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 17 = true) → (¬ c 41 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_59
  simp only [a0, a1, a2, a3]; decide

private lemma cl_422 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 17 = true) → (c 41 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_59
  simp only [a0, a1, a2, a3]; decide

private lemma cl_423 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 17 = true) → (¬ c 19 = true) → (¬ c 73 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_60
  simp only [a0, a1, a2, a3]; decide

private lemma cl_424 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 17 = true) → (c 19 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0
  apply h.he_60
  simp only [a0, a1, a2, a3]; decide

private lemma cl_425 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 19 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_61
  simp only [a0, a1, a2, a3]; decide

private lemma cl_426 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 19 = true) → (¬ c 23 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a3
  apply h.he_61
  simp only [a0, a1, a2, a3]; decide

private lemma cl_427 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_62
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_428 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_62
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_429 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (¬ c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2 a4
  apply h.he_62
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_430 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (c 59 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3
  apply h.he_62
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_431 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (¬ c 19 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_63
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_432 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 11 = true) → (c 19 = true) → (¬ c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a2 a4
  apply h.he_63
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_433 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 11 = true) → (¬ c 19 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_63
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_434 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 11 = true) → (c 19 = true) → (c 29 = true) → False := by
  intro a0 a1 a2 a3 a4
  apply h.he_63
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_435 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a2 a3 a4
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_436 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a1 a4
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_437 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a2
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_438 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_439 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → (c 11 = true) → (c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_440 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → (¬ c 11 = true) → (c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a1 a3
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_441 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a2 a3 a4
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_442 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 5 = true) → (c 11 = true) → (¬ c 17 = true) → False := by
  intro a0 a1 a2 a3 a4
  simp only [Bool.not_eq_true] at a4
  apply h.he_64
  simp only [a0, a1, a2, a3, a4]; decide

private lemma cl_443 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (¬ c 17 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a1 a2 a3
  apply h.he_65
  simp only [a0, a1, a2, a3]; decide

private lemma cl_444 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 11 = true) → (¬ c 17 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a0 a3
  apply h.he_65
  simp only [a0, a1, a2, a3]; decide

private lemma cl_445 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (¬ c 11 = true) → (c 17 = true) → False := by
  intro a0 a1 a2 a3
  simp only [Bool.not_eq_true] at a1 a2
  apply h.he_65
  simp only [a0, a1, a2, a3]; decide

private lemma cl_446 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (c 11 = true) → (c 17 = true) → False := by
  intro a0 a1 a2 a3
  apply h.he_65
  simp only [a0, a1, a2, a3]; decide

private lemma cl_447 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_66
  simp only [a0, a1, a2]; decide

private lemma cl_448 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (c 3 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a0
  apply h.he_66
  simp only [a0, a1, a2]; decide

private lemma cl_449 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 3 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a0 a1 a2
  apply h.he_67
  simp only [a0, a1, a2]; decide

private lemma cl_450 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 3 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  simp only [Bool.not_eq_true] at a1
  apply h.he_67
  simp only [a0, a1, a2]; decide

private lemma cl_451 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 23 = true) → (c 37 = true) → (c 47 = true) → (c 59 = true) → (c 83 = true) → (c 109 = true) → (c 151 = true) → (c 167 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have u0 : (¬ c 5 = true) := fun hh => cl_292 h a0 hh a3 a5
  have u1 : (¬ c 17 = true) := fun hh => cl_143 h a0 u0 hh a2 a9
  have u2 : (c 2 = true) := Classical.byContradiction (fun hh => cl_49 h hh a0 u0 u1 a1 a6 a8)
  exact cl_289 h u2 a0 u0 u1 a4 a7

private lemma cl_452 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 59 = true) → (c 61 = true) → (c 73 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (¬ c 2 = true) := fun hh => cl_330 h hh a0 a1 a4
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_447 h u0 a0 hh)
  exact cl_240 h u0 a0 u1 a1 a2 a3

private lemma cl_453 {c : ℕ → Bool} (h : MultCore c) : (c 37 = true) → (c 47 = true) → (c 3 = true) → (c 59 = true) → (c 83 = true) → (c 109 = true) → (c 131 = true) → (c 151 = true) → (c 167 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have u0 : (c 19 = true) := Classical.byContradiction (fun hh => cl_43 h a2 hh a1 a5 a8)
  have u1 : (¬ c 5 = true) := fun hh => cl_292 h a2 hh a1 a4
  have u2 : (¬ c 23 = true) := fun hh => cl_451 h a2 hh a0 a1 a3 a4 a5 a7 a8 a9
  have u3 : (¬ c 17 = true) := fun hh => cl_143 h a2 u1 hh a0 a9
  have u4 : (¬ c 2 = true) := fun hh => cl_57 h hh a2 u1 u3 u2 a5 a8
  have u5 : (¬ c 11 = true) := fun hh => cl_444 h u4 a2 hh u3
  exact cl_248 h u4 a2 u5 u0 a6

private lemma cl_454 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 23 = true) → (¬ c 5 = true) → (c 19 = true) → (c 3 = true) → (c 97 = true) → (c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (¬ c 11 = true) := fun hh => cl_233 h a0 a4 a2 hh a1 a5
  exact cl_248 h a0 a4 u0 a3 a6

private lemma cl_455 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (c 19 = true) → (c 3 = true) → (c 59 = true) → (c 79 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (c 11 = true) := Classical.byContradiction (fun hh => cl_151 h a0 a3 a1 hh a2 a5)
  have u1 : (c 17 = true) := Classical.byContradiction (fun hh => cl_289 h a0 a3 a1 hh a4 a6)
  exact cl_446 h a0 a3 u0 u1

private lemma cl_456 {c : ℕ → Bool} (h : MultCore c) : (c 47 = true) → (c 3 = true) → (c 59 = true) → (c 79 = true) → (c 83 = true) → (c 109 = true) → (c 131 = true) → (c 151 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : (c 19 = true) := Classical.byContradiction (fun hh => cl_43 h a1 hh a0 a5 a8)
  have u1 : (¬ c 5 = true) := fun hh => cl_292 h a1 hh a0 a4
  have u2 : (¬ c 2 = true) := fun hh => cl_455 h hh u1 u0 a1 a2 a3 a7
  have u3 : (c 11 = true) := Classical.byContradiction (fun hh => cl_248 h u2 a1 hh u0 a6)
  exact cl_428 h u2 a1 u1 u3 a2

private lemma cl_457 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (¬ c 47 = true) → (c 3 = true) → (c 73 = true) → (c 79 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 17 = true) := Classical.byContradiction (fun hh => cl_99 h a0 a3 a1 hh a2 a5)
  have u1 : (¬ c 19 = true) := fun hh => cl_424 h a0 u0 hh a4
  exact cl_315 h a3 a1 u0 u1 a2

private lemma cl_458 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (¬ c 47 = true) → (c 3 = true) → (c 59 = true) → (c 73 = true) → (c 79 = true) → (c 131 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_457 h hh a0 a1 a2 a4 a5)
  have u1 : (c 19 = true) := Classical.byContradiction (fun hh => cl_131 h u0 a2 a0 hh a6 a7)
  have u2 : (c 11 = true) := Classical.byContradiction (fun hh => cl_151 h u0 a2 a0 hh u1 a5)
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_289 h u0 a2 a0 hh a3 a7)
  exact cl_446 h u0 a2 u2 u3

private lemma cl_459 {c : ℕ → Bool} (h : MultCore c) : (c 59 = true) → (c 61 = true) → (c 73 = true) → (c 79 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_452 h hh a0 a1 a2 a12)
  have u1 : (¬ c 47 = true) := fun hh => cl_456 h hh u0 a0 a3 a4 a7 a9 a11 a12
  have u2 : (c 5 = true) := Classical.byContradiction (fun hh => cl_458 h hh u1 u0 a0 a2 a3 a9 a11)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 u2)
  have u4 : (¬ c 11 = true) := fun hh => cl_320 h u3 u0 u2 hh a8
  have u5 : (¬ c 29 = true) := fun hh => cl_24 h u0 u2 hh a5 a6 a10
  have u6 : (¬ c 23 = true) := fun hh => cl_385 h u3 u2 u4 hh u1 a8
  exact cl_410 h u0 u2 u4 u6 u5

private lemma cl_460 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 59 = true) → (c 61 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a0 a1)
  exact cl_246 h u0 a0 a1 a2 a3 a4

private lemma cl_461 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (¬ c 59 = true) → (c 61 = true) → (c 73 = true) → (c 83 = true) → (c 97 = true) → (c 113 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (¬ c 3 = true) := fun hh => cl_460 h hh a0 a1 a2 a3
  have u1 : (¬ c 2 = true) := fun hh => cl_450 h hh u0 a0
  have u2 : (¬ c 19 = true) := fun hh => cl_352 h u1 u0 a0 hh a4 a6
  have u3 : (¬ c 11 = true) := fun hh => cl_373 h u1 u0 a0 hh u2
  have u4 : (c 29 = true) := Classical.byContradiction (fun hh => cl_431 h u1 u0 u3 u2 hh)
  exact cl_191 h u1 a0 u3 u4 a1 a5

private lemma cl_462 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (c 97 = true) → (c 101 = true) → (c 149 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_447 h hh a0 a1)
  have u1 : (¬ c 29 = true) := fun hh => cl_18 h a0 a1 hh a2 a3 a4
  exact cl_211 h u0 a0 a1 u1 a3 a5

private lemma cl_463 {c : ℕ → Bool} (h : MultCore c) : (c 61 = true) → (c 73 = true) → (c 79 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have u0 : (¬ c 59 = true) := fun hh => cl_459 h hh a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have u1 : (¬ c 5 = true) := fun hh => cl_461 h hh u0 a0 a1 a3 a4 a7
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_462 h hh u1 a4 a5 a9 a10)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_241 h hh u2 u1 u0 a0 a1)
  have u4 : (c 31 = true) := Classical.byContradiction (fun hh => cl_389 h u3 u2 u1 hh a6)
  have u5 : (c 19 = true) := Classical.byContradiction (fun hh => cl_131 h u3 u2 u1 hh a8 a10)
  have u6 : (c 7 = true) := Classical.byContradiction (fun hh => cl_198 h u3 u1 hh u4)
  have u7 : (¬ c 29 = true) := fun hh => cl_327 h u3 u2 u1 u6 hh a12
  exact cl_350 h u3 u2 u1 u6 u5 u7

private lemma cl_464 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 109 = true) → (c 131 = true) → (c 151 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (c 31 = true) := Classical.byContradiction (fun hh => cl_389 h a0 a1 a2 hh a3)
  have u1 : (c 19 = true) := Classical.byContradiction (fun hh => cl_131 h a0 a1 a2 hh a4 a5)
  have u2 : (c 7 = true) := Classical.byContradiction (fun hh => cl_198 h a0 a2 hh u0)
  have u3 : (¬ c 29 = true) := fun hh => cl_327 h a0 a1 a2 u2 hh a6
  exact cl_350 h a0 a1 a2 u2 u1 u3

private lemma cl_465 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (¬ c 61 = true) → (c 73 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 109 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_462 h hh a0 a4 a5 a8 a9)
  have u1 : (¬ c 2 = true) := fun hh => cl_464 h hh u0 a0 a6 a7 a9 a11
  have u2 : (c 17 = true) := Classical.byContradiction (fun hh => cl_376 h u1 hh a1)
  have u3 : (c 31 = true) := Classical.byContradiction (fun hh => cl_340 h u1 u0 hh a3 a8)
  have u4 : (¬ c 19 = true) := fun hh => cl_424 h u1 u2 hh a2
  exact cl_183 h u1 u0 a0 u4 u3 a10

private lemma cl_466 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 113 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (¬ c 47 = true) := fun hh => cl_292 h a0 a1 hh a2
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a0 a1)
  have u2 : (¬ c 29 = true) := fun hh => cl_24 h a0 a1 hh a3 a4 a6
  have u3 : (¬ c 11 = true) := fun hh => cl_320 h u1 a0 a1 hh a5
  have u4 : (¬ c 23 = true) := fun hh => cl_385 h u1 a1 u3 hh u0 a5
  exact cl_410 h a0 a1 u3 u4 u2

private lemma cl_467 {c : ℕ → Bool} (h : MultCore c) : (c 73 = true) → (c 79 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have u0 : (¬ c 61 = true) := fun hh => cl_463 h hh a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_465 h hh u0 a0 a2 a3 a4 a5 a7 a8 a9 a10 a11)
  have u2 : (¬ c 3 = true) := fun hh => cl_466 h hh u1 a2 a3 a4 a6 a8
  have u3 : (¬ c 2 = true) := fun hh => cl_450 h hh u2 u1
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_376 h u3 hh u0)
  have u5 : (¬ c 19 = true) := fun hh => cl_352 h u3 u2 u1 hh a2 a6
  have u6 : (¬ c 29 = true) := fun hh => cl_154 h u3 u2 u4 hh a8 a12
  have u7 : (¬ c 11 = true) := fun hh => cl_70 h u3 hh u4 a2 a9
  exact cl_431 h u3 u2 u7 u5 u6

private lemma cl_468 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (¬ c 73 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 113 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (¬ c 3 = true) := fun hh => cl_466 h hh a0 a2 a3 a4 a5 a6
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_377 h hh u0 a1)
  exact cl_450 h u1 u0 a0

private lemma cl_469 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 109 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_462 h hh a0 a2 a3 a6 a7)
  have u1 : (¬ c 2 = true) := fun hh => cl_464 h hh u0 a0 a4 a5 a7 a9
  have u2 : (c 31 = true) := Classical.byContradiction (fun hh => cl_340 h u1 u0 hh a1 a6)
  have u3 : (c 19 = true) := Classical.byContradiction (fun hh => cl_183 h u1 u0 a0 hh u2 a8)
  have u4 : (c 11 = true) := Classical.byContradiction (fun hh => cl_248 h u1 u0 hh u3 a5)
  have u5 : (c 17 = true) := Classical.byContradiction (fun hh => cl_444 h u1 u0 u4 hh)
  exact cl_437 h u1 u0 a0 u4 u5

private lemma cl_470 {c : ℕ → Bool} (h : MultCore c) : (c 83 = true) → (c 97 = true) → (c 101 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have u0 : (c 5 = true) := Classical.byContradiction (fun hh => cl_469 h hh a0 a1 a2 a3 a5 a6 a7 a8 a9)
  have u1 : (¬ c 3 = true) := fun hh => cl_466 h hh u0 a0 a1 a2 a4 a6
  have u2 : (¬ c 2 = true) := fun hh => cl_450 h hh u1 u0
  have u3 : (¬ c 19 = true) := fun hh => cl_352 h u2 u1 u0 hh a0 a4
  have u4 : (¬ c 11 = true) := fun hh => cl_373 h u2 u1 u0 hh u3
  have u5 : (c 17 = true) := Classical.byContradiction (fun hh => cl_443 h u2 u1 u4 hh)
  have u6 : (c 29 = true) := Classical.byContradiction (fun hh => cl_431 h u2 u1 u4 u3 hh)
  exact cl_154 h u2 u1 u5 u6 a6 a10

private lemma cl_471 {c : ℕ → Bool} (h : MultCore c) : (¬ c 11 = true) → (¬ c 2 = true) → (¬ c 3 = true) → (c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (c 73 = true) := Classical.byContradiction (fun hh => cl_377 h a1 a2 hh)
  have u1 : (c 17 = true) := Classical.byContradiction (fun hh => cl_443 h a1 a2 a0 hh)
  have u2 : (¬ c 19 = true) := fun hh => cl_424 h a1 u1 hh u0
  have u3 : (¬ c 29 = true) := fun hh => cl_154 h a1 a2 u1 hh a3 a4
  exact cl_431 h a1 a2 a0 u2 u3

private lemma cl_472 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (c 97 = true) → (c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (¬ c 2 = true) := fun hh => cl_450 h hh a0 a1
  have u1 : (c 11 = true) := Classical.byContradiction (fun hh => cl_471 h hh u0 a0 a3 a4)
  have u2 : (c 19 = true) := Classical.byContradiction (fun hh => cl_373 h u0 a0 a1 u1 hh)
  have u3 : (¬ c 47 = true) := fun hh => cl_400 h u0 a0 a1 u1 hh a2
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_436 h u0 a0 a1 u1 hh)
  exact cl_314 h a0 a1 u4 u2 u3

private lemma cl_473 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (¬ c 83 = true) → (c 97 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_472 h hh a0 a2 a5 a7)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a0)
  have u2 : (¬ c 19 = true) := fun hh => cl_132 h u1 u0 a0 hh a4 a6
  exact cl_358 h u1 u0 a0 u2 a1 a3

private lemma cl_474 {c : ℕ → Bool} (h : MultCore c) : (¬ c 19 = true) → (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 109 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (¬ c 47 = true) := fun hh => cl_43 h a2 a0 hh a4 a5
  have u1 : (¬ c 31 = true) := fun hh => cl_183 h a1 a2 a3 a0 hh a5
  have u2 : (¬ c 17 = true) := fun hh => cl_315 h a2 a3 hh a0 u0
  have u3 : (c 7 = true) := Classical.byContradiction (fun hh => cl_197 h a1 a3 hh u1)
  have u4 : (¬ c 79 = true) := fun hh => cl_99 h a1 a2 a3 u2 u0 hh
  exact cl_30 h a1 a2 a3 u3 u2 u4

private lemma cl_475 {c : ℕ → Bool} (h : MultCore c) : (c 97 = true) → (c 101 = true) → (c 251 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have u0 : (¬ c 83 = true) := fun hh => cl_470 h hh a0 a1 a3 a4 a5 a6 a7 a8 a9 a2
  have u1 : (¬ c 5 = true) := fun hh => cl_473 h hh u0 a0 a4 a5 a6 a7 a2
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_462 h hh u1 a0 a1 a6 a7)
  have u3 : (¬ c 2 = true) := fun hh => cl_464 h hh u2 u1 a3 a5 a7 a9
  have u4 : (c 19 = true) := Classical.byContradiction (fun hh => cl_474 h hh u3 u2 u1 a3 a8)
  have u5 : (c 11 = true) := Classical.byContradiction (fun hh => cl_248 h u3 u2 hh u4 a5)
  have u6 : (c 17 = true) := Classical.byContradiction (fun hh => cl_444 h u3 u2 u5 hh)
  exact cl_437 h u3 u2 u1 u5 u6

private lemma cl_476 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 5 = true) → (¬ c 97 = true) → (c 101 = true) → (c 109 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have u0 : (¬ c 2 = true) := fun hh => cl_464 h hh a0 a1 a4 a5 a7 a9
  have u1 : (c 29 = true) := Classical.byContradiction (fun hh => cl_21 h a0 a1 hh a2 a3 a6)
  have u2 : (c 19 = true) := Classical.byContradiction (fun hh => cl_474 h hh u0 a0 a1 a4 a8)
  have u3 : (c 7 = true) := Classical.byContradiction (fun hh => cl_323 h u0 a0 a1 hh u1 a9)
  exact cl_346 h u0 a0 a1 u3 u2 u1

private lemma cl_477 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (¬ c 97 = true) → (c 197 = true) → (c 101 = true) → (c 109 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : (¬ c 3 = true) := fun hh => cl_476 h hh a0 a1 a3 a4 a5 a6 a7 a8 a2
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_447 h hh u0 a0)
  have u2 : (¬ c 59 = true) := fun hh => cl_330 h u1 u0 hh a8
  have u3 : (¬ c 11 = true) := fun hh => cl_429 h u1 u0 a0 hh u2
  have u4 : (¬ c 17 = true) := fun hh => cl_445 h u1 u0 u3 hh
  have u5 : (¬ c 19 = true) := fun hh => cl_374 h u1 u0 a0 u3 hh
  have u6 : (c 23 = true) := Classical.byContradiction (fun hh => cl_425 h u0 a0 u5 hh)
  exact cl_93 h u1 u0 u4 u5 u6 a8

private lemma cl_478 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (¬ c 97 = true) → (c 101 = true) → (c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (¬ c 2 = true) := fun hh => cl_450 h hh a0 a1
  have u1 : (c 29 = true) := Classical.byContradiction (fun hh => cl_19 h a0 a1 hh a2 a3 a4)
  have u2 : (c 11 = true) := Classical.byContradiction (fun hh => cl_471 h hh u0 a0 a4 a5)
  have u3 : (¬ c 17 = true) := fun hh => cl_154 h u0 a0 hh u1 a4 a5
  exact cl_436 h u0 a0 a1 u2 u3

private lemma cl_479 {c : ℕ → Bool} (h : MultCore c) : (c 101 = true) → (c 109 = true) → (c 251 = true) → (c 197 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : (¬ c 97 = true) := fun hh => cl_475 h hh a0 a2 a1 a4 a5 a6 a7 a8 a3
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_477 h hh u0 a3 a0 a1 a5 a6 a7 a8)
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_478 h hh u1 u0 a0 a6 a2)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u2 u1)
  have u4 : (¬ c 19 = true) := fun hh => cl_132 h u3 u2 u1 hh a5 a7
  have u5 : (¬ c 11 = true) := fun hh => cl_320 h u3 u2 u1 hh a4
  have u6 : (¬ c 47 = true) := fun hh => cl_43 h u2 u4 hh a1 a8
  exact cl_406 h u3 u2 u1 u5 u6 u0

private lemma cl_480 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a0 a1)
  have u1 : (¬ c 19 = true) := fun hh => cl_132 h u0 a0 a1 hh a4 a5
  have u2 : (¬ c 13 = true) := fun hh => cl_312 h u0 a0 hh a2
  have u3 : (¬ c 11 = true) := fun hh => cl_320 h u0 a0 a1 hh a3
  have u4 : (¬ c 47 = true) := fun hh => cl_43 h a0 u1 hh a2 a6
  have u5 : (¬ c 7 = true) := fun hh => cl_222 h u0 a0 a1 hh u2 u4
  have u6 : (¬ c 23 = true) := fun hh => cl_385 h u0 a1 u3 hh u4 a3
  have u7 : (¬ c 29 = true) := fun hh => cl_328 h u0 a0 a1 u5 hh a7
  exact cl_410 h a0 a1 u3 u6 u7

private lemma cl_481 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (c 109 = true) → (c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have u0 : (¬ c 3 = true) := fun hh => cl_480 h hh a0 a1 a2 a3 a5 a6 a7
  have u1 : (¬ c 2 = true) := fun hh => cl_450 h hh u0 a0
  have u2 : (c 11 = true) := Classical.byContradiction (fun hh => cl_471 h hh u1 u0 a4 a8)
  have u3 : (c 19 = true) := Classical.byContradiction (fun hh => cl_373 h u1 u0 a0 u2 hh)
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_436 h u1 u0 a0 u2 hh)
  have u5 : (¬ c 47 = true) := fun hh => cl_42 h u0 u3 hh a1 a6
  exact cl_314 h u0 a0 u4 u3 u5

private lemma cl_482 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → (c 167 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_447 h hh a0 a1)
  have u1 : (¬ c 59 = true) := fun hh => cl_330 h u0 a0 hh a2
  have u2 : (¬ c 11 = true) := fun hh => cl_429 h u0 a0 a1 hh u1
  have u3 : (¬ c 17 = true) := fun hh => cl_445 h u0 a0 u2 hh
  have u4 : (¬ c 19 = true) := fun hh => cl_374 h u0 a0 a1 u2 hh
  have u5 : (¬ c 23 = true) := fun hh => cl_93 h u0 a0 u3 u4 hh a2
  exact cl_425 h a0 a1 u4 u5

private lemma cl_483 {c : ℕ → Bool} (h : MultCore c) : (c 109 = true) → (c 113 = true) → (c 251 = true) → (c 197 = true) → (c 167 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have u0 : (¬ c 101 = true) := fun hh => cl_479 h hh a0 a2 a3 a1 a5 a6 a7 a4
  have u1 : (¬ c 5 = true) := fun hh => cl_481 h hh a0 a1 a5 a6 a7 a4 a3 a2
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh u1 a4)
  have u3 : (¬ c 2 = true) := fun hh => cl_464 h hh u2 u1 a0 a5 a7 a3
  have u4 : (¬ c 29 = true) := fun hh => cl_209 h u3 u2 u1 hh u0 a7
  have u5 : (c 19 = true) := Classical.byContradiction (fun hh => cl_474 h hh u3 u2 u1 a0 a4)
  have u6 : (c 17 = true) := Classical.byContradiction (fun hh => cl_155 h u3 u2 hh u4 a6 a2)
  have u7 : (c 11 = true) := Classical.byContradiction (fun hh => cl_248 h u3 u2 hh u5 a5)
  exact cl_437 h u3 u2 u1 u7 u6

private lemma cl_484 {c : ℕ → Bool} (h : MultCore c) : (c 11 = true) → (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 17 = true) := Classical.byContradiction (fun hh => cl_444 h a1 a2 a0 hh)
  exact cl_437 h a1 a2 a3 a0 u0

private lemma cl_485 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (¬ c 109 = true) → (c 131 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh a1 a4)
  have u1 : (¬ c 13 = true) := fun hh => cl_310 h a0 u0 hh a2
  have u2 : (¬ c 11 = true) := fun hh => cl_484 h hh a0 u0 a1
  have u3 : (¬ c 19 = true) := fun hh => cl_248 h a0 u0 u2 hh a3
  have u4 : (¬ c 31 = true) := fun hh => cl_183 h a0 u0 a1 u3 hh a4
  have u5 : (c 7 = true) := Classical.byContradiction (fun hh => cl_197 h a0 a1 hh u4)
  have u6 : (¬ c 47 = true) := fun hh => cl_217 h a0 u0 a1 u5 u1 hh
  have u7 : (¬ c 17 = true) := fun hh => cl_315 h u0 a1 hh u3 u6
  have u8 : (¬ c 79 = true) := fun hh => cl_99 h a0 u0 a1 u7 u6 hh
  exact cl_30 h a0 u0 a1 u5 u7 u8

private lemma cl_486 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (¬ c 109 = true) → (c 113 = true) → (c 131 = true) → (c 151 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh a0 a5)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_485 h hh a0 a1 a3 a5)
  have u2 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u3 : (c 19 = true) := Classical.byContradiction (fun hh => cl_131 h u1 u0 a0 hh a3 a4)
  have u4 : (c 11 = true) := Classical.byContradiction (fun hh => cl_319 h u1 u0 a0 hh a2)
  have u5 : (¬ c 17 = true) := fun hh => cl_446 h u1 u0 u4 hh
  have u6 : (¬ c 29 = true) := fun hh => cl_434 h u1 u0 u4 u3 hh
  have u7 : (c 7 = true) := Classical.byContradiction (fun hh => cl_121 h u1 u0 a0 hh u4 u5 u2)
  exact cl_350 h u1 u0 a0 u7 u3 u6

private lemma cl_487 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 109 = true) → (c 113 = true) → (c 131 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a0 a1)
  have u1 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u0 a0 hh)
  have u2 : (¬ c 19 = true) := fun hh => cl_132 h u0 a0 a1 hh a4 a5
  have u3 : (¬ c 11 = true) := fun hh => cl_320 h u0 a0 a1 hh a3
  have u4 : (¬ c 31 = true) := fun hh => cl_390 h u0 a0 a1 hh a2
  have u5 : (c 83 = true) := Classical.byContradiction (fun hh => cl_358 h u0 a0 a1 u2 hh a3)
  have u6 : (¬ c 29 = true) := fun hh => cl_68 h u0 a0 a1 hh u4 u1
  have u7 : (¬ c 47 = true) := fun hh => cl_292 h a0 a1 hh u5
  have u8 : (c 23 = true) := Classical.byContradiction (fun hh => cl_410 h a0 a1 u3 hh u6)
  exact cl_385 h u0 a1 u3 u8 u7 a3

private lemma cl_488 {c : ℕ → Bool} (h : MultCore c) : (c 113 = true) → (c 131 = true) → (c 251 = true) → (c 197 = true) → (c 167 = true) → (c 151 = true) → (c 149 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (¬ c 109 = true) := fun hh => cl_483 h hh a0 a2 a3 a4 a1 a6 a5
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_486 h hh u0 a0 a1 a5 a4)
  have u2 : (¬ c 3 = true) := fun hh => cl_487 h hh u1 u0 a0 a1 a5
  have u3 : (¬ c 2 = true) := fun hh => cl_450 h hh u2 u1
  have u4 : (c 73 = true) := Classical.byContradiction (fun hh => cl_377 h u3 u2 hh)
  have u5 : (c 11 = true) := Classical.byContradiction (fun hh => cl_471 h hh u3 u2 a6 a2)
  have u6 : (c 19 = true) := Classical.byContradiction (fun hh => cl_373 h u3 u2 u1 u5 hh)
  have u7 : (c 17 = true) := Classical.byContradiction (fun hh => cl_436 h u3 u2 u1 u5 hh)
  exact cl_424 h u3 u7 u6 u4

private lemma cl_489 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → (¬ c 113 = true) → (c 149 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (¬ c 2 = true) := fun hh => cl_450 h hh a0 a1
  have u1 : (c 11 = true) := Classical.byContradiction (fun hh => cl_471 h hh u0 a0 a3 a4)
  exact cl_318 h u0 a0 a1 u1 a2

private lemma cl_490 {c : ℕ → Bool} (h : MultCore c) : (c 11 = true) → (c 3 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a1 a2)
  have u1 : (¬ c 17 = true) := fun hh => cl_446 h u0 a1 a0 hh
  exact cl_442 h u0 a1 a2 a0 u1

private lemma cl_491 {c : ℕ → Bool} (h : MultCore c) : (¬ c 7 = true) → (c 3 = true) → (c 5 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a1 a2)
  have u1 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u0 a1 hh)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh a1 a2
  have u3 : (¬ c 29 = true) := fun hh => cl_328 h u0 a1 a2 a0 hh a3
  have u4 : (c 23 = true) := Classical.byContradiction (fun hh => cl_410 h a1 a2 u2 hh u3)
  have u5 : (¬ c 59 = true) := fun hh => cl_414 h u0 a2 a0 u4 hh
  have u6 : (c 61 = true) := Classical.byContradiction (fun hh => cl_337 h u0 a1 a2 a0 u4 hh)
  exact cl_246 h u0 a1 a2 u5 u6 u1

private lemma cl_492 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (¬ c 113 = true) → (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_489 h hh a0 a1 a2 a6)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a0)
  have u2 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u3 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a0
  have u4 : (c 7 = true) := Classical.byContradiction (fun hh => cl_491 h hh u0 a0 a5)
  have u5 : (c 17 = true) := Classical.byContradiction (fun hh => cl_124 h u1 u0 a0 u4 u3 hh u2)
  have u6 : (¬ c 59 = true) := fun hh => cl_290 h u1 u0 a0 u5 hh a3
  have u7 : (¬ c 83 = true) := fun hh => cl_71 h u1 u3 u5 hh a3
  have u8 : (¬ c 61 = true) := fun hh => cl_246 h u1 u0 a0 u6 hh u2
  have u9 : (c 31 = true) := Classical.byContradiction (fun hh => cl_342 h u1 u0 hh u7 a2)
  have u10 : (c 29 = true) := Classical.byContradiction (fun hh => cl_281 h u1 u0 a0 u3 u5 hh u8)
  have u11 : (c 109 = true) := Classical.byContradiction (fun hh => cl_390 h u1 u0 a0 u9 hh)
  have u12 : (c 97 = true) := Classical.byContradiction (fun hh => cl_195 h u1 a0 u3 u10 u6 hh)
  have u13 : (c 23 = true) := Classical.byContradiction (fun hh => cl_60 h u1 u0 a0 u5 hh u11 a4)
  exact cl_238 h u1 u0 a0 u3 u13 u12

private lemma cl_493 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 113 = true) → (c 131 = true) → (c 149 = true) → (c 151 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have u0 : (c 19 = true) := Classical.byContradiction (fun hh => cl_131 h a0 a1 a2 hh a4 a6)
  have u1 : (¬ c 83 = true) := fun hh => cl_357 h a0 a1 a2 u0 hh a3
  have u2 : (c 31 = true) := Classical.byContradiction (fun hh => cl_342 h a0 a1 hh u1 a5)
  have u3 : (c 7 = true) := Classical.byContradiction (fun hh => cl_198 h a0 a2 hh u2)
  have u4 : (¬ c 29 = true) := fun hh => cl_327 h a0 a1 a2 u3 hh a7
  exact cl_350 h a0 a1 a2 u3 u0 u4

private lemma cl_494 {c : ℕ → Bool} (h : MultCore c) : (c 131 = true) → (c 149 = true) → (c 251 = true) → (c 197 = true) → (c 167 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (¬ c 113 = true) := fun hh => cl_488 h hh a0 a2 a3 a4 a5 a1
  have u1 : (¬ c 5 = true) := fun hh => cl_492 h hh u0 a1 a5 a4 a3 a2
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh u1 a4)
  have u3 : (¬ c 2 = true) := fun hh => cl_493 h hh u2 u1 u0 a0 a1 a5 a3
  have u4 : (¬ c 11 = true) := fun hh => cl_484 h hh u3 u2 u1
  have u5 : (c 109 = true) := Classical.byContradiction (fun hh => cl_485 h u3 u1 hh a0 a4)
  have u6 : (¬ c 19 = true) := fun hh => cl_248 h u3 u2 u4 hh a0
  exact cl_474 h u6 u3 u2 u1 u5 a4

private lemma cl_495 {c : ℕ → Bool} (h : MultCore c) : (¬ c 19 = true) → (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (¬ c 31 = true) := fun hh => cl_183 h a1 a2 a3 a0 hh a4
  have u1 : (¬ c 109 = true) := fun hh => cl_474 h a0 a1 a2 a3 hh a4
  have u2 : (c 7 = true) := Classical.byContradiction (fun hh => cl_197 h a1 a3 hh u0)
  have u3 : (¬ c 13 = true) := fun hh => cl_310 h a1 a2 hh u1
  have u4 : (¬ c 47 = true) := fun hh => cl_217 h a1 a2 a3 u2 u3 hh
  have u5 : (¬ c 17 = true) := fun hh => cl_315 h a2 a3 hh a0 u4
  have u6 : (¬ c 79 = true) := fun hh => cl_99 h a1 a2 a3 u5 u4 hh
  exact cl_30 h a1 a2 a3 u2 u5 u6

private lemma cl_496 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh a1 a2)
  have u1 : (¬ c 11 = true) := fun hh => cl_484 h hh a0 u0 a1
  have u2 : (c 19 = true) := Classical.byContradiction (fun hh => cl_495 h hh a0 u0 a1 a2)
  have u3 : (c 29 = true) := Classical.byContradiction (fun hh => cl_432 h a0 u0 u1 u2 hh)
  have u4 : (c 7 = true) := Classical.byContradiction (fun hh => cl_323 h a0 u0 a1 hh u3 a3)
  exact cl_346 h a0 u0 a1 u4 u2 u3

private lemma cl_497 {c : ℕ → Bool} (h : MultCore c) : (c 19 = true) → (c 83 = true) → (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 131 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 113 = true) := Classical.byContradiction (fun hh => cl_357 h a2 a3 a4 a0 a1 hh)
  have u1 : (¬ c 11 = true) := fun hh => cl_250 h a2 a3 hh a0 a5
  exact cl_319 h a2 a3 a4 u1 u0

private lemma cl_498 {c : ℕ → Bool} (h : MultCore c) : (¬ c 11 = true) → (c 83 = true) → (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 151 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 17 = true) := Classical.byContradiction (fun hh => cl_441 h a2 a3 a4 a0 hh)
  exact cl_71 h a2 a0 u0 a1 a5

private lemma cl_499 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (¬ c 131 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → (c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh a0 a3)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_496 h hh a0 a3 a4)
  have u2 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u3 : (c 83 = true) := Classical.byContradiction (fun hh => cl_108 h u1 u0 hh a1 a5)
  have u4 : (¬ c 19 = true) := fun hh => cl_497 h hh u3 u1 u0 a0 a1
  have u5 : (c 11 = true) := Classical.byContradiction (fun hh => cl_498 h hh u3 u1 u0 a0 a2)
  have u6 : (¬ c 17 = true) := fun hh => cl_446 h u1 u0 u5 hh
  have u7 : (c 7 = true) := Classical.byContradiction (fun hh => cl_121 h u1 u0 a0 hh u5 u6 u2)
  have u8 : (c 79 = true) := Classical.byContradiction (fun hh => cl_152 h u1 u0 a0 u5 u4 hh)
  exact cl_38 h u1 u0 a0 u7 u6 u8

private lemma cl_500 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → (¬ c 131 = true) → (c 151 = true) → (c 197 = true) → (c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a0 a1)
  have u1 : (¬ c 11 = true) := fun hh => cl_490 h hh a0 a1
  have u2 : (c 7 = true) := Classical.byContradiction (fun hh => cl_491 h hh a0 a1 a4)
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u0 a0 hh)
  have u4 : (c 83 = true) := Classical.byContradiction (fun hh => cl_108 h u0 a0 hh a2 a5)
  have u5 : (¬ c 17 = true) := fun hh => cl_71 h u0 u1 hh u4 a3
  exact cl_124 h u0 a0 a1 u2 u1 u5 u3

private lemma cl_501 {c : ℕ → Bool} (h : MultCore c) : (c 149 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → (c 251 = true) → (c 337 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (¬ c 131 = true) := fun hh => cl_494 h hh a0 a4 a3 a2 a1
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_499 h hh u0 a1 a2 a3 a5)
  have u2 : (¬ c 3 = true) := fun hh => cl_500 h hh u1 u0 a1 a3 a5
  have u3 : (¬ c 2 = true) := fun hh => cl_450 h hh u2 u1
  have u4 : (c 73 = true) := Classical.byContradiction (fun hh => cl_377 h u3 u2 hh)
  have u5 : (c 11 = true) := Classical.byContradiction (fun hh => cl_471 h hh u3 u2 a0 a4)
  have u6 : (c 19 = true) := Classical.byContradiction (fun hh => cl_373 h u3 u2 u1 u5 hh)
  have u7 : (c 17 = true) := Classical.byContradiction (fun hh => cl_436 h u3 u2 u1 u5 hh)
  exact cl_424 h u3 u7 u6 u4

private lemma cl_502 {c : ℕ → Bool} (h : MultCore c) : (c 11 = true) → (¬ c 3 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (¬ c 2 = true) := fun hh => cl_450 h hh a1 a2
  have u1 : (c 73 = true) := Classical.byContradiction (fun hh => cl_377 h u0 a1 hh)
  have u2 : (c 19 = true) := Classical.byContradiction (fun hh => cl_373 h u0 a1 a2 a0 hh)
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_436 h u0 a1 a2 a0 hh)
  exact cl_424 h u0 u3 u2 u1

private lemma cl_503 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (c 5 = true) → False := by
  intro a0 a1
  have u0 : (¬ c 2 = true) := fun hh => cl_450 h hh a0 a1
  have u1 : (c 73 = true) := Classical.byContradiction (fun hh => cl_377 h u0 a0 hh)
  have u2 : (¬ c 11 = true) := fun hh => cl_502 h hh a0 a1
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_443 h u0 a0 u2 hh)
  have u4 : (¬ c 19 = true) := fun hh => cl_424 h u0 u3 hh u1
  have u5 : (¬ c 23 = true) := fun hh => cl_392 h u0 a0 a1 u3 u4 hh
  have u6 : (¬ c 7 = true) := fun hh => cl_226 h u0 a0 a1 hh u2 u5
  have u7 : (c 79 = true) := Classical.byContradiction (fun hh => cl_27 h u0 a0 a1 u6 u3 hh)
  have u8 : (c 47 = true) := Classical.byContradiction (fun hh => cl_415 h u0 a0 u6 u5 hh)
  exact cl_98 h u0 a0 a1 u3 u8 u7

private lemma cl_504 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (c 151 = true) → (c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a0)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a0)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a0
  have u3 : (c 7 = true) := Classical.byContradiction (fun hh => cl_491 h hh u0 a0 a3)
  have u4 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u5 : (c 17 = true) := Classical.byContradiction (fun hh => cl_124 h u1 u0 a0 u3 u2 hh u4)
  have u6 : (¬ c 59 = true) := fun hh => cl_290 h u1 u0 a0 u5 hh a1
  have u7 : (¬ c 61 = true) := fun hh => cl_246 h u1 u0 a0 u6 hh u4
  have u8 : (c 29 = true) := Classical.byContradiction (fun hh => cl_281 h u1 u0 a0 u2 u5 hh u7)
  have u9 : (c 31 = true) := Classical.byContradiction (fun hh => cl_68 h u1 u0 a0 u8 hh u4)
  have u10 : (c 97 = true) := Classical.byContradiction (fun hh => cl_195 h u1 a0 u2 u8 u6 hh)
  have u11 : (c 109 = true) := Classical.byContradiction (fun hh => cl_390 h u1 u0 a0 u9 hh)
  have u12 : (¬ c 23 = true) := fun hh => cl_238 h u1 u0 a0 u2 hh u10
  exact cl_60 h u1 u0 a0 u5 u12 u11 a2

private lemma cl_505 {c : ℕ → Bool} (h : MultCore c) : (¬ c 11 = true) → (c 19 = true) → (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 17 = true) := Classical.byContradiction (fun hh => cl_441 h a2 a3 a4 a0 hh)
  have u1 : (¬ c 79 = true) := fun hh => cl_151 h a2 a3 a4 a0 a1 hh
  have u2 : (¬ c 37 = true) := fun hh => cl_143 h a3 a4 u0 hh a5
  have u3 : (c 7 = true) := Classical.byContradiction (fun hh => cl_37 h a2 a3 a4 hh u0 u1)
  exact cl_206 h a2 a3 a4 u3 u0 u2

private lemma cl_506 {c : ℕ → Bool} (h : MultCore c) : (c 151 = true) → (c 167 = true) → (c 337 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (¬ c 149 = true) := fun hh => cl_501 h hh a0 a1 a3 a4 a2
  have u1 : (¬ c 5 = true) := fun hh => cl_504 h hh a0 a1 a3
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh u1 a1)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_496 h hh u1 a1 a3)
  have u4 : (c 131 = true) := Classical.byContradiction (fun hh => cl_499 h u1 hh a0 a1 a3 a2)
  have u5 : (c 19 = true) := Classical.byContradiction (fun hh => cl_131 h u3 u2 u1 hh u4 a0)
  have u6 : (c 11 = true) := Classical.byContradiction (fun hh => cl_505 h hh u5 u3 u2 u1 a4)
  have u7 : (¬ c 17 = true) := fun hh => cl_446 h u3 u2 u6 hh
  have u8 : (¬ c 29 = true) := fun hh => cl_434 h u3 u2 u6 u5 hh
  exact cl_159 h u3 u2 u7 u8 u0 a4

private lemma cl_507 {c : ℕ → Bool} (h : MultCore c) : (c 11 = true) → (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h a1 a2 hh)
  have u1 : (¬ c 17 = true) := fun hh => cl_446 h a1 a2 a0 hh
  have u2 : (c 7 = true) := Classical.byContradiction (fun hh => cl_121 h a1 a2 a3 hh a0 u1 u0)
  have u3 : (¬ c 79 = true) := fun hh => cl_38 h a1 a2 a3 u2 u1 hh
  have u4 : (¬ c 29 = true) := fun hh => cl_327 h a1 a2 a3 u2 hh a4
  have u5 : (c 19 = true) := Classical.byContradiction (fun hh => cl_152 h a1 a2 a3 a0 hh u3)
  exact cl_350 h a1 a2 a3 u2 u5 u4

private lemma cl_508 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_482 h hh a0 a1)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_496 h hh a0 a1 a2)
  have u2 : (¬ c 11 = true) := fun hh => cl_507 h hh u1 u0 a0 a2
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_441 h u1 u0 a0 u2 hh)
  have u4 : (¬ c 19 = true) := fun hh => cl_505 h u2 hh u1 u0 a0 a3
  have u5 : (¬ c 37 = true) := fun hh => cl_143 h u0 a0 u3 hh a3
  have u6 : (c 47 = true) := Classical.byContradiction (fun hh => cl_315 h u0 a0 u3 u4 hh)
  have u7 : (¬ c 7 = true) := fun hh => cl_206 h u1 u0 a0 hh u3 u5
  have u8 : (¬ c 79 = true) := fun hh => cl_103 h u1 u0 a0 u3 u6 hh
  exact cl_37 h u1 u0 a0 u7 u3 u8

private lemma cl_509 {c : ℕ → Bool} (h : MultCore c) : (c 47 = true) → (¬ c 19 = true) → (c 5 = true) → (¬ c 151 = true) → (c 167 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a2)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a2)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a2
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (¬ c 109 = true) := fun hh => cl_43 h u0 a1 a0 hh a4
  have u5 : (¬ c 83 = true) := fun hh => cl_292 h u0 a2 a0 hh
  have u6 : (¬ c 31 = true) := fun hh => cl_390 h u1 u0 a2 hh u4
  have u7 : (¬ c 149 = true) := fun hh => cl_342 h u1 u0 u6 u5 hh
  have u8 : (¬ c 29 = true) := fun hh => cl_68 h u1 u0 a2 hh u6 u3
  have u9 : (¬ c 101 = true) := fun hh => cl_214 h u1 u0 a2 u8 hh a3
  have u10 : (c 23 = true) := Classical.byContradiction (fun hh => cl_410 h u0 a2 u2 hh u8)
  have u11 : (c 97 = true) := Classical.byContradiction (fun hh => cl_23 h u0 a2 u8 hh u9 u7)
  exact cl_238 h u1 u0 a2 u2 u10 u11

private lemma cl_510 {c : ℕ → Bool} (h : MultCore c) : (¬ c 47 = true) → (c 7 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a2)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a2)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a2
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (c 97 = true) := Classical.byContradiction (fun hh => cl_406 h u1 u0 a2 u2 a0 hh)
  have u5 : (c 13 = true) := Classical.byContradiction (fun hh => cl_222 h u1 u0 a2 a1 hh a0)
  have u6 : (¬ c 23 = true) := fun hh => cl_238 h u1 u0 a2 u2 hh u4
  have u7 : (¬ c 109 = true) := fun hh => cl_312 h u1 u0 u5 hh
  have u8 : (c 29 = true) := Classical.byContradiction (fun hh => cl_410 h u0 a2 u2 u6 hh)
  have u9 : (¬ c 31 = true) := fun hh => cl_390 h u1 u0 a2 hh u7
  exact cl_68 h u1 u0 a2 u8 u9 u3

private lemma cl_511 {c : ℕ → Bool} (h : MultCore c) : (c 167 = true) → (c 197 = true) → (c 337 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (¬ c 151 = true) := fun hh => cl_506 h hh a0 a2 a1 a3
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_508 h hh a0 a1 a3)
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh u1)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u2 u1)
  have u4 : (¬ c 11 = true) := fun hh => cl_490 h hh u2 u1
  have u5 : (c 7 = true) := Classical.byContradiction (fun hh => cl_491 h hh u2 u1 a1)
  have u6 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u3 u2 hh)
  have u7 : (c 17 = true) := Classical.byContradiction (fun hh => cl_124 h u3 u2 u1 u5 u4 hh u6)
  have u8 : (c 47 = true) := Classical.byContradiction (fun hh => cl_510 h hh u5 u1)
  have u9 : (¬ c 83 = true) := fun hh => cl_292 h u2 u1 u8 hh
  have u10 : (c 19 = true) := Classical.byContradiction (fun hh => cl_509 h u8 hh u1 u0 a0)
  have u11 : (c 23 = true) := Classical.byContradiction (fun hh => cl_426 h u2 u1 u10 hh)
  have u12 : (¬ c 31 = true) := fun hh => cl_6 h u2 u4 u7 u10 hh a0
  have u13 : (¬ c 97 = true) := fun hh => cl_238 h u3 u2 u1 u4 u11 hh
  have u14 : (¬ c 149 = true) := fun hh => cl_342 h u3 u2 u12 u9 hh
  have u15 : (¬ c 29 = true) := fun hh => cl_68 h u3 u2 u1 hh u12 u6
  have u16 : (c 101 = true) := Classical.byContradiction (fun hh => cl_23 h u2 u1 u15 u13 hh u14)
  exact cl_214 h u3 u2 u1 u15 u16 u0

private lemma cl_512 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → (¬ c 167 = true) → (c 197 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a0)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a0)
  have u2 : (c 7 = true) := Classical.byContradiction (fun hh => cl_491 h hh u0 a0 a2)
  exact cl_164 h u1 u0 a0 u2 a1

private lemma cl_513 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (c 3 = true) → (¬ c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (¬ c 5 = true) := fun hh => cl_512 h hh a2 a3
  have u1 : (¬ c 11 = true) := fun hh => cl_507 h hh a0 a1 u0 a3
  have u2 : (c 17 = true) := Classical.byContradiction (fun hh => cl_441 h a0 a1 u0 u1 hh)
  have u3 : (¬ c 19 = true) := fun hh => cl_505 h u1 hh a0 a1 u0 a4
  have u4 : (¬ c 37 = true) := fun hh => cl_143 h a1 u0 u2 hh a4
  have u5 : (c 31 = true) := Classical.byContradiction (fun hh => cl_187 h a0 a1 u0 u3 hh a2)
  have u6 : (¬ c 7 = true) := fun hh => cl_206 h a0 a1 u0 hh u2 u4
  exact cl_198 h a0 u0 u6 u5

private lemma cl_514 {c : ℕ → Bool} (h : MultCore c) : (¬ c 7 = true) → (¬ c 73 = true) → (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 41 = true) → (c 197 = true) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have u0 : (¬ c 11 = true) := fun hh => cl_484 h hh a2 a3 a4
  have u1 : (¬ c 23 = true) := fun hh => cl_227 h a2 a3 a4 a0 u0 hh
  have u2 : (¬ c 29 = true) := fun hh => cl_323 h a2 a3 a4 a0 hh a6
  have u3 : (c 19 = true) := Classical.byContradiction (fun hh => cl_255 h a2 a3 u0 hh u1 a5 a1)
  exact cl_432 h a2 a3 u0 u3 u2

private lemma cl_515 {c : ℕ → Bool} (h : MultCore c) : (c 7 = true) → (¬ c 73 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → (¬ c 2 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (¬ c 17 = true) := fun hh => cl_114 h a5 a2 a3 a0 a4 hh a1
  have u1 : (c 19 = true) := Classical.byContradiction (fun hh => cl_423 h a5 u0 hh a1)
  have u2 : (¬ c 29 = true) := fun hh => cl_346 h a5 a2 a3 a0 u1 hh
  exact cl_432 h a5 a2 a4 u1 u2

private lemma cl_516 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (¬ c 167 = true) → (c 197 = true) → (c 251 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 41 = true) := Classical.byContradiction (fun hh => cl_367 h hh a1)
  have u1 : (¬ c 5 = true) := fun hh => cl_512 h hh a1 a2
  have u2 : (¬ c 2 = true) := fun hh => cl_513 h hh a0 a1 a2 a3
  have u3 : (¬ c 11 = true) := fun hh => cl_484 h hh u2 a0 u1
  have u4 : (¬ c 73 = true) := fun hh => cl_11 h u2 a0 u1 u3 hh a1
  have u5 : (c 7 = true) := Classical.byContradiction (fun hh => cl_514 h hh u4 u2 a0 u1 u0 a2)
  exact cl_515 h u5 u4 a0 u1 u3 u2

private lemma cl_517 {c : ℕ → Bool} (h : MultCore c) : (c 197 = true) → (c 251 = true) → (c 337 = true) → False := by
  intro a0 a1 a2
  have u0 : (¬ c 167 = true) := fun hh => cl_511 h hh a0 a2 a1
  have u1 : (c 41 = true) := Classical.byContradiction (fun hh => cl_367 h hh u0)
  have u2 : (¬ c 5 = true) := fun hh => cl_512 h hh u0 a0
  have u3 : (¬ c 3 = true) := fun hh => cl_516 h hh u0 a0 a1
  have u4 : (c 2 = true) := Classical.byContradiction (fun hh => cl_447 h hh u3 u2)
  have u5 : (c 17 = true) := Classical.byContradiction (fun hh => cl_422 h u4 u3 hh u1)
  have u6 : (c 11 = true) := Classical.byContradiction (fun hh => cl_445 h u4 u3 hh u5)
  exact cl_439 h u4 u3 u2 u6 u5

private lemma cl_518 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → (¬ c 5 = true) → False := by
  intro a0 a1
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_447 h hh a0 a1)
  have u1 : (¬ c 167 = true) := fun hh => cl_482 h a0 a1 hh
  have u2 : (c 41 = true) := Classical.byContradiction (fun hh => cl_367 h hh u1)
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_422 h u0 a0 hh u2)
  have u4 : (c 11 = true) := Classical.byContradiction (fun hh => cl_445 h u0 a0 hh u3)
  exact cl_439 h u0 a0 a1 u4 u3

private lemma cl_519 {c : ℕ → Bool} (h : MultCore c) : (¬ c 17 = true) → (c 11 = true) → (c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (c 73 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (c 7 = true) := Classical.byContradiction (fun hh => cl_121 h a2 a3 a4 hh a1 a0 a5)
  have u1 : (¬ c 79 = true) := fun hh => cl_38 h a2 a3 a4 u0 a0 hh
  have u2 : (c 19 = true) := Classical.byContradiction (fun hh => cl_152 h a2 a3 a4 a1 hh u1)
  have u3 : (¬ c 29 = true) := fun hh => cl_434 h a2 a3 a1 u2 hh
  exact cl_350 h a2 a3 a4 u0 u2 u3

private lemma cl_520 {c : ℕ → Bool} (h : MultCore c) : (c 11 = true) → (c 2 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_518 h hh a2)
  have u1 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h a1 u0 hh)
  have u2 : (¬ c 17 = true) := fun hh => cl_446 h a1 u0 a0 hh
  exact cl_519 h u2 a0 a1 u0 a2 u1

private lemma cl_521 {c : ℕ → Bool} (h : MultCore c) : (c 2 = true) → (¬ c 5 = true) → (c 251 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_518 h hh a1)
  have u1 : (¬ c 11 = true) := fun hh => cl_520 h hh a0 a1
  have u2 : (c 17 = true) := Classical.byContradiction (fun hh => cl_441 h a0 u0 a1 u1 hh)
  have u3 : (¬ c 19 = true) := fun hh => cl_505 h u1 hh a0 u0 a1 a2
  have u4 : (¬ c 37 = true) := fun hh => cl_143 h u0 a1 u2 hh a2
  have u5 : (c 47 = true) := Classical.byContradiction (fun hh => cl_315 h u0 a1 u2 u3 hh)
  have u6 : (¬ c 7 = true) := fun hh => cl_206 h a0 u0 a1 hh u2 u4
  have u7 : (¬ c 79 = true) := fun hh => cl_103 h a0 u0 a1 u2 u5 hh
  exact cl_37 h a0 u0 a1 u6 u2 u7

private lemma cl_522 {c : ℕ → Bool} (h : MultCore c) : (¬ c 19 = true) → (¬ c 23 = true) → (¬ c 2 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_518 h hh a3)
  have u1 : (¬ c 11 = true) := fun hh => cl_484 h hh a2 u0 a3
  have u2 : (¬ c 167 = true) := fun hh => cl_495 h a0 a2 u0 a3 hh
  have u3 : (c 41 = true) := Classical.byContradiction (fun hh => cl_367 h hh u2)
  have u4 : (¬ c 73 = true) := fun hh => cl_11 h a2 u0 a3 u1 hh u2
  exact cl_255 h a2 u0 u1 a0 a1 u3 u4

private lemma cl_523 {c : ℕ → Bool} (h : MultCore c) : (¬ c 7 = true) → (c 17 = true) → (¬ c 2 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_518 h hh a3)
  have u1 : (¬ c 11 = true) := fun hh => cl_484 h hh a2 u0 a3
  have u2 : (¬ c 23 = true) := fun hh => cl_227 h a2 u0 a3 a0 u1 hh
  have u3 : (¬ c 61 = true) := fun hh => cl_333 h a2 u0 a3 a0 u2 hh
  have u4 : (c 19 = true) := Classical.byContradiction (fun hh => cl_522 h hh u2 a2 a3)
  have u5 : (¬ c 131 = true) := fun hh => cl_248 h a2 u0 u1 u4 hh
  exact cl_82 h u0 a3 a0 a1 u4 u3 u5

private lemma cl_524 {c : ℕ → Bool} (h : MultCore c) : (c 17 = true) → (¬ c 2 = true) → (¬ c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_518 h hh a2)
  have u1 : (¬ c 11 = true) := fun hh => cl_484 h hh a1 u0 a2
  have u2 : (c 7 = true) := Classical.byContradiction (fun hh => cl_523 h hh a0 a1 a2)
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_515 h u2 hh u0 a2 u1 a1)
  have u4 : (c 167 = true) := Classical.byContradiction (fun hh => cl_11 h a1 u0 a2 u1 u3 hh)
  have u5 : (¬ c 19 = true) := fun hh => cl_424 h a1 a0 hh u3
  exact cl_495 h u5 a1 u0 a2 u4

private lemma cl_525 {c : ℕ → Bool} (h : MultCore c) : (c 7 = true) → (¬ c 2 = true) → (c 3 = true) → (¬ c 5 = true) → (¬ c 11 = true) → False := by
  intro a0 a1 a2 a3 a4
  have u0 : (c 73 = true) := Classical.byContradiction (fun hh => cl_515 h a0 hh a2 a3 a4 a1)
  have u1 : (c 167 = true) := Classical.byContradiction (fun hh => cl_11 h a1 a2 a3 a4 u0 hh)
  have u2 : (c 19 = true) := Classical.byContradiction (fun hh => cl_495 h hh a1 a2 a3 u1)
  have u3 : (¬ c 29 = true) := fun hh => cl_346 h a1 a2 a3 a0 u2 hh
  exact cl_432 h a1 a2 a4 u2 u3

private lemma cl_526 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → (¬ c 5 = true) → (c 3 = true) → False := by
  intro a0 a1 a2
  have u0 : (¬ c 11 = true) := fun hh => cl_484 h hh a0 a2 a1
  have u1 : (¬ c 17 = true) := fun hh => cl_524 h hh a0 a1
  have u2 : (c 61 = true) := Classical.byContradiction (fun hh => cl_376 h a0 u1 hh)
  have u3 : (¬ c 7 = true) := fun hh => cl_525 h hh a0 a2 a1 u0
  have u4 : (¬ c 23 = true) := fun hh => cl_227 h a0 a2 a1 u3 u0 hh
  exact cl_333 h a0 a2 a1 u3 u4 u2

private lemma cl_527 {c : ℕ → Bool} (h : MultCore c) : (¬ c 5 = true) → (c 251 = true) → False := by
  intro a0 a1
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_518 h hh a0)
  have u1 : (¬ c 2 = true) := fun hh => cl_521 h hh a0 a1
  exact cl_526 h u1 a0 u0

private lemma cl_528 {c : ℕ → Bool} (h : MultCore c) : (¬ c 23 = true) → (¬ c 17 = true) → (c 5 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a2)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a2)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a2
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (¬ c 19 = true) := fun hh => cl_426 h u0 a2 hh a0
  have u5 : (c 41 = true) := Classical.byContradiction (fun hh => cl_263 h u1 u0 u2 u4 a0 hh u3)
  have u6 : (c 89 = true) := Classical.byContradiction (fun hh => cl_366 h u1 u0 a2 a1 a0 hh)
  have u7 : (¬ c 43 = true) := fun hh => cl_169 h u1 a1 u4 hh a3
  exact cl_420 h u1 u5 u7 u6

private lemma cl_529 {c : ℕ → Bool} (h : MultCore c) : (c 23 = true) → (¬ c 7 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a2)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a2)
  have u2 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u3 : (¬ c 59 = true) := fun hh => cl_414 h u1 a2 a1 a0 hh
  have u4 : (c 61 = true) := Classical.byContradiction (fun hh => cl_337 h u1 u0 a2 a1 a0 hh)
  exact cl_246 h u1 u0 a2 u3 u4 u2

private lemma cl_530 {c : ℕ → Bool} (h : MultCore c) : (¬ c 23 = true) → (c 5 = true) → (¬ c 197 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a1)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a1)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a1
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (¬ c 19 = true) := fun hh => cl_426 h u0 a1 hh a0
  have u5 : (c 29 = true) := Classical.byContradiction (fun hh => cl_410 h u0 a1 u2 a0 hh)
  have u6 : (c 17 = true) := Classical.byContradiction (fun hh => cl_528 h a0 hh a1 a2)
  have u7 : (c 167 = true) := Classical.byContradiction (fun hh => cl_96 h u1 u0 u6 u4 a0 hh)
  have u8 : (c 31 = true) := Classical.byContradiction (fun hh => cl_68 h u1 u0 a1 u5 hh u3)
  have u9 : (¬ c 109 = true) := fun hh => cl_60 h u1 u0 a1 u6 a0 hh u7
  exact cl_390 h u1 u0 a1 u8 u9

private lemma cl_531 {c : ℕ → Bool} (h : MultCore c) : (¬ c 59 = true) → (c 17 = true) → (¬ c 97 = true) → (c 5 = true) → False := by
  intro a0 a1 a2 a3
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a3)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a3)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a3
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (¬ c 61 = true) := fun hh => cl_246 h u1 u0 a3 a0 hh u3
  have u5 : (¬ c 29 = true) := fun hh => cl_195 h u1 a3 u2 hh a0 a2
  exact cl_281 h u1 u0 a3 u2 a1 u5 u4

private lemma cl_532 {c : ℕ → Bool} (h : MultCore c) : (c 251 = true) → (c 337 = true) → False := by
  intro a0 a1
  have u0 : (¬ c 197 = true) := fun hh => cl_517 h hh a0 a1
  have u1 : (c 5 = true) := Classical.byContradiction (fun hh => cl_527 h hh a0)
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh u1)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u2 u1)
  have u4 : (¬ c 11 = true) := fun hh => cl_490 h hh u2 u1
  have u5 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u3 u2 hh)
  have u6 : (c 23 = true) := Classical.byContradiction (fun hh => cl_530 h hh u1 u0)
  have u7 : (¬ c 97 = true) := fun hh => cl_238 h u3 u2 u1 u4 u6 hh
  have u8 : (c 7 = true) := Classical.byContradiction (fun hh => cl_529 h u6 hh u1)
  have u9 : (c 47 = true) := Classical.byContradiction (fun hh => cl_406 h u3 u2 u1 u4 hh u7)
  have u10 : (c 167 = true) := Classical.byContradiction (fun hh => cl_164 h u3 u2 u1 u8 hh)
  have u11 : (c 17 = true) := Classical.byContradiction (fun hh => cl_124 h u3 u2 u1 u8 u4 hh u5)
  have u12 : (¬ c 83 = true) := fun hh => cl_292 h u2 u1 u9 hh
  have u13 : (c 59 = true) := Classical.byContradiction (fun hh => cl_531 h hh u11 u7 u1)
  have u14 : (¬ c 151 = true) := fun hh => cl_290 h u3 u2 u1 u11 u13 hh
  have u15 : (c 19 = true) := Classical.byContradiction (fun hh => cl_509 h u9 hh u1 u14 u10)
  have u16 : (¬ c 31 = true) := fun hh => cl_6 h u2 u4 u11 u15 hh u10
  have u17 : (¬ c 29 = true) := fun hh => cl_68 h u3 u2 u1 hh u16 u5
  have u18 : (¬ c 149 = true) := fun hh => cl_342 h u3 u2 u16 u12 hh
  have u19 : (¬ c 101 = true) := fun hh => cl_214 h u3 u2 u1 u17 hh u14
  exact cl_23 h u2 u1 u17 u7 u19 u18

private lemma cl_533 {c : ℕ → Bool} (h : MultCore c) : (c 23 = true) → (c 17 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a2)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a2)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a2
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (¬ c 97 = true) := fun hh => cl_238 h u1 u0 a2 u2 a0 hh
  have u5 : (c 7 = true) := Classical.byContradiction (fun hh => cl_529 h a0 hh a2)
  have u6 : (c 47 = true) := Classical.byContradiction (fun hh => cl_406 h u1 u0 a2 u2 hh u4)
  have u7 : (c 59 = true) := Classical.byContradiction (fun hh => cl_531 h hh a1 u4 a2)
  have u8 : (c 167 = true) := Classical.byContradiction (fun hh => cl_164 h u1 u0 a2 u5 hh)
  have u9 : (¬ c 83 = true) := fun hh => cl_292 h u0 a2 u6 hh
  have u10 : (¬ c 151 = true) := fun hh => cl_290 h u1 u0 a2 a1 u7 hh
  have u11 : (c 19 = true) := Classical.byContradiction (fun hh => cl_509 h u6 hh a2 u10 u8)
  have u12 : (¬ c 31 = true) := fun hh => cl_6 h u0 u2 a1 u11 hh u8
  have u13 : (¬ c 29 = true) := fun hh => cl_68 h u1 u0 a2 hh u12 u3
  have u14 : (¬ c 149 = true) := fun hh => cl_342 h u1 u0 u12 u9 hh
  have u15 : (¬ c 101 = true) := fun hh => cl_214 h u1 u0 a2 u13 hh u10
  exact cl_23 h u0 a2 u13 u4 u15 u14

private lemma cl_534 {c : ℕ → Bool} (h : MultCore c) : (c 17 = true) → (c 5 = true) → False := by
  intro a0 a1
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a1)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh u0 a1)
  have u2 : (¬ c 11 = true) := fun hh => cl_490 h hh u0 a1
  have u3 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u1 u0 hh)
  have u4 : (¬ c 23 = true) := fun hh => cl_533 h hh a0 a1
  have u5 : (¬ c 19 = true) := fun hh => cl_426 h u0 a1 hh u4
  have u6 : (c 29 = true) := Classical.byContradiction (fun hh => cl_410 h u0 a1 u2 u4 hh)
  have u7 : (c 167 = true) := Classical.byContradiction (fun hh => cl_96 h u1 u0 a0 u5 u4 hh)
  have u8 : (c 31 = true) := Classical.byContradiction (fun hh => cl_68 h u1 u0 a1 u6 hh u3)
  have u9 : (¬ c 109 = true) := fun hh => cl_60 h u1 u0 a1 a0 u4 hh u7
  exact cl_390 h u1 u0 a1 u8 u9

private lemma cl_535 {c : ℕ → Bool} (h : MultCore c) : (¬ c 7 = true) → (c 3 = true) → (c 5 = true) → False := by
  intro a0 a1 a2
  have u0 : (¬ c 197 = true) := fun hh => cl_491 h a0 a1 a2 hh
  have u1 : (¬ c 23 = true) := fun hh => cl_529 h hh a0 a2
  exact cl_530 h u1 a2 u0

private lemma cl_536 {c : ℕ → Bool} (h : MultCore c) : (¬ c 17 = true) → (c 73 = true) → (c 2 = true) → (c 3 = true) → (c 5 = true) → (¬ c 11 = true) → False := by
  intro a0 a1 a2 a3 a4 a5
  have u0 : (¬ c 7 = true) := fun hh => cl_124 h a2 a3 a4 hh a5 a0 a1
  exact cl_535 h u0 a3 a4

private lemma cl_537 {c : ℕ → Bool} (h : MultCore c) : (c 3 = true) → (c 5 = true) → False := by
  intro a0 a1
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_448 h hh a0 a1)
  have u1 : (¬ c 11 = true) := fun hh => cl_490 h hh a0 a1
  have u2 : (c 73 = true) := Classical.byContradiction (fun hh => cl_378 h u0 a0 hh)
  have u3 : (¬ c 17 = true) := fun hh => cl_534 h hh a1
  exact cl_536 h u3 u2 u0 a0 a1 u1

private lemma cl_538 {c : ℕ → Bool} (h : MultCore c) : (c 5 = true) → False := by
  intro a0
  have u0 : (c 3 = true) := Classical.byContradiction (fun hh => cl_503 h hh a0)
  exact cl_537 h u0 a0

private lemma cl_539 {c : ℕ → Bool} (h : MultCore c) : (¬ c 3 = true) → False := by
  intro a0
  have u0 : (¬ c 5 = true) := fun hh => cl_538 h hh
  exact cl_518 h a0 u0

private lemma cl_540 {c : ℕ → Bool} (h : MultCore c) : (¬ c 2 = true) → False := by
  intro a0
  have u0 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u1 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  exact cl_526 h a0 u0 u1

private lemma cl_541 {c : ℕ → Bool} (h : MultCore c) : (¬ c 73 = true) → False := by
  intro a0
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u1 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  exact cl_378 h u0 u1 a0

private lemma cl_542 {c : ℕ → Bool} (h : MultCore c) : (c 11 = true) → False := by
  intro a0
  have u0 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  exact cl_520 h a0 u0 u1

private lemma cl_543 {c : ℕ → Bool} (h : MultCore c) : (c 113 = true) → False := by
  intro a0
  have u0 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  exact cl_319 h u3 u2 u1 u0 a0

private lemma cl_544 {c : ℕ → Bool} (h : MultCore c) : (c 59 = true) → False := by
  intro a0
  have u0 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  exact cl_430 h u3 u2 u1 u0 a0

private lemma cl_545 {c : ℕ → Bool} (h : MultCore c) : (¬ c 17 = true) → False := by
  intro a0
  have u0 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  exact cl_441 h u3 u2 u1 u0 a0

private lemma cl_546 {c : ℕ → Bool} (h : MultCore c) : (c 79 = true) → False := by
  intro a0
  have u0 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u2 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  have u3 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u4 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u5 : (¬ c 19 = true) := fun hh => cl_151 h u1 u3 u4 u0 hh a0
  have u6 : (¬ c 47 = true) := fun hh => cl_103 h u1 u3 u4 u2 hh a0
  exact cl_315 h u3 u4 u2 u5 u6

private lemma cl_547 {c : ℕ → Bool} (h : MultCore c) : (¬ c 7 = true) → False := by
  intro a0
  have u0 : (¬ c 79 = true) := fun hh => cl_546 h hh
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  exact cl_37 h u1 u2 u3 a0 u4 u0

private lemma cl_548 {c : ℕ → Bool} (h : MultCore c) : (¬ c 37 = true) → False := by
  intro a0
  have u0 : (c 7 = true) := Classical.byContradiction (fun hh => cl_547 h hh)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  exact cl_206 h u1 u2 u3 u0 u4 a0

private lemma cl_549 {c : ℕ → Bool} (h : MultCore c) : (c 19 = true) → False := by
  intro a0
  have u0 : (¬ c 113 = true) := fun hh => cl_543 h hh
  have u1 : (c 7 = true) := Classical.byContradiction (fun hh => cl_547 h hh)
  have u2 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u3 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  have u5 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u6 : (c 29 = true) := Classical.byContradiction (fun hh => cl_350 h u5 u3 u2 u1 a0 hh)
  have u7 : (¬ c 83 = true) := fun hh => cl_357 h u5 u3 u2 a0 hh u0
  have u8 : (¬ c 197 = true) := fun hh => cl_327 h u5 u3 u2 u1 u6 hh
  have u9 : (c 43 = true) := Classical.byContradiction (fun hh => cl_371 h u5 u3 u2 hh u7)
  exact cl_172 h u5 u4 a0 u9 u8

private lemma cl_550 {c : ℕ → Bool} (h : MultCore c) : (¬ c 47 = true) → False := by
  intro a0
  have u0 : (¬ c 19 = true) := fun hh => cl_549 h hh
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  exact cl_315 h u2 u1 u3 u0 a0

private lemma cl_551 {c : ℕ → Bool} (h : MultCore c) : (¬ c 23 = true) → False := by
  intro a0
  have u0 : (c 47 = true) := Classical.byContradiction (fun hh => cl_550 h hh)
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u3 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u4 : (¬ c 113 = true) := fun hh => cl_543 h hh
  exact cl_383 h u2 u1 u3 a0 u0 u4

private lemma cl_552 {c : ℕ → Bool} (h : MultCore c) : (c 41 = true) → False := by
  intro a0
  have u0 : (c 23 = true) := Classical.byContradiction (fun hh => cl_551 h hh)
  have u1 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u2 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u4 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  have u5 : (c 37 = true) := Classical.byContradiction (fun hh => cl_548 h hh)
  exact cl_306 h u3 u1 u2 u4 u0 u5 a0

private lemma cl_553 {c : ℕ → Bool} (h : MultCore c) : (¬ c 167 = true) → False := by
  intro a0
  have u0 : (¬ c 41 = true) := fun hh => cl_552 h hh
  exact cl_367 h u0 a0

private lemma cl_554 {c : ℕ → Bool} (h : MultCore c) : (¬ c 97 = true) → False := by
  intro a0
  have u0 : (¬ c 41 = true) := fun hh => cl_552 h hh
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u2 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u3 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  have u4 : (c 47 = true) := Classical.byContradiction (fun hh => cl_550 h hh)
  exact cl_138 h u1 u2 u3 u0 u4 a0

private lemma cl_555 {c : ℕ → Bool} (h : MultCore c) : (c 109 = true) → False := by
  intro a0
  have u0 : (c 167 = true) := Classical.byContradiction (fun hh => cl_553 h hh)
  have u1 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u2 : (c 47 = true) := Classical.byContradiction (fun hh => cl_550 h hh)
  have u3 : (¬ c 19 = true) := fun hh => cl_549 h hh
  exact cl_43 h u1 u3 u2 a0 u0

private lemma cl_556 {c : ℕ → Bool} (h : MultCore c) : (¬ c 29 = true) → False := by
  intro a0
  have u0 : (c 97 = true) := Classical.byContradiction (fun hh => cl_554 h hh)
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u3 : (¬ c 59 = true) := fun hh => cl_544 h hh
  have u4 : (¬ c 11 = true) := fun hh => cl_542 h hh
  exact cl_193 h u2 u1 u4 a0 u3 u0

private lemma cl_557 {c : ℕ → Bool} (h : MultCore c) : (c 197 = true) → False := by
  intro a0
  have u0 : (c 29 = true) := Classical.byContradiction (fun hh => cl_556 h hh)
  have u1 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u4 : (c 7 = true) := Classical.byContradiction (fun hh => cl_547 h hh)
  exact cl_327 h u3 u2 u1 u4 u0 a0

private lemma cl_558 {c : ℕ → Bool} (h : MultCore c) : (c 61 = true) → False := by
  intro a0
  have u0 : (c 29 = true) := Classical.byContradiction (fun hh => cl_556 h hh)
  have u1 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u2 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u3 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u4 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u5 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  exact cl_279 h u1 u2 u3 u4 u5 u0 a0

private lemma cl_559 {c : ℕ → Bool} (h : MultCore c) : (c 337 = true) → False := by
  intro a0
  have u0 : (c 17 = true) := Classical.byContradiction (fun hh => cl_545 h hh)
  have u1 : (c 97 = true) := Classical.byContradiction (fun hh => cl_554 h hh)
  have u2 : (c 29 = true) := Classical.byContradiction (fun hh => cl_556 h hh)
  have u3 : (¬ c 11 = true) := fun hh => cl_542 h hh
  have u4 : (¬ c 19 = true) := fun hh => cl_549 h hh
  have u5 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u6 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u7 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  have u8 : (¬ c 251 = true) := fun hh => cl_532 h hh a0
  have u9 : (¬ c 149 = true) := fun hh => cl_160 h u6 u7 u0 u2 hh u8
  have u10 : (c 101 = true) := Classical.byContradiction (fun hh => cl_22 h u7 u5 u2 u1 hh u9)
  have u11 : (c 151 = true) := Classical.byContradiction (fun hh => cl_213 h u6 u7 u5 u2 u10 hh)
  have u12 : (¬ c 83 = true) := fun hh => cl_498 h u3 hh u6 u7 u5 u11
  have u13 : (¬ c 131 = true) := fun hh => cl_131 h u6 u7 u5 u4 hh u11
  exact cl_108 h u6 u7 u12 u13 a0

private lemma cl_560 {c : ℕ → Bool} (h : MultCore c) : False := by
  have u0 : (¬ c 5 = true) := fun hh => cl_538 h hh
  have u1 : (¬ c 337 = true) := fun hh => cl_559 h hh
  have u2 : (c 2 = true) := Classical.byContradiction (fun hh => cl_540 h hh)
  have u3 : (c 23 = true) := Classical.byContradiction (fun hh => cl_551 h hh)
  have u4 : (c 29 = true) := Classical.byContradiction (fun hh => cl_556 h hh)
  have u5 : (c 3 = true) := Classical.byContradiction (fun hh => cl_539 h hh)
  exact cl_179 h u2 u5 u0 u3 u4 u1


private lemma monochromatic_cube_collision {c : ℕ → Bool}
    (hc : ∀ i, IsSidon ((fun a : ℕ => a ^ 3) '' {n | 0 < n ∧ c n = i}))
    (a b d e : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e)
    (heq : a ^ 3 + b ^ 3 = d ^ 3 + e ^ 3)
    (had : a ^ 3 ≠ d ^ 3) (hae : a ^ 3 ≠ e ^ 3) :
    ¬ (c a = c b ∧ c a = c d ∧ c a = c e) := by
  rintro ⟨hcb, hcd, hce⟩
  have h := hc (c a) _ ⟨a, ⟨ha, rfl⟩, rfl⟩
    _ ⟨d, ⟨hd, hcd.symm⟩, rfl⟩ _ ⟨b, ⟨hb, hcb.symm⟩, rfl⟩
    _ ⟨e, ⟨he, hce.symm⟩, rfl⟩ heq
  rcases h with h | h
  · exact had h.1
  · exact hae h.1

private lemma xor_cancel (a b : Bool) : Bool.xor a (Bool.xor a b) = b := by
  cases a <;> cases b <;> rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma no_multiplicative_bool_cube_coloring (c : ℕ → Bool)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a * b) = Bool.xor (c a) (c b)) :
    ¬ (∀ i, IsSidon ((fun a : ℕ => a ^ 3) '' {n | 0 < n ∧ c n = i})) := by
  intro hc
  have hf_1 : c 1 = false := by
    simpa only [one_mul, Bool.xor_self] using hmul 1 1 (by norm_num) (by norm_num)
  have hf_4 : c 4 = (Bool.xor (c 2) (c 2)) := by
    have h := hmul 2 2 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_6 : c 6 = (Bool.xor (c 2) (c 3)) := by
    have h := hmul 2 3 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_8 : c 8 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 2)))) := by
    have h := hmul 2 4 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_4] using h
  have hf_9 : c 9 = (Bool.xor (c 3) (c 3)) := by
    have h := hmul 3 3 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_10 : c 10 = (Bool.xor (c 2) (c 5)) := by
    have h := hmul 2 5 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_12 : c 12 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 3)))) := by
    have h := hmul 2 6 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_6] using h
  have hf_14 : c 14 = (Bool.xor (c 2) (c 7)) := by
    have h := hmul 2 7 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_15 : c 15 = (Bool.xor (c 3) (c 5)) := by
    have h := hmul 3 5 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_16 : c 16 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 2)))))) := by
    have h := hmul 2 8 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_8] using h
  have hf_18 : c 18 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 3)))) := by
    have h := hmul 2 9 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_9] using h
  have hf_20 : c 20 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 5)))) := by
    have h := hmul 2 10 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_10] using h
  have hf_21 : c 21 = (Bool.xor (c 3) (c 7)) := by
    have h := hmul 3 7 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_22 : c 22 = (Bool.xor (c 2) (c 11)) := by
    have h := hmul 2 11 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_24 : c 24 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 3)))))) := by
    have h := hmul 2 12 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_12] using h
  have hf_25 : c 25 = (Bool.xor (c 5) (c 5)) := by
    have h := hmul 5 5 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_27 : c 27 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))) := by
    have h := hmul 3 9 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_9] using h
  have hf_28 : c 28 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 7)))) := by
    have h := hmul 2 14 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_14] using h
  have hf_30 : c 30 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 5)))) := by
    have h := hmul 2 15 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_15] using h
  have hf_32 : c 32 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 2)))))))) := by
    have h := hmul 2 16 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_16] using h
  have hf_33 : c 33 = (Bool.xor (c 3) (c 11)) := by
    have h := hmul 3 11 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_34 : c 34 = (Bool.xor (c 2) (c 17)) := by
    have h := hmul 2 17 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_35 : c 35 = (Bool.xor (c 5) (c 7)) := by
    have h := hmul 5 7 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_36 : c 36 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 3)))))) := by
    have h := hmul 2 18 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_18] using h
  have hf_38 : c 38 = (Bool.xor (c 2) (c 19)) := by
    have h := hmul 2 19 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_39 : c 39 = (Bool.xor (c 3) (c 13)) := by
    have h := hmul 3 13 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_40 : c 40 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 5)))))) := by
    have h := hmul 2 20 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_20] using h
  have hf_42 : c 42 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 7)))) := by
    have h := hmul 2 21 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_21] using h
  have hf_44 : c 44 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 11)))) := by
    have h := hmul 2 22 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_22] using h
  have hf_45 : c 45 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 5)))) := by
    have h := hmul 3 15 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_15] using h
  have hf_46 : c 46 = (Bool.xor (c 2) (c 23)) := by
    have h := hmul 2 23 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_48 : c 48 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 3)))))))) := by
    have h := hmul 2 24 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_24] using h
  have hf_49 : c 49 = (Bool.xor (c 7) (c 7)) := by
    have h := hmul 7 7 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_50 : c 50 = (Bool.xor (c 2) ((Bool.xor (c 5) (c 5)))) := by
    have h := hmul 2 25 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_25] using h
  have hf_51 : c 51 = (Bool.xor (c 3) (c 17)) := by
    have h := hmul 3 17 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_54 : c 54 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))) := by
    have h := hmul 2 27 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_27] using h
  have hf_55 : c 55 = (Bool.xor (c 5) (c 11)) := by
    have h := hmul 5 11 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_56 : c 56 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 7)))))) := by
    have h := hmul 2 28 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_28] using h
  have hf_57 : c 57 = (Bool.xor (c 3) (c 19)) := by
    have h := hmul 3 19 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_58 : c 58 = (Bool.xor (c 2) (c 29)) := by
    have h := hmul 2 29 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_60 : c 60 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 5)))))) := by
    have h := hmul 2 30 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_30] using h
  have hf_62 : c 62 = (Bool.xor (c 2) (c 31)) := by
    have h := hmul 2 31 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_63 : c 63 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 7)))) := by
    have h := hmul 3 21 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_21] using h
  have hf_64 : c 64 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 2)))))))))) := by
    have h := hmul 2 32 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_32] using h
  have hf_65 : c 65 = (Bool.xor (c 5) (c 13)) := by
    have h := hmul 5 13 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_66 : c 66 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 11)))) := by
    have h := hmul 2 33 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_33] using h
  have hf_68 : c 68 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 17)))) := by
    have h := hmul 2 34 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_34] using h
  have hf_69 : c 69 = (Bool.xor (c 3) (c 23)) := by
    have h := hmul 3 23 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_70 : c 70 = (Bool.xor (c 2) ((Bool.xor (c 5) (c 7)))) := by
    have h := hmul 2 35 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_35] using h
  have hf_72 : c 72 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 3)))))))) := by
    have h := hmul 2 36 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_36] using h
  have hf_75 : c 75 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 5)))) := by
    have h := hmul 3 25 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_25] using h
  have hf_76 : c 76 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 19)))) := by
    have h := hmul 2 38 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_38] using h
  have hf_78 : c 78 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 13)))) := by
    have h := hmul 2 39 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_39] using h
  have hf_80 : c 80 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 5)))))))) := by
    have h := hmul 2 40 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_40] using h
  have hf_81 : c 81 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))) := by
    have h := hmul 3 27 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_27] using h
  have hf_82 : c 82 = (Bool.xor (c 2) (c 41)) := by
    have h := hmul 2 41 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_84 : c 84 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 7)))))) := by
    have h := hmul 2 42 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_42] using h
  have hf_85 : c 85 = (Bool.xor (c 5) (c 17)) := by
    have h := hmul 5 17 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_86 : c 86 = (Bool.xor (c 2) (c 43)) := by
    have h := hmul 2 43 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_87 : c 87 = (Bool.xor (c 3) (c 29)) := by
    have h := hmul 3 29 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_88 : c 88 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 11)))))) := by
    have h := hmul 2 44 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_44] using h
  have hf_90 : c 90 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 5)))))) := by
    have h := hmul 2 45 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_45] using h
  have hf_91 : c 91 = (Bool.xor (c 7) (c 13)) := by
    have h := hmul 7 13 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_92 : c 92 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 23)))) := by
    have h := hmul 2 46 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_46] using h
  have hf_93 : c 93 = (Bool.xor (c 3) (c 31)) := by
    have h := hmul 3 31 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_94 : c 94 = (Bool.xor (c 2) (c 47)) := by
    have h := hmul 2 47 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_95 : c 95 = (Bool.xor (c 5) (c 19)) := by
    have h := hmul 5 19 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_96 : c 96 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 3)))))))))) := by
    have h := hmul 2 48 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_48] using h
  have hf_98 : c 98 = (Bool.xor (c 2) ((Bool.xor (c 7) (c 7)))) := by
    have h := hmul 2 49 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_49] using h
  have hf_99 : c 99 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 11)))) := by
    have h := hmul 3 33 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_33] using h
  have hf_100 : c 100 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 5) (c 5)))))) := by
    have h := hmul 2 50 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_50] using h
  have hf_102 : c 102 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 17)))) := by
    have h := hmul 2 51 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_51] using h
  have hf_105 : c 105 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 7)))) := by
    have h := hmul 3 35 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_35] using h
  have hf_108 : c 108 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))))) := by
    have h := hmul 2 54 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_54] using h
  have hf_110 : c 110 = (Bool.xor (c 2) ((Bool.xor (c 5) (c 11)))) := by
    have h := hmul 2 55 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_55] using h
  have hf_111 : c 111 = (Bool.xor (c 3) (c 37)) := by
    have h := hmul 3 37 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_112 : c 112 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 7)))))))) := by
    have h := hmul 2 56 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_56] using h
  have hf_114 : c 114 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 19)))) := by
    have h := hmul 2 57 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_57] using h
  have hf_115 : c 115 = (Bool.xor (c 5) (c 23)) := by
    have h := hmul 5 23 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_116 : c 116 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 29)))) := by
    have h := hmul 2 58 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_58] using h
  have hf_118 : c 118 = (Bool.xor (c 2) (c 59)) := by
    have h := hmul 2 59 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_119 : c 119 = (Bool.xor (c 7) (c 17)) := by
    have h := hmul 7 17 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_120 : c 120 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 5)))))))) := by
    have h := hmul 2 60 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_60] using h
  have hf_121 : c 121 = (Bool.xor (c 11) (c 11)) := by
    have h := hmul 11 11 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_122 : c 122 = (Bool.xor (c 2) (c 61)) := by
    have h := hmul 2 61 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_123 : c 123 = (Bool.xor (c 3) (c 41)) := by
    have h := hmul 3 41 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_124 : c 124 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 31)))) := by
    have h := hmul 2 62 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_62] using h
  have hf_125 : c 125 = (Bool.xor (c 5) ((Bool.xor (c 5) (c 5)))) := by
    have h := hmul 5 25 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_25] using h
  have hf_126 : c 126 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 7)))))) := by
    have h := hmul 2 63 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_63] using h
  have hf_129 : c 129 = (Bool.xor (c 3) (c 43)) := by
    have h := hmul 3 43 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_130 : c 130 = (Bool.xor (c 2) ((Bool.xor (c 5) (c 13)))) := by
    have h := hmul 2 65 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_65] using h
  have hf_132 : c 132 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 11)))))) := by
    have h := hmul 2 66 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_66] using h
  have hf_133 : c 133 = (Bool.xor (c 7) (c 19)) := by
    have h := hmul 7 19 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_135 : c 135 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 5)))))) := by
    have h := hmul 3 45 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_45] using h
  have hf_138 : c 138 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 23)))) := by
    have h := hmul 2 69 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_69] using h
  have hf_140 : c 140 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 5) (c 7)))))) := by
    have h := hmul 2 70 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_70] using h
  have hf_141 : c 141 = (Bool.xor (c 3) (c 47)) := by
    have h := hmul 3 47 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_144 : c 144 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 3)))))))))) := by
    have h := hmul 2 72 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_72] using h
  have hf_145 : c 145 = (Bool.xor (c 5) (c 29)) := by
    have h := hmul 5 29 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_146 : c 146 = (Bool.xor (c 2) (c 73)) := by
    have h := hmul 2 73 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_147 : c 147 = (Bool.xor (c 3) ((Bool.xor (c 7) (c 7)))) := by
    have h := hmul 3 49 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_49] using h
  have hf_150 : c 150 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 5)))))) := by
    have h := hmul 2 75 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_75] using h
  have hf_152 : c 152 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 19)))))) := by
    have h := hmul 2 76 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_76] using h
  have hf_153 : c 153 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 17)))) := by
    have h := hmul 3 51 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_51] using h
  have hf_156 : c 156 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 13)))))) := by
    have h := hmul 2 78 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_78] using h
  have hf_158 : c 158 = (Bool.xor (c 2) (c 79)) := by
    have h := hmul 2 79 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_162 : c 162 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))))) := by
    have h := hmul 2 81 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_81] using h
  have hf_164 : c 164 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 41)))) := by
    have h := hmul 2 82 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_82] using h
  have hf_165 : c 165 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 11)))) := by
    have h := hmul 3 55 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_55] using h
  have hf_166 : c 166 = (Bool.xor (c 2) (c 83)) := by
    have h := hmul 2 83 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_169 : c 169 = (Bool.xor (c 13) (c 13)) := by
    have h := hmul 13 13 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_171 : c 171 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 19)))) := by
    have h := hmul 3 57 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_57] using h
  have hf_172 : c 172 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 43)))) := by
    have h := hmul 2 86 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_86] using h
  have hf_174 : c 174 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 29)))) := by
    have h := hmul 2 87 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_87] using h
  have hf_176 : c 176 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 11)))))))) := by
    have h := hmul 2 88 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_88] using h
  have hf_177 : c 177 = (Bool.xor (c 3) (c 59)) := by
    have h := hmul 3 59 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_178 : c 178 = (Bool.xor (c 2) (c 89)) := by
    have h := hmul 2 89 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_180 : c 180 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 5)))))))) := by
    have h := hmul 2 90 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_90] using h
  have hf_183 : c 183 = (Bool.xor (c 3) (c 61)) := by
    have h := hmul 3 61 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_185 : c 185 = (Bool.xor (c 5) (c 37)) := by
    have h := hmul 5 37 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_187 : c 187 = (Bool.xor (c 11) (c 17)) := by
    have h := hmul 11 17 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_188 : c 188 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 47)))) := by
    have h := hmul 2 94 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_94] using h
  have hf_189 : c 189 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 7)))))) := by
    have h := hmul 3 63 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_63] using h
  have hf_192 : c 192 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 3)))))))))))) := by
    have h := hmul 2 96 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_96] using h
  have hf_194 : c 194 = (Bool.xor (c 2) (c 97)) := by
    have h := hmul 2 97 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_196 : c 196 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 7) (c 7)))))) := by
    have h := hmul 2 98 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_98] using h
  have hf_198 : c 198 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 11)))))) := by
    have h := hmul 2 99 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_99] using h
  have hf_204 : c 204 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 17)))))) := by
    have h := hmul 2 102 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_102] using h
  have hf_207 : c 207 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 23)))) := by
    have h := hmul 3 69 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_69] using h
  have hf_209 : c 209 = (Bool.xor (c 11) (c 19)) := by
    have h := hmul 11 19 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_210 : c 210 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 7)))))) := by
    have h := hmul 2 105 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_105] using h
  have hf_216 : c 216 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))))))) := by
    have h := hmul 2 108 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_108] using h
  have hf_218 : c 218 = (Bool.xor (c 2) (c 109)) := by
    have h := hmul 2 109 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_219 : c 219 = (Bool.xor (c 3) (c 73)) := by
    have h := hmul 3 73 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_220 : c 220 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 5) (c 11)))))) := by
    have h := hmul 2 110 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_110] using h
  have hf_224 : c 224 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 7)))))))))) := by
    have h := hmul 2 112 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_112] using h
  have hf_225 : c 225 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 5)))))) := by
    have h := hmul 3 75 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_75] using h
  have hf_226 : c 226 = (Bool.xor (c 2) (c 113)) := by
    have h := hmul 2 113 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_228 : c 228 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 19)))))) := by
    have h := hmul 2 114 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_114] using h
  have hf_235 : c 235 = (Bool.xor (c 5) (c 47)) := by
    have h := hmul 5 47 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_236 : c 236 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 59)))) := by
    have h := hmul 2 118 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_118] using h
  have hf_237 : c 237 = (Bool.xor (c 3) (c 79)) := by
    have h := hmul 3 79 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_238 : c 238 = (Bool.xor (c 2) ((Bool.xor (c 7) (c 17)))) := by
    have h := hmul 2 119 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_119] using h
  have hf_240 : c 240 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 5)))))))))) := by
    have h := hmul 2 120 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_120] using h
  have hf_243 : c 243 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))))) := by
    have h := hmul 3 81 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_81] using h
  have hf_244 : c 244 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 61)))) := by
    have h := hmul 2 122 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_122] using h
  have hf_246 : c 246 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 41)))) := by
    have h := hmul 2 123 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_123] using h
  have hf_248 : c 248 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 31)))))) := by
    have h := hmul 2 124 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_124] using h
  have hf_249 : c 249 = (Bool.xor (c 3) (c 83)) := by
    have h := hmul 3 83 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_252 : c 252 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 7)))))))) := by
    have h := hmul 2 126 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_126] using h
  have hf_255 : c 255 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 17)))) := by
    have h := hmul 3 85 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_85] using h
  have hf_262 : c 262 = (Bool.xor (c 2) (c 131)) := by
    have h := hmul 2 131 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_264 : c 264 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 11)))))))) := by
    have h := hmul 2 132 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_132] using h
  have hf_270 : c 270 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 5)))))))) := by
    have h := hmul 2 135 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_135] using h
  have hf_273 : c 273 = (Bool.xor (c 3) ((Bool.xor (c 7) (c 13)))) := by
    have h := hmul 3 91 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_91] using h
  have hf_275 : c 275 = (Bool.xor (c 5) ((Bool.xor (c 5) (c 11)))) := by
    have h := hmul 5 55 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_55] using h
  have hf_276 : c 276 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 23)))))) := by
    have h := hmul 2 138 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_138] using h
  have hf_280 : c 280 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 5) (c 7)))))))) := by
    have h := hmul 2 140 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_140] using h
  have hf_282 : c 282 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 47)))) := by
    have h := hmul 2 141 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_141] using h
  have hf_285 : c 285 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 19)))) := by
    have h := hmul 3 95 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_95] using h
  have hf_290 : c 290 = (Bool.xor (c 2) ((Bool.xor (c 5) (c 29)))) := by
    have h := hmul 2 145 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_145] using h
  have hf_295 : c 295 = (Bool.xor (c 5) (c 59)) := by
    have h := hmul 5 59 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_298 : c 298 = (Bool.xor (c 2) (c 149)) := by
    have h := hmul 2 149 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_300 : c 300 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 5)))))))) := by
    have h := hmul 2 150 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_150] using h
  have hf_302 : c 302 = (Bool.xor (c 2) (c 151)) := by
    have h := hmul 2 151 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_303 : c 303 = (Bool.xor (c 3) (c 101)) := by
    have h := hmul 3 101 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_306 : c 306 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 17)))))) := by
    have h := hmul 2 153 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_153] using h
  have hf_315 : c 315 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 7)))))) := by
    have h := hmul 3 105 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_105] using h
  have hf_319 : c 319 = (Bool.xor (c 11) (c 29)) := by
    have h := hmul 11 29 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_323 : c 323 = (Bool.xor (c 17) (c 19)) := by
    have h := hmul 17 19 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_324 : c 324 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 3)))))))))) := by
    have h := hmul 2 162 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_162] using h
  have hf_332 : c 332 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 83)))) := by
    have h := hmul 2 166 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_166] using h
  have hf_333 : c 333 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 37)))) := by
    have h := hmul 3 111 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_111] using h
  have hf_334 : c 334 = (Bool.xor (c 2) (c 167)) := by
    have h := hmul 2 167 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_342 : c 342 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 19)))))) := by
    have h := hmul 2 171 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_171] using h
  have hf_343 : c 343 = (Bool.xor (c 7) ((Bool.xor (c 7) (c 7)))) := by
    have h := hmul 7 49 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_49] using h
  have hf_344 : c 344 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 43)))))) := by
    have h := hmul 2 172 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_172] using h
  have hf_345 : c 345 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 23)))) := by
    have h := hmul 3 115 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_115] using h
  have hf_348 : c 348 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) (c 29)))))) := by
    have h := hmul 2 174 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_174] using h
  have hf_352 : c 352 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 11)))))))))) := by
    have h := hmul 2 176 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_176] using h
  have hf_365 : c 365 = (Bool.xor (c 5) (c 73)) := by
    have h := hmul 5 73 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_374 : c 374 = (Bool.xor (c 2) ((Bool.xor (c 11) (c 17)))) := by
    have h := hmul 2 187 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_187] using h
  have hf_375 : c 375 = (Bool.xor (c 3) ((Bool.xor (c 5) ((Bool.xor (c 5) (c 5)))))) := by
    have h := hmul 3 125 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_125] using h
  have hf_376 : c 376 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 47)))))) := by
    have h := hmul 2 188 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_188] using h
  have hf_393 : c 393 = (Bool.xor (c 3) (c 131)) := by
    have h := hmul 3 131 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_396 : c 396 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 11)))))))) := by
    have h := hmul 2 198 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_198] using h
  have hf_399 : c 399 = (Bool.xor (c 3) ((Bool.xor (c 7) (c 19)))) := by
    have h := hmul 3 133 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_133] using h
  have hf_405 : c 405 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 5)))))))) := by
    have h := hmul 3 135 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_135] using h
  have hf_414 : c 414 = (Bool.xor (c 2) ((Bool.xor (c 3) ((Bool.xor (c 3) (c 23)))))) := by
    have h := hmul 2 207 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_207] using h
  have hf_423 : c 423 = (Bool.xor (c 3) ((Bool.xor (c 3) (c 47)))) := by
    have h := hmul 3 141 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_141] using h
  have hf_425 : c 425 = (Bool.xor (c 5) ((Bool.xor (c 5) (c 17)))) := by
    have h := hmul 5 85 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_85] using h
  have hf_427 : c 427 = (Bool.xor (c 7) (c 61)) := by
    have h := hmul 7 61 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_435 : c 435 = (Bool.xor (c 3) ((Bool.xor (c 5) (c 29)))) := by
    have h := hmul 3 145 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_145] using h
  have hf_436 : c 436 = (Bool.xor (c 2) ((Bool.xor (c 2) (c 109)))) := by
    have h := hmul 2 218 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_218] using h
  have hf_438 : c 438 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 73)))) := by
    have h := hmul 2 219 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_219] using h
  have hf_447 : c 447 = (Bool.xor (c 3) (c 149)) := by
    have h := hmul 3 149 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_448 : c 448 = (Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) ((Bool.xor (c 2) (c 7)))))))))))) := by
    have h := hmul 2 224 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_224] using h
  have hf_474 : c 474 = (Bool.xor (c 2) ((Bool.xor (c 3) (c 79)))) := by
    have h := hmul 2 237 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_237] using h
  have hf_485 : c 485 = (Bool.xor (c 5) (c 97)) := by
    have h := hmul 5 97 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_495 : c 495 = (Bool.xor (c 3) ((Bool.xor (c 3) ((Bool.xor (c 5) (c 11)))))) := by
    have h := hmul 3 165 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    simpa only [hf_165] using h
  have hf_501 : c 501 = (Bool.xor (c 3) (c 167)) := by
    have h := hmul 3 167 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have hf_527 : c 527 = (Bool.xor (c 17) (c 31)) := by
    have h := hmul 17 31 (by norm_num) (by norm_num)
    norm_num only [Nat.reduceMul] at h
    exact h
  have he_0 := monochromatic_cube_collision hc 501 275 527 57
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_501, hf_275, hf_527, hf_57] at he_0
  have he_1 := monochromatic_cube_collision hc 495 1 438 334
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_495, hf_1, hf_438, hf_334] at he_1
  have he_2 := monochromatic_cube_collision hc 447 303 485 145
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_447, hf_303, hf_485, hf_145] at he_2
  have he_3 := monochromatic_cube_collision hc 448 255 474 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_448, hf_255, hf_474] at he_3
  have he_4 := monochromatic_cube_collision hc 423 228 436 167
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_423, hf_228, hf_436] at he_4
  have he_5 := monochromatic_cube_collision hc 414 255 436 167
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_414, hf_255, hf_436] at he_5
  have he_6 := monochromatic_cube_collision hc 438 62 435 125
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_438, hf_62, hf_435, hf_125] at he_6
  have he_7 := monochromatic_cube_collision hc 425 151 352 332
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_425, hf_352, hf_332] at he_7
  have he_8 := monochromatic_cube_collision hc 399 255 427 131
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_399, hf_255, hf_427] at he_8
  have he_9 := monochromatic_cube_collision hc 334 323 414 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_334, hf_323, hf_414] at he_9
  have he_10 := monochromatic_cube_collision hc 376 237 405 34
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_376, hf_237, hf_405, hf_34] at he_10
  have he_11 := monochromatic_cube_collision hc 393 166 337 300
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_393, hf_166, hf_300] at he_11
  have he_12 := monochromatic_cube_collision hc 365 238 396 21
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_365, hf_238, hf_396, hf_21] at he_12
  have he_13 := monochromatic_cube_collision hc 324 302 393 95
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_324, hf_302, hf_393, hf_95] at he_13
  have he_14 := monochromatic_cube_collision hc 376 41 374 97
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_376, hf_374] at he_14
  have he_15 := monochromatic_cube_collision hc 375 17 333 251
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_375, hf_333] at he_15
  have he_16 := monochromatic_cube_collision hc 285 275 342 158
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_285, hf_275, hf_342, hf_158] at he_16
  have he_17 := monochromatic_cube_collision hc 298 251 348 51
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_298, hf_348, hf_51] at he_17
  have he_18 := monochromatic_cube_collision hc 343 105 334 162
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_343, hf_105, hf_334, hf_162] at he_18
  have he_19 := monochromatic_cube_collision hc 344 86 323 197
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_344, hf_86, hf_323] at he_19
  have he_20 := monochromatic_cube_collision hc 345 58 337 144
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_345, hf_58, hf_144] at he_20
  have he_21 := monochromatic_cube_collision hc 285 243 334 62
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_285, hf_243, hf_334, hf_62] at he_21
  have he_22 := monochromatic_cube_collision hc 295 194 319 80
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_295, hf_194, hf_319, hf_80] at he_22
  have he_23 := monochromatic_cube_collision hc 252 248 315 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_252, hf_248, hf_315] at he_23
  have he_24 := monochromatic_cube_collision hc 280 189 306 37
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_280, hf_189, hf_306] at he_24
  have he_25 := monochromatic_cube_collision hc 303 24 290 151
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_303, hf_24, hf_290] at he_25
  have he_26 := monochromatic_cube_collision hc 282 49 273 130
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_282, hf_49, hf_273, hf_130] at he_26
  have he_27 := monochromatic_cube_collision hc 276 99 280 35
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_276, hf_99, hf_280, hf_35] at he_27
  have he_28 := monochromatic_cube_collision hc 275 69 240 194
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_275, hf_69, hf_240, hf_194] at he_28
  have he_29 := monochromatic_cube_collision hc 270 73 244 177
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_270, hf_244, hf_177] at he_29
  have he_30 := monochromatic_cube_collision hc 264 19 262 75
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_264, hf_262, hf_75] at he_30
  have he_31 := monochromatic_cube_collision hc 246 146 209 207
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_246, hf_146, hf_209, hf_207] at he_31
  have he_32 := monochromatic_cube_collision hc 220 183 255 58
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_220, hf_183, hf_255, hf_58] at he_32
  have he_33 := monochromatic_cube_collision hc 236 151 255 18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_236, hf_255, hf_18] at he_33
  have he_34 := monochromatic_cube_collision hc 235 135 249 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_235, hf_135, hf_249, hf_1] at he_34
  have he_35 := monochromatic_cube_collision hc 246 68 207 185
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_246, hf_68, hf_207, hf_185] at he_35
  have he_36 := monochromatic_cube_collision hc 218 169 225 156
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_218, hf_169, hf_225, hf_156] at he_36
  have he_37 := monochromatic_cube_collision hc 204 171 235 80
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_204, hf_171, hf_235, hf_80] at he_37
  have he_38 := monochromatic_cube_collision hc 226 24 225 55
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_226, hf_24, hf_225, hf_55] at he_38
  have he_39 := monochromatic_cube_collision hc 210 116 197 147
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_210, hf_116, hf_147] at he_39
  have he_40 := monochromatic_cube_collision hc 177 167 216 50
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_177, hf_216, hf_50] at he_40
  have he_41 := monochromatic_cube_collision hc 207 14 183 140
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_207, hf_14, hf_183, hf_140] at he_41
  have he_42 := monochromatic_cube_collision hc 166 149 192 93
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_166, hf_192, hf_93] at he_42
  have he_43 := monochromatic_cube_collision hc 174 133 196 45
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_174, hf_133, hf_196, hf_45] at he_43
  have he_44 := monochromatic_cube_collision hc 166 113 180 57
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_166, hf_180, hf_57] at he_44
  have he_45 := monochromatic_cube_collision hc 178 51 162 115
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_178, hf_51, hf_162, hf_115] at he_45
  have he_46 := monochromatic_cube_collision hc 164 64 167 25
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_164, hf_64, hf_25] at he_46
  have he_47 := monochromatic_cube_collision hc 166 32 135 129
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_166, hf_32, hf_135, hf_129] at he_47
  have he_48 := monochromatic_cube_collision hc 152 100 165 27
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_152, hf_100, hf_165, hf_27] at he_48
  have he_49 := monochromatic_cube_collision hc 153 18 122 121
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_153, hf_18, hf_122, hf_121] at he_49
  have he_50 := monochromatic_cube_collision hc 150 1 144 73
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_150, hf_1, hf_144] at he_50
  have he_51 := monochromatic_cube_collision hc 113 55 94 92
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_55, hf_94, hf_92] at he_51
  have he_52 := monochromatic_cube_collision hc 109 62 93 90
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_62, hf_93, hf_90] at he_52
  have he_53 := monochromatic_cube_collision hc 102 23 95 60
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_102, hf_95, hf_60] at he_53
  have he_54 := monochromatic_cube_collision hc 90 66 97 47
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_90, hf_66] at he_54
  have he_55 := monochromatic_cube_collision hc 92 60 99 29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_92, hf_60, hf_99] at he_55
  have he_56 := monochromatic_cube_collision hc 98 35 92 59
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_98, hf_35, hf_92] at he_56
  have he_57 := monochromatic_cube_collision hc 94 23 84 63
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_94, hf_84, hf_63] at he_57
  have he_58 := monochromatic_cube_collision hc 86 41 89 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_86] at he_58
  have he_59 := monochromatic_cube_collision hc 75 64 82 51
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_75, hf_64, hf_82, hf_51] at he_59
  have he_60 := monochromatic_cube_collision hc 73 38 76 17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_38, hf_76] at he_60
  have he_61 := monochromatic_cube_collision hc 76 5 69 48
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_76, hf_69, hf_48] at he_61
  have he_62 := monochromatic_cube_collision hc 59 22 60 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_22, hf_60] at he_62
  have he_63 := monochromatic_cube_collision hc 58 9 57 22
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_58, hf_9, hf_57, hf_22] at he_63
  have he_64 := monochromatic_cube_collision hc 55 17 54 24
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_55, hf_54, hf_24] at he_64
  have he_65 := monochromatic_cube_collision hc 33 16 34 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_33, hf_16, hf_34, hf_9] at he_65
  have he_66 := monochromatic_cube_collision hc 15 9 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_15, hf_9, hf_16] at he_66
  have he_67 := monochromatic_cube_collision hc 10 9 12 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [hf_10, hf_9, hf_12, hf_1] at he_67
  simp only [xor_cancel, Bool.xor_self, Bool.xor_false] at he_0 he_1 he_2 he_3 he_4 he_5 he_6 he_7 he_8 he_9 he_10 he_11 he_12 he_13 he_14 he_15 he_16 he_17 he_18 he_19 he_20 he_21 he_22 he_23 he_24 he_25 he_26 he_27 he_28 he_29 he_30 he_31 he_32 he_33 he_34 he_35 he_36 he_37 he_38 he_39 he_40 he_41 he_42 he_43 he_44 he_45 he_46 he_47 he_48 he_49 he_50 he_51 he_52 he_53 he_54 he_55 he_56 he_57 he_58 he_59 he_60 he_61 he_62 he_63 he_64 he_65 he_66 he_67
  exact cl_560 ({ he_0 := he_0, he_1 := he_1, he_2 := he_2, he_3 := by simpa only [eq_self_iff_true] using he_3, he_4 := he_4, he_5 := he_5, he_6 := he_6, he_7 := he_7, he_8 := he_8, he_9 := he_9, he_10 := he_10, he_11 := he_11, he_12 := he_12, he_13 := he_13, he_14 := he_14, he_15 := he_15, he_16 := he_16, he_17 := he_17, he_18 := he_18, he_19 := by simpa only [eq_self_iff_true] using he_19, he_20 := he_20, he_21 := he_21, he_22 := he_22, he_23 := he_23, he_24 := he_24, he_25 := he_25, he_26 := he_26, he_27 := he_27, he_28 := he_28, he_29 := he_29, he_30 := he_30, he_31 := he_31, he_32 := he_32, he_33 := he_33, he_34 := he_34, he_35 := he_35, he_36 := he_36, he_37 := he_37, he_38 := he_38, he_39 := he_39, he_40 := he_40, he_41 := he_41, he_42 := he_42, he_43 := he_43, he_44 := he_44, he_45 := he_45, he_46 := he_46, he_47 := he_47, he_48 := he_48, he_49 := he_49, he_50 := he_50, he_51 := he_51, he_52 := he_52, he_53 := he_53, he_54 := he_54, he_55 := he_55, he_56 := he_56, he_57 := he_57, he_58 := he_58, he_59 := he_59, he_60 := he_60, he_61 := he_61, he_62 := he_62, he_63 := he_63, he_64 := he_64, he_65 := he_65, he_66 := he_66, he_67 := he_67 } : MultCore c)

private lemma cube_sidon_of_dilation_into {A B : Set ℕ}
    (hB : IsSidon ((fun a : ℕ => a ^ 3) '' B)) {q : ℕ} (hq : 0 < q)
    (hAB : ∀ a ∈ A, q * a ∈ B) : IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ heq
  have heq' : (q * a) ^ 3 + (q * d) ^ 3 = (q * b) ^ 3 + (q * e) ^ 3 := by
    simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q ^ 3 * n) heq
  have h := hB _ ⟨q * a, hAB a ha, rfl⟩ _ ⟨q * b, hAB b hb, rfl⟩
    _ ⟨q * d, hAB d hd, rfl⟩ _ ⟨q * e, hAB e he, rfl⟩ heq'
  simp only [mul_pow] at h
  have hqp : 0 < q ^ 3 := pow_pos hq _
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hqp h₁, Nat.eq_of_mul_eq_mul_left hqp h₂⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hqp h₁, Nat.eq_of_mul_eq_mul_left hqp h₂⟩

lemma multiplicative_bool_kernel_not_cube_sidon (c : ℕ → Bool)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a * b) = Bool.xor (c a) (c b)) :
    ¬ IsSidon ((fun a : ℕ => a ^ 3) '' {n | 0 < n ∧ c n = false}) := by
  classical
  intro hfalse
  apply no_multiplicative_bool_cube_coloring c hmul
  intro i
  cases i with
  | false => exact hfalse
  | true =>
    by_cases hex : ∃ q : ℕ, 0 < q ∧ c q = true
    · obtain ⟨q, hq, hcq⟩ := hex
      apply cube_sidon_of_dilation_into hfalse hq
      intro a ha
      exact ⟨Nat.mul_pos hq ha.1, by simp only [hmul q a hq ha.1, hcq, ha.2, Bool.xor_self]⟩
    · have hemp : {n : ℕ | 0 < n ∧ c n = true} = ∅ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hn => hex ⟨n, hn⟩
      simp only [hemp, Set.image_empty]
      simp [IsSidon]

lemma multiplicative_bool_nonempty_fiber_not_cube_sidon (c : ℕ → Bool)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → c (a * b) = Bool.xor (c a) (c b)) (i : Bool)
    (hne : ∃ q : ℕ, 0 < q ∧ c q = i) :
    ¬ IsSidon ((fun a : ℕ => a ^ 3) '' {n | 0 < n ∧ c n = i}) := by
  cases i with
  | false => exact multiplicative_bool_kernel_not_cube_sidon c hmul
  | true =>
    intro htrue
    obtain ⟨q, hq, hcq⟩ := hne
    apply multiplicative_bool_kernel_not_cube_sidon c hmul
    apply cube_sidon_of_dilation_into htrue hq
    intro a ha
    exact ⟨Nat.mul_pos hq ha.1, by simp only [hmul q a hq ha.1, hcq, ha.2, Bool.xor_false]⟩

end Erdos1206
