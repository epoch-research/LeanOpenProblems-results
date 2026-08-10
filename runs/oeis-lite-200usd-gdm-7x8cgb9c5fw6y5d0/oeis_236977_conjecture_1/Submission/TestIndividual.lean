import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

theorem a_pos_of_exists (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < (n - 1) / 2 + 1)
    (hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)) : a n > 0 := by
  have hk : k ∈ Ico 1 ((n - 1) / 2 + 1) := mem_Ico.2 ⟨hk1, hk2⟩
  have h_le : (if sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) then 1 else 0) ≤ a n := by
    apply single_le_sum (fun i _ => Nat.zero_le _) hk
  rw [hsq] at h_le
  simp only [if_true] at h_le
  exact h_le

theorem sqrt_eq_of_sq (M : ℕ) (r : ℕ) (h : r ^ 2 = M) : sqrt M ^ 2 = M := by
  rw [← h]
  rw [sqrt_eq']

theorem proof_9 : a 9 > 0 :=
  a_pos_of_exists 9 1 (by decide) (by decide) (sqrt_eq_of_sq 4 2 (by decide))

theorem proof_10 : a 10 > 0 :=
  a_pos_of_exists 10 2 (by decide) (by decide) (sqrt_eq_of_sq 4 2 (by decide))

theorem proof_11 : a 11 > 0 :=
  a_pos_of_exists 11 1 (by decide) (by decide) (sqrt_eq_of_sq 4 2 (by decide))

theorem proof_12 : a 12 > 0 :=
  a_pos_of_exists 12 2 (by decide) (by decide) (sqrt_eq_of_sq 4 2 (by decide))

theorem proof_13 : a 13 > 0 :=
  a_pos_of_exists 13 1 (by decide) (by decide) (sqrt_eq_of_sq 4 2 (by decide))

theorem proof_14 : a 14 > 0 :=
  a_pos_of_exists 14 2 (by decide) (by decide) (sqrt_eq_of_sq 4 2 (by decide))

theorem proof_15 : a 15 > 0 :=
  a_pos_of_exists 15 5 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_16 : a 16 > 0 :=
  a_pos_of_exists 16 7 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_17 : a 17 > 0 :=
  a_pos_of_exists 17 5 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_18 : a 18 > 0 :=
  a_pos_of_exists 18 1 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_19 : a 19 > 0 :=
  a_pos_of_exists 19 2 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_20 : a 20 > 0 :=
  a_pos_of_exists 20 4 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_21 : a 21 > 0 :=
  a_pos_of_exists 21 6 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_22 : a 22 > 0 :=
  a_pos_of_exists 22 3 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_23 : a 23 > 0 :=
  a_pos_of_exists 23 3 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_24 : a 24 > 0 :=
  a_pos_of_exists 24 4 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_25 : a 25 > 0 :=
  a_pos_of_exists 25 6 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_26 : a 26 > 0 :=
  a_pos_of_exists 26 6 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_27 : a 27 > 0 :=
  a_pos_of_exists 27 3 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_28 : a 28 > 0 :=
  a_pos_of_exists 28 4 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_29 : a 29 > 0 :=
  a_pos_of_exists 29 12 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_30 : a 30 > 0 :=
  a_pos_of_exists 30 3 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_31 : a 31 > 0 :=
  a_pos_of_exists 31 4 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_32 : a 32 > 0 :=
  a_pos_of_exists 32 14 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_33 : a 33 > 0 :=
  a_pos_of_exists 33 1 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_34 : a 34 > 0 :=
  a_pos_of_exists 34 2 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_35 : a 35 > 0 :=
  a_pos_of_exists 35 1 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_36 : a 36 > 0 :=
  a_pos_of_exists 36 2 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_37 : a 37 > 0 :=
  a_pos_of_exists 37 5 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_38 : a 38 > 0 :=
  a_pos_of_exists 38 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_39 : a 39 > 0 :=
  a_pos_of_exists 39 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_40 : a 40 > 0 :=
  a_pos_of_exists 40 8 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_41 : a 41 > 0 :=
  a_pos_of_exists 41 1 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_42 : a 42 > 0 :=
  a_pos_of_exists 42 2 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_43 : a 43 > 0 :=
  a_pos_of_exists 43 16 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_44 : a 44 > 0 :=
  a_pos_of_exists 44 6 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_45 : a 45 > 0 :=
  a_pos_of_exists 45 5 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_46 : a 46 > 0 :=
  a_pos_of_exists 46 7 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_47 : a 47 > 0 :=
  a_pos_of_exists 47 10 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_48 : a 48 > 0 :=
  a_pos_of_exists 48 8 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_49 : a 49 > 0 :=
  a_pos_of_exists 49 1 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_50 : a 50 > 0 :=
  a_pos_of_exists 50 2 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_51 : a 51 > 0 :=
  a_pos_of_exists 51 17 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_52 : a 52 > 0 :=
  a_pos_of_exists 52 7 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_53 : a 53 > 0 :=
  a_pos_of_exists 53 5 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_54 : a 54 > 0 :=
  a_pos_of_exists 54 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_55 : a 55 > 0 :=
  a_pos_of_exists 55 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_56 : a 56 > 0 :=
  a_pos_of_exists 56 8 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_57 : a 57 > 0 :=
  a_pos_of_exists 57 3 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_58 : a 58 > 0 :=
  a_pos_of_exists 58 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_59 : a 59 > 0 :=
  a_pos_of_exists 59 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_60 : a 60 > 0 :=
  a_pos_of_exists 60 6 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_61 : a 61 > 0 :=
  a_pos_of_exists 61 1 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_62 : a 62 > 0 :=
  a_pos_of_exists 62 2 (by decide) (by decide) (sqrt_eq_of_sq 16 4 (by decide))

theorem proof_63 : a 63 > 0 :=
  a_pos_of_exists 63 7 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_64 : a 64 > 0 :=
  a_pos_of_exists 64 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_65 : a 65 > 0 :=
  a_pos_of_exists 65 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_66 : a 66 > 0 :=
  a_pos_of_exists 66 11 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_67 : a 67 > 0 :=
  a_pos_of_exists 67 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_68 : a 68 > 0 :=
  a_pos_of_exists 68 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_69 : a 69 > 0 :=
  a_pos_of_exists 69 12 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_70 : a 70 > 0 :=
  a_pos_of_exists 70 6 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_71 : a 71 > 0 :=
  a_pos_of_exists 71 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_72 : a 72 > 0 :=
  a_pos_of_exists 72 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_73 : a 73 > 0 :=
  a_pos_of_exists 73 10 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_74 : a 74 > 0 :=
  a_pos_of_exists 74 6 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_75 : a 75 > 0 :=
  a_pos_of_exists 75 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_76 : a 76 > 0 :=
  a_pos_of_exists 76 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_77 : a 77 > 0 :=
  a_pos_of_exists 77 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_78 : a 78 > 0 :=
  a_pos_of_exists 78 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_79 : a 79 > 0 :=
  a_pos_of_exists 79 5 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_80 : a 80 > 0 :=
  a_pos_of_exists 80 16 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_81 : a 81 > 0 :=
  a_pos_of_exists 81 5 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_82 : a 82 > 0 :=
  a_pos_of_exists 82 8 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_83 : a 83 > 0 :=
  a_pos_of_exists 83 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_84 : a 84 > 0 :=
  a_pos_of_exists 84 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_85 : a 85 > 0 :=
  a_pos_of_exists 85 7 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_86 : a 86 > 0 :=
  a_pos_of_exists 86 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_87 : a 87 > 0 :=
  a_pos_of_exists 87 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_88 : a 88 > 0 :=
  a_pos_of_exists 88 7 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_89 : a 89 > 0 :=
  a_pos_of_exists 89 16 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_90 : a 90 > 0 :=
  a_pos_of_exists 90 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_91 : a 91 > 0 :=
  a_pos_of_exists 91 7 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_92 : a 92 > 0 :=
  a_pos_of_exists 92 14 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_93 : a 93 > 0 :=
  a_pos_of_exists 93 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_94 : a 94 > 0 :=
  a_pos_of_exists 94 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_95 : a 95 > 0 :=
  a_pos_of_exists 95 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_96 : a 96 > 0 :=
  a_pos_of_exists 96 16 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_97 : a 97 > 0 :=
  a_pos_of_exists 97 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_98 : a 98 > 0 :=
  a_pos_of_exists 98 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_99 : a 99 > 0 :=
  a_pos_of_exists 99 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_100 : a 100 > 0 :=
  a_pos_of_exists 100 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_101 : a 101 > 0 :=
  a_pos_of_exists 101 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_102 : a 102 > 0 :=
  a_pos_of_exists 102 1 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_103 : a 103 > 0 :=
  a_pos_of_exists 103 2 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_104 : a 104 > 0 :=
  a_pos_of_exists 104 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_105 : a 105 > 0 :=
  a_pos_of_exists 105 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_106 : a 106 > 0 :=
  a_pos_of_exists 106 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_107 : a 107 > 0 :=
  a_pos_of_exists 107 16 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_108 : a 108 > 0 :=
  a_pos_of_exists 108 6 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_109 : a 109 > 0 :=
  a_pos_of_exists 109 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_110 : a 110 > 0 :=
  a_pos_of_exists 110 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_111 : a 111 > 0 :=
  a_pos_of_exists 111 10 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_112 : a 112 > 0 :=
  a_pos_of_exists 112 16 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_113 : a 113 > 0 :=
  a_pos_of_exists 113 5 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_114 : a 114 > 0 :=
  a_pos_of_exists 114 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_115 : a 115 > 0 :=
  a_pos_of_exists 115 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_116 : a 116 > 0 :=
  a_pos_of_exists 116 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_117 : a 117 > 0 :=
  a_pos_of_exists 117 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_118 : a 118 > 0 :=
  a_pos_of_exists 118 10 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_119 : a 119 > 0 :=
  a_pos_of_exists 119 5 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_120 : a 120 > 0 :=
  a_pos_of_exists 120 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_121 : a 121 > 0 :=
  a_pos_of_exists 121 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_122 : a 122 > 0 :=
  a_pos_of_exists 122 8 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_123 : a 123 > 0 :=
  a_pos_of_exists 123 3 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_124 : a 124 > 0 :=
  a_pos_of_exists 124 4 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_125 : a 125 > 0 :=
  a_pos_of_exists 125 13 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_126 : a 126 > 0 :=
  a_pos_of_exists 126 1 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_127 : a 127 > 0 :=
  a_pos_of_exists 127 1 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_128 : a 128 > 0 :=
  a_pos_of_exists 128 2 (by decide) (by decide) (sqrt_eq_of_sq 36 6 (by decide))

theorem proof_129 : a 129 > 0 :=
  a_pos_of_exists 129 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_130 : a 130 > 0 :=
  a_pos_of_exists 130 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_131 : a 131 > 0 :=
  a_pos_of_exists 131 5 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_132 : a 132 > 0 :=
  a_pos_of_exists 132 15 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_133 : a 133 > 0 :=
  a_pos_of_exists 133 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_134 : a 134 > 0 :=
  a_pos_of_exists 134 8 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_135 : a 135 > 0 :=
  a_pos_of_exists 135 10 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_136 : a 136 > 0 :=
  a_pos_of_exists 136 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_137 : a 137 > 0 :=
  a_pos_of_exists 137 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_138 : a 138 > 0 :=
  a_pos_of_exists 138 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_139 : a 139 > 0 :=
  a_pos_of_exists 139 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_140 : a 140 > 0 :=
  a_pos_of_exists 140 12 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_141 : a 141 > 0 :=
  a_pos_of_exists 141 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_142 : a 142 > 0 :=
  a_pos_of_exists 142 17 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_143 : a 143 > 0 :=
  a_pos_of_exists 143 11 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_144 : a 144 > 0 :=
  a_pos_of_exists 144 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_145 : a 145 > 0 :=
  a_pos_of_exists 145 17 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_146 : a 146 > 0 :=
  a_pos_of_exists 146 10 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_147 : a 147 > 0 :=
  a_pos_of_exists 147 27 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_148 : a 148 > 0 :=
  a_pos_of_exists 148 12 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_149 : a 149 > 0 :=
  a_pos_of_exists 149 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_150 : a 150 > 0 :=
  a_pos_of_exists 150 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_151 : a 151 > 0 :=
  a_pos_of_exists 151 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_152 : a 152 > 0 :=
  a_pos_of_exists 152 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_153 : a 153 > 0 :=
  a_pos_of_exists 153 13 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_154 : a 154 > 0 :=
  a_pos_of_exists 154 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_155 : a 155 > 0 :=
  a_pos_of_exists 155 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_156 : a 156 > 0 :=
  a_pos_of_exists 156 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_157 : a 157 > 0 :=
  a_pos_of_exists 157 13 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_158 : a 158 > 0 :=
  a_pos_of_exists 158 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_159 : a 159 > 0 :=
  a_pos_of_exists 159 24 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_160 : a 160 > 0 :=
  a_pos_of_exists 160 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_161 : a 161 > 0 :=
  a_pos_of_exists 161 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_162 : a 162 > 0 :=
  a_pos_of_exists 162 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_163 : a 163 > 0 :=
  a_pos_of_exists 163 15 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_164 : a 164 > 0 :=
  a_pos_of_exists 164 16 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_165 : a 165 > 0 :=
  a_pos_of_exists 165 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_166 : a 166 > 0 :=
  a_pos_of_exists 166 3 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_167 : a 167 > 0 :=
  a_pos_of_exists 167 4 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_168 : a 168 > 0 :=
  a_pos_of_exists 168 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_169 : a 169 > 0 :=
  a_pos_of_exists 169 6 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_170 : a 170 > 0 :=
  a_pos_of_exists 170 10 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_171 : a 171 > 0 :=
  a_pos_of_exists 171 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_172 : a 172 > 0 :=
  a_pos_of_exists 172 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_173 : a 173 > 0 :=
  a_pos_of_exists 173 27 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_174 : a 174 > 0 :=
  a_pos_of_exists 174 29 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_175 : a 175 > 0 :=
  a_pos_of_exists 175 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_176 : a 176 > 0 :=
  a_pos_of_exists 176 14 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_177 : a 177 > 0 :=
  a_pos_of_exists 177 17 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_178 : a 178 > 0 :=
  a_pos_of_exists 178 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_179 : a 179 > 0 :=
  a_pos_of_exists 179 16 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_180 : a 180 > 0 :=
  a_pos_of_exists 180 10 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_181 : a 181 > 0 :=
  a_pos_of_exists 181 13 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_182 : a 182 > 0 :=
  a_pos_of_exists 182 12 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_183 : a 183 > 0 :=
  a_pos_of_exists 183 20 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_184 : a 184 > 0 :=
  a_pos_of_exists 184 13 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_185 : a 185 > 0 :=
  a_pos_of_exists 185 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_186 : a 186 > 0 :=
  a_pos_of_exists 186 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_187 : a 187 > 0 :=
  a_pos_of_exists 187 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_188 : a 188 > 0 :=
  a_pos_of_exists 188 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_189 : a 189 > 0 :=
  a_pos_of_exists 189 21 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_190 : a 190 > 0 :=
  a_pos_of_exists 190 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_191 : a 191 > 0 :=
  a_pos_of_exists 191 41 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_192 : a 192 > 0 :=
  a_pos_of_exists 192 21 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_193 : a 193 > 0 :=
  a_pos_of_exists 193 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_194 : a 194 > 0 :=
  a_pos_of_exists 194 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_195 : a 195 > 0 :=
  a_pos_of_exists 195 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_196 : a 196 > 0 :=
  a_pos_of_exists 196 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_197 : a 197 > 0 :=
  a_pos_of_exists 197 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_198 : a 198 > 0 :=
  a_pos_of_exists 198 1 (by decide) (by decide) (sqrt_eq_of_sq 196 14 (by decide))

theorem proof_199 : a 199 > 0 :=
  a_pos_of_exists 199 2 (by decide) (by decide) (sqrt_eq_of_sq 196 14 (by decide))

theorem proof_200 : a 200 > 0 :=
  a_pos_of_exists 200 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_201 : a 201 > 0 :=
  a_pos_of_exists 201 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_202 : a 202 > 0 :=
  a_pos_of_exists 202 5 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_203 : a 203 > 0 :=
  a_pos_of_exists 203 1 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_204 : a 204 > 0 :=
  a_pos_of_exists 204 2 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_205 : a 205 > 0 :=
  a_pos_of_exists 205 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_206 : a 206 > 0 :=
  a_pos_of_exists 206 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_207 : a 207 > 0 :=
  a_pos_of_exists 207 5 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_208 : a 208 > 0 :=
  a_pos_of_exists 208 14 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_209 : a 209 > 0 :=
  a_pos_of_exists 209 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_210 : a 210 > 0 :=
  a_pos_of_exists 210 8 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_211 : a 211 > 0 :=
  a_pos_of_exists 211 85 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_212 : a 212 > 0 :=
  a_pos_of_exists 212 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_213 : a 213 > 0 :=
  a_pos_of_exists 213 18 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_214 : a 214 > 0 :=
  a_pos_of_exists 214 10 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_215 : a 215 > 0 :=
  a_pos_of_exists 215 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_216 : a 216 > 0 :=
  a_pos_of_exists 216 11 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_217 : a 217 > 0 :=
  a_pos_of_exists 217 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_218 : a 218 > 0 :=
  a_pos_of_exists 218 48 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_219 : a 219 > 0 :=
  a_pos_of_exists 219 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_220 : a 220 > 0 :=
  a_pos_of_exists 220 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_221 : a 221 > 0 :=
  a_pos_of_exists 221 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_222 : a 222 > 0 :=
  a_pos_of_exists 222 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_223 : a 223 > 0 :=
  a_pos_of_exists 223 13 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_224 : a 224 > 0 :=
  a_pos_of_exists 224 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_225 : a 225 > 0 :=
  a_pos_of_exists 225 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_226 : a 226 > 0 :=
  a_pos_of_exists 226 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_227 : a 227 > 0 :=
  a_pos_of_exists 227 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_228 : a 228 > 0 :=
  a_pos_of_exists 228 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_229 : a 229 > 0 :=
  a_pos_of_exists 229 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_230 : a 230 > 0 :=
  a_pos_of_exists 230 35 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_231 : a 231 > 0 :=
  a_pos_of_exists 231 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_232 : a 232 > 0 :=
  a_pos_of_exists 232 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_233 : a 233 > 0 :=
  a_pos_of_exists 233 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_234 : a 234 > 0 :=
  a_pos_of_exists 234 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_235 : a 235 > 0 :=
  a_pos_of_exists 235 19 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_236 : a 236 > 0 :=
  a_pos_of_exists 236 17 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_237 : a 237 > 0 :=
  a_pos_of_exists 237 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_238 : a 238 > 0 :=
  a_pos_of_exists 238 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_239 : a 239 > 0 :=
  a_pos_of_exists 239 21 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_240 : a 240 > 0 :=
  a_pos_of_exists 240 6 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_241 : a 241 > 0 :=
  a_pos_of_exists 241 1 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_242 : a 242 > 0 :=
  a_pos_of_exists 242 2 (by decide) (by decide) (sqrt_eq_of_sq 64 8 (by decide))

theorem proof_243 : a 243 > 0 :=
  a_pos_of_exists 243 15 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_244 : a 244 > 0 :=
  a_pos_of_exists 244 16 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_245 : a 245 > 0 :=
  a_pos_of_exists 245 5 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_246 : a 246 > 0 :=
  a_pos_of_exists 246 3 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_247 : a 247 > 0 :=
  a_pos_of_exists 247 4 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_248 : a 248 > 0 :=
  a_pos_of_exists 248 8 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_249 : a 249 > 0 :=
  a_pos_of_exists 249 6 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_250 : a 250 > 0 :=
  a_pos_of_exists 250 10 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_251 : a 251 > 0 :=
  a_pos_of_exists 251 1 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_252 : a 252 > 0 :=
  a_pos_of_exists 252 2 (by decide) (by decide) (sqrt_eq_of_sq 100 10 (by decide))

theorem proof_253 : a 253 > 0 :=
  a_pos_of_exists 253 19 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_254 : a 254 > 0 :=
  a_pos_of_exists 254 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_255 : a 255 > 0 :=
  a_pos_of_exists 255 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_256 : a 256 > 0 :=
  a_pos_of_exists 256 4 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_257 : a 257 > 0 :=
  a_pos_of_exists 257 17 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_258 : a 258 > 0 :=
  a_pos_of_exists 258 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_259 : a 259 > 0 :=
  a_pos_of_exists 259 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_260 : a 260 > 0 :=
  a_pos_of_exists 260 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_261 : a 261 > 0 :=
  a_pos_of_exists 261 6 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_262 : a 262 > 0 :=
  a_pos_of_exists 262 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_263 : a 263 > 0 :=
  a_pos_of_exists 263 20 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_264 : a 264 > 0 :=
  a_pos_of_exists 264 30 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_265 : a 265 > 0 :=
  a_pos_of_exists 265 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_266 : a 266 > 0 :=
  a_pos_of_exists 266 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_267 : a 267 > 0 :=
  a_pos_of_exists 267 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_268 : a 268 > 0 :=
  a_pos_of_exists 268 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_269 : a 269 > 0 :=
  a_pos_of_exists 269 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_270 : a 270 > 0 :=
  a_pos_of_exists 270 15 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_271 : a 271 > 0 :=
  a_pos_of_exists 271 15 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_272 : a 272 > 0 :=
  a_pos_of_exists 272 16 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_273 : a 273 > 0 :=
  a_pos_of_exists 273 3 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_274 : a 274 > 0 :=
  a_pos_of_exists 274 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_275 : a 275 > 0 :=
  a_pos_of_exists 275 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_276 : a 276 > 0 :=
  a_pos_of_exists 276 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_277 : a 277 > 0 :=
  a_pos_of_exists 277 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_278 : a 278 > 0 :=
  a_pos_of_exists 278 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_279 : a 279 > 0 :=
  a_pos_of_exists 279 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_280 : a 280 > 0 :=
  a_pos_of_exists 280 24 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_281 : a 281 > 0 :=
  a_pos_of_exists 281 6 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_282 : a 282 > 0 :=
  a_pos_of_exists 282 27 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_283 : a 283 > 0 :=
  a_pos_of_exists 283 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_284 : a 284 > 0 :=
  a_pos_of_exists 284 34 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_285 : a 285 > 0 :=
  a_pos_of_exists 285 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_286 : a 286 > 0 :=
  a_pos_of_exists 286 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_287 : a 287 > 0 :=
  a_pos_of_exists 287 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_288 : a 288 > 0 :=
  a_pos_of_exists 288 16 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_289 : a 289 > 0 :=
  a_pos_of_exists 289 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_290 : a 290 > 0 :=
  a_pos_of_exists 290 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_291 : a 291 > 0 :=
  a_pos_of_exists 291 16 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_292 : a 292 > 0 :=
  a_pos_of_exists 292 20 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_293 : a 293 > 0 :=
  a_pos_of_exists 293 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_294 : a 294 > 0 :=
  a_pos_of_exists 294 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_295 : a 295 > 0 :=
  a_pos_of_exists 295 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_296 : a 296 > 0 :=
  a_pos_of_exists 296 24 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_297 : a 297 > 0 :=
  a_pos_of_exists 297 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_298 : a 298 > 0 :=
  a_pos_of_exists 298 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_299 : a 299 > 0 :=
  a_pos_of_exists 299 23 (by decide) (by decide) (sqrt_eq_of_sq 1936 44 (by decide))

theorem proof_300 : a 300 > 0 :=
  a_pos_of_exists 300 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_301 : a 301 > 0 :=
  a_pos_of_exists 301 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_302 : a 302 > 0 :=
  a_pos_of_exists 302 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_303 : a 303 > 0 :=
  a_pos_of_exists 303 51 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_304 : a 304 > 0 :=
  a_pos_of_exists 304 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_305 : a 305 > 0 :=
  a_pos_of_exists 305 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_306 : a 306 > 0 :=
  a_pos_of_exists 306 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_307 : a 307 > 0 :=
  a_pos_of_exists 307 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_308 : a 308 > 0 :=
  a_pos_of_exists 308 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_309 : a 309 > 0 :=
  a_pos_of_exists 309 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_310 : a 310 > 0 :=
  a_pos_of_exists 310 37 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_311 : a 311 > 0 :=
  a_pos_of_exists 311 9 (by decide) (by decide) (sqrt_eq_of_sq 900 30 (by decide))

theorem proof_312 : a 312 > 0 :=
  a_pos_of_exists 312 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_313 : a 313 > 0 :=
  a_pos_of_exists 313 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_314 : a 314 > 0 :=
  a_pos_of_exists 314 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_315 : a 315 > 0 :=
  a_pos_of_exists 315 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_316 : a 316 > 0 :=
  a_pos_of_exists 316 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_317 : a 317 > 0 :=
  a_pos_of_exists 317 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_318 : a 318 > 0 :=
  a_pos_of_exists 318 15 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_319 : a 319 > 0 :=
  a_pos_of_exists 319 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_320 : a 320 > 0 :=
  a_pos_of_exists 320 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_321 : a 321 > 0 :=
  a_pos_of_exists 321 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_322 : a 322 > 0 :=
  a_pos_of_exists 322 19 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_323 : a 323 > 0 :=
  a_pos_of_exists 323 3 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_324 : a 324 > 0 :=
  a_pos_of_exists 324 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_325 : a 325 > 0 :=
  a_pos_of_exists 325 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_326 : a 326 > 0 :=
  a_pos_of_exists 326 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_327 : a 327 > 0 :=
  a_pos_of_exists 327 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_328 : a 328 > 0 :=
  a_pos_of_exists 328 32 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_329 : a 329 > 0 :=
  a_pos_of_exists 329 3 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_330 : a 330 > 0 :=
  a_pos_of_exists 330 4 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_331 : a 331 > 0 :=
  a_pos_of_exists 331 65 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_332 : a 332 > 0 :=
  a_pos_of_exists 332 6 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_333 : a 333 > 0 :=
  a_pos_of_exists 333 30 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_334 : a 334 > 0 :=
  a_pos_of_exists 334 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_335 : a 335 > 0 :=
  a_pos_of_exists 335 15 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_336 : a 336 > 0 :=
  a_pos_of_exists 336 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_337 : a 337 > 0 :=
  a_pos_of_exists 337 13 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_338 : a 338 > 0 :=
  a_pos_of_exists 338 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_339 : a 339 > 0 :=
  a_pos_of_exists 339 11 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_340 : a 340 > 0 :=
  a_pos_of_exists 340 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_341 : a 341 > 0 :=
  a_pos_of_exists 341 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_342 : a 342 > 0 :=
  a_pos_of_exists 342 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_343 : a 343 > 0 :=
  a_pos_of_exists 343 3 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_344 : a 344 > 0 :=
  a_pos_of_exists 344 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_345 : a 345 > 0 :=
  a_pos_of_exists 345 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_346 : a 346 > 0 :=
  a_pos_of_exists 346 6 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_347 : a 347 > 0 :=
  a_pos_of_exists 347 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_348 : a 348 > 0 :=
  a_pos_of_exists 348 58 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_349 : a 349 > 0 :=
  a_pos_of_exists 349 34 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_350 : a 350 > 0 :=
  a_pos_of_exists 350 7 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_351 : a 351 > 0 :=
  a_pos_of_exists 351 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_352 : a 352 > 0 :=
  a_pos_of_exists 352 9 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_353 : a 353 > 0 :=
  a_pos_of_exists 353 27 (by decide) (by decide) (sqrt_eq_of_sq 2916 54 (by decide))

theorem proof_354 : a 354 > 0 :=
  a_pos_of_exists 354 13 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_355 : a 355 > 0 :=
  a_pos_of_exists 355 13 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_356 : a 356 > 0 :=
  a_pos_of_exists 356 16 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_357 : a 357 > 0 :=
  a_pos_of_exists 357 14 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_358 : a 358 > 0 :=
  a_pos_of_exists 358 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_359 : a 359 > 0 :=
  a_pos_of_exists 359 19 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_360 : a 360 > 0 :=
  a_pos_of_exists 360 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_361 : a 361 > 0 :=
  a_pos_of_exists 361 18 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_362 : a 362 > 0 :=
  a_pos_of_exists 362 21 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_363 : a 363 > 0 :=
  a_pos_of_exists 363 11 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_364 : a 364 > 0 :=
  a_pos_of_exists 364 24 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_365 : a 365 > 0 :=
  a_pos_of_exists 365 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_366 : a 366 > 0 :=
  a_pos_of_exists 366 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_367 : a 367 > 0 :=
  a_pos_of_exists 367 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_368 : a 368 > 0 :=
  a_pos_of_exists 368 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_369 : a 369 > 0 :=
  a_pos_of_exists 369 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_370 : a 370 > 0 :=
  a_pos_of_exists 370 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_371 : a 371 > 0 :=
  a_pos_of_exists 371 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_372 : a 372 > 0 :=
  a_pos_of_exists 372 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_373 : a 373 > 0 :=
  a_pos_of_exists 373 117 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_374 : a 374 > 0 :=
  a_pos_of_exists 374 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_375 : a 375 > 0 :=
  a_pos_of_exists 375 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_376 : a 376 > 0 :=
  a_pos_of_exists 376 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_377 : a 377 > 0 :=
  a_pos_of_exists 377 29 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_378 : a 378 > 0 :=
  a_pos_of_exists 378 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_379 : a 379 > 0 :=
  a_pos_of_exists 379 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_380 : a 380 > 0 :=
  a_pos_of_exists 380 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_381 : a 381 > 0 :=
  a_pos_of_exists 381 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_382 : a 382 > 0 :=
  a_pos_of_exists 382 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_383 : a 383 > 0 :=
  a_pos_of_exists 383 26 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_384 : a 384 > 0 :=
  a_pos_of_exists 384 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_385 : a 385 > 0 :=
  a_pos_of_exists 385 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_386 : a 386 > 0 :=
  a_pos_of_exists 386 35 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_387 : a 387 > 0 :=
  a_pos_of_exists 387 3 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_388 : a 388 > 0 :=
  a_pos_of_exists 388 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_389 : a 389 > 0 :=
  a_pos_of_exists 389 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_390 : a 390 > 0 :=
  a_pos_of_exists 390 6 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_391 : a 391 > 0 :=
  a_pos_of_exists 391 13 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_392 : a 392 > 0 :=
  a_pos_of_exists 392 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_393 : a 393 > 0 :=
  a_pos_of_exists 393 36 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_394 : a 394 > 0 :=
  a_pos_of_exists 394 19 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_395 : a 395 > 0 :=
  a_pos_of_exists 395 1 (by decide) (by decide) (sqrt_eq_of_sq 196 14 (by decide))

theorem proof_396 : a 396 > 0 :=
  a_pos_of_exists 396 2 (by decide) (by decide) (sqrt_eq_of_sq 196 14 (by decide))

theorem proof_397 : a 397 > 0 :=
  a_pos_of_exists 397 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_398 : a 398 > 0 :=
  a_pos_of_exists 398 34 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_399 : a 399 > 0 :=
  a_pos_of_exists 399 5 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_400 : a 400 > 0 :=
  a_pos_of_exists 400 16 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_401 : a 401 > 0 :=
  a_pos_of_exists 401 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_402 : a 402 > 0 :=
  a_pos_of_exists 402 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_403 : a 403 > 0 :=
  a_pos_of_exists 403 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_404 : a 404 > 0 :=
  a_pos_of_exists 404 10 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_405 : a 405 > 0 :=
  a_pos_of_exists 405 30 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_406 : a 406 > 0 :=
  a_pos_of_exists 406 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_407 : a 407 > 0 :=
  a_pos_of_exists 407 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_408 : a 408 > 0 :=
  a_pos_of_exists 408 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_409 : a 409 > 0 :=
  a_pos_of_exists 409 8 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_410 : a 410 > 0 :=
  a_pos_of_exists 410 6 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_411 : a 411 > 0 :=
  a_pos_of_exists 411 3 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_412 : a 412 > 0 :=
  a_pos_of_exists 412 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_413 : a 413 > 0 :=
  a_pos_of_exists 413 12 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_414 : a 414 > 0 :=
  a_pos_of_exists 414 6 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_415 : a 415 > 0 :=
  a_pos_of_exists 415 41 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_416 : a 416 > 0 :=
  a_pos_of_exists 416 28 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_417 : a 417 > 0 :=
  a_pos_of_exists 417 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_418 : a 418 > 0 :=
  a_pos_of_exists 418 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_419 : a 419 > 0 :=
  a_pos_of_exists 419 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_420 : a 420 > 0 :=
  a_pos_of_exists 420 16 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_421 : a 421 > 0 :=
  a_pos_of_exists 421 11 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_422 : a 422 > 0 :=
  a_pos_of_exists 422 22 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_423 : a 423 > 0 :=
  a_pos_of_exists 423 15 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_424 : a 424 > 0 :=
  a_pos_of_exists 424 16 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_425 : a 425 > 0 :=
  a_pos_of_exists 425 22 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_426 : a 426 > 0 :=
  a_pos_of_exists 426 32 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_427 : a 427 > 0 :=
  a_pos_of_exists 427 7 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_428 : a 428 > 0 :=
  a_pos_of_exists 428 20 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_429 : a 429 > 0 :=
  a_pos_of_exists 429 9 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_430 : a 430 > 0 :=
  a_pos_of_exists 430 42 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_431 : a 431 > 0 :=
  a_pos_of_exists 431 27 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_432 : a 432 > 0 :=
  a_pos_of_exists 432 22 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_433 : a 433 > 0 :=
  a_pos_of_exists 433 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_434 : a 434 > 0 :=
  a_pos_of_exists 434 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_435 : a 435 > 0 :=
  a_pos_of_exists 435 27 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_436 : a 436 > 0 :=
  a_pos_of_exists 436 96 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_437 : a 437 > 0 :=
  a_pos_of_exists 437 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_438 : a 438 > 0 :=
  a_pos_of_exists 438 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_439 : a 439 > 0 :=
  a_pos_of_exists 439 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_440 : a 440 > 0 :=
  a_pos_of_exists 440 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_441 : a 441 > 0 :=
  a_pos_of_exists 441 40 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_442 : a 442 > 0 :=
  a_pos_of_exists 442 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_443 : a 443 > 0 :=
  a_pos_of_exists 443 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_444 : a 444 > 0 :=
  a_pos_of_exists 444 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_445 : a 445 > 0 :=
  a_pos_of_exists 445 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_446 : a 446 > 0 :=
  a_pos_of_exists 446 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_447 : a 447 > 0 :=
  a_pos_of_exists 447 105 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_448 : a 448 > 0 :=
  a_pos_of_exists 448 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_449 : a 449 > 0 :=
  a_pos_of_exists 449 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_450 : a 450 > 0 :=
  a_pos_of_exists 450 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_451 : a 451 > 0 :=
  a_pos_of_exists 451 11 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_452 : a 452 > 0 :=
  a_pos_of_exists 452 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_453 : a 453 > 0 :=
  a_pos_of_exists 453 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_454 : a 454 > 0 :=
  a_pos_of_exists 454 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_455 : a 455 > 0 :=
  a_pos_of_exists 455 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_456 : a 456 > 0 :=
  a_pos_of_exists 456 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_457 : a 457 > 0 :=
  a_pos_of_exists 457 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_458 : a 458 > 0 :=
  a_pos_of_exists 458 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_459 : a 459 > 0 :=
  a_pos_of_exists 459 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_460 : a 460 > 0 :=
  a_pos_of_exists 460 70 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_461 : a 461 > 0 :=
  a_pos_of_exists 461 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_462 : a 462 > 0 :=
  a_pos_of_exists 462 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_463 : a 463 > 0 :=
  a_pos_of_exists 463 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_464 : a 464 > 0 :=
  a_pos_of_exists 464 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_465 : a 465 > 0 :=
  a_pos_of_exists 465 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_466 : a 466 > 0 :=
  a_pos_of_exists 466 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_467 : a 467 > 0 :=
  a_pos_of_exists 467 33 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_468 : a 468 > 0 :=
  a_pos_of_exists 468 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_469 : a 469 > 0 :=
  a_pos_of_exists 469 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_470 : a 470 > 0 :=
  a_pos_of_exists 470 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_471 : a 471 > 0 :=
  a_pos_of_exists 471 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_472 : a 472 > 0 :=
  a_pos_of_exists 472 34 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_473 : a 473 > 0 :=
  a_pos_of_exists 473 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_474 : a 474 > 0 :=
  a_pos_of_exists 474 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_475 : a 475 > 0 :=
  a_pos_of_exists 475 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_476 : a 476 > 0 :=
  a_pos_of_exists 476 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_477 : a 477 > 0 :=
  a_pos_of_exists 477 53 (by decide) (by decide) (sqrt_eq_of_sq 10816 104 (by decide))

theorem proof_478 : a 478 > 0 :=
  a_pos_of_exists 478 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_479 : a 479 > 0 :=
  a_pos_of_exists 479 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_480 : a 480 > 0 :=
  a_pos_of_exists 480 12 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_481 : a 481 > 0 :=
  a_pos_of_exists 481 28 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_482 : a 482 > 0 :=
  a_pos_of_exists 482 27 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_483 : a 483 > 0 :=
  a_pos_of_exists 483 3 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_484 : a 484 > 0 :=
  a_pos_of_exists 484 4 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_485 : a 485 > 0 :=
  a_pos_of_exists 485 17 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_486 : a 486 > 0 :=
  a_pos_of_exists 486 6 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_487 : a 487 > 0 :=
  a_pos_of_exists 487 89 (by decide) (by decide) (sqrt_eq_of_sq 17424 132 (by decide))

theorem proof_488 : a 488 > 0 :=
  a_pos_of_exists 488 32 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_489 : a 489 > 0 :=
  a_pos_of_exists 489 3 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_490 : a 490 > 0 :=
  a_pos_of_exists 490 1 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_491 : a 491 > 0 :=
  a_pos_of_exists 491 2 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_492 : a 492 > 0 :=
  a_pos_of_exists 492 6 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_493 : a 493 > 0 :=
  a_pos_of_exists 493 31 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_494 : a 494 > 0 :=
  a_pos_of_exists 494 5 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_495 : a 495 > 0 :=
  a_pos_of_exists 495 15 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_496 : a 496 > 0 :=
  a_pos_of_exists 496 9 (by decide) (by decide) (sqrt_eq_of_sq 2916 54 (by decide))

theorem proof_497 : a 497 > 0 :=
  a_pos_of_exists 497 8 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_498 : a 498 > 0 :=
  a_pos_of_exists 498 60 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_499 : a 499 > 0 :=
  a_pos_of_exists 499 10 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_500 : a 500 > 0 :=
  a_pos_of_exists 500 20 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_501 : a 501 > 0 :=
  a_pos_of_exists 501 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_502 : a 502 > 0 :=
  a_pos_of_exists 502 11 (by decide) (by decide) (sqrt_eq_of_sq 4900 70 (by decide))

theorem proof_503 : a 503 > 0 :=
  a_pos_of_exists 503 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_504 : a 504 > 0 :=
  a_pos_of_exists 504 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_505 : a 505 > 0 :=
  a_pos_of_exists 505 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_506 : a 506 > 0 :=
  a_pos_of_exists 506 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_507 : a 507 > 0 :=
  a_pos_of_exists 507 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_508 : a 508 > 0 :=
  a_pos_of_exists 508 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_509 : a 509 > 0 :=
  a_pos_of_exists 509 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_510 : a 510 > 0 :=
  a_pos_of_exists 510 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_511 : a 511 > 0 :=
  a_pos_of_exists 511 60 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_512 : a 512 > 0 :=
  a_pos_of_exists 512 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_513 : a 513 > 0 :=
  a_pos_of_exists 513 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_514 : a 514 > 0 :=
  a_pos_of_exists 514 1 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_515 : a 515 > 0 :=
  a_pos_of_exists 515 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_516 : a 516 > 0 :=
  a_pos_of_exists 516 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_517 : a 517 > 0 :=
  a_pos_of_exists 517 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_518 : a 518 > 0 :=
  a_pos_of_exists 518 5 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_519 : a 519 > 0 :=
  a_pos_of_exists 519 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_520 : a 520 > 0 :=
  a_pos_of_exists 520 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_521 : a 521 > 0 :=
  a_pos_of_exists 521 8 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_522 : a 522 > 0 :=
  a_pos_of_exists 522 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_523 : a 523 > 0 :=
  a_pos_of_exists 523 10 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_524 : a 524 > 0 :=
  a_pos_of_exists 524 10 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_525 : a 525 > 0 :=
  a_pos_of_exists 525 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_526 : a 526 > 0 :=
  a_pos_of_exists 526 12 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_527 : a 527 > 0 :=
  a_pos_of_exists 527 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_528 : a 528 > 0 :=
  a_pos_of_exists 528 60 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_529 : a 529 > 0 :=
  a_pos_of_exists 529 17 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_530 : a 530 > 0 :=
  a_pos_of_exists 530 17 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_531 : a 531 > 0 :=
  a_pos_of_exists 531 17 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_532 : a 532 > 0 :=
  a_pos_of_exists 532 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_533 : a 533 > 0 :=
  a_pos_of_exists 533 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_534 : a 534 > 0 :=
  a_pos_of_exists 534 24 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_535 : a 535 > 0 :=
  a_pos_of_exists 535 80 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_536 : a 536 > 0 :=
  a_pos_of_exists 536 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_537 : a 537 > 0 :=
  a_pos_of_exists 537 26 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_538 : a 538 > 0 :=
  a_pos_of_exists 538 34 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_539 : a 539 > 0 :=
  a_pos_of_exists 539 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_540 : a 540 > 0 :=
  a_pos_of_exists 540 30 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_541 : a 541 > 0 :=
  a_pos_of_exists 541 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_542 : a 542 > 0 :=
  a_pos_of_exists 542 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_543 : a 543 > 0 :=
  a_pos_of_exists 543 41 (by decide) (by decide) (sqrt_eq_of_sq 10000 100 (by decide))

theorem proof_544 : a 544 > 0 :=
  a_pos_of_exists 544 32 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_545 : a 545 > 0 :=
  a_pos_of_exists 545 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_546 : a 546 > 0 :=
  a_pos_of_exists 546 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_547 : a 547 > 0 :=
  a_pos_of_exists 547 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_548 : a 548 > 0 :=
  a_pos_of_exists 548 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_549 : a 549 > 0 :=
  a_pos_of_exists 549 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_550 : a 550 > 0 :=
  a_pos_of_exists 550 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_551 : a 551 > 0 :=
  a_pos_of_exists 551 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_552 : a 552 > 0 :=
  a_pos_of_exists 552 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_553 : a 553 > 0 :=
  a_pos_of_exists 553 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_554 : a 554 > 0 :=
  a_pos_of_exists 554 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_555 : a 555 > 0 :=
  a_pos_of_exists 555 70 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_556 : a 556 > 0 :=
  a_pos_of_exists 556 6 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_557 : a 557 > 0 :=
  a_pos_of_exists 557 17 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_558 : a 558 > 0 :=
  a_pos_of_exists 558 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_559 : a 559 > 0 :=
  a_pos_of_exists 559 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_560 : a 560 > 0 :=
  a_pos_of_exists 560 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_561 : a 561 > 0 :=
  a_pos_of_exists 561 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_562 : a 562 > 0 :=
  a_pos_of_exists 562 42 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_563 : a 563 > 0 :=
  a_pos_of_exists 563 17 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_564 : a 564 > 0 :=
  a_pos_of_exists 564 31 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_565 : a 565 > 0 :=
  a_pos_of_exists 565 15 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_566 : a 566 > 0 :=
  a_pos_of_exists 566 16 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_567 : a 567 > 0 :=
  a_pos_of_exists 567 35 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_568 : a 568 > 0 :=
  a_pos_of_exists 568 1 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_569 : a 569 > 0 :=
  a_pos_of_exists 569 2 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_570 : a 570 > 0 :=
  a_pos_of_exists 570 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_571 : a 571 > 0 :=
  a_pos_of_exists 571 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_572 : a 572 > 0 :=
  a_pos_of_exists 572 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_573 : a 573 > 0 :=
  a_pos_of_exists 573 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_574 : a 574 > 0 :=
  a_pos_of_exists 574 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_575 : a 575 > 0 :=
  a_pos_of_exists 575 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_576 : a 576 > 0 :=
  a_pos_of_exists 576 32 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_577 : a 577 > 0 :=
  a_pos_of_exists 577 10 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_578 : a 578 > 0 :=
  a_pos_of_exists 578 1 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_579 : a 579 > 0 :=
  a_pos_of_exists 579 2 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_580 : a 580 > 0 :=
  a_pos_of_exists 580 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_581 : a 581 > 0 :=
  a_pos_of_exists 581 21 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_582 : a 582 > 0 :=
  a_pos_of_exists 582 5 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_583 : a 583 > 0 :=
  a_pos_of_exists 583 25 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_584 : a 584 > 0 :=
  a_pos_of_exists 584 17 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_585 : a 585 > 0 :=
  a_pos_of_exists 585 8 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_586 : a 586 > 0 :=
  a_pos_of_exists 586 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_587 : a 587 > 0 :=
  a_pos_of_exists 587 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_588 : a 588 > 0 :=
  a_pos_of_exists 588 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_589 : a 589 > 0 :=
  a_pos_of_exists 589 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_590 : a 590 > 0 :=
  a_pos_of_exists 590 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_591 : a 591 > 0 :=
  a_pos_of_exists 591 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_592 : a 592 > 0 :=
  a_pos_of_exists 592 48 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_593 : a 593 > 0 :=
  a_pos_of_exists 593 14 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_594 : a 594 > 0 :=
  a_pos_of_exists 594 3 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_595 : a 595 > 0 :=
  a_pos_of_exists 595 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_596 : a 596 > 0 :=
  a_pos_of_exists 596 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_597 : a 597 > 0 :=
  a_pos_of_exists 597 6 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_598 : a 598 > 0 :=
  a_pos_of_exists 598 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_599 : a 599 > 0 :=
  a_pos_of_exists 599 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_600 : a 600 > 0 :=
  a_pos_of_exists 600 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_601 : a 601 > 0 :=
  a_pos_of_exists 601 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_602 : a 602 > 0 :=
  a_pos_of_exists 602 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_603 : a 603 > 0 :=
  a_pos_of_exists 603 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_604 : a 604 > 0 :=
  a_pos_of_exists 604 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_605 : a 605 > 0 :=
  a_pos_of_exists 605 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_606 : a 606 > 0 :=
  a_pos_of_exists 606 15 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_607 : a 607 > 0 :=
  a_pos_of_exists 607 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_608 : a 608 > 0 :=
  a_pos_of_exists 608 7 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_609 : a 609 > 0 :=
  a_pos_of_exists 609 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_610 : a 610 > 0 :=
  a_pos_of_exists 610 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_611 : a 611 > 0 :=
  a_pos_of_exists 611 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_612 : a 612 > 0 :=
  a_pos_of_exists 612 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_613 : a 613 > 0 :=
  a_pos_of_exists 613 18 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_614 : a 614 > 0 :=
  a_pos_of_exists 614 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_615 : a 615 > 0 :=
  a_pos_of_exists 615 14 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_616 : a 616 > 0 :=
  a_pos_of_exists 616 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_617 : a 617 > 0 :=
  a_pos_of_exists 617 13 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_618 : a 618 > 0 :=
  a_pos_of_exists 618 27 (by decide) (by decide) (sqrt_eq_of_sq 7056 84 (by decide))

theorem proof_619 : a 619 > 0 :=
  a_pos_of_exists 619 18 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_620 : a 620 > 0 :=
  a_pos_of_exists 620 74 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_621 : a 621 > 0 :=
  a_pos_of_exists 621 15 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_622 : a 622 > 0 :=
  a_pos_of_exists 622 16 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_623 : a 623 > 0 :=
  a_pos_of_exists 623 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_624 : a 624 > 0 :=
  a_pos_of_exists 624 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_625 : a 625 > 0 :=
  a_pos_of_exists 625 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_626 : a 626 > 0 :=
  a_pos_of_exists 626 20 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_627 : a 627 > 0 :=
  a_pos_of_exists 627 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_628 : a 628 > 0 :=
  a_pos_of_exists 628 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_629 : a 629 > 0 :=
  a_pos_of_exists 629 38 (by decide) (by decide) (sqrt_eq_of_sq 7056 84 (by decide))

theorem proof_630 : a 630 > 0 :=
  a_pos_of_exists 630 1 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_631 : a 631 > 0 :=
  a_pos_of_exists 631 1 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_632 : a 632 > 0 :=
  a_pos_of_exists 632 2 (by decide) (by decide) (sqrt_eq_of_sq 144 12 (by decide))

theorem proof_633 : a 633 > 0 :=
  a_pos_of_exists 633 21 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_634 : a 634 > 0 :=
  a_pos_of_exists 634 5 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_635 : a 635 > 0 :=
  a_pos_of_exists 635 5 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_636 : a 636 > 0 :=
  a_pos_of_exists 636 30 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_637 : a 637 > 0 :=
  a_pos_of_exists 637 8 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_638 : a 638 > 0 :=
  a_pos_of_exists 638 8 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_639 : a 639 > 0 :=
  a_pos_of_exists 639 10 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_640 : a 640 > 0 :=
  a_pos_of_exists 640 10 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_641 : a 641 > 0 :=
  a_pos_of_exists 641 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_642 : a 642 > 0 :=
  a_pos_of_exists 642 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_643 : a 643 > 0 :=
  a_pos_of_exists 643 51 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_644 : a 644 > 0 :=
  a_pos_of_exists 644 38 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_645 : a 645 > 0 :=
  a_pos_of_exists 645 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_646 : a 646 > 0 :=
  a_pos_of_exists 646 17 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_647 : a 647 > 0 :=
  a_pos_of_exists 647 17 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_648 : a 648 > 0 :=
  a_pos_of_exists 648 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_649 : a 649 > 0 :=
  a_pos_of_exists 649 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_650 : a 650 > 0 :=
  a_pos_of_exists 650 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_651 : a 651 > 0 :=
  a_pos_of_exists 651 56 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_652 : a 652 > 0 :=
  a_pos_of_exists 652 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_653 : a 653 > 0 :=
  a_pos_of_exists 653 1 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_654 : a 654 > 0 :=
  a_pos_of_exists 654 2 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_655 : a 655 > 0 :=
  a_pos_of_exists 655 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_656 : a 656 > 0 :=
  a_pos_of_exists 656 64 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_657 : a 657 > 0 :=
  a_pos_of_exists 657 5 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_658 : a 658 > 0 :=
  a_pos_of_exists 658 33 (by decide) (by decide) (sqrt_eq_of_sq 10000 100 (by decide))

theorem proof_659 : a 659 > 0 :=
  a_pos_of_exists 659 44 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_660 : a 660 > 0 :=
  a_pos_of_exists 660 8 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_661 : a 661 > 0 :=
  a_pos_of_exists 661 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_662 : a 662 > 0 :=
  a_pos_of_exists 662 10 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_663 : a 663 > 0 :=
  a_pos_of_exists 663 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_664 : a 664 > 0 :=
  a_pos_of_exists 664 12 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_665 : a 665 > 0 :=
  a_pos_of_exists 665 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_666 : a 666 > 0 :=
  a_pos_of_exists 666 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_667 : a 667 > 0 :=
  a_pos_of_exists 667 37 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_668 : a 668 > 0 :=
  a_pos_of_exists 668 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_669 : a 669 > 0 :=
  a_pos_of_exists 669 17 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_670 : a 670 > 0 :=
  a_pos_of_exists 670 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_671 : a 671 > 0 :=
  a_pos_of_exists 671 11 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_672 : a 672 > 0 :=
  a_pos_of_exists 672 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_673 : a 673 > 0 :=
  a_pos_of_exists 673 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_674 : a 674 > 0 :=
  a_pos_of_exists 674 34 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_675 : a 675 > 0 :=
  a_pos_of_exists 675 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_676 : a 676 > 0 :=
  a_pos_of_exists 676 30 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_677 : a 677 > 0 :=
  a_pos_of_exists 677 14 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_678 : a 678 > 0 :=
  a_pos_of_exists 678 1 (by decide) (by decide) (sqrt_eq_of_sq 676 26 (by decide))

theorem proof_679 : a 679 > 0 :=
  a_pos_of_exists 679 2 (by decide) (by decide) (sqrt_eq_of_sq 676 26 (by decide))

theorem proof_680 : a 680 > 0 :=
  a_pos_of_exists 680 1 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_681 : a 681 > 0 :=
  a_pos_of_exists 681 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_682 : a 682 > 0 :=
  a_pos_of_exists 682 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_683 : a 683 > 0 :=
  a_pos_of_exists 683 26 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_684 : a 684 > 0 :=
  a_pos_of_exists 684 5 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_685 : a 685 > 0 :=
  a_pos_of_exists 685 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_686 : a 686 > 0 :=
  a_pos_of_exists 686 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_687 : a 687 > 0 :=
  a_pos_of_exists 687 8 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_688 : a 688 > 0 :=
  a_pos_of_exists 688 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_689 : a 689 > 0 :=
  a_pos_of_exists 689 10 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_690 : a 690 > 0 :=
  a_pos_of_exists 690 10 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_691 : a 691 > 0 :=
  a_pos_of_exists 691 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_692 : a 692 > 0 :=
  a_pos_of_exists 692 12 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_693 : a 693 > 0 :=
  a_pos_of_exists 693 7 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_694 : a 694 > 0 :=
  a_pos_of_exists 694 17 (by decide) (by decide) (sqrt_eq_of_sq 10816 104 (by decide))

theorem proof_695 : a 695 > 0 :=
  a_pos_of_exists 695 9 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_696 : a 696 > 0 :=
  a_pos_of_exists 696 17 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_697 : a 697 > 0 :=
  a_pos_of_exists 697 17 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_698 : a 698 > 0 :=
  a_pos_of_exists 698 14 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_699 : a 699 > 0 :=
  a_pos_of_exists 699 42 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_700 : a 700 > 0 :=
  a_pos_of_exists 700 14 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_701 : a 701 > 0 :=
  a_pos_of_exists 701 35 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_702 : a 702 > 0 :=
  a_pos_of_exists 702 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_703 : a 703 > 0 :=
  a_pos_of_exists 703 21 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_704 : a 704 > 0 :=
  a_pos_of_exists 704 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_705 : a 705 > 0 :=
  a_pos_of_exists 705 39 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_706 : a 706 > 0 :=
  a_pos_of_exists 706 3 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_707 : a 707 > 0 :=
  a_pos_of_exists 707 4 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_708 : a 708 > 0 :=
  a_pos_of_exists 708 11 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_709 : a 709 > 0 :=
  a_pos_of_exists 709 6 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_710 : a 710 > 0 :=
  a_pos_of_exists 710 28 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_711 : a 711 > 0 :=
  a_pos_of_exists 711 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_712 : a 712 > 0 :=
  a_pos_of_exists 712 32 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_713 : a 713 > 0 :=
  a_pos_of_exists 713 34 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_714 : a 714 > 0 :=
  a_pos_of_exists 714 7 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_715 : a 715 > 0 :=
  a_pos_of_exists 715 22 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_716 : a 716 > 0 :=
  a_pos_of_exists 716 9 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_717 : a 717 > 0 :=
  a_pos_of_exists 717 37 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_718 : a 718 > 0 :=
  a_pos_of_exists 718 15 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_719 : a 719 > 0 :=
  a_pos_of_exists 719 16 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_720 : a 720 > 0 :=
  a_pos_of_exists 720 18 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_721 : a 721 > 0 :=
  a_pos_of_exists 721 14 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_722 : a 722 > 0 :=
  a_pos_of_exists 722 19 (by decide) (by decide) (sqrt_eq_of_sq 11664 108 (by decide))

theorem proof_723 : a 723 > 0 :=
  a_pos_of_exists 723 20 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_724 : a 724 > 0 :=
  a_pos_of_exists 724 42 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_725 : a 725 > 0 :=
  a_pos_of_exists 725 18 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_726 : a 726 > 0 :=
  a_pos_of_exists 726 72 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_727 : a 727 > 0 :=
  a_pos_of_exists 727 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_728 : a 728 > 0 :=
  a_pos_of_exists 728 48 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_729 : a 729 > 0 :=
  a_pos_of_exists 729 23 (by decide) (by decide) (sqrt_eq_of_sq 7744 88 (by decide))

theorem proof_730 : a 730 > 0 :=
  a_pos_of_exists 730 27 (by decide) (by decide) (sqrt_eq_of_sq 11664 108 (by decide))

theorem proof_731 : a 731 > 0 :=
  a_pos_of_exists 731 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_732 : a 732 > 0 :=
  a_pos_of_exists 732 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_733 : a 733 > 0 :=
  a_pos_of_exists 733 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_734 : a 734 > 0 :=
  a_pos_of_exists 734 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_735 : a 735 > 0 :=
  a_pos_of_exists 735 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_736 : a 736 > 0 :=
  a_pos_of_exists 736 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_737 : a 737 > 0 :=
  a_pos_of_exists 737 33 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_738 : a 738 > 0 :=
  a_pos_of_exists 738 9 (by decide) (by decide) (sqrt_eq_of_sq 2916 54 (by decide))

theorem proof_739 : a 739 > 0 :=
  a_pos_of_exists 739 60 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_740 : a 740 > 0 :=
  a_pos_of_exists 740 26 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_741 : a 741 > 0 :=
  a_pos_of_exists 741 14 (by decide) (by decide) (sqrt_eq_of_sq 4356 66 (by decide))

theorem proof_742 : a 742 > 0 :=
  a_pos_of_exists 742 28 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_743 : a 743 > 0 :=
  a_pos_of_exists 743 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_744 : a 744 > 0 :=
  a_pos_of_exists 744 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_745 : a 745 > 0 :=
  a_pos_of_exists 745 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_746 : a 746 > 0 :=
  a_pos_of_exists 746 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_747 : a 747 > 0 :=
  a_pos_of_exists 747 18 (by decide) (by decide) (sqrt_eq_of_sq 2916 54 (by decide))

theorem proof_748 : a 748 > 0 :=
  a_pos_of_exists 748 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_749 : a 749 > 0 :=
  a_pos_of_exists 749 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_750 : a 750 > 0 :=
  a_pos_of_exists 750 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_751 : a 751 > 0 :=
  a_pos_of_exists 751 74 (by decide) (by decide) (sqrt_eq_of_sq 24336 156 (by decide))

theorem proof_752 : a 752 > 0 :=
  a_pos_of_exists 752 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_753 : a 753 > 0 :=
  a_pos_of_exists 753 3 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_754 : a 754 > 0 :=
  a_pos_of_exists 754 4 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_755 : a 755 > 0 :=
  a_pos_of_exists 755 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_756 : a 756 > 0 :=
  a_pos_of_exists 756 6 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_757 : a 757 > 0 :=
  a_pos_of_exists 757 27 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_758 : a 758 > 0 :=
  a_pos_of_exists 758 30 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_759 : a 759 > 0 :=
  a_pos_of_exists 759 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_760 : a 760 > 0 :=
  a_pos_of_exists 760 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_761 : a 761 > 0 :=
  a_pos_of_exists 761 61 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_762 : a 762 > 0 :=
  a_pos_of_exists 762 7 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_763 : a 763 > 0 :=
  a_pos_of_exists 763 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_764 : a 764 > 0 :=
  a_pos_of_exists 764 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_765 : a 765 > 0 :=
  a_pos_of_exists 765 9 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_766 : a 766 > 0 :=
  a_pos_of_exists 766 3 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_767 : a 767 > 0 :=
  a_pos_of_exists 767 4 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_768 : a 768 > 0 :=
  a_pos_of_exists 768 38 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_769 : a 769 > 0 :=
  a_pos_of_exists 769 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_770 : a 770 > 0 :=
  a_pos_of_exists 770 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_771 : a 771 > 0 :=
  a_pos_of_exists 771 68 (by decide) (by decide) (sqrt_eq_of_sq 20736 144 (by decide))

theorem proof_772 : a 772 > 0 :=
  a_pos_of_exists 772 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_773 : a 773 > 0 :=
  a_pos_of_exists 773 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_774 : a 774 > 0 :=
  a_pos_of_exists 774 3 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_775 : a 775 > 0 :=
  a_pos_of_exists 775 4 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_776 : a 776 > 0 :=
  a_pos_of_exists 776 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_777 : a 777 > 0 :=
  a_pos_of_exists 777 6 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_778 : a 778 > 0 :=
  a_pos_of_exists 778 10 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_779 : a 779 > 0 :=
  a_pos_of_exists 779 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_780 : a 780 > 0 :=
  a_pos_of_exists 780 12 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_781 : a 781 > 0 :=
  a_pos_of_exists 781 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_782 : a 782 > 0 :=
  a_pos_of_exists 782 7 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_783 : a 783 > 0 :=
  a_pos_of_exists 783 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_784 : a 784 > 0 :=
  a_pos_of_exists 784 9 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_785 : a 785 > 0 :=
  a_pos_of_exists 785 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_786 : a 786 > 0 :=
  a_pos_of_exists 786 14 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_787 : a 787 > 0 :=
  a_pos_of_exists 787 16 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_788 : a 788 > 0 :=
  a_pos_of_exists 788 38 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_789 : a 789 > 0 :=
  a_pos_of_exists 789 14 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_790 : a 790 > 0 :=
  a_pos_of_exists 790 13 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_791 : a 791 > 0 :=
  a_pos_of_exists 791 3 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_792 : a 792 > 0 :=
  a_pos_of_exists 792 4 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_793 : a 793 > 0 :=
  a_pos_of_exists 793 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_794 : a 794 > 0 :=
  a_pos_of_exists 794 6 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_795 : a 795 > 0 :=
  a_pos_of_exists 795 24 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_796 : a 796 > 0 :=
  a_pos_of_exists 796 68 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_797 : a 797 > 0 :=
  a_pos_of_exists 797 28 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_798 : a 798 > 0 :=
  a_pos_of_exists 798 21 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_799 : a 799 > 0 :=
  a_pos_of_exists 799 61 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_800 : a 800 > 0 :=
  a_pos_of_exists 800 32 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_801 : a 801 > 0 :=
  a_pos_of_exists 801 21 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_802 : a 802 > 0 :=
  a_pos_of_exists 802 34 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_803 : a 803 > 0 :=
  a_pos_of_exists 803 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_804 : a 804 > 0 :=
  a_pos_of_exists 804 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_805 : a 805 > 0 :=
  a_pos_of_exists 805 7 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_806 : a 806 > 0 :=
  a_pos_of_exists 806 26 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_807 : a 807 > 0 :=
  a_pos_of_exists 807 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_808 : a 808 > 0 :=
  a_pos_of_exists 808 20 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_809 : a 809 > 0 :=
  a_pos_of_exists 809 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_810 : a 810 > 0 :=
  a_pos_of_exists 810 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_811 : a 811 > 0 :=
  a_pos_of_exists 811 35 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_812 : a 812 > 0 :=
  a_pos_of_exists 812 10 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_813 : a 813 > 0 :=
  a_pos_of_exists 813 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_814 : a 814 > 0 :=
  a_pos_of_exists 814 12 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_815 : a 815 > 0 :=
  a_pos_of_exists 815 27 (by decide) (by decide) (sqrt_eq_of_sq 7056 84 (by decide))

theorem proof_816 : a 816 > 0 :=
  a_pos_of_exists 816 8 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_817 : a 817 > 0 :=
  a_pos_of_exists 817 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_818 : a 818 > 0 :=
  a_pos_of_exists 818 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_819 : a 819 > 0 :=
  a_pos_of_exists 819 4 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_820 : a 820 > 0 :=
  a_pos_of_exists 820 12 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_821 : a 821 > 0 :=
  a_pos_of_exists 821 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_822 : a 822 > 0 :=
  a_pos_of_exists 822 11 (by decide) (by decide) (sqrt_eq_of_sq 8100 90 (by decide))

theorem proof_823 : a 823 > 0 :=
  a_pos_of_exists 823 44 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_824 : a 824 > 0 :=
  a_pos_of_exists 824 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_825 : a 825 > 0 :=
  a_pos_of_exists 825 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_826 : a 826 > 0 :=
  a_pos_of_exists 826 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_827 : a 827 > 0 :=
  a_pos_of_exists 827 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_828 : a 828 > 0 :=
  a_pos_of_exists 828 12 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_829 : a 829 > 0 :=
  a_pos_of_exists 829 50 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_830 : a 830 > 0 :=
  a_pos_of_exists 830 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_831 : a 831 > 0 :=
  a_pos_of_exists 831 16 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_832 : a 832 > 0 :=
  a_pos_of_exists 832 13 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_833 : a 833 > 0 :=
  a_pos_of_exists 833 8 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_834 : a 834 > 0 :=
  a_pos_of_exists 834 19 (by decide) (by decide) (sqrt_eq_of_sq 11664 108 (by decide))

theorem proof_835 : a 835 > 0 :=
  a_pos_of_exists 835 10 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_836 : a 836 > 0 :=
  a_pos_of_exists 836 22 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_837 : a 837 > 0 :=
  a_pos_of_exists 837 12 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_838 : a 838 > 0 :=
  a_pos_of_exists 838 135 (by decide) (by decide) (sqrt_eq_of_sq 46656 216 (by decide))

theorem proof_839 : a 839 > 0 :=
  a_pos_of_exists 839 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_840 : a 840 > 0 :=
  a_pos_of_exists 840 21 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_841 : a 841 > 0 :=
  a_pos_of_exists 841 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_842 : a 842 > 0 :=
  a_pos_of_exists 842 17 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_843 : a 843 > 0 :=
  a_pos_of_exists 843 45 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_844 : a 844 > 0 :=
  a_pos_of_exists 844 44 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_845 : a 845 > 0 :=
  a_pos_of_exists 845 25 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_846 : a 846 > 0 :=
  a_pos_of_exists 846 14 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_847 : a 847 > 0 :=
  a_pos_of_exists 847 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_848 : a 848 > 0 :=
  a_pos_of_exists 848 32 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_849 : a 849 > 0 :=
  a_pos_of_exists 849 39 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_850 : a 850 > 0 :=
  a_pos_of_exists 850 18 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_851 : a 851 > 0 :=
  a_pos_of_exists 851 80 (by decide) (by decide) (sqrt_eq_of_sq 16384 128 (by decide))

theorem proof_852 : a 852 > 0 :=
  a_pos_of_exists 852 41 (by decide) (by decide) (sqrt_eq_of_sq 32400 180 (by decide))

theorem proof_853 : a 853 > 0 :=
  a_pos_of_exists 853 13 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_854 : a 854 > 0 :=
  a_pos_of_exists 854 56 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_855 : a 855 > 0 :=
  a_pos_of_exists 855 36 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_856 : a 856 > 0 :=
  a_pos_of_exists 856 40 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_857 : a 857 > 0 :=
  a_pos_of_exists 857 32 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_858 : a 858 > 0 :=
  a_pos_of_exists 858 22 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_859 : a 859 > 0 :=
  a_pos_of_exists 859 34 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_860 : a 860 > 0 :=
  a_pos_of_exists 860 84 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_861 : a 861 > 0 :=
  a_pos_of_exists 861 21 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_862 : a 862 > 0 :=
  a_pos_of_exists 862 37 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_863 : a 863 > 0 :=
  a_pos_of_exists 863 69 (by decide) (by decide) (sqrt_eq_of_sq 17424 132 (by decide))

theorem proof_864 : a 864 > 0 :=
  a_pos_of_exists 864 44 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_865 : a 865 > 0 :=
  a_pos_of_exists 865 11 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_866 : a 866 > 0 :=
  a_pos_of_exists 866 26 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_867 : a 867 > 0 :=
  a_pos_of_exists 867 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_868 : a 868 > 0 :=
  a_pos_of_exists 868 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_869 : a 869 > 0 :=
  a_pos_of_exists 869 54 (by decide) (by decide) (sqrt_eq_of_sq 11664 108 (by decide))

theorem proof_870 : a 870 > 0 :=
  a_pos_of_exists 870 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_871 : a 871 > 0 :=
  a_pos_of_exists 871 39 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_872 : a 872 > 0 :=
  a_pos_of_exists 872 97 (by decide) (by decide) (sqrt_eq_of_sq 57600 240 (by decide))

theorem proof_873 : a 873 > 0 :=
  a_pos_of_exists 873 48 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_874 : a 874 > 0 :=
  a_pos_of_exists 874 1 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_875 : a 875 > 0 :=
  a_pos_of_exists 875 2 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_876 : a 876 > 0 :=
  a_pos_of_exists 876 21 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_877 : a 877 > 0 :=
  a_pos_of_exists 877 41 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_878 : a 878 > 0 :=
  a_pos_of_exists 878 5 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_879 : a 879 > 0 :=
  a_pos_of_exists 879 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_880 : a 880 > 0 :=
  a_pos_of_exists 880 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_881 : a 881 > 0 :=
  a_pos_of_exists 881 8 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_882 : a 882 > 0 :=
  a_pos_of_exists 882 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_883 : a 883 > 0 :=
  a_pos_of_exists 883 10 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_884 : a 884 > 0 :=
  a_pos_of_exists 884 9 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_885 : a 885 > 0 :=
  a_pos_of_exists 885 12 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_886 : a 886 > 0 :=
  a_pos_of_exists 886 3 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_887 : a 887 > 0 :=
  a_pos_of_exists 887 4 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_888 : a 888 > 0 :=
  a_pos_of_exists 888 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_889 : a 889 > 0 :=
  a_pos_of_exists 889 6 (by decide) (by decide) (sqrt_eq_of_sq 1764 42 (by decide))

theorem proof_890 : a 890 > 0 :=
  a_pos_of_exists 890 17 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_891 : a 891 > 0 :=
  a_pos_of_exists 891 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_892 : a 892 > 0 :=
  a_pos_of_exists 892 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_893 : a 893 > 0 :=
  a_pos_of_exists 893 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_894 : a 894 > 0 :=
  a_pos_of_exists 894 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_895 : a 895 > 0 :=
  a_pos_of_exists 895 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_896 : a 896 > 0 :=
  a_pos_of_exists 896 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_897 : a 897 > 0 :=
  a_pos_of_exists 897 42 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_898 : a 898 > 0 :=
  a_pos_of_exists 898 14 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_899 : a 899 > 0 :=
  a_pos_of_exists 899 16 (by decide) (by decide) (sqrt_eq_of_sq 7056 84 (by decide))

theorem proof_900 : a 900 > 0 :=
  a_pos_of_exists 900 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_901 : a 901 > 0 :=
  a_pos_of_exists 901 76 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_902 : a 902 > 0 :=
  a_pos_of_exists 902 18 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_903 : a 903 > 0 :=
  a_pos_of_exists 903 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_904 : a 904 > 0 :=
  a_pos_of_exists 904 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_905 : a 905 > 0 :=
  a_pos_of_exists 905 9 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_906 : a 906 > 0 :=
  a_pos_of_exists 906 30 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_907 : a 907 > 0 :=
  a_pos_of_exists 907 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_908 : a 908 > 0 :=
  a_pos_of_exists 908 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_909 : a 909 > 0 :=
  a_pos_of_exists 909 41 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_910 : a 910 > 0 :=
  a_pos_of_exists 910 8 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_911 : a 911 > 0 :=
  a_pos_of_exists 911 29 (by decide) (by decide) (sqrt_eq_of_sq 7056 84 (by decide))

theorem proof_912 : a 912 > 0 :=
  a_pos_of_exists 912 10 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_913 : a 913 > 0 :=
  a_pos_of_exists 913 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_914 : a 914 > 0 :=
  a_pos_of_exists 914 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_915 : a 915 > 0 :=
  a_pos_of_exists 915 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_916 : a 916 > 0 :=
  a_pos_of_exists 916 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_917 : a 917 > 0 :=
  a_pos_of_exists 917 46 (by decide) (by decide) (sqrt_eq_of_sq 17424 132 (by decide))

theorem proof_918 : a 918 > 0 :=
  a_pos_of_exists 918 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_919 : a 919 > 0 :=
  a_pos_of_exists 919 13 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_920 : a 920 > 0 :=
  a_pos_of_exists 920 45 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_921 : a 921 > 0 :=
  a_pos_of_exists 921 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_922 : a 922 > 0 :=
  a_pos_of_exists 922 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_923 : a 923 > 0 :=
  a_pos_of_exists 923 14 (by decide) (by decide) (sqrt_eq_of_sq 3600 60 (by decide))

theorem proof_924 : a 924 > 0 :=
  a_pos_of_exists 924 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_925 : a 925 > 0 :=
  a_pos_of_exists 925 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_926 : a 926 > 0 :=
  a_pos_of_exists 926 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_927 : a 927 > 0 :=
  a_pos_of_exists 927 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_928 : a 928 > 0 :=
  a_pos_of_exists 928 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_929 : a 929 > 0 :=
  a_pos_of_exists 929 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_930 : a 930 > 0 :=
  a_pos_of_exists 930 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_931 : a 931 > 0 :=
  a_pos_of_exists 931 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_932 : a 932 > 0 :=
  a_pos_of_exists 932 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_933 : a 933 > 0 :=
  a_pos_of_exists 933 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_934 : a 934 > 0 :=
  a_pos_of_exists 934 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_935 : a 935 > 0 :=
  a_pos_of_exists 935 39 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_936 : a 936 > 0 :=
  a_pos_of_exists 936 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_937 : a 937 > 0 :=
  a_pos_of_exists 937 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_938 : a 938 > 0 :=
  a_pos_of_exists 938 20 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_939 : a 939 > 0 :=
  a_pos_of_exists 939 3 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_940 : a 940 > 0 :=
  a_pos_of_exists 940 4 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_941 : a 941 > 0 :=
  a_pos_of_exists 941 45 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_942 : a 942 > 0 :=
  a_pos_of_exists 942 6 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_943 : a 943 > 0 :=
  a_pos_of_exists 943 23 (by decide) (by decide) (sqrt_eq_of_sq 7744 88 (by decide))

theorem proof_944 : a 944 > 0 :=
  a_pos_of_exists 944 35 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_945 : a 945 > 0 :=
  a_pos_of_exists 945 27 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_946 : a 946 > 0 :=
  a_pos_of_exists 946 11 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_947 : a 947 > 0 :=
  a_pos_of_exists 947 64 (by decide) (by decide) (sqrt_eq_of_sq 28224 168 (by decide))

theorem proof_948 : a 948 > 0 :=
  a_pos_of_exists 948 30 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_949 : a 949 > 0 :=
  a_pos_of_exists 949 44 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_950 : a 950 > 0 :=
  a_pos_of_exists 950 25 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_951 : a 951 > 0 :=
  a_pos_of_exists 951 15 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_952 : a 952 > 0 :=
  a_pos_of_exists 952 16 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_953 : a 953 > 0 :=
  a_pos_of_exists 953 78 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_954 : a 954 > 0 :=
  a_pos_of_exists 954 45 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_955 : a 955 > 0 :=
  a_pos_of_exists 955 19 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_956 : a 956 > 0 :=
  a_pos_of_exists 956 7 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_957 : a 957 > 0 :=
  a_pos_of_exists 957 22 (by decide) (by decide) (sqrt_eq_of_sq 6400 80 (by decide))

theorem proof_958 : a 958 > 0 :=
  a_pos_of_exists 958 9 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_959 : a 959 > 0 :=
  a_pos_of_exists 959 7 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_960 : a 960 > 0 :=
  a_pos_of_exists 960 24 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_961 : a 961 > 0 :=
  a_pos_of_exists 961 1 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_962 : a 962 > 0 :=
  a_pos_of_exists 962 2 (by decide) (by decide) (sqrt_eq_of_sq 256 16 (by decide))

theorem proof_963 : a 963 > 0 :=
  a_pos_of_exists 963 14 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_964 : a 964 > 0 :=
  a_pos_of_exists 964 54 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_965 : a 965 > 0 :=
  a_pos_of_exists 965 5 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_966 : a 966 > 0 :=
  a_pos_of_exists 966 14 (by decide) (by decide) (sqrt_eq_of_sq 2304 48 (by decide))

theorem proof_967 : a 967 > 0 :=
  a_pos_of_exists 967 18 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_968 : a 968 > 0 :=
  a_pos_of_exists 968 8 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_969 : a 969 > 0 :=
  a_pos_of_exists 969 44 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_970 : a 970 > 0 :=
  a_pos_of_exists 970 1 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_971 : a 971 > 0 :=
  a_pos_of_exists 971 2 (by decide) (by decide) (sqrt_eq_of_sq 576 24 (by decide))

theorem proof_972 : a 972 > 0 :=
  a_pos_of_exists 972 12 (by decide) (by decide) (sqrt_eq_of_sq 1024 32 (by decide))

theorem proof_973 : a 973 > 0 :=
  a_pos_of_exists 973 1 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_974 : a 974 > 0 :=
  a_pos_of_exists 974 2 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_975 : a 975 > 0 :=
  a_pos_of_exists 975 13 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_976 : a 976 > 0 :=
  a_pos_of_exists 976 41 (by decide) (by decide) (sqrt_eq_of_sq 25600 160 (by decide))

theorem proof_977 : a 977 > 0 :=
  a_pos_of_exists 977 5 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_978 : a 978 > 0 :=
  a_pos_of_exists 978 13 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_979 : a 979 > 0 :=
  a_pos_of_exists 979 1 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_980 : a 980 > 0 :=
  a_pos_of_exists 980 2 (by decide) (by decide) (sqrt_eq_of_sq 324 18 (by decide))

theorem proof_981 : a 981 > 0 :=
  a_pos_of_exists 981 7 (by decide) (by decide) (sqrt_eq_of_sq 2916 54 (by decide))

theorem proof_982 : a 982 > 0 :=
  a_pos_of_exists 982 10 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_983 : a 983 > 0 :=
  a_pos_of_exists 983 5 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_984 : a 984 > 0 :=
  a_pos_of_exists 984 3 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_985 : a 985 > 0 :=
  a_pos_of_exists 985 4 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_986 : a 986 > 0 :=
  a_pos_of_exists 986 1 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_987 : a 987 > 0 :=
  a_pos_of_exists 987 2 (by decide) (by decide) (sqrt_eq_of_sq 784 28 (by decide))

theorem proof_988 : a 988 > 0 :=
  a_pos_of_exists 988 10 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_989 : a 989 > 0 :=
  a_pos_of_exists 989 17 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_990 : a 990 > 0 :=
  a_pos_of_exists 990 5 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_991 : a 991 > 0 :=
  a_pos_of_exists 991 26 (by decide) (by decide) (sqrt_eq_of_sq 9216 96 (by decide))

theorem proof_992 : a 992 > 0 :=
  a_pos_of_exists 992 18 (by decide) (by decide) (sqrt_eq_of_sq 2916 54 (by decide))

theorem proof_993 : a 993 > 0 :=
  a_pos_of_exists 993 8 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_994 : a 994 > 0 :=
  a_pos_of_exists 994 34 (by decide) (by decide) (sqrt_eq_of_sq 4096 64 (by decide))

theorem proof_995 : a 995 > 0 :=
  a_pos_of_exists 995 10 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_996 : a 996 > 0 :=
  a_pos_of_exists 996 15 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_997 : a 997 > 0 :=
  a_pos_of_exists 997 12 (by decide) (by decide) (sqrt_eq_of_sq 3136 56 (by decide))

theorem proof_998 : a 998 > 0 :=
  a_pos_of_exists 998 36 (by decide) (by decide) (sqrt_eq_of_sq 5184 72 (by decide))

theorem proof_999 : a 999 > 0 :=
  a_pos_of_exists 999 90 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_1000 : a 1000 > 0 :=
  a_pos_of_exists 1000 19 (by decide) (by decide) (sqrt_eq_of_sq 11664 108 (by decide))

theorem proof_1001 : a 1001 > 0 :=
  a_pos_of_exists 1001 1 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_1002 : a 1002 > 0 :=
  a_pos_of_exists 1002 2 (by decide) (by decide) (sqrt_eq_of_sq 400 20 (by decide))

theorem proof_1003 : a 1003 > 0 :=
  a_pos_of_exists 1003 4 (by decide) (by decide) (sqrt_eq_of_sq 1296 36 (by decide))

theorem proof_1004 : a 1004 > 0 :=
  a_pos_of_exists 1004 22 (by decide) (by decide) (sqrt_eq_of_sq 4900 70 (by decide))

theorem proof_1005 : a 1005 > 0 :=
  a_pos_of_exists 1005 5 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))

theorem proof_1006 : a 1006 > 0 :=
  a_pos_of_exists 1006 31 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_1007 : a 1007 > 0 :=
  a_pos_of_exists 1007 31 (by decide) (by decide) (sqrt_eq_of_sq 14400 120 (by decide))

theorem proof_1008 : a 1008 > 0 :=
  a_pos_of_exists 1008 8 (by decide) (by decide) (sqrt_eq_of_sq 1600 40 (by decide))
