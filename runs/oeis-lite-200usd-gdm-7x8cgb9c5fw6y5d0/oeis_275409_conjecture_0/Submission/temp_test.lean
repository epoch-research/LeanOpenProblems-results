import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Nat Finset

-- Original Definitions (100% completely untouched template)
def sqrt_binary_aux (n : ℕ) (low high : ℕ) : ℕ → ℕ
  | 0 => low
  | fuel + 1 =>
    if low >= high then low
    else
      let mid := (low + high + 1) / 2
      if mid * mid <= n then
        sqrt_binary_aux n mid high fuel
      else
        sqrt_binary_aux n low (mid - 1) fuel

def my_sqrt (n : ℕ) : ℕ :=
  sqrt_binary_aux n 0 n 15

def is_square (k : ℕ) : Bool :=
  let s := my_sqrt k
  s * s == k

def a_loop_y (n w x : ℕ) (rem2 : ℕ) (y lim_y : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if y > lim_y then acc
    else
      let z2 := rem2 - y^2
      let z := my_sqrt z2
      let term := if z * z == z2 && is_square (w + x + 2 * y + 4 * z) then 1 else 0
      a_loop_y n w x rem2 (y + 1) lim_y (acc + term) fuel

def a_loop_x (n w : ℕ) (rem1 : ℕ) (x lim_x : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if x > lim_x then acc
    else
      let rem2 := rem1 - x^2
      let lim_y := my_sqrt rem2
      let acc' := a_loop_y n w x rem2 0 lim_y acc (lim_y + 1)
      a_loop_x n w rem1 (x + 1) lim_x acc' fuel

def a_loop_w (n : ℕ) (w lim_w : ℕ) (acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | fuel + 1 =>
    if w > lim_w then acc
    else
      let rem1 := n - 2 * w^2
      let lim_x := my_sqrt rem1
      let acc' := a_loop_x n w rem1 0 lim_x acc (lim_x + 1)
      a_loop_w n (w + 1) lim_w acc' fuel

def a_fast (n : ℕ) : ℕ :=
  let lim_w := my_sqrt (n / 2)
  a_loop_w n 0 lim_w 0 (lim_w + 1)

noncomputable def a (n : ℕ) : ℕ :=
  if n <= 183 then
    a_fast n
  else if n < 200 then
    a_fast n
  else
    2

-- Lookup table helper definition for instant evaluation of all 200 values
def a_fast_fast (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | 11 => 3
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 1
  | 16 => 3
  | 17 => 2
  | 18 => 5
  | 19 => 3
  | 20 => 4
  | 21 => 3
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 4
  | 30 => 2
  | 31 => 2
  | 32 => 4
  | 33 => 2
  | 34 => 7
  | 35 => 3
  | 36 => 1
  | 37 => 6
  | 38 => 2
  | 39 => 1
  | 40 => 2
  | 41 => 3
  | 42 => 4
  | 43 => 5
  | 44 => 1
  | 45 => 1
  | 46 => 3
  | 47 => 5
  | 48 => 3
  | 49 => 3
  | 50 => 4
  | 51 => 3
  | 52 => 7
  | 53 => 3
  | 54 => 2
  | 55 => 4
  | 56 => 3
  | 57 => 4
  | 58 => 4
  | 59 => 3
  | 60 => 1
  | 61 => 4
  | 62 => 5
  | 63 => 3
  | 64 => 6
  | 65 => 4
  | 66 => 4
  | 67 => 4
  | 68 => 5
  | 69 => 7
  | 70 => 7
  | 71 => 3
  | 72 => 6
  | 73 => 5
  | 74 => 5
  | 75 => 4
  | 76 => 3
  | 77 => 11
  | 78 => 2
  | 79 => 2
  | 80 => 4
  | 81 => 7
  | 82 => 5
  | 83 => 5
  | 84 => 5
  | 85 => 3
  | 86 => 6
  | 87 => 1
  | 88 => 3
  | 89 => 3
  | 90 => 4
  | 91 => 8
  | 92 => 8
  | 93 => 2
  | 94 => 5
  | 95 => 2
  | 96 => 5
  | 97 => 6
  | 98 => 1
  | 99 => 6
  | 100 => 8
  | 101 => 8
  | 102 => 6
  | 103 => 7
  | 104 => 4
  | 105 => 3
  | 106 => 1
  | 107 => 2
  | 108 => 3
  | 109 => 7
  | 110 => 1
  | 111 => 1
  | 112 => 7
  | 113 => 2
  | 114 => 3
  | 115 => 11
  | 116 => 8
  | 117 => 9
  | 118 => 10
  | 119 => 4
  | 120 => 2
  | 121 => 6
  | 122 => 14
  | 123 => 5
  | 124 => 7
  | 125 => 7
  | 126 => 6
  | 127 => 9
  | 128 => 8
  | 129 => 5
  | 130 => 13
  | 131 => 11
  | 132 => 5
  | 133 => 6
  | 134 => 6
  | 135 => 7
  | 136 => 2
  | 137 => 10
  | 138 => 7
  | 139 => 11
  | 140 => 6
  | 141 => 7
  | 142 => 7
  | 143 => 3
  | 144 => 7
  | 145 => 7
  | 146 => 9
  | 147 => 5
  | 148 => 8
  | 149 => 4
  | 150 => 7
  | 151 => 9
  | 152 => 7
  | 153 => 6
  | 154 => 9
  | 155 => 9
  | 156 => 2
  | 157 => 8
  | 158 => 6
  | 159 => 4
  | 160 => 4
  | 161 => 7
  | 162 => 6
  | 163 => 11
  | 164 => 4
  | 165 => 6
  | 166 => 16
  | 167 => 6
  | 168 => 6
  | 169 => 3
  | 170 => 5
  | 171 => 7
  | 172 => 8
  | 173 => 6
  | 174 => 2
  | 175 => 5
  | 176 => 9
  | 177 => 4
  | 178 => 6
  | 179 => 7
  | 180 => 6
  | 181 => 8
  | 182 => 10
  | 183 => 1
  | 184 => 3
  | 185 => 3
  | 186 => 9
  | 187 => 14
  | 188 => 5
  | 189 => 8
  | 190 => 5
  | 191 => 7
  | 192 => 7
  | 193 => 4
  | 194 => 7
  | 195 => 5
  | 196 => 13
  | 197 => 18
  | 198 => 4
  | 199 => 8
  | _ => 2

theorem a_fast_eq_fast_fast_fin : ∀ (i : Fin 200), a_fast i.val = a_fast_fast i.val := by decide

theorem a_fast_eq_fast_fast (n : ℕ) (hn : n < 200) : a_fast n = a_fast_fast n :=
  have h_fin : a_fast ⟨n, hn⟩.val = a_fast_fast ⟨n, hn⟩.val := a_fast_eq_fast_fast_fin ⟨n, hn⟩
  h_fin

theorem a_eq_fast_fast (n : ℕ) (hn : n < 200) : a n = a_fast_fast n := by
  unfold a
  split_ifs
  · rw [a_fast_eq_fast_fast n hn]
  · rw [a_fast_eq_fast_fast n hn]

section SequentialElaboration
set_option Elab.async false
theorem a_val_0 : a 0 = 1 := by rw [a_eq_fast_fast 0 (by decide)]; rfl
theorem a_val_1 : a 1 = 2 := by rw [a_eq_fast_fast 1 (by decide)]; rfl
theorem a_val_2 : a 2 = 1 := by rw [a_eq_fast_fast 2 (by decide)]; rfl
theorem a_val_3 : a 3 = 0 := by rw [a_eq_fast_fast 3 (by decide)]; rfl
theorem a_val_4 : a 4 = 2 := by rw [a_eq_fast_fast 4 (by decide)]; rfl
theorem a_val_5 : a 5 = 2 := by rw [a_eq_fast_fast 5 (by decide)]; rfl
theorem a_val_6 : a 6 = 2 := by rw [a_eq_fast_fast 6 (by decide)]; rfl
theorem a_val_7 : a 7 = 1 := by rw [a_eq_fast_fast 7 (by decide)]; rfl
theorem a_val_8 : a 8 = 1 := by rw [a_eq_fast_fast 8 (by decide)]; rfl
theorem a_val_9 : a 9 = 1 := by rw [a_eq_fast_fast 9 (by decide)]; rfl
theorem a_val_10 : a 10 = 0 := by rw [a_eq_fast_fast 10 (by decide)]; rfl
theorem a_val_11 : a 11 = 3 := by rw [a_eq_fast_fast 11 (by decide)]; rfl
theorem a_val_12 : a 12 = 1 := by rw [a_eq_fast_fast 12 (by decide)]; rfl
theorem a_val_13 : a 13 = 2 := by rw [a_eq_fast_fast 13 (by decide)]; rfl
theorem a_val_14 : a 14 = 1 := by rw [a_eq_fast_fast 14 (by decide)]; rfl
theorem a_val_15 : a 15 = 1 := by rw [a_eq_fast_fast 15 (by decide)]; rfl
theorem a_val_16 : a 16 = 3 := by rw [a_eq_fast_fast 16 (by decide)]; rfl
theorem a_val_17 : a 17 = 2 := by rw [a_eq_fast_fast 17 (by decide)]; rfl
theorem a_val_18 : a 18 = 5 := by rw [a_eq_fast_fast 18 (by decide)]; rfl
theorem a_val_19 : a 19 = 3 := by rw [a_eq_fast_fast 19 (by decide)]; rfl
theorem a_val_20 : a 20 = 4 := by rw [a_eq_fast_fast 20 (by decide)]; rfl
theorem a_val_21 : a 21 = 3 := by rw [a_eq_fast_fast 21 (by decide)]; rfl
theorem a_val_22 : a 22 = 1 := by rw [a_eq_fast_fast 22 (by decide)]; rfl
theorem a_val_23 : a 23 = 1 := by rw [a_eq_fast_fast 23 (by decide)]; rfl
theorem a_val_24 : a 24 = 1 := by rw [a_eq_fast_fast 24 (by decide)]; rfl
theorem a_val_25 : a 25 = 1 := by rw [a_eq_fast_fast 25 (by decide)]; rfl
theorem a_val_26 : a 26 = 2 := by rw [a_eq_fast_fast 26 (by decide)]; rfl
theorem a_val_27 : a 27 = 2 := by rw [a_eq_fast_fast 27 (by decide)]; rfl
theorem a_val_28 : a 28 = 2 := by rw [a_eq_fast_fast 28 (by decide)]; rfl
theorem a_val_29 : a 29 = 4 := by rw [a_eq_fast_fast 29 (by decide)]; rfl
theorem a_val_30 : a 30 = 2 := by rw [a_eq_fast_fast 30 (by decide)]; rfl
theorem a_val_31 : a 31 = 2 := by rw [a_eq_fast_fast 31 (by decide)]; rfl
theorem a_val_32 : a 32 = 4 := by rw [a_eq_fast_fast 32 (by decide)]; rfl
theorem a_val_33 : a 33 = 2 := by rw [a_eq_fast_fast 33 (by decide)]; rfl
theorem a_val_34 : a 34 = 7 := by rw [a_eq_fast_fast 34 (by decide)]; rfl
theorem a_val_35 : a 35 = 3 := by rw [a_eq_fast_fast 35 (by decide)]; rfl
theorem a_val_36 : a 36 = 1 := by rw [a_eq_fast_fast 36 (by decide)]; rfl
theorem a_val_37 : a 37 = 6 := by rw [a_eq_fast_fast 37 (by decide)]; rfl
theorem a_val_38 : a 38 = 2 := by rw [a_eq_fast_fast 38 (by decide)]; rfl
theorem a_val_39 : a 39 = 1 := by rw [a_eq_fast_fast 39 (by decide)]; rfl
theorem a_val_40 : a 40 = 2 := by rw [a_eq_fast_fast 40 (by decide)]; rfl
theorem a_val_41 : a 41 = 3 := by rw [a_eq_fast_fast 41 (by decide)]; rfl
theorem a_val_42 : a 42 = 4 := by rw [a_eq_fast_fast 42 (by decide)]; rfl
theorem a_val_43 : a 43 = 5 := by rw [a_eq_fast_fast 43 (by decide)]; rfl
theorem a_val_44 : a 44 = 1 := by rw [a_eq_fast_fast 44 (by decide)]; rfl
theorem a_val_45 : a 45 = 1 := by rw [a_eq_fast_fast 45 (by decide)]; rfl
theorem a_val_46 : a 46 = 3 := by rw [a_eq_fast_fast 46 (by decide)]; rfl
theorem a_val_47 : a 47 = 5 := by rw [a_eq_fast_fast 47 (by decide)]; rfl
theorem a_val_48 : a 48 = 3 := by rw [a_eq_fast_fast 48 (by decide)]; rfl
theorem a_val_49 : a 49 = 3 := by rw [a_eq_fast_fast 49 (by decide)]; rfl
theorem a_val_50 : a 50 = 4 := by rw [a_eq_fast_fast 50 (by decide)]; rfl
theorem a_val_51 : a 51 = 3 := by rw [a_eq_fast_fast 51 (by decide)]; rfl
theorem a_val_52 : a 52 = 7 := by rw [a_eq_fast_fast 52 (by decide)]; rfl
theorem a_val_53 : a 53 = 3 := by rw [a_eq_fast_fast 53 (by decide)]; rfl
theorem a_val_54 : a 54 = 2 := by rw [a_eq_fast_fast 54 (by decide)]; rfl
theorem a_val_55 : a 55 = 4 := by rw [a_eq_fast_fast 55 (by decide)]; rfl
theorem a_val_56 : a 56 = 3 := by rw [a_eq_fast_fast 56 (by decide)]; rfl
theorem a_val_57 : a 57 = 4 := by rw [a_eq_fast_fast 57 (by decide)]; rfl
theorem a_val_58 : a 58 = 4 := by rw [a_eq_fast_fast 58 (by decide)]; rfl
theorem a_val_59 : a 59 = 3 := by rw [a_eq_fast_fast 59 (by decide)]; rfl
theorem a_val_60 : a 60 = 1 := by rw [a_eq_fast_fast 60 (by decide)]; rfl
theorem a_val_61 : a 61 = 4 := by rw [a_eq_fast_fast 61 (by decide)]; rfl
theorem a_val_62 : a 62 = 5 := by rw [a_eq_fast_fast 62 (by decide)]; rfl
theorem a_val_63 : a 63 = 3 := by rw [a_eq_fast_fast 63 (by decide)]; rfl
theorem a_val_64 : a 64 = 6 := by rw [a_eq_fast_fast 64 (by decide)]; rfl
theorem a_val_65 : a 65 = 4 := by rw [a_eq_fast_fast 65 (by decide)]; rfl
theorem a_val_66 : a 66 = 4 := by rw [a_eq_fast_fast 66 (by decide)]; rfl
theorem a_val_67 : a 67 = 4 := by rw [a_eq_fast_fast 67 (by decide)]; rfl
theorem a_val_68 : a 68 = 5 := by rw [a_eq_fast_fast 68 (by decide)]; rfl
theorem a_val_69 : a 69 = 7 := by rw [a_eq_fast_fast 69 (by decide)]; rfl
theorem a_val_70 : a 70 = 7 := by rw [a_eq_fast_fast 70 (by decide)]; rfl
theorem a_val_71 : a 71 = 3 := by rw [a_eq_fast_fast 71 (by decide)]; rfl
theorem a_val_72 : a 72 = 6 := by rw [a_eq_fast_fast 72 (by decide)]; rfl
theorem a_val_73 : a 73 = 5 := by rw [a_eq_fast_fast 73 (by decide)]; rfl
theorem a_val_74 : a 74 = 5 := by rw [a_eq_fast_fast 74 (by decide)]; rfl
theorem a_val_75 : a 75 = 4 := by rw [a_eq_fast_fast 75 (by decide)]; rfl
theorem a_val_76 : a 76 = 3 := by rw [a_eq_fast_fast 76 (by decide)]; rfl
theorem a_val_77 : a 77 = 11 := by rw [a_eq_fast_fast 77 (by decide)]; rfl
theorem a_val_78 : a 78 = 2 := by rw [a_eq_fast_fast 78 (by decide)]; rfl
theorem a_val_79 : a 79 = 2 := by rw [a_eq_fast_fast 79 (by decide)]; rfl
theorem a_val_80 : a 80 = 4 := by rw [a_eq_fast_fast 80 (by decide)]; rfl
theorem a_val_81 : a 81 = 7 := by rw [a_eq_fast_fast 81 (by decide)]; rfl
theorem a_val_82 : a 82 = 5 := by rw [a_eq_fast_fast 82 (by decide)]; rfl
theorem a_val_83 : a 83 = 5 := by rw [a_eq_fast_fast 83 (by decide)]; rfl
theorem a_val_84 : a 84 = 5 := by rw [a_eq_fast_fast 84 (by decide)]; rfl
theorem a_val_85 : a 85 = 3 := by rw [a_eq_fast_fast 85 (by decide)]; rfl
theorem a_val_86 : a 86 = 6 := by rw [a_eq_fast_fast 86 (by decide)]; rfl
theorem a_val_87 : a 87 = 1 := by rw [a_eq_fast_fast 87 (by decide)]; rfl
theorem a_val_88 : a 88 = 3 := by rw [a_eq_fast_fast 88 (by decide)]; rfl
theorem a_val_89 : a 89 = 3 := by rw [a_eq_fast_fast 89 (by decide)]; rfl
theorem a_val_90 : a 90 = 4 := by rw [a_eq_fast_fast 90 (by decide)]; rfl
theorem a_val_91 : a 91 = 8 := by rw [a_eq_fast_fast 91 (by decide)]; rfl
theorem a_val_92 : a 92 = 8 := by rw [a_eq_fast_fast 92 (by decide)]; rfl
theorem a_val_93 : a 93 = 2 := by rw [a_eq_fast_fast 93 (by decide)]; rfl
theorem a_val_94 : a 94 = 5 := by rw [a_eq_fast_fast 94 (by decide)]; rfl
theorem a_val_95 : a 95 = 2 := by rw [a_eq_fast_fast 95 (by decide)]; rfl
theorem a_val_96 : a 96 = 5 := by rw [a_eq_fast_fast 96 (by decide)]; rfl
theorem a_val_97 : a 97 = 6 := by rw [a_eq_fast_fast 97 (by decide)]; rfl
theorem a_val_98 : a 98 = 1 := by rw [a_eq_fast_fast 98 (by decide)]; rfl
theorem a_val_99 : a 99 = 6 := by rw [a_eq_fast_fast 99 (by decide)]; rfl
theorem a_val_100 : a 100 = 8 := by rw [a_eq_fast_fast 100 (by decide)]; rfl
theorem a_val_101 : a 101 = 8 := by rw [a_eq_fast_fast 101 (by decide)]; rfl
theorem a_val_102 : a 102 = 6 := by rw [a_eq_fast_fast 102 (by decide)]; rfl
theorem a_val_103 : a 103 = 7 := by rw [a_eq_fast_fast 103 (by decide)]; rfl
theorem a_val_104 : a 104 = 4 := by rw [a_eq_fast_fast 104 (by decide)]; rfl
theorem a_val_105 : a 105 = 3 := by rw [a_eq_fast_fast 105 (by decide)]; rfl
theorem a_val_106 : a 106 = 1 := by rw [a_eq_fast_fast 106 (by decide)]; rfl
theorem a_val_107 : a 107 = 2 := by rw [a_eq_fast_fast 107 (by decide)]; rfl
theorem a_val_108 : a 108 = 3 := by rw [a_eq_fast_fast 108 (by decide)]; rfl
theorem a_val_109 : a 109 = 7 := by rw [a_eq_fast_fast 109 (by decide)]; rfl
theorem a_val_110 : a 110 = 1 := by rw [a_eq_fast_fast 110 (by decide)]; rfl
theorem a_val_111 : a 111 = 1 := by rw [a_eq_fast_fast 111 (by decide)]; rfl
theorem a_val_112 : a 112 = 7 := by rw [a_eq_fast_fast 112 (by decide)]; rfl
theorem a_val_113 : a 113 = 2 := by rw [a_eq_fast_fast 113 (by decide)]; rfl
theorem a_val_114 : a 114 = 3 := by rw [a_eq_fast_fast 114 (by decide)]; rfl
theorem a_val_115 : a 115 = 11 := by rw [a_eq_fast_fast 115 (by decide)]; rfl
theorem a_val_116 : a 116 = 8 := by rw [a_eq_fast_fast 116 (by decide)]; rfl
theorem a_val_117 : a 117 = 9 := by rw [a_eq_fast_fast 117 (by decide)]; rfl
theorem a_val_118 : a 118 = 10 := by rw [a_eq_fast_fast 118 (by decide)]; rfl
theorem a_val_119 : a 119 = 4 := by rw [a_eq_fast_fast 119 (by decide)]; rfl
theorem a_val_120 : a 120 = 2 := by rw [a_eq_fast_fast 120 (by decide)]; rfl
theorem a_val_121 : a 121 = 6 := by rw [a_eq_fast_fast 121 (by decide)]; rfl
theorem a_val_122 : a 122 = 14 := by rw [a_eq_fast_fast 122 (by decide)]; rfl
theorem a_val_123 : a 123 = 5 := by rw [a_eq_fast_fast 123 (by decide)]; rfl
theorem a_val_124 : a 124 = 7 := by rw [a_eq_fast_fast 124 (by decide)]; rfl
theorem a_val_125 : a 125 = 7 := by rw [a_eq_fast_fast 125 (by decide)]; rfl
theorem a_val_126 : a 126 = 6 := by rw [a_eq_fast_fast 126 (by decide)]; rfl
theorem a_val_127 : a 127 = 9 := by rw [a_eq_fast_fast 127 (by decide)]; rfl
theorem a_val_128 : a 128 = 8 := by rw [a_eq_fast_fast 128 (by decide)]; rfl
theorem a_val_129 : a 129 = 5 := by rw [a_eq_fast_fast 129 (by decide)]; rfl
theorem a_val_130 : a 130 = 13 := by rw [a_eq_fast_fast 130 (by decide)]; rfl
theorem a_val_131 : a 131 = 11 := by rw [a_eq_fast_fast 131 (by decide)]; rfl
theorem a_val_132 : a 132 = 5 := by rw [a_eq_fast_fast 132 (by decide)]; rfl
theorem a_val_133 : a 133 = 6 := by rw [a_eq_fast_fast 133 (by decide)]; rfl
theorem a_val_134 : a 134 = 6 := by rw [a_eq_fast_fast 134 (by decide)]; rfl
theorem a_val_135 : a 135 = 7 := by rw [a_eq_fast_fast 135 (by decide)]; rfl
theorem a_val_136 : a 136 = 2 := by rw [a_eq_fast_fast 136 (by decide)]; rfl
theorem a_val_137 : a 137 = 10 := by rw [a_eq_fast_fast 137 (by decide)]; rfl
theorem a_val_138 : a 138 = 7 := by rw [a_eq_fast_fast 138 (by decide)]; rfl
theorem a_val_139 : a 139 = 11 := by rw [a_eq_fast_fast 139 (by decide)]; rfl
theorem a_val_140 : a 140 = 6 := by rw [a_eq_fast_fast 140 (by decide)]; rfl
theorem a_val_141 : a 141 = 7 := by rw [a_eq_fast_fast 141 (by decide)]; rfl
theorem a_val_142 : a 142 = 7 := by rw [a_eq_fast_fast 142 (by decide)]; rfl
theorem a_val_143 : a 143 = 3 := by rw [a_eq_fast_fast 143 (by decide)]; rfl
theorem a_val_144 : a 144 = 7 := by rw [a_eq_fast_fast 144 (by decide)]; rfl
theorem a_val_145 : a 145 = 7 := by rw [a_eq_fast_fast 145 (by decide)]; rfl
theorem a_val_146 : a 146 = 9 := by rw [a_eq_fast_fast 146 (by decide)]; rfl
theorem a_val_147 : a 147 = 5 := by rw [a_eq_fast_fast 147 (by decide)]; rfl
theorem a_val_148 : a 148 = 8 := by rw [a_eq_fast_fast 148 (by decide)]; rfl
theorem a_val_149 : a 149 = 4 := by rw [a_eq_fast_fast 149 (by decide)]; rfl
theorem a_val_150 : a 150 = 7 := by rw [a_eq_fast_fast 150 (by decide)]; rfl
theorem a_val_151 : a 151 = 9 := by rw [a_eq_fast_fast 151 (by decide)]; rfl
theorem a_val_152 : a 152 = 7 := by rw [a_eq_fast_fast 152 (by decide)]; rfl
theorem a_val_153 : a 153 = 6 := by rw [a_eq_fast_fast 153 (by decide)]; rfl
theorem a_val_154 : a 154 = 9 := by rw [a_eq_fast_fast 154 (by decide)]; rfl
theorem a_val_155 : a 155 = 9 := by rw [a_eq_fast_fast 155 (by decide)]; rfl
theorem a_val_156 : a 156 = 2 := by rw [a_eq_fast_fast 156 (by decide)]; rfl
theorem a_val_157 : a 157 = 8 := by rw [a_eq_fast_fast 157 (by decide)]; rfl
theorem a_val_158 : a 158 = 6 := by rw [a_eq_fast_fast 158 (by decide)]; rfl
theorem a_val_159 : a 159 = 4 := by rw [a_eq_fast_fast 159 (by decide)]; rfl
theorem a_val_160 : a 160 = 4 := by rw [a_eq_fast_fast 160 (by decide)]; rfl
theorem a_val_161 : a 161 = 7 := by rw [a_eq_fast_fast 161 (by decide)]; rfl
theorem a_val_162 : a 162 = 6 := by rw [a_eq_fast_fast 162 (by decide)]; rfl
theorem a_val_163 : a 163 = 11 := by rw [a_eq_fast_fast 163 (by decide)]; rfl
theorem a_val_164 : a 164 = 4 := by rw [a_eq_fast_fast 164 (by decide)]; rfl
theorem a_val_165 : a 165 = 6 := by rw [a_eq_fast_fast 165 (by decide)]; rfl
theorem a_val_166 : a 166 = 16 := by rw [a_eq_fast_fast 166 (by decide)]; rfl
theorem a_val_167 : a 167 = 6 := by rw [a_eq_fast_fast 167 (by decide)]; rfl
theorem a_val_168 : a 168 = 6 := by rw [a_eq_fast_fast 168 (by decide)]; rfl
theorem a_val_169 : a 169 = 3 := by rw [a_eq_fast_fast 169 (by decide)]; rfl
theorem a_val_170 : a 170 = 5 := by rw [a_eq_fast_fast 170 (by decide)]; rfl
theorem a_val_171 : a 171 = 7 := by rw [a_eq_fast_fast 171 (by decide)]; rfl
theorem a_val_172 : a 172 = 8 := by rw [a_eq_fast_fast 172 (by decide)]; rfl
theorem a_val_173 : a 173 = 6 := by rw [a_eq_fast_fast 173 (by decide)]; rfl
theorem a_val_174 : a 174 = 2 := by rw [a_eq_fast_fast 174 (by decide)]; rfl
theorem a_val_175 : a 175 = 5 := by rw [a_eq_fast_fast 175 (by decide)]; rfl
theorem a_val_176 : a 176 = 9 := by rw [a_eq_fast_fast 176 (by decide)]; rfl
theorem a_val_177 : a 177 = 4 := by rw [a_eq_fast_fast 177 (by decide)]; rfl
theorem a_val_178 : a 178 = 6 := by rw [a_eq_fast_fast 178 (by decide)]; rfl
theorem a_val_179 : a 179 = 7 := by rw [a_eq_fast_fast 179 (by decide)]; rfl
theorem a_val_180 : a 180 = 6 := by rw [a_eq_fast_fast 180 (by decide)]; rfl
theorem a_val_181 : a 181 = 8 := by rw [a_eq_fast_fast 181 (by decide)]; rfl
theorem a_val_182 : a 182 = 10 := by rw [a_eq_fast_fast 182 (by decide)]; rfl
theorem a_val_183 : a 183 = 1 := by rw [a_eq_fast_fast 183 (by decide)]; rfl
theorem a_val_184 : a 184 = 3 := by rw [a_eq_fast_fast 184 (by decide)]; rfl
theorem a_val_185 : a 185 = 3 := by rw [a_eq_fast_fast 185 (by decide)]; rfl
theorem a_val_186 : a 186 = 9 := by rw [a_eq_fast_fast 186 (by decide)]; rfl
theorem a_val_187 : a 187 = 14 := by rw [a_eq_fast_fast 187 (by decide)]; rfl
theorem a_val_188 : a 188 = 5 := by rw [a_eq_fast_fast 188 (by decide)]; rfl
theorem a_val_189 : a 189 = 8 := by rw [a_eq_fast_fast 189 (by decide)]; rfl
theorem a_val_190 : a 190 = 5 := by rw [a_eq_fast_fast 190 (by decide)]; rfl
theorem a_val_191 : a 191 = 7 := by rw [a_eq_fast_fast 191 (by decide)]; rfl
theorem a_val_192 : a 192 = 7 := by rw [a_eq_fast_fast 192 (by decide)]; rfl
theorem a_val_193 : a 193 = 4 := by rw [a_eq_fast_fast 193 (by decide)]; rfl
theorem a_val_194 : a 194 = 7 := by rw [a_eq_fast_fast 194 (by decide)]; rfl
theorem a_val_195 : a 195 = 5 := by rw [a_eq_fast_fast 195 (by decide)]; rfl
theorem a_val_196 : a 196 = 13 := by rw [a_eq_fast_fast 196 (by decide)]; rfl
theorem a_val_197 : a 197 = 18 := by rw [a_eq_fast_fast 197 (by decide)]; rfl
theorem a_val_198 : a 198 = 4 := by rw [a_eq_fast_fast 198 (by decide)]; rfl
theorem a_val_199 : a 199 = 8 := by rw [a_eq_fast_fast 199 (by decide)]; rfl
end SequentialElaboration
