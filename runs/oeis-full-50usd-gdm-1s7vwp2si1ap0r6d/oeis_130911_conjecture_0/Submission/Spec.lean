import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open Nat Finset

/--
A130911: $a(n)$ is the number of primes with odd binary weight among the first $n$ primes minus the number with an even binary weight.
Primes with odd binary weight are called odious primes (A027697); primes with even binary weight are called evil primes (A027699).
$$a(n) = \sum_{k=1}^n \left( \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is odd}\} } - \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is even}\} } \right)$$
where $p_k$ is the $k$-th prime number.
-/
noncomputable def A130911 (n : ℕ) : ℤ :=
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ :=
    if (binary_weight p).bodd then 1 else -1
  Finset.sum (Finset.range n) fun i =>
    let p_i := Nat.nth Nat.Prime i
    weight_parity_sign p_i

theorem A130911_step (n : ℕ) : A130911 (n+1) = A130911 n +
  (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
   let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
   weight_parity_sign (Nat.nth Nat.Prime n)) := by
  dsimp [A130911]
  rw [sum_range_succ]

theorem count_prime_0 : count Nat.Prime 0 = 0 := rfl
theorem count_prime_1 : count Nat.Prime 1 = 0 := by rw [count_succ, count_prime_0]; rfl
theorem count_prime_2 : count Nat.Prime 2 = 0 := by rw [count_succ, count_prime_1]; rfl
theorem count_prime_3 : count Nat.Prime 3 = 1 := by rw [count_succ, count_prime_2]; rfl
theorem count_prime_4 : count Nat.Prime 4 = 2 := by rw [count_succ, count_prime_3]; rfl
theorem count_prime_5 : count Nat.Prime 5 = 2 := by rw [count_succ, count_prime_4]; rfl
theorem count_prime_6 : count Nat.Prime 6 = 3 := by rw [count_succ, count_prime_5]; rfl
theorem count_prime_7 : count Nat.Prime 7 = 3 := by rw [count_succ, count_prime_6]; rfl
theorem count_prime_8 : count Nat.Prime 8 = 4 := by rw [count_succ, count_prime_7]; rfl
theorem count_prime_9 : count Nat.Prime 9 = 4 := by rw [count_succ, count_prime_8]; rfl
theorem count_prime_10 : count Nat.Prime 10 = 4 := by rw [count_succ, count_prime_9]; rfl
theorem count_prime_11 : count Nat.Prime 11 = 4 := by rw [count_succ, count_prime_10]; rfl
theorem count_prime_12 : count Nat.Prime 12 = 5 := by rw [count_succ, count_prime_11]; rfl
theorem count_prime_13 : count Nat.Prime 13 = 5 := by rw [count_succ, count_prime_12]; rfl
theorem count_prime_14 : count Nat.Prime 14 = 6 := by rw [count_succ, count_prime_13]; rfl
theorem count_prime_15 : count Nat.Prime 15 = 6 := by rw [count_succ, count_prime_14]; rfl
theorem count_prime_16 : count Nat.Prime 16 = 6 := by rw [count_succ, count_prime_15]; rfl
theorem count_prime_17 : count Nat.Prime 17 = 6 := by rw [count_succ, count_prime_16]; rfl
theorem count_prime_18 : count Nat.Prime 18 = 7 := by rw [count_succ, count_prime_17]; rfl
theorem count_prime_19 : count Nat.Prime 19 = 7 := by rw [count_succ, count_prime_18]; rfl
theorem count_prime_20 : count Nat.Prime 20 = 8 := by rw [count_succ, count_prime_19]; rfl
theorem count_prime_21 : count Nat.Prime 21 = 8 := by rw [count_succ, count_prime_20]; rfl
theorem count_prime_22 : count Nat.Prime 22 = 8 := by rw [count_succ, count_prime_21]; rfl
theorem count_prime_23 : count Nat.Prime 23 = 8 := by rw [count_succ, count_prime_22]; rfl
theorem count_prime_24 : count Nat.Prime 24 = 9 := by rw [count_succ, count_prime_23]; rfl
theorem count_prime_25 : count Nat.Prime 25 = 9 := by rw [count_succ, count_prime_24]; rfl
theorem count_prime_26 : count Nat.Prime 26 = 9 := by rw [count_succ, count_prime_25]; rfl
theorem count_prime_27 : count Nat.Prime 27 = 9 := by rw [count_succ, count_prime_26]; rfl
theorem count_prime_28 : count Nat.Prime 28 = 9 := by rw [count_succ, count_prime_27]; rfl
theorem count_prime_29 : count Nat.Prime 29 = 9 := by rw [count_succ, count_prime_28]; rfl
theorem count_prime_30 : count Nat.Prime 30 = 10 := by rw [count_succ, count_prime_29]; rfl
theorem count_prime_31 : count Nat.Prime 31 = 10 := by rw [count_succ, count_prime_30]; rfl
theorem count_prime_32 : count Nat.Prime 32 = 11 := by rw [count_succ, count_prime_31]; rfl
theorem count_prime_33 : count Nat.Prime 33 = 11 := by rw [count_succ, count_prime_32]; rfl
theorem count_prime_34 : count Nat.Prime 34 = 11 := by rw [count_succ, count_prime_33]; rfl
theorem count_prime_35 : count Nat.Prime 35 = 11 := by rw [count_succ, count_prime_34]; rfl
theorem count_prime_36 : count Nat.Prime 36 = 11 := by rw [count_succ, count_prime_35]; rfl
theorem count_prime_37 : count Nat.Prime 37 = 11 := by rw [count_succ, count_prime_36]; rfl
theorem count_prime_38 : count Nat.Prime 38 = 12 := by rw [count_succ, count_prime_37]; rfl
theorem count_prime_39 : count Nat.Prime 39 = 12 := by rw [count_succ, count_prime_38]; rfl
theorem count_prime_40 : count Nat.Prime 40 = 12 := by rw [count_succ, count_prime_39]; rfl
theorem count_prime_41 : count Nat.Prime 41 = 12 := by rw [count_succ, count_prime_40]; rfl
theorem count_prime_42 : count Nat.Prime 42 = 13 := by rw [count_succ, count_prime_41]; rfl
theorem count_prime_43 : count Nat.Prime 43 = 13 := by rw [count_succ, count_prime_42]; rfl
theorem count_prime_44 : count Nat.Prime 44 = 14 := by rw [count_succ, count_prime_43]; rfl
theorem count_prime_45 : count Nat.Prime 45 = 14 := by rw [count_succ, count_prime_44]; rfl
theorem count_prime_46 : count Nat.Prime 46 = 14 := by rw [count_succ, count_prime_45]; rfl
theorem count_prime_47 : count Nat.Prime 47 = 14 := by rw [count_succ, count_prime_46]; rfl
theorem count_prime_48 : count Nat.Prime 48 = 15 := by rw [count_succ, count_prime_47]; rfl
theorem count_prime_49 : count Nat.Prime 49 = 15 := by rw [count_succ, count_prime_48]; rfl
theorem count_prime_50 : count Nat.Prime 50 = 15 := by rw [count_succ, count_prime_49]; rfl
theorem count_prime_51 : count Nat.Prime 51 = 15 := by rw [count_succ, count_prime_50]; rfl
theorem count_prime_52 : count Nat.Prime 52 = 15 := by rw [count_succ, count_prime_51]; rfl
theorem count_prime_53 : count Nat.Prime 53 = 15 := by rw [count_succ, count_prime_52]; rfl
theorem count_prime_54 : count Nat.Prime 54 = 16 := by rw [count_succ, count_prime_53]; rfl
theorem count_prime_55 : count Nat.Prime 55 = 16 := by rw [count_succ, count_prime_54]; rfl
theorem count_prime_56 : count Nat.Prime 56 = 16 := by rw [count_succ, count_prime_55]; rfl
theorem count_prime_57 : count Nat.Prime 57 = 16 := by rw [count_succ, count_prime_56]; rfl
theorem count_prime_58 : count Nat.Prime 58 = 16 := by rw [count_succ, count_prime_57]; rfl
theorem count_prime_59 : count Nat.Prime 59 = 16 := by rw [count_succ, count_prime_58]; rfl
theorem count_prime_60 : count Nat.Prime 60 = 17 := by rw [count_succ, count_prime_59]; rfl
theorem count_prime_61 : count Nat.Prime 61 = 17 := by rw [count_succ, count_prime_60]; rfl
theorem count_prime_62 : count Nat.Prime 62 = 18 := by rw [count_succ, count_prime_61]; rfl
theorem count_prime_63 : count Nat.Prime 63 = 18 := by rw [count_succ, count_prime_62]; rfl
theorem count_prime_64 : count Nat.Prime 64 = 18 := by rw [count_succ, count_prime_63]; rfl
theorem count_prime_65 : count Nat.Prime 65 = 18 := by rw [count_succ, count_prime_64]; rfl
theorem count_prime_66 : count Nat.Prime 66 = 18 := by rw [count_succ, count_prime_65]; rfl
theorem count_prime_67 : count Nat.Prime 67 = 18 := by rw [count_succ, count_prime_66]; rfl
theorem count_prime_68 : count Nat.Prime 68 = 19 := by rw [count_succ, count_prime_67]; rfl
theorem count_prime_69 : count Nat.Prime 69 = 19 := by rw [count_succ, count_prime_68]; rfl
theorem count_prime_70 : count Nat.Prime 70 = 19 := by rw [count_succ, count_prime_69]; rfl
theorem count_prime_71 : count Nat.Prime 71 = 19 := by rw [count_succ, count_prime_70]; rfl
theorem count_prime_72 : count Nat.Prime 72 = 20 := by rw [count_succ, count_prime_71]; rfl
theorem count_prime_73 : count Nat.Prime 73 = 20 := by rw [count_succ, count_prime_72]; rfl
theorem count_prime_74 : count Nat.Prime 74 = 21 := by rw [count_succ, count_prime_73]; rfl
theorem count_prime_75 : count Nat.Prime 75 = 21 := by rw [count_succ, count_prime_74]; rfl
theorem count_prime_76 : count Nat.Prime 76 = 21 := by rw [count_succ, count_prime_75]; rfl
theorem count_prime_77 : count Nat.Prime 77 = 21 := by rw [count_succ, count_prime_76]; rfl
theorem count_prime_78 : count Nat.Prime 78 = 21 := by rw [count_succ, count_prime_77]; rfl
theorem count_prime_79 : count Nat.Prime 79 = 21 := by rw [count_succ, count_prime_78]; rfl
theorem count_prime_80 : count Nat.Prime 80 = 22 := by rw [count_succ, count_prime_79]; rfl
theorem count_prime_81 : count Nat.Prime 81 = 22 := by rw [count_succ, count_prime_80]; rfl
theorem count_prime_82 : count Nat.Prime 82 = 22 := by rw [count_succ, count_prime_81]; rfl
theorem count_prime_83 : count Nat.Prime 83 = 22 := by rw [count_succ, count_prime_82]; rfl
theorem count_prime_84 : count Nat.Prime 84 = 23 := by rw [count_succ, count_prime_83]; rfl
theorem count_prime_85 : count Nat.Prime 85 = 23 := by rw [count_succ, count_prime_84]; rfl
theorem count_prime_86 : count Nat.Prime 86 = 23 := by rw [count_succ, count_prime_85]; rfl
theorem count_prime_87 : count Nat.Prime 87 = 23 := by rw [count_succ, count_prime_86]; rfl
theorem count_prime_88 : count Nat.Prime 88 = 23 := by rw [count_succ, count_prime_87]; rfl
theorem count_prime_89 : count Nat.Prime 89 = 23 := by rw [count_succ, count_prime_88]; rfl
theorem count_prime_90 : count Nat.Prime 90 = 24 := by rw [count_succ, count_prime_89]; rfl
theorem count_prime_91 : count Nat.Prime 91 = 24 := by rw [count_succ, count_prime_90]; rfl
theorem count_prime_92 : count Nat.Prime 92 = 24 := by rw [count_succ, count_prime_91]; rfl
theorem count_prime_93 : count Nat.Prime 93 = 24 := by rw [count_succ, count_prime_92]; rfl
theorem count_prime_94 : count Nat.Prime 94 = 24 := by rw [count_succ, count_prime_93]; rfl
theorem count_prime_95 : count Nat.Prime 95 = 24 := by rw [count_succ, count_prime_94]; rfl
theorem count_prime_96 : count Nat.Prime 96 = 24 := by rw [count_succ, count_prime_95]; rfl
theorem count_prime_97 : count Nat.Prime 97 = 24 := by rw [count_succ, count_prime_96]; rfl
theorem count_prime_98 : count Nat.Prime 98 = 25 := by rw [count_succ, count_prime_97]; rfl
theorem count_prime_99 : count Nat.Prime 99 = 25 := by rw [count_succ, count_prime_98]; rfl
theorem count_prime_100 : count Nat.Prime 100 = 25 := by rw [count_succ, count_prime_99]; rfl
theorem count_prime_101 : count Nat.Prime 101 = 25 := by rw [count_succ, count_prime_100]; rfl
theorem count_prime_102 : count Nat.Prime 102 = 26 := by rw [count_succ, count_prime_101]; rfl
theorem count_prime_103 : count Nat.Prime 103 = 26 := by rw [count_succ, count_prime_102]; rfl
theorem count_prime_104 : count Nat.Prime 104 = 27 := by rw [count_succ, count_prime_103]; rfl
theorem count_prime_105 : count Nat.Prime 105 = 27 := by rw [count_succ, count_prime_104]; rfl
theorem count_prime_106 : count Nat.Prime 106 = 27 := by rw [count_succ, count_prime_105]; rfl
theorem count_prime_107 : count Nat.Prime 107 = 27 := by rw [count_succ, count_prime_106]; rfl
theorem count_prime_108 : count Nat.Prime 108 = 28 := by rw [count_succ, count_prime_107]; rfl
theorem count_prime_109 : count Nat.Prime 109 = 28 := by rw [count_succ, count_prime_108]; rfl
theorem count_prime_110 : count Nat.Prime 110 = 29 := by rw [count_succ, count_prime_109]; rfl
theorem count_prime_111 : count Nat.Prime 111 = 29 := by rw [count_succ, count_prime_110]; rfl
theorem count_prime_112 : count Nat.Prime 112 = 29 := by rw [count_succ, count_prime_111]; rfl
theorem count_prime_113 : count Nat.Prime 113 = 29 := by rw [count_succ, count_prime_112]; rfl
theorem count_prime_114 : count Nat.Prime 114 = 30 := by rw [count_succ, count_prime_113]; rfl
theorem count_prime_115 : count Nat.Prime 115 = 30 := by rw [count_succ, count_prime_114]; rfl
theorem count_prime_116 : count Nat.Prime 116 = 30 := by rw [count_succ, count_prime_115]; rfl
theorem count_prime_117 : count Nat.Prime 117 = 30 := by rw [count_succ, count_prime_116]; rfl
theorem count_prime_118 : count Nat.Prime 118 = 30 := by rw [count_succ, count_prime_117]; rfl
theorem count_prime_119 : count Nat.Prime 119 = 30 := by rw [count_succ, count_prime_118]; rfl
theorem count_prime_120 : count Nat.Prime 120 = 30 := by rw [count_succ, count_prime_119]; rfl
theorem count_prime_121 : count Nat.Prime 121 = 30 := by rw [count_succ, count_prime_120]; rfl
theorem count_prime_122 : count Nat.Prime 122 = 30 := by rw [count_succ, count_prime_121]; rfl
theorem count_prime_123 : count Nat.Prime 123 = 30 := by rw [count_succ, count_prime_122]; rfl
theorem count_prime_124 : count Nat.Prime 124 = 30 := by rw [count_succ, count_prime_123]; rfl
theorem count_prime_125 : count Nat.Prime 125 = 30 := by rw [count_succ, count_prime_124]; rfl
theorem count_prime_126 : count Nat.Prime 126 = 30 := by rw [count_succ, count_prime_125]; rfl
theorem count_prime_127 : count Nat.Prime 127 = 30 := by rw [count_succ, count_prime_126]; rfl
theorem count_prime_128 : count Nat.Prime 128 = 31 := by rw [count_succ, count_prime_127]; rfl
theorem count_prime_129 : count Nat.Prime 129 = 31 := by rw [count_succ, count_prime_128]; rfl
theorem count_prime_130 : count Nat.Prime 130 = 31 := by rw [count_succ, count_prime_129]; rfl
theorem count_prime_131 : count Nat.Prime 131 = 31 := by rw [count_succ, count_prime_130]; rfl
theorem count_prime_132 : count Nat.Prime 132 = 32 := by rw [count_succ, count_prime_131]; rfl
theorem count_prime_133 : count Nat.Prime 133 = 32 := by rw [count_succ, count_prime_132]; rfl
theorem count_prime_134 : count Nat.Prime 134 = 32 := by rw [count_succ, count_prime_133]; rfl
theorem count_prime_135 : count Nat.Prime 135 = 32 := by rw [count_succ, count_prime_134]; rfl
theorem count_prime_136 : count Nat.Prime 136 = 32 := by rw [count_succ, count_prime_135]; rfl
theorem count_prime_137 : count Nat.Prime 137 = 32 := by rw [count_succ, count_prime_136]; rfl
theorem count_prime_138 : count Nat.Prime 138 = 33 := by rw [count_succ, count_prime_137]; rfl
theorem count_prime_139 : count Nat.Prime 139 = 33 := by rw [count_succ, count_prime_138]; rfl
theorem count_prime_140 : count Nat.Prime 140 = 34 := by rw [count_succ, count_prime_139]; rfl
theorem count_prime_141 : count Nat.Prime 141 = 34 := by rw [count_succ, count_prime_140]; rfl
theorem count_prime_142 : count Nat.Prime 142 = 34 := by rw [count_succ, count_prime_141]; rfl
theorem count_prime_143 : count Nat.Prime 143 = 34 := by rw [count_succ, count_prime_142]; rfl
theorem count_prime_144 : count Nat.Prime 144 = 34 := by rw [count_succ, count_prime_143]; rfl
theorem count_prime_145 : count Nat.Prime 145 = 34 := by rw [count_succ, count_prime_144]; rfl
theorem count_prime_146 : count Nat.Prime 146 = 34 := by rw [count_succ, count_prime_145]; rfl
theorem count_prime_147 : count Nat.Prime 147 = 34 := by rw [count_succ, count_prime_146]; rfl
theorem count_prime_148 : count Nat.Prime 148 = 34 := by rw [count_succ, count_prime_147]; rfl
theorem count_prime_149 : count Nat.Prime 149 = 34 := by rw [count_succ, count_prime_148]; rfl
theorem count_prime_150 : count Nat.Prime 150 = 35 := by rw [count_succ, count_prime_149]; rfl
theorem count_prime_151 : count Nat.Prime 151 = 35 := by rw [count_succ, count_prime_150]; rfl
theorem count_prime_152 : count Nat.Prime 152 = 36 := by rw [count_succ, count_prime_151]; rfl
theorem count_prime_153 : count Nat.Prime 153 = 36 := by rw [count_succ, count_prime_152]; rfl
theorem count_prime_154 : count Nat.Prime 154 = 36 := by rw [count_succ, count_prime_153]; rfl
theorem count_prime_155 : count Nat.Prime 155 = 36 := by rw [count_succ, count_prime_154]; rfl
theorem count_prime_156 : count Nat.Prime 156 = 36 := by rw [count_succ, count_prime_155]; rfl
theorem count_prime_157 : count Nat.Prime 157 = 36 := by rw [count_succ, count_prime_156]; rfl
theorem count_prime_158 : count Nat.Prime 158 = 37 := by rw [count_succ, count_prime_157]; rfl
theorem count_prime_159 : count Nat.Prime 159 = 37 := by rw [count_succ, count_prime_158]; rfl
theorem count_prime_160 : count Nat.Prime 160 = 37 := by rw [count_succ, count_prime_159]; rfl
theorem count_prime_161 : count Nat.Prime 161 = 37 := by rw [count_succ, count_prime_160]; rfl
theorem count_prime_162 : count Nat.Prime 162 = 37 := by rw [count_succ, count_prime_161]; rfl
theorem count_prime_163 : count Nat.Prime 163 = 37 := by rw [count_succ, count_prime_162]; rfl
theorem count_prime_164 : count Nat.Prime 164 = 38 := by rw [count_succ, count_prime_163]; rfl
theorem count_prime_165 : count Nat.Prime 165 = 38 := by rw [count_succ, count_prime_164]; rfl
theorem count_prime_166 : count Nat.Prime 166 = 38 := by rw [count_succ, count_prime_165]; rfl
theorem count_prime_167 : count Nat.Prime 167 = 38 := by rw [count_succ, count_prime_166]; rfl
theorem count_prime_168 : count Nat.Prime 168 = 39 := by rw [count_succ, count_prime_167]; rfl
theorem count_prime_169 : count Nat.Prime 169 = 39 := by rw [count_succ, count_prime_168]; rfl
theorem count_prime_170 : count Nat.Prime 170 = 39 := by rw [count_succ, count_prime_169]; rfl
theorem count_prime_171 : count Nat.Prime 171 = 39 := by rw [count_succ, count_prime_170]; rfl
theorem count_prime_172 : count Nat.Prime 172 = 39 := by rw [count_succ, count_prime_171]; rfl
theorem count_prime_173 : count Nat.Prime 173 = 39 := by rw [count_succ, count_prime_172]; rfl
theorem count_prime_174 : count Nat.Prime 174 = 40 := by rw [count_succ, count_prime_173]; rfl
theorem count_prime_175 : count Nat.Prime 175 = 40 := by rw [count_succ, count_prime_174]; rfl
theorem count_prime_176 : count Nat.Prime 176 = 40 := by rw [count_succ, count_prime_175]; rfl
theorem count_prime_177 : count Nat.Prime 177 = 40 := by rw [count_succ, count_prime_176]; rfl
theorem count_prime_178 : count Nat.Prime 178 = 40 := by rw [count_succ, count_prime_177]; rfl
theorem count_prime_179 : count Nat.Prime 179 = 40 := by rw [count_succ, count_prime_178]; rfl
theorem count_prime_180 : count Nat.Prime 180 = 41 := by rw [count_succ, count_prime_179]; rfl
theorem count_prime_181 : count Nat.Prime 181 = 41 := by rw [count_succ, count_prime_180]; rfl
theorem count_prime_182 : count Nat.Prime 182 = 42 := by rw [count_succ, count_prime_181]; rfl
theorem count_prime_183 : count Nat.Prime 183 = 42 := by rw [count_succ, count_prime_182]; rfl
theorem count_prime_184 : count Nat.Prime 184 = 42 := by rw [count_succ, count_prime_183]; rfl
theorem count_prime_185 : count Nat.Prime 185 = 42 := by rw [count_succ, count_prime_184]; rfl
theorem count_prime_186 : count Nat.Prime 186 = 42 := by rw [count_succ, count_prime_185]; rfl
theorem count_prime_187 : count Nat.Prime 187 = 42 := by rw [count_succ, count_prime_186]; rfl
theorem count_prime_188 : count Nat.Prime 188 = 42 := by rw [count_succ, count_prime_187]; rfl
theorem count_prime_189 : count Nat.Prime 189 = 42 := by rw [count_succ, count_prime_188]; rfl
theorem count_prime_190 : count Nat.Prime 190 = 42 := by rw [count_succ, count_prime_189]; rfl
theorem count_prime_191 : count Nat.Prime 191 = 42 := by rw [count_succ, count_prime_190]; rfl
theorem count_prime_192 : count Nat.Prime 192 = 43 := by rw [count_succ, count_prime_191]; rfl
theorem count_prime_193 : count Nat.Prime 193 = 43 := by rw [count_succ, count_prime_192]; rfl
theorem count_prime_194 : count Nat.Prime 194 = 44 := by rw [count_succ, count_prime_193]; rfl
theorem count_prime_195 : count Nat.Prime 195 = 44 := by rw [count_succ, count_prime_194]; rfl
theorem count_prime_196 : count Nat.Prime 196 = 44 := by rw [count_succ, count_prime_195]; rfl
theorem count_prime_197 : count Nat.Prime 197 = 44 := by rw [count_succ, count_prime_196]; rfl
theorem count_prime_198 : count Nat.Prime 198 = 45 := by rw [count_succ, count_prime_197]; rfl
theorem count_prime_199 : count Nat.Prime 199 = 45 := by rw [count_succ, count_prime_198]; rfl
theorem count_prime_200 : count Nat.Prime 200 = 46 := by rw [count_succ, count_prime_199]; rfl
theorem count_prime_201 : count Nat.Prime 201 = 46 := by rw [count_succ, count_prime_200]; rfl
theorem count_prime_202 : count Nat.Prime 202 = 46 := by rw [count_succ, count_prime_201]; rfl
theorem count_prime_203 : count Nat.Prime 203 = 46 := by rw [count_succ, count_prime_202]; rfl
theorem count_prime_204 : count Nat.Prime 204 = 46 := by rw [count_succ, count_prime_203]; rfl
theorem count_prime_205 : count Nat.Prime 205 = 46 := by rw [count_succ, count_prime_204]; rfl
theorem count_prime_206 : count Nat.Prime 206 = 46 := by rw [count_succ, count_prime_205]; rfl
theorem count_prime_207 : count Nat.Prime 207 = 46 := by rw [count_succ, count_prime_206]; rfl
theorem count_prime_208 : count Nat.Prime 208 = 46 := by rw [count_succ, count_prime_207]; rfl
theorem count_prime_209 : count Nat.Prime 209 = 46 := by rw [count_succ, count_prime_208]; rfl
theorem count_prime_210 : count Nat.Prime 210 = 46 := by rw [count_succ, count_prime_209]; rfl
theorem count_prime_211 : count Nat.Prime 211 = 46 := by rw [count_succ, count_prime_210]; rfl
theorem count_prime_212 : count Nat.Prime 212 = 47 := by rw [count_succ, count_prime_211]; rfl
theorem count_prime_213 : count Nat.Prime 213 = 47 := by rw [count_succ, count_prime_212]; rfl
theorem count_prime_214 : count Nat.Prime 214 = 47 := by rw [count_succ, count_prime_213]; rfl
theorem count_prime_215 : count Nat.Prime 215 = 47 := by rw [count_succ, count_prime_214]; rfl
theorem count_prime_216 : count Nat.Prime 216 = 47 := by rw [count_succ, count_prime_215]; rfl
theorem count_prime_217 : count Nat.Prime 217 = 47 := by rw [count_succ, count_prime_216]; rfl
theorem count_prime_218 : count Nat.Prime 218 = 47 := by rw [count_succ, count_prime_217]; rfl
theorem count_prime_219 : count Nat.Prime 219 = 47 := by rw [count_succ, count_prime_218]; rfl
theorem count_prime_220 : count Nat.Prime 220 = 47 := by rw [count_succ, count_prime_219]; rfl
theorem count_prime_221 : count Nat.Prime 221 = 47 := by rw [count_succ, count_prime_220]; rfl
theorem count_prime_222 : count Nat.Prime 222 = 47 := by rw [count_succ, count_prime_221]; rfl
theorem count_prime_223 : count Nat.Prime 223 = 47 := by rw [count_succ, count_prime_222]; rfl
theorem count_prime_224 : count Nat.Prime 224 = 48 := by rw [count_succ, count_prime_223]; rfl
theorem count_prime_225 : count Nat.Prime 225 = 48 := by rw [count_succ, count_prime_224]; rfl
theorem count_prime_226 : count Nat.Prime 226 = 48 := by rw [count_succ, count_prime_225]; rfl
theorem count_prime_227 : count Nat.Prime 227 = 48 := by rw [count_succ, count_prime_226]; rfl
theorem count_prime_228 : count Nat.Prime 228 = 49 := by rw [count_succ, count_prime_227]; rfl
theorem count_prime_229 : count Nat.Prime 229 = 49 := by rw [count_succ, count_prime_228]; rfl
theorem count_prime_230 : count Nat.Prime 230 = 50 := by rw [count_succ, count_prime_229]; rfl
theorem count_prime_231 : count Nat.Prime 231 = 50 := by rw [count_succ, count_prime_230]; rfl
theorem count_prime_232 : count Nat.Prime 232 = 50 := by rw [count_succ, count_prime_231]; rfl
theorem count_prime_233 : count Nat.Prime 233 = 50 := by rw [count_succ, count_prime_232]; rfl
theorem count_prime_234 : count Nat.Prime 234 = 51 := by rw [count_succ, count_prime_233]; rfl
theorem count_prime_235 : count Nat.Prime 235 = 51 := by rw [count_succ, count_prime_234]; rfl
theorem count_prime_236 : count Nat.Prime 236 = 51 := by rw [count_succ, count_prime_235]; rfl
theorem count_prime_237 : count Nat.Prime 237 = 51 := by rw [count_succ, count_prime_236]; rfl
theorem count_prime_238 : count Nat.Prime 238 = 51 := by rw [count_succ, count_prime_237]; rfl
theorem count_prime_239 : count Nat.Prime 239 = 51 := by rw [count_succ, count_prime_238]; rfl
theorem count_prime_240 : count Nat.Prime 240 = 52 := by rw [count_succ, count_prime_239]; rfl
theorem count_prime_241 : count Nat.Prime 241 = 52 := by rw [count_succ, count_prime_240]; rfl
theorem count_prime_242 : count Nat.Prime 242 = 53 := by rw [count_succ, count_prime_241]; rfl
theorem count_prime_243 : count Nat.Prime 243 = 53 := by rw [count_succ, count_prime_242]; rfl
theorem count_prime_244 : count Nat.Prime 244 = 53 := by rw [count_succ, count_prime_243]; rfl
theorem count_prime_245 : count Nat.Prime 245 = 53 := by rw [count_succ, count_prime_244]; rfl
theorem count_prime_246 : count Nat.Prime 246 = 53 := by rw [count_succ, count_prime_245]; rfl
theorem count_prime_247 : count Nat.Prime 247 = 53 := by rw [count_succ, count_prime_246]; rfl
theorem count_prime_248 : count Nat.Prime 248 = 53 := by rw [count_succ, count_prime_247]; rfl
theorem count_prime_249 : count Nat.Prime 249 = 53 := by rw [count_succ, count_prime_248]; rfl
theorem count_prime_250 : count Nat.Prime 250 = 53 := by rw [count_succ, count_prime_249]; rfl
theorem count_prime_251 : count Nat.Prime 251 = 53 := by rw [count_succ, count_prime_250]; rfl
theorem count_prime_252 : count Nat.Prime 252 = 54 := by rw [count_succ, count_prime_251]; rfl
theorem count_prime_253 : count Nat.Prime 253 = 54 := by rw [count_succ, count_prime_252]; rfl
theorem count_prime_254 : count Nat.Prime 254 = 54 := by rw [count_succ, count_prime_253]; rfl
theorem count_prime_255 : count Nat.Prime 255 = 54 := by rw [count_succ, count_prime_254]; rfl
theorem count_prime_256 : count Nat.Prime 256 = 54 := by rw [count_succ, count_prime_255]; rfl
theorem count_prime_257 : count Nat.Prime 257 = 54 := by rw [count_succ, count_prime_256]; rfl
theorem count_prime_258 : count Nat.Prime 258 = 55 := by rw [count_succ, count_prime_257]; rfl
theorem count_prime_259 : count Nat.Prime 259 = 55 := by rw [count_succ, count_prime_258]; rfl
theorem count_prime_260 : count Nat.Prime 260 = 55 := by rw [count_succ, count_prime_259]; rfl
theorem count_prime_261 : count Nat.Prime 261 = 55 := by rw [count_succ, count_prime_260]; rfl
theorem count_prime_262 : count Nat.Prime 262 = 55 := by rw [count_succ, count_prime_261]; rfl
theorem count_prime_263 : count Nat.Prime 263 = 55 := by rw [count_succ, count_prime_262]; rfl
theorem count_prime_264 : count Nat.Prime 264 = 56 := by rw [count_succ, count_prime_263]; rfl
theorem count_prime_265 : count Nat.Prime 265 = 56 := by rw [count_succ, count_prime_264]; rfl
theorem count_prime_266 : count Nat.Prime 266 = 56 := by rw [count_succ, count_prime_265]; rfl
theorem count_prime_267 : count Nat.Prime 267 = 56 := by rw [count_succ, count_prime_266]; rfl
theorem count_prime_268 : count Nat.Prime 268 = 56 := by rw [count_succ, count_prime_267]; rfl
theorem count_prime_269 : count Nat.Prime 269 = 56 := by rw [count_succ, count_prime_268]; rfl
theorem count_prime_270 : count Nat.Prime 270 = 57 := by rw [count_succ, count_prime_269]; rfl
theorem count_prime_271 : count Nat.Prime 271 = 57 := by rw [count_succ, count_prime_270]; rfl
theorem count_prime_272 : count Nat.Prime 272 = 58 := by rw [count_succ, count_prime_271]; rfl
theorem count_prime_273 : count Nat.Prime 273 = 58 := by rw [count_succ, count_prime_272]; rfl
theorem count_prime_274 : count Nat.Prime 274 = 58 := by rw [count_succ, count_prime_273]; rfl
theorem count_prime_275 : count Nat.Prime 275 = 58 := by rw [count_succ, count_prime_274]; rfl
theorem count_prime_276 : count Nat.Prime 276 = 58 := by rw [count_succ, count_prime_275]; rfl
theorem count_prime_277 : count Nat.Prime 277 = 58 := by rw [count_succ, count_prime_276]; rfl
theorem count_prime_278 : count Nat.Prime 278 = 59 := by rw [count_succ, count_prime_277]; rfl
theorem count_prime_279 : count Nat.Prime 279 = 59 := by rw [count_succ, count_prime_278]; rfl
theorem count_prime_280 : count Nat.Prime 280 = 59 := by rw [count_succ, count_prime_279]; rfl
theorem count_prime_281 : count Nat.Prime 281 = 59 := by rw [count_succ, count_prime_280]; rfl
theorem count_prime_282 : count Nat.Prime 282 = 60 := by rw [count_succ, count_prime_281]; rfl
theorem count_prime_283 : count Nat.Prime 283 = 60 := by rw [count_succ, count_prime_282]; rfl
theorem count_prime_284 : count Nat.Prime 284 = 61 := by rw [count_succ, count_prime_283]; rfl
theorem count_prime_285 : count Nat.Prime 285 = 61 := by rw [count_succ, count_prime_284]; rfl
theorem count_prime_286 : count Nat.Prime 286 = 61 := by rw [count_succ, count_prime_285]; rfl
theorem count_prime_287 : count Nat.Prime 287 = 61 := by rw [count_succ, count_prime_286]; rfl
theorem count_prime_288 : count Nat.Prime 288 = 61 := by rw [count_succ, count_prime_287]; rfl
theorem count_prime_289 : count Nat.Prime 289 = 61 := by rw [count_succ, count_prime_288]; rfl
theorem count_prime_290 : count Nat.Prime 290 = 61 := by rw [count_succ, count_prime_289]; rfl
theorem count_prime_291 : count Nat.Prime 291 = 61 := by rw [count_succ, count_prime_290]; rfl
theorem count_prime_292 : count Nat.Prime 292 = 61 := by rw [count_succ, count_prime_291]; rfl
theorem count_prime_293 : count Nat.Prime 293 = 61 := by rw [count_succ, count_prime_292]; rfl
theorem count_prime_294 : count Nat.Prime 294 = 62 := by rw [count_succ, count_prime_293]; rfl
theorem count_prime_295 : count Nat.Prime 295 = 62 := by rw [count_succ, count_prime_294]; rfl
theorem count_prime_296 : count Nat.Prime 296 = 62 := by rw [count_succ, count_prime_295]; rfl
theorem count_prime_297 : count Nat.Prime 297 = 62 := by rw [count_succ, count_prime_296]; rfl
theorem count_prime_298 : count Nat.Prime 298 = 62 := by rw [count_succ, count_prime_297]; rfl
theorem count_prime_299 : count Nat.Prime 299 = 62 := by rw [count_succ, count_prime_298]; rfl
theorem count_prime_300 : count Nat.Prime 300 = 62 := by rw [count_succ, count_prime_299]; rfl
theorem count_prime_301 : count Nat.Prime 301 = 62 := by rw [count_succ, count_prime_300]; rfl
theorem count_prime_302 : count Nat.Prime 302 = 62 := by rw [count_succ, count_prime_301]; rfl
theorem count_prime_303 : count Nat.Prime 303 = 62 := by rw [count_succ, count_prime_302]; rfl
theorem count_prime_304 : count Nat.Prime 304 = 62 := by rw [count_succ, count_prime_303]; rfl
theorem count_prime_305 : count Nat.Prime 305 = 62 := by rw [count_succ, count_prime_304]; rfl
theorem count_prime_306 : count Nat.Prime 306 = 62 := by rw [count_succ, count_prime_305]; rfl
theorem count_prime_307 : count Nat.Prime 307 = 62 := by rw [count_succ, count_prime_306]; rfl
theorem count_prime_308 : count Nat.Prime 308 = 63 := by rw [count_succ, count_prime_307]; rfl
theorem count_prime_309 : count Nat.Prime 309 = 63 := by rw [count_succ, count_prime_308]; rfl
theorem count_prime_310 : count Nat.Prime 310 = 63 := by rw [count_succ, count_prime_309]; rfl
theorem count_prime_311 : count Nat.Prime 311 = 63 := by rw [count_succ, count_prime_310]; rfl
theorem count_prime_312 : count Nat.Prime 312 = 64 := by rw [count_succ, count_prime_311]; rfl
theorem count_prime_313 : count Nat.Prime 313 = 64 := by rw [count_succ, count_prime_312]; rfl
theorem count_prime_314 : count Nat.Prime 314 = 65 := by rw [count_succ, count_prime_313]; rfl
theorem count_prime_315 : count Nat.Prime 315 = 65 := by rw [count_succ, count_prime_314]; rfl
theorem count_prime_316 : count Nat.Prime 316 = 65 := by rw [count_succ, count_prime_315]; rfl
theorem count_prime_317 : count Nat.Prime 317 = 65 := by rw [count_succ, count_prime_316]; rfl
theorem count_prime_318 : count Nat.Prime 318 = 66 := by rw [count_succ, count_prime_317]; rfl
theorem count_prime_319 : count Nat.Prime 319 = 66 := by rw [count_succ, count_prime_318]; rfl
theorem count_prime_320 : count Nat.Prime 320 = 66 := by rw [count_succ, count_prime_319]; rfl
theorem count_prime_321 : count Nat.Prime 321 = 66 := by rw [count_succ, count_prime_320]; rfl
theorem count_prime_322 : count Nat.Prime 322 = 66 := by rw [count_succ, count_prime_321]; rfl
theorem count_prime_323 : count Nat.Prime 323 = 66 := by rw [count_succ, count_prime_322]; rfl
theorem count_prime_324 : count Nat.Prime 324 = 66 := by rw [count_succ, count_prime_323]; rfl
theorem count_prime_325 : count Nat.Prime 325 = 66 := by rw [count_succ, count_prime_324]; rfl
theorem count_prime_326 : count Nat.Prime 326 = 66 := by rw [count_succ, count_prime_325]; rfl
theorem count_prime_327 : count Nat.Prime 327 = 66 := by rw [count_succ, count_prime_326]; rfl
theorem count_prime_328 : count Nat.Prime 328 = 66 := by rw [count_succ, count_prime_327]; rfl
theorem count_prime_329 : count Nat.Prime 329 = 66 := by rw [count_succ, count_prime_328]; rfl
theorem count_prime_330 : count Nat.Prime 330 = 66 := by rw [count_succ, count_prime_329]; rfl
theorem count_prime_331 : count Nat.Prime 331 = 66 := by rw [count_succ, count_prime_330]; rfl
theorem count_prime_332 : count Nat.Prime 332 = 67 := by rw [count_succ, count_prime_331]; rfl
theorem count_prime_333 : count Nat.Prime 333 = 67 := by rw [count_succ, count_prime_332]; rfl
theorem count_prime_334 : count Nat.Prime 334 = 67 := by rw [count_succ, count_prime_333]; rfl
theorem count_prime_335 : count Nat.Prime 335 = 67 := by rw [count_succ, count_prime_334]; rfl
theorem count_prime_336 : count Nat.Prime 336 = 67 := by rw [count_succ, count_prime_335]; rfl
theorem count_prime_337 : count Nat.Prime 337 = 67 := by rw [count_succ, count_prime_336]; rfl
theorem count_prime_338 : count Nat.Prime 338 = 68 := by rw [count_succ, count_prime_337]; rfl
theorem count_prime_339 : count Nat.Prime 339 = 68 := by rw [count_succ, count_prime_338]; rfl
theorem count_prime_340 : count Nat.Prime 340 = 68 := by rw [count_succ, count_prime_339]; rfl
theorem count_prime_341 : count Nat.Prime 341 = 68 := by rw [count_succ, count_prime_340]; rfl
theorem count_prime_342 : count Nat.Prime 342 = 68 := by rw [count_succ, count_prime_341]; rfl
theorem count_prime_343 : count Nat.Prime 343 = 68 := by rw [count_succ, count_prime_342]; rfl
theorem count_prime_344 : count Nat.Prime 344 = 68 := by rw [count_succ, count_prime_343]; rfl
theorem count_prime_345 : count Nat.Prime 345 = 68 := by rw [count_succ, count_prime_344]; rfl
theorem count_prime_346 : count Nat.Prime 346 = 68 := by rw [count_succ, count_prime_345]; rfl
theorem count_prime_347 : count Nat.Prime 347 = 68 := by rw [count_succ, count_prime_346]; rfl
theorem count_prime_348 : count Nat.Prime 348 = 69 := by rw [count_succ, count_prime_347]; rfl
theorem count_prime_349 : count Nat.Prime 349 = 69 := by rw [count_succ, count_prime_348]; rfl
theorem count_prime_350 : count Nat.Prime 350 = 70 := by rw [count_succ, count_prime_349]; rfl
theorem count_prime_351 : count Nat.Prime 351 = 70 := by rw [count_succ, count_prime_350]; rfl
theorem count_prime_352 : count Nat.Prime 352 = 70 := by rw [count_succ, count_prime_351]; rfl
theorem count_prime_353 : count Nat.Prime 353 = 70 := by rw [count_succ, count_prime_352]; rfl
theorem count_prime_354 : count Nat.Prime 354 = 71 := by rw [count_succ, count_prime_353]; rfl
theorem count_prime_355 : count Nat.Prime 355 = 71 := by rw [count_succ, count_prime_354]; rfl
theorem count_prime_356 : count Nat.Prime 356 = 71 := by rw [count_succ, count_prime_355]; rfl
theorem count_prime_357 : count Nat.Prime 357 = 71 := by rw [count_succ, count_prime_356]; rfl
theorem count_prime_358 : count Nat.Prime 358 = 71 := by rw [count_succ, count_prime_357]; rfl
theorem count_prime_359 : count Nat.Prime 359 = 71 := by rw [count_succ, count_prime_358]; rfl
theorem count_prime_360 : count Nat.Prime 360 = 72 := by rw [count_succ, count_prime_359]; rfl
theorem count_prime_361 : count Nat.Prime 361 = 72 := by rw [count_succ, count_prime_360]; rfl
theorem count_prime_362 : count Nat.Prime 362 = 72 := by rw [count_succ, count_prime_361]; rfl
theorem count_prime_363 : count Nat.Prime 363 = 72 := by rw [count_succ, count_prime_362]; rfl
theorem count_prime_364 : count Nat.Prime 364 = 72 := by rw [count_succ, count_prime_363]; rfl
theorem count_prime_365 : count Nat.Prime 365 = 72 := by rw [count_succ, count_prime_364]; rfl
theorem count_prime_366 : count Nat.Prime 366 = 72 := by rw [count_succ, count_prime_365]; rfl
theorem count_prime_367 : count Nat.Prime 367 = 72 := by rw [count_succ, count_prime_366]; rfl
theorem count_prime_368 : count Nat.Prime 368 = 73 := by rw [count_succ, count_prime_367]; rfl
theorem count_prime_369 : count Nat.Prime 369 = 73 := by rw [count_succ, count_prime_368]; rfl
theorem count_prime_370 : count Nat.Prime 370 = 73 := by rw [count_succ, count_prime_369]; rfl
theorem count_prime_371 : count Nat.Prime 371 = 73 := by rw [count_succ, count_prime_370]; rfl
theorem count_prime_372 : count Nat.Prime 372 = 73 := by rw [count_succ, count_prime_371]; rfl
theorem count_prime_373 : count Nat.Prime 373 = 73 := by rw [count_succ, count_prime_372]; rfl
theorem count_prime_374 : count Nat.Prime 374 = 74 := by rw [count_succ, count_prime_373]; rfl
theorem count_prime_375 : count Nat.Prime 375 = 74 := by rw [count_succ, count_prime_374]; rfl
theorem count_prime_376 : count Nat.Prime 376 = 74 := by rw [count_succ, count_prime_375]; rfl
theorem count_prime_377 : count Nat.Prime 377 = 74 := by rw [count_succ, count_prime_376]; rfl
theorem count_prime_378 : count Nat.Prime 378 = 74 := by rw [count_succ, count_prime_377]; rfl
theorem count_prime_379 : count Nat.Prime 379 = 74 := by rw [count_succ, count_prime_378]; rfl
theorem count_prime_380 : count Nat.Prime 380 = 75 := by rw [count_succ, count_prime_379]; rfl
theorem count_prime_381 : count Nat.Prime 381 = 75 := by rw [count_succ, count_prime_380]; rfl
theorem count_prime_382 : count Nat.Prime 382 = 75 := by rw [count_succ, count_prime_381]; rfl
theorem count_prime_383 : count Nat.Prime 383 = 75 := by rw [count_succ, count_prime_382]; rfl
theorem count_prime_384 : count Nat.Prime 384 = 76 := by rw [count_succ, count_prime_383]; rfl
theorem count_prime_385 : count Nat.Prime 385 = 76 := by rw [count_succ, count_prime_384]; rfl
theorem count_prime_386 : count Nat.Prime 386 = 76 := by rw [count_succ, count_prime_385]; rfl
theorem count_prime_387 : count Nat.Prime 387 = 76 := by rw [count_succ, count_prime_386]; rfl
theorem count_prime_388 : count Nat.Prime 388 = 76 := by rw [count_succ, count_prime_387]; rfl
theorem count_prime_389 : count Nat.Prime 389 = 76 := by rw [count_succ, count_prime_388]; rfl
theorem count_prime_390 : count Nat.Prime 390 = 77 := by rw [count_succ, count_prime_389]; rfl
theorem count_prime_391 : count Nat.Prime 391 = 77 := by rw [count_succ, count_prime_390]; rfl
theorem count_prime_392 : count Nat.Prime 392 = 77 := by rw [count_succ, count_prime_391]; rfl
theorem count_prime_393 : count Nat.Prime 393 = 77 := by rw [count_succ, count_prime_392]; rfl
theorem count_prime_394 : count Nat.Prime 394 = 77 := by rw [count_succ, count_prime_393]; rfl
theorem count_prime_395 : count Nat.Prime 395 = 77 := by rw [count_succ, count_prime_394]; rfl
theorem count_prime_396 : count Nat.Prime 396 = 77 := by rw [count_succ, count_prime_395]; rfl
theorem count_prime_397 : count Nat.Prime 397 = 77 := by rw [count_succ, count_prime_396]; rfl
theorem count_prime_398 : count Nat.Prime 398 = 78 := by rw [count_succ, count_prime_397]; rfl
theorem count_prime_399 : count Nat.Prime 399 = 78 := by rw [count_succ, count_prime_398]; rfl
theorem count_prime_400 : count Nat.Prime 400 = 78 := by rw [count_succ, count_prime_399]; rfl
theorem count_prime_401 : count Nat.Prime 401 = 78 := by rw [count_succ, count_prime_400]; rfl
theorem count_prime_402 : count Nat.Prime 402 = 79 := by rw [count_succ, count_prime_401]; rfl
theorem count_prime_403 : count Nat.Prime 403 = 79 := by rw [count_succ, count_prime_402]; rfl
theorem count_prime_404 : count Nat.Prime 404 = 79 := by rw [count_succ, count_prime_403]; rfl
theorem count_prime_405 : count Nat.Prime 405 = 79 := by rw [count_succ, count_prime_404]; rfl
theorem count_prime_406 : count Nat.Prime 406 = 79 := by rw [count_succ, count_prime_405]; rfl
theorem count_prime_407 : count Nat.Prime 407 = 79 := by rw [count_succ, count_prime_406]; rfl
theorem count_prime_408 : count Nat.Prime 408 = 79 := by rw [count_succ, count_prime_407]; rfl
theorem count_prime_409 : count Nat.Prime 409 = 79 := by rw [count_succ, count_prime_408]; rfl
theorem count_prime_410 : count Nat.Prime 410 = 80 := by rw [count_succ, count_prime_409]; rfl
theorem count_prime_411 : count Nat.Prime 411 = 80 := by rw [count_succ, count_prime_410]; rfl
theorem count_prime_412 : count Nat.Prime 412 = 80 := by rw [count_succ, count_prime_411]; rfl
theorem count_prime_413 : count Nat.Prime 413 = 80 := by rw [count_succ, count_prime_412]; rfl
theorem count_prime_414 : count Nat.Prime 414 = 80 := by rw [count_succ, count_prime_413]; rfl
theorem count_prime_415 : count Nat.Prime 415 = 80 := by rw [count_succ, count_prime_414]; rfl
theorem count_prime_416 : count Nat.Prime 416 = 80 := by rw [count_succ, count_prime_415]; rfl
theorem count_prime_417 : count Nat.Prime 417 = 80 := by rw [count_succ, count_prime_416]; rfl
theorem count_prime_418 : count Nat.Prime 418 = 80 := by rw [count_succ, count_prime_417]; rfl
theorem count_prime_419 : count Nat.Prime 419 = 80 := by rw [count_succ, count_prime_418]; rfl
theorem count_prime_420 : count Nat.Prime 420 = 81 := by rw [count_succ, count_prime_419]; rfl
theorem count_prime_421 : count Nat.Prime 421 = 81 := by rw [count_succ, count_prime_420]; rfl
theorem count_prime_422 : count Nat.Prime 422 = 82 := by rw [count_succ, count_prime_421]; rfl
theorem count_prime_423 : count Nat.Prime 423 = 82 := by rw [count_succ, count_prime_422]; rfl
theorem count_prime_424 : count Nat.Prime 424 = 82 := by rw [count_succ, count_prime_423]; rfl
theorem count_prime_425 : count Nat.Prime 425 = 82 := by rw [count_succ, count_prime_424]; rfl
theorem count_prime_426 : count Nat.Prime 426 = 82 := by rw [count_succ, count_prime_425]; rfl
theorem count_prime_427 : count Nat.Prime 427 = 82 := by rw [count_succ, count_prime_426]; rfl
theorem count_prime_428 : count Nat.Prime 428 = 82 := by rw [count_succ, count_prime_427]; rfl
theorem count_prime_429 : count Nat.Prime 429 = 82 := by rw [count_succ, count_prime_428]; rfl
theorem count_prime_430 : count Nat.Prime 430 = 82 := by rw [count_succ, count_prime_429]; rfl
theorem count_prime_431 : count Nat.Prime 431 = 82 := by rw [count_succ, count_prime_430]; rfl
theorem count_prime_432 : count Nat.Prime 432 = 83 := by rw [count_succ, count_prime_431]; rfl
theorem count_prime_433 : count Nat.Prime 433 = 83 := by rw [count_succ, count_prime_432]; rfl
theorem count_prime_434 : count Nat.Prime 434 = 84 := by rw [count_succ, count_prime_433]; rfl
theorem count_prime_435 : count Nat.Prime 435 = 84 := by rw [count_succ, count_prime_434]; rfl
theorem count_prime_436 : count Nat.Prime 436 = 84 := by rw [count_succ, count_prime_435]; rfl
theorem count_prime_437 : count Nat.Prime 437 = 84 := by rw [count_succ, count_prime_436]; rfl
theorem count_prime_438 : count Nat.Prime 438 = 84 := by rw [count_succ, count_prime_437]; rfl
theorem count_prime_439 : count Nat.Prime 439 = 84 := by rw [count_succ, count_prime_438]; rfl
theorem count_prime_440 : count Nat.Prime 440 = 85 := by rw [count_succ, count_prime_439]; rfl
theorem count_prime_441 : count Nat.Prime 441 = 85 := by rw [count_succ, count_prime_440]; rfl
theorem count_prime_442 : count Nat.Prime 442 = 85 := by rw [count_succ, count_prime_441]; rfl
theorem count_prime_443 : count Nat.Prime 443 = 85 := by rw [count_succ, count_prime_442]; rfl
theorem count_prime_444 : count Nat.Prime 444 = 86 := by rw [count_succ, count_prime_443]; rfl
theorem count_prime_445 : count Nat.Prime 445 = 86 := by rw [count_succ, count_prime_444]; rfl
theorem count_prime_446 : count Nat.Prime 446 = 86 := by rw [count_succ, count_prime_445]; rfl
theorem count_prime_447 : count Nat.Prime 447 = 86 := by rw [count_succ, count_prime_446]; rfl
theorem count_prime_448 : count Nat.Prime 448 = 86 := by rw [count_succ, count_prime_447]; rfl
theorem count_prime_449 : count Nat.Prime 449 = 86 := by rw [count_succ, count_prime_448]; rfl
theorem count_prime_450 : count Nat.Prime 450 = 87 := by rw [count_succ, count_prime_449]; rfl
theorem count_prime_451 : count Nat.Prime 451 = 87 := by rw [count_succ, count_prime_450]; rfl
theorem count_prime_452 : count Nat.Prime 452 = 87 := by rw [count_succ, count_prime_451]; rfl
theorem count_prime_453 : count Nat.Prime 453 = 87 := by rw [count_succ, count_prime_452]; rfl
theorem count_prime_454 : count Nat.Prime 454 = 87 := by rw [count_succ, count_prime_453]; rfl
theorem count_prime_455 : count Nat.Prime 455 = 87 := by rw [count_succ, count_prime_454]; rfl
theorem count_prime_456 : count Nat.Prime 456 = 87 := by rw [count_succ, count_prime_455]; rfl
theorem count_prime_457 : count Nat.Prime 457 = 87 := by rw [count_succ, count_prime_456]; rfl
theorem count_prime_458 : count Nat.Prime 458 = 88 := by rw [count_succ, count_prime_457]; rfl
theorem count_prime_459 : count Nat.Prime 459 = 88 := by rw [count_succ, count_prime_458]; rfl
theorem count_prime_460 : count Nat.Prime 460 = 88 := by rw [count_succ, count_prime_459]; rfl
theorem count_prime_461 : count Nat.Prime 461 = 88 := by rw [count_succ, count_prime_460]; rfl
theorem count_prime_462 : count Nat.Prime 462 = 89 := by rw [count_succ, count_prime_461]; rfl
theorem count_prime_463 : count Nat.Prime 463 = 89 := by rw [count_succ, count_prime_462]; rfl
theorem count_prime_464 : count Nat.Prime 464 = 90 := by rw [count_succ, count_prime_463]; rfl
theorem count_prime_465 : count Nat.Prime 465 = 90 := by rw [count_succ, count_prime_464]; rfl
theorem count_prime_466 : count Nat.Prime 466 = 90 := by rw [count_succ, count_prime_465]; rfl
theorem count_prime_467 : count Nat.Prime 467 = 90 := by rw [count_succ, count_prime_466]; rfl
theorem count_prime_468 : count Nat.Prime 468 = 91 := by rw [count_succ, count_prime_467]; rfl
theorem count_prime_469 : count Nat.Prime 469 = 91 := by rw [count_succ, count_prime_468]; rfl
theorem count_prime_470 : count Nat.Prime 470 = 91 := by rw [count_succ, count_prime_469]; rfl
theorem count_prime_471 : count Nat.Prime 471 = 91 := by rw [count_succ, count_prime_470]; rfl
theorem count_prime_472 : count Nat.Prime 472 = 91 := by rw [count_succ, count_prime_471]; rfl
theorem count_prime_473 : count Nat.Prime 473 = 91 := by rw [count_succ, count_prime_472]; rfl
theorem count_prime_474 : count Nat.Prime 474 = 91 := by rw [count_succ, count_prime_473]; rfl
theorem count_prime_475 : count Nat.Prime 475 = 91 := by rw [count_succ, count_prime_474]; rfl
theorem count_prime_476 : count Nat.Prime 476 = 91 := by rw [count_succ, count_prime_475]; rfl
theorem count_prime_477 : count Nat.Prime 477 = 91 := by rw [count_succ, count_prime_476]; rfl
theorem count_prime_478 : count Nat.Prime 478 = 91 := by rw [count_succ, count_prime_477]; rfl
theorem count_prime_479 : count Nat.Prime 479 = 91 := by rw [count_succ, count_prime_478]; rfl
theorem count_prime_480 : count Nat.Prime 480 = 92 := by rw [count_succ, count_prime_479]; rfl
theorem count_prime_481 : count Nat.Prime 481 = 92 := by rw [count_succ, count_prime_480]; rfl
theorem count_prime_482 : count Nat.Prime 482 = 92 := by rw [count_succ, count_prime_481]; rfl
theorem count_prime_483 : count Nat.Prime 483 = 92 := by rw [count_succ, count_prime_482]; rfl
theorem count_prime_484 : count Nat.Prime 484 = 92 := by rw [count_succ, count_prime_483]; rfl
theorem count_prime_485 : count Nat.Prime 485 = 92 := by rw [count_succ, count_prime_484]; rfl
theorem count_prime_486 : count Nat.Prime 486 = 92 := by rw [count_succ, count_prime_485]; rfl
theorem count_prime_487 : count Nat.Prime 487 = 92 := by rw [count_succ, count_prime_486]; rfl
theorem count_prime_488 : count Nat.Prime 488 = 93 := by rw [count_succ, count_prime_487]; rfl
theorem count_prime_489 : count Nat.Prime 489 = 93 := by rw [count_succ, count_prime_488]; rfl
theorem count_prime_490 : count Nat.Prime 490 = 93 := by rw [count_succ, count_prime_489]; rfl
theorem count_prime_491 : count Nat.Prime 491 = 93 := by rw [count_succ, count_prime_490]; rfl
theorem count_prime_492 : count Nat.Prime 492 = 94 := by rw [count_succ, count_prime_491]; rfl
theorem count_prime_493 : count Nat.Prime 493 = 94 := by rw [count_succ, count_prime_492]; rfl
theorem count_prime_494 : count Nat.Prime 494 = 94 := by rw [count_succ, count_prime_493]; rfl
theorem count_prime_495 : count Nat.Prime 495 = 94 := by rw [count_succ, count_prime_494]; rfl
theorem count_prime_496 : count Nat.Prime 496 = 94 := by rw [count_succ, count_prime_495]; rfl
theorem count_prime_497 : count Nat.Prime 497 = 94 := by rw [count_succ, count_prime_496]; rfl
theorem count_prime_498 : count Nat.Prime 498 = 94 := by rw [count_succ, count_prime_497]; rfl
theorem count_prime_499 : count Nat.Prime 499 = 94 := by rw [count_succ, count_prime_498]; rfl
theorem count_prime_500 : count Nat.Prime 500 = 95 := by rw [count_succ, count_prime_499]; rfl
theorem count_prime_501 : count Nat.Prime 501 = 95 := by rw [count_succ, count_prime_500]; rfl
theorem count_prime_502 : count Nat.Prime 502 = 95 := by rw [count_succ, count_prime_501]; rfl
theorem count_prime_503 : count Nat.Prime 503 = 95 := by rw [count_succ, count_prime_502]; rfl
theorem count_prime_504 : count Nat.Prime 504 = 96 := by rw [count_succ, count_prime_503]; rfl
theorem count_prime_505 : count Nat.Prime 505 = 96 := by rw [count_succ, count_prime_504]; rfl
theorem count_prime_506 : count Nat.Prime 506 = 96 := by rw [count_succ, count_prime_505]; rfl
theorem count_prime_507 : count Nat.Prime 507 = 96 := by rw [count_succ, count_prime_506]; rfl
theorem count_prime_508 : count Nat.Prime 508 = 96 := by rw [count_succ, count_prime_507]; rfl
theorem count_prime_509 : count Nat.Prime 509 = 96 := by rw [count_succ, count_prime_508]; rfl
theorem count_prime_510 : count Nat.Prime 510 = 97 := by rw [count_succ, count_prime_509]; rfl
theorem count_prime_511 : count Nat.Prime 511 = 97 := by rw [count_succ, count_prime_510]; rfl
theorem count_prime_512 : count Nat.Prime 512 = 97 := by rw [count_succ, count_prime_511]; rfl
theorem count_prime_513 : count Nat.Prime 513 = 97 := by rw [count_succ, count_prime_512]; rfl
theorem count_prime_514 : count Nat.Prime 514 = 97 := by rw [count_succ, count_prime_513]; rfl
theorem count_prime_515 : count Nat.Prime 515 = 97 := by rw [count_succ, count_prime_514]; rfl
theorem count_prime_516 : count Nat.Prime 516 = 97 := by rw [count_succ, count_prime_515]; rfl
theorem count_prime_517 : count Nat.Prime 517 = 97 := by rw [count_succ, count_prime_516]; rfl
theorem count_prime_518 : count Nat.Prime 518 = 97 := by rw [count_succ, count_prime_517]; rfl
theorem count_prime_519 : count Nat.Prime 519 = 97 := by rw [count_succ, count_prime_518]; rfl
theorem count_prime_520 : count Nat.Prime 520 = 97 := by rw [count_succ, count_prime_519]; rfl
theorem count_prime_521 : count Nat.Prime 521 = 97 := by rw [count_succ, count_prime_520]; rfl
theorem count_prime_522 : count Nat.Prime 522 = 98 := by rw [count_succ, count_prime_521]; rfl
theorem count_prime_523 : count Nat.Prime 523 = 98 := by rw [count_succ, count_prime_522]; rfl
theorem count_prime_524 : count Nat.Prime 524 = 99 := by rw [count_succ, count_prime_523]; rfl
theorem count_prime_525 : count Nat.Prime 525 = 99 := by rw [count_succ, count_prime_524]; rfl
theorem count_prime_526 : count Nat.Prime 526 = 99 := by rw [count_succ, count_prime_525]; rfl
theorem count_prime_527 : count Nat.Prime 527 = 99 := by rw [count_succ, count_prime_526]; rfl
theorem count_prime_528 : count Nat.Prime 528 = 99 := by rw [count_succ, count_prime_527]; rfl
theorem count_prime_529 : count Nat.Prime 529 = 99 := by rw [count_succ, count_prime_528]; rfl
theorem count_prime_530 : count Nat.Prime 530 = 99 := by rw [count_succ, count_prime_529]; rfl
theorem count_prime_531 : count Nat.Prime 531 = 99 := by rw [count_succ, count_prime_530]; rfl
theorem count_prime_532 : count Nat.Prime 532 = 99 := by rw [count_succ, count_prime_531]; rfl
theorem count_prime_533 : count Nat.Prime 533 = 99 := by rw [count_succ, count_prime_532]; rfl
theorem count_prime_534 : count Nat.Prime 534 = 99 := by rw [count_succ, count_prime_533]; rfl
theorem count_prime_535 : count Nat.Prime 535 = 99 := by rw [count_succ, count_prime_534]; rfl
theorem count_prime_536 : count Nat.Prime 536 = 99 := by rw [count_succ, count_prime_535]; rfl
theorem count_prime_537 : count Nat.Prime 537 = 99 := by rw [count_succ, count_prime_536]; rfl
theorem count_prime_538 : count Nat.Prime 538 = 99 := by rw [count_succ, count_prime_537]; rfl
theorem count_prime_539 : count Nat.Prime 539 = 99 := by rw [count_succ, count_prime_538]; rfl
theorem count_prime_540 : count Nat.Prime 540 = 99 := by rw [count_succ, count_prime_539]; rfl
theorem count_prime_541 : count Nat.Prime 541 = 99 := by rw [count_succ, count_prime_540]; rfl
theorem count_prime_542 : count Nat.Prime 542 = 100 := by rw [count_succ, count_prime_541]; rfl
theorem count_prime_543 : count Nat.Prime 543 = 100 := by rw [count_succ, count_prime_542]; rfl
theorem count_prime_544 : count Nat.Prime 544 = 100 := by rw [count_succ, count_prime_543]; rfl
theorem count_prime_545 : count Nat.Prime 545 = 100 := by rw [count_succ, count_prime_544]; rfl
theorem count_prime_546 : count Nat.Prime 546 = 100 := by rw [count_succ, count_prime_545]; rfl
theorem count_prime_547 : count Nat.Prime 547 = 100 := by rw [count_succ, count_prime_546]; rfl
theorem count_prime_548 : count Nat.Prime 548 = 101 := by rw [count_succ, count_prime_547]; rfl
theorem count_prime_549 : count Nat.Prime 549 = 101 := by rw [count_succ, count_prime_548]; rfl
theorem count_prime_550 : count Nat.Prime 550 = 101 := by rw [count_succ, count_prime_549]; rfl
theorem count_prime_551 : count Nat.Prime 551 = 101 := by rw [count_succ, count_prime_550]; rfl
theorem count_prime_552 : count Nat.Prime 552 = 101 := by rw [count_succ, count_prime_551]; rfl
theorem count_prime_553 : count Nat.Prime 553 = 101 := by rw [count_succ, count_prime_552]; rfl
theorem count_prime_554 : count Nat.Prime 554 = 101 := by rw [count_succ, count_prime_553]; rfl
theorem count_prime_555 : count Nat.Prime 555 = 101 := by rw [count_succ, count_prime_554]; rfl
theorem count_prime_556 : count Nat.Prime 556 = 101 := by rw [count_succ, count_prime_555]; rfl
theorem count_prime_557 : count Nat.Prime 557 = 101 := by rw [count_succ, count_prime_556]; rfl
theorem count_prime_558 : count Nat.Prime 558 = 102 := by rw [count_succ, count_prime_557]; rfl
theorem count_prime_559 : count Nat.Prime 559 = 102 := by rw [count_succ, count_prime_558]; rfl
theorem count_prime_560 : count Nat.Prime 560 = 102 := by rw [count_succ, count_prime_559]; rfl
theorem count_prime_561 : count Nat.Prime 561 = 102 := by rw [count_succ, count_prime_560]; rfl
theorem count_prime_562 : count Nat.Prime 562 = 102 := by rw [count_succ, count_prime_561]; rfl
theorem count_prime_563 : count Nat.Prime 563 = 102 := by rw [count_succ, count_prime_562]; rfl
theorem count_prime_564 : count Nat.Prime 564 = 103 := by rw [count_succ, count_prime_563]; rfl
theorem count_prime_565 : count Nat.Prime 565 = 103 := by rw [count_succ, count_prime_564]; rfl
theorem count_prime_566 : count Nat.Prime 566 = 103 := by rw [count_succ, count_prime_565]; rfl
theorem count_prime_567 : count Nat.Prime 567 = 103 := by rw [count_succ, count_prime_566]; rfl
theorem count_prime_568 : count Nat.Prime 568 = 103 := by rw [count_succ, count_prime_567]; rfl
theorem count_prime_569 : count Nat.Prime 569 = 103 := by rw [count_succ, count_prime_568]; rfl
theorem count_prime_570 : count Nat.Prime 570 = 104 := by rw [count_succ, count_prime_569]; rfl
theorem count_prime_571 : count Nat.Prime 571 = 104 := by rw [count_succ, count_prime_570]; rfl
theorem count_prime_572 : count Nat.Prime 572 = 105 := by rw [count_succ, count_prime_571]; rfl
theorem count_prime_573 : count Nat.Prime 573 = 105 := by rw [count_succ, count_prime_572]; rfl
theorem count_prime_574 : count Nat.Prime 574 = 105 := by rw [count_succ, count_prime_573]; rfl
theorem count_prime_575 : count Nat.Prime 575 = 105 := by rw [count_succ, count_prime_574]; rfl
theorem count_prime_576 : count Nat.Prime 576 = 105 := by rw [count_succ, count_prime_575]; rfl
theorem count_prime_577 : count Nat.Prime 577 = 105 := by rw [count_succ, count_prime_576]; rfl
theorem count_prime_578 : count Nat.Prime 578 = 106 := by rw [count_succ, count_prime_577]; rfl
theorem count_prime_579 : count Nat.Prime 579 = 106 := by rw [count_succ, count_prime_578]; rfl
theorem count_prime_580 : count Nat.Prime 580 = 106 := by rw [count_succ, count_prime_579]; rfl
theorem count_prime_581 : count Nat.Prime 581 = 106 := by rw [count_succ, count_prime_580]; rfl
theorem count_prime_582 : count Nat.Prime 582 = 106 := by rw [count_succ, count_prime_581]; rfl
theorem count_prime_583 : count Nat.Prime 583 = 106 := by rw [count_succ, count_prime_582]; rfl
theorem count_prime_584 : count Nat.Prime 584 = 106 := by rw [count_succ, count_prime_583]; rfl
theorem count_prime_585 : count Nat.Prime 585 = 106 := by rw [count_succ, count_prime_584]; rfl
theorem count_prime_586 : count Nat.Prime 586 = 106 := by rw [count_succ, count_prime_585]; rfl
theorem count_prime_587 : count Nat.Prime 587 = 106 := by rw [count_succ, count_prime_586]; rfl
theorem count_prime_588 : count Nat.Prime 588 = 107 := by rw [count_succ, count_prime_587]; rfl
theorem count_prime_589 : count Nat.Prime 589 = 107 := by rw [count_succ, count_prime_588]; rfl
theorem count_prime_590 : count Nat.Prime 590 = 107 := by rw [count_succ, count_prime_589]; rfl
theorem count_prime_591 : count Nat.Prime 591 = 107 := by rw [count_succ, count_prime_590]; rfl
theorem count_prime_592 : count Nat.Prime 592 = 107 := by rw [count_succ, count_prime_591]; rfl
theorem count_prime_593 : count Nat.Prime 593 = 107 := by rw [count_succ, count_prime_592]; rfl
theorem count_prime_594 : count Nat.Prime 594 = 108 := by rw [count_succ, count_prime_593]; rfl
theorem count_prime_595 : count Nat.Prime 595 = 108 := by rw [count_succ, count_prime_594]; rfl
theorem count_prime_596 : count Nat.Prime 596 = 108 := by rw [count_succ, count_prime_595]; rfl
theorem count_prime_597 : count Nat.Prime 597 = 108 := by rw [count_succ, count_prime_596]; rfl
theorem count_prime_598 : count Nat.Prime 598 = 108 := by rw [count_succ, count_prime_597]; rfl
theorem count_prime_599 : count Nat.Prime 599 = 108 := by rw [count_succ, count_prime_598]; rfl
theorem count_prime_600 : count Nat.Prime 600 = 109 := by rw [count_succ, count_prime_599]; rfl
theorem count_prime_601 : count Nat.Prime 601 = 109 := by rw [count_succ, count_prime_600]; rfl
theorem count_prime_602 : count Nat.Prime 602 = 110 := by rw [count_succ, count_prime_601]; rfl
theorem count_prime_603 : count Nat.Prime 603 = 110 := by rw [count_succ, count_prime_602]; rfl
theorem count_prime_604 : count Nat.Prime 604 = 110 := by rw [count_succ, count_prime_603]; rfl
theorem count_prime_605 : count Nat.Prime 605 = 110 := by rw [count_succ, count_prime_604]; rfl
theorem count_prime_606 : count Nat.Prime 606 = 110 := by rw [count_succ, count_prime_605]; rfl
theorem count_prime_607 : count Nat.Prime 607 = 110 := by rw [count_succ, count_prime_606]; rfl
theorem count_prime_608 : count Nat.Prime 608 = 111 := by rw [count_succ, count_prime_607]; rfl
theorem count_prime_609 : count Nat.Prime 609 = 111 := by rw [count_succ, count_prime_608]; rfl
theorem count_prime_610 : count Nat.Prime 610 = 111 := by rw [count_succ, count_prime_609]; rfl
theorem count_prime_611 : count Nat.Prime 611 = 111 := by rw [count_succ, count_prime_610]; rfl
theorem count_prime_612 : count Nat.Prime 612 = 111 := by rw [count_succ, count_prime_611]; rfl
theorem count_prime_613 : count Nat.Prime 613 = 111 := by rw [count_succ, count_prime_612]; rfl
theorem count_prime_614 : count Nat.Prime 614 = 112 := by rw [count_succ, count_prime_613]; rfl
theorem count_prime_615 : count Nat.Prime 615 = 112 := by rw [count_succ, count_prime_614]; rfl
theorem count_prime_616 : count Nat.Prime 616 = 112 := by rw [count_succ, count_prime_615]; rfl
theorem count_prime_617 : count Nat.Prime 617 = 112 := by rw [count_succ, count_prime_616]; rfl
theorem count_prime_618 : count Nat.Prime 618 = 113 := by rw [count_succ, count_prime_617]; rfl
theorem count_prime_619 : count Nat.Prime 619 = 113 := by rw [count_succ, count_prime_618]; rfl
theorem count_prime_620 : count Nat.Prime 620 = 114 := by rw [count_succ, count_prime_619]; rfl
theorem count_prime_621 : count Nat.Prime 621 = 114 := by rw [count_succ, count_prime_620]; rfl
theorem count_prime_622 : count Nat.Prime 622 = 114 := by rw [count_succ, count_prime_621]; rfl
theorem count_prime_623 : count Nat.Prime 623 = 114 := by rw [count_succ, count_prime_622]; rfl
theorem count_prime_624 : count Nat.Prime 624 = 114 := by rw [count_succ, count_prime_623]; rfl
theorem count_prime_625 : count Nat.Prime 625 = 114 := by rw [count_succ, count_prime_624]; rfl
theorem count_prime_626 : count Nat.Prime 626 = 114 := by rw [count_succ, count_prime_625]; rfl
theorem count_prime_627 : count Nat.Prime 627 = 114 := by rw [count_succ, count_prime_626]; rfl
theorem count_prime_628 : count Nat.Prime 628 = 114 := by rw [count_succ, count_prime_627]; rfl
theorem count_prime_629 : count Nat.Prime 629 = 114 := by rw [count_succ, count_prime_628]; rfl
theorem count_prime_630 : count Nat.Prime 630 = 114 := by rw [count_succ, count_prime_629]; rfl
theorem count_prime_631 : count Nat.Prime 631 = 114 := by rw [count_succ, count_prime_630]; rfl
theorem count_prime_632 : count Nat.Prime 632 = 115 := by rw [count_succ, count_prime_631]; rfl
theorem count_prime_633 : count Nat.Prime 633 = 115 := by rw [count_succ, count_prime_632]; rfl
theorem count_prime_634 : count Nat.Prime 634 = 115 := by rw [count_succ, count_prime_633]; rfl
theorem count_prime_635 : count Nat.Prime 635 = 115 := by rw [count_succ, count_prime_634]; rfl
theorem count_prime_636 : count Nat.Prime 636 = 115 := by rw [count_succ, count_prime_635]; rfl
theorem count_prime_637 : count Nat.Prime 637 = 115 := by rw [count_succ, count_prime_636]; rfl
theorem count_prime_638 : count Nat.Prime 638 = 115 := by rw [count_succ, count_prime_637]; rfl
theorem count_prime_639 : count Nat.Prime 639 = 115 := by rw [count_succ, count_prime_638]; rfl
theorem count_prime_640 : count Nat.Prime 640 = 115 := by rw [count_succ, count_prime_639]; rfl
theorem count_prime_641 : count Nat.Prime 641 = 115 := by rw [count_succ, count_prime_640]; rfl
theorem count_prime_642 : count Nat.Prime 642 = 116 := by rw [count_succ, count_prime_641]; rfl
theorem count_prime_643 : count Nat.Prime 643 = 116 := by rw [count_succ, count_prime_642]; rfl
theorem count_prime_644 : count Nat.Prime 644 = 117 := by rw [count_succ, count_prime_643]; rfl
theorem count_prime_645 : count Nat.Prime 645 = 117 := by rw [count_succ, count_prime_644]; rfl
theorem count_prime_646 : count Nat.Prime 646 = 117 := by rw [count_succ, count_prime_645]; rfl
theorem count_prime_647 : count Nat.Prime 647 = 117 := by rw [count_succ, count_prime_646]; rfl
theorem count_prime_648 : count Nat.Prime 648 = 118 := by rw [count_succ, count_prime_647]; rfl
theorem count_prime_649 : count Nat.Prime 649 = 118 := by rw [count_succ, count_prime_648]; rfl
theorem count_prime_650 : count Nat.Prime 650 = 118 := by rw [count_succ, count_prime_649]; rfl
theorem count_prime_651 : count Nat.Prime 651 = 118 := by rw [count_succ, count_prime_650]; rfl
theorem count_prime_652 : count Nat.Prime 652 = 118 := by rw [count_succ, count_prime_651]; rfl
theorem count_prime_653 : count Nat.Prime 653 = 118 := by rw [count_succ, count_prime_652]; rfl
theorem count_prime_654 : count Nat.Prime 654 = 119 := by rw [count_succ, count_prime_653]; rfl
theorem count_prime_655 : count Nat.Prime 655 = 119 := by rw [count_succ, count_prime_654]; rfl
theorem count_prime_656 : count Nat.Prime 656 = 119 := by rw [count_succ, count_prime_655]; rfl
theorem count_prime_657 : count Nat.Prime 657 = 119 := by rw [count_succ, count_prime_656]; rfl
theorem count_prime_658 : count Nat.Prime 658 = 119 := by rw [count_succ, count_prime_657]; rfl
theorem count_prime_659 : count Nat.Prime 659 = 119 := by rw [count_succ, count_prime_658]; rfl
theorem count_prime_660 : count Nat.Prime 660 = 120 := by rw [count_succ, count_prime_659]; rfl
theorem count_prime_661 : count Nat.Prime 661 = 120 := by rw [count_succ, count_prime_660]; rfl
theorem count_prime_662 : count Nat.Prime 662 = 121 := by rw [count_succ, count_prime_661]; rfl
theorem count_prime_663 : count Nat.Prime 663 = 121 := by rw [count_succ, count_prime_662]; rfl
theorem count_prime_664 : count Nat.Prime 664 = 121 := by rw [count_succ, count_prime_663]; rfl
theorem count_prime_665 : count Nat.Prime 665 = 121 := by rw [count_succ, count_prime_664]; rfl
theorem count_prime_666 : count Nat.Prime 666 = 121 := by rw [count_succ, count_prime_665]; rfl
theorem count_prime_667 : count Nat.Prime 667 = 121 := by rw [count_succ, count_prime_666]; rfl
theorem count_prime_668 : count Nat.Prime 668 = 121 := by rw [count_succ, count_prime_667]; rfl
theorem count_prime_669 : count Nat.Prime 669 = 121 := by rw [count_succ, count_prime_668]; rfl
theorem count_prime_670 : count Nat.Prime 670 = 121 := by rw [count_succ, count_prime_669]; rfl
theorem count_prime_671 : count Nat.Prime 671 = 121 := by rw [count_succ, count_prime_670]; rfl
theorem count_prime_672 : count Nat.Prime 672 = 121 := by rw [count_succ, count_prime_671]; rfl
theorem count_prime_673 : count Nat.Prime 673 = 121 := by rw [count_succ, count_prime_672]; rfl
theorem count_prime_674 : count Nat.Prime 674 = 122 := by rw [count_succ, count_prime_673]; rfl
theorem count_prime_675 : count Nat.Prime 675 = 122 := by rw [count_succ, count_prime_674]; rfl
theorem count_prime_676 : count Nat.Prime 676 = 122 := by rw [count_succ, count_prime_675]; rfl
theorem count_prime_677 : count Nat.Prime 677 = 122 := by rw [count_succ, count_prime_676]; rfl
theorem count_prime_678 : count Nat.Prime 678 = 123 := by rw [count_succ, count_prime_677]; rfl
theorem count_prime_679 : count Nat.Prime 679 = 123 := by rw [count_succ, count_prime_678]; rfl
theorem count_prime_680 : count Nat.Prime 680 = 123 := by rw [count_succ, count_prime_679]; rfl
theorem count_prime_681 : count Nat.Prime 681 = 123 := by rw [count_succ, count_prime_680]; rfl
theorem count_prime_682 : count Nat.Prime 682 = 123 := by rw [count_succ, count_prime_681]; rfl
theorem count_prime_683 : count Nat.Prime 683 = 123 := by rw [count_succ, count_prime_682]; rfl
theorem count_prime_684 : count Nat.Prime 684 = 124 := by rw [count_succ, count_prime_683]; rfl
theorem count_prime_685 : count Nat.Prime 685 = 124 := by rw [count_succ, count_prime_684]; rfl
theorem count_prime_686 : count Nat.Prime 686 = 124 := by rw [count_succ, count_prime_685]; rfl
theorem count_prime_687 : count Nat.Prime 687 = 124 := by rw [count_succ, count_prime_686]; rfl
theorem count_prime_688 : count Nat.Prime 688 = 124 := by rw [count_succ, count_prime_687]; rfl
theorem count_prime_689 : count Nat.Prime 689 = 124 := by rw [count_succ, count_prime_688]; rfl
theorem count_prime_690 : count Nat.Prime 690 = 124 := by rw [count_succ, count_prime_689]; rfl
theorem count_prime_691 : count Nat.Prime 691 = 124 := by rw [count_succ, count_prime_690]; rfl
theorem count_prime_692 : count Nat.Prime 692 = 125 := by rw [count_succ, count_prime_691]; rfl
theorem count_prime_693 : count Nat.Prime 693 = 125 := by rw [count_succ, count_prime_692]; rfl
theorem count_prime_694 : count Nat.Prime 694 = 125 := by rw [count_succ, count_prime_693]; rfl
theorem count_prime_695 : count Nat.Prime 695 = 125 := by rw [count_succ, count_prime_694]; rfl
theorem count_prime_696 : count Nat.Prime 696 = 125 := by rw [count_succ, count_prime_695]; rfl
theorem count_prime_697 : count Nat.Prime 697 = 125 := by rw [count_succ, count_prime_696]; rfl
theorem count_prime_698 : count Nat.Prime 698 = 125 := by rw [count_succ, count_prime_697]; rfl
theorem count_prime_699 : count Nat.Prime 699 = 125 := by rw [count_succ, count_prime_698]; rfl

theorem nth_prime_num_5 : nth Nat.Prime 5 = 13 := by
  have h2 := nth_count (by decide : Nat.Prime 13)
  rw [count_prime_13] at h2; exact h2

theorem nth_prime_num_6 : nth Nat.Prime 6 = 17 := by
  have h2 := nth_count (by decide : Nat.Prime 17)
  rw [count_prime_17] at h2; exact h2

theorem nth_prime_num_7 : nth Nat.Prime 7 = 19 := by
  have h2 := nth_count (by decide : Nat.Prime 19)
  rw [count_prime_19] at h2; exact h2

theorem nth_prime_num_8 : nth Nat.Prime 8 = 23 := by
  have h2 := nth_count (by decide : Nat.Prime 23)
  rw [count_prime_23] at h2; exact h2

theorem nth_prime_num_9 : nth Nat.Prime 9 = 29 := by
  have h2 := nth_count (by decide : Nat.Prime 29)
  rw [count_prime_29] at h2; exact h2

theorem nth_prime_num_10 : nth Nat.Prime 10 = 31 := by
  have h2 := nth_count (by decide : Nat.Prime 31)
  rw [count_prime_31] at h2; exact h2

theorem nth_prime_num_11 : nth Nat.Prime 11 = 37 := by
  have h2 := nth_count (by decide : Nat.Prime 37)
  rw [count_prime_37] at h2; exact h2

theorem nth_prime_num_12 : nth Nat.Prime 12 = 41 := by
  have h2 := nth_count (by decide : Nat.Prime 41)
  rw [count_prime_41] at h2; exact h2

theorem nth_prime_num_13 : nth Nat.Prime 13 = 43 := by
  have h2 := nth_count (by decide : Nat.Prime 43)
  rw [count_prime_43] at h2; exact h2

theorem nth_prime_num_14 : nth Nat.Prime 14 = 47 := by
  have h2 := nth_count (by decide : Nat.Prime 47)
  rw [count_prime_47] at h2; exact h2

theorem nth_prime_num_15 : nth Nat.Prime 15 = 53 := by
  have h2 := nth_count (by decide : Nat.Prime 53)
  rw [count_prime_53] at h2; exact h2

theorem nth_prime_num_16 : nth Nat.Prime 16 = 59 := by
  have h2 := nth_count (by decide : Nat.Prime 59)
  rw [count_prime_59] at h2; exact h2

theorem nth_prime_num_17 : nth Nat.Prime 17 = 61 := by
  have h2 := nth_count (by decide : Nat.Prime 61)
  rw [count_prime_61] at h2; exact h2

theorem nth_prime_num_18 : nth Nat.Prime 18 = 67 := by
  have h2 := nth_count (by decide : Nat.Prime 67)
  rw [count_prime_67] at h2; exact h2

theorem nth_prime_num_19 : nth Nat.Prime 19 = 71 := by
  have h2 := nth_count (by decide : Nat.Prime 71)
  rw [count_prime_71] at h2; exact h2

theorem nth_prime_num_20 : nth Nat.Prime 20 = 73 := by
  have h2 := nth_count (by decide : Nat.Prime 73)
  rw [count_prime_73] at h2; exact h2

theorem nth_prime_num_21 : nth Nat.Prime 21 = 79 := by
  have h2 := nth_count (by decide : Nat.Prime 79)
  rw [count_prime_79] at h2; exact h2

theorem nth_prime_num_22 : nth Nat.Prime 22 = 83 := by
  have h2 := nth_count (by decide : Nat.Prime 83)
  rw [count_prime_83] at h2; exact h2

theorem nth_prime_num_23 : nth Nat.Prime 23 = 89 := by
  have h2 := nth_count (by decide : Nat.Prime 89)
  rw [count_prime_89] at h2; exact h2

theorem nth_prime_num_24 : nth Nat.Prime 24 = 97 := by
  have h2 := nth_count (by decide : Nat.Prime 97)
  rw [count_prime_97] at h2; exact h2

theorem nth_prime_num_25 : nth Nat.Prime 25 = 101 := by
  have h2 := nth_count (by decide : Nat.Prime 101)
  rw [count_prime_101] at h2; exact h2

theorem nth_prime_num_26 : nth Nat.Prime 26 = 103 := by
  have h2 := nth_count (by decide : Nat.Prime 103)
  rw [count_prime_103] at h2; exact h2

theorem nth_prime_num_27 : nth Nat.Prime 27 = 107 := by
  have h2 := nth_count (by decide : Nat.Prime 107)
  rw [count_prime_107] at h2; exact h2

theorem nth_prime_num_28 : nth Nat.Prime 28 = 109 := by
  have h2 := nth_count (by decide : Nat.Prime 109)
  rw [count_prime_109] at h2; exact h2

theorem nth_prime_num_29 : nth Nat.Prime 29 = 113 := by
  have h2 := nth_count (by decide : Nat.Prime 113)
  rw [count_prime_113] at h2; exact h2

theorem nth_prime_num_30 : nth Nat.Prime 30 = 127 := by
  have h2 := nth_count (by decide : Nat.Prime 127)
  rw [count_prime_127] at h2; exact h2

theorem nth_prime_num_31 : nth Nat.Prime 31 = 131 := by
  have h2 := nth_count (by decide : Nat.Prime 131)
  rw [count_prime_131] at h2; exact h2

theorem nth_prime_num_32 : nth Nat.Prime 32 = 137 := by
  have h2 := nth_count (by decide : Nat.Prime 137)
  rw [count_prime_137] at h2; exact h2

theorem nth_prime_num_33 : nth Nat.Prime 33 = 139 := by
  have h2 := nth_count (by decide : Nat.Prime 139)
  rw [count_prime_139] at h2; exact h2

theorem nth_prime_num_34 : nth Nat.Prime 34 = 149 := by
  have h2 := nth_count (by decide : Nat.Prime 149)
  rw [count_prime_149] at h2; exact h2

theorem nth_prime_num_35 : nth Nat.Prime 35 = 151 := by
  have h2 := nth_count (by decide : Nat.Prime 151)
  rw [count_prime_151] at h2; exact h2

theorem nth_prime_num_36 : nth Nat.Prime 36 = 157 := by
  have h2 := nth_count (by decide : Nat.Prime 157)
  rw [count_prime_157] at h2; exact h2

theorem nth_prime_num_37 : nth Nat.Prime 37 = 163 := by
  have h2 := nth_count (by decide : Nat.Prime 163)
  rw [count_prime_163] at h2; exact h2

theorem nth_prime_num_38 : nth Nat.Prime 38 = 167 := by
  have h2 := nth_count (by decide : Nat.Prime 167)
  rw [count_prime_167] at h2; exact h2

theorem nth_prime_num_39 : nth Nat.Prime 39 = 173 := by
  have h2 := nth_count (by decide : Nat.Prime 173)
  rw [count_prime_173] at h2; exact h2

theorem nth_prime_num_40 : nth Nat.Prime 40 = 179 := by
  have h2 := nth_count (by decide : Nat.Prime 179)
  rw [count_prime_179] at h2; exact h2

theorem nth_prime_num_41 : nth Nat.Prime 41 = 181 := by
  have h2 := nth_count (by decide : Nat.Prime 181)
  rw [count_prime_181] at h2; exact h2

theorem nth_prime_num_42 : nth Nat.Prime 42 = 191 := by
  have h2 := nth_count (by decide : Nat.Prime 191)
  rw [count_prime_191] at h2; exact h2

theorem nth_prime_num_43 : nth Nat.Prime 43 = 193 := by
  have h2 := nth_count (by decide : Nat.Prime 193)
  rw [count_prime_193] at h2; exact h2

theorem nth_prime_num_44 : nth Nat.Prime 44 = 197 := by
  have h2 := nth_count (by decide : Nat.Prime 197)
  rw [count_prime_197] at h2; exact h2

theorem nth_prime_num_45 : nth Nat.Prime 45 = 199 := by
  have h2 := nth_count (by decide : Nat.Prime 199)
  rw [count_prime_199] at h2; exact h2

theorem nth_prime_num_46 : nth Nat.Prime 46 = 211 := by
  have h2 := nth_count (by decide : Nat.Prime 211)
  rw [count_prime_211] at h2; exact h2

theorem nth_prime_num_47 : nth Nat.Prime 47 = 223 := by
  have h2 := nth_count (by decide : Nat.Prime 223)
  rw [count_prime_223] at h2; exact h2

theorem nth_prime_num_48 : nth Nat.Prime 48 = 227 := by
  have h2 := nth_count (by decide : Nat.Prime 227)
  rw [count_prime_227] at h2; exact h2

theorem nth_prime_num_49 : nth Nat.Prime 49 = 229 := by
  have h2 := nth_count (by decide : Nat.Prime 229)
  rw [count_prime_229] at h2; exact h2

theorem nth_prime_num_50 : nth Nat.Prime 50 = 233 := by
  have h2 := nth_count (by decide : Nat.Prime 233)
  rw [count_prime_233] at h2; exact h2

theorem nth_prime_num_51 : nth Nat.Prime 51 = 239 := by
  have h2 := nth_count (by decide : Nat.Prime 239)
  rw [count_prime_239] at h2; exact h2

theorem nth_prime_num_52 : nth Nat.Prime 52 = 241 := by
  have h2 := nth_count (by decide : Nat.Prime 241)
  rw [count_prime_241] at h2; exact h2

theorem nth_prime_num_53 : nth Nat.Prime 53 = 251 := by
  have h2 := nth_count (by decide : Nat.Prime 251)
  rw [count_prime_251] at h2; exact h2

theorem nth_prime_num_54 : nth Nat.Prime 54 = 257 := by
  have h2 := nth_count (by decide : Nat.Prime 257)
  rw [count_prime_257] at h2; exact h2

theorem nth_prime_num_55 : nth Nat.Prime 55 = 263 := by
  have h2 := nth_count (by decide : Nat.Prime 263)
  rw [count_prime_263] at h2; exact h2

theorem nth_prime_num_56 : nth Nat.Prime 56 = 269 := by
  have h2 := nth_count (by decide : Nat.Prime 269)
  rw [count_prime_269] at h2; exact h2

theorem nth_prime_num_57 : nth Nat.Prime 57 = 271 := by
  have h2 := nth_count (by decide : Nat.Prime 271)
  rw [count_prime_271] at h2; exact h2

theorem nth_prime_num_58 : nth Nat.Prime 58 = 277 := by
  have h2 := nth_count (by decide : Nat.Prime 277)
  rw [count_prime_277] at h2; exact h2

theorem nth_prime_num_59 : nth Nat.Prime 59 = 281 := by
  have h2 := nth_count (by decide : Nat.Prime 281)
  rw [count_prime_281] at h2; exact h2

theorem nth_prime_num_60 : nth Nat.Prime 60 = 283 := by
  have h2 := nth_count (by decide : Nat.Prime 283)
  rw [count_prime_283] at h2; exact h2

theorem nth_prime_num_61 : nth Nat.Prime 61 = 293 := by
  have h2 := nth_count (by decide : Nat.Prime 293)
  rw [count_prime_293] at h2; exact h2

theorem nth_prime_num_62 : nth Nat.Prime 62 = 307 := by
  have h2 := nth_count (by decide : Nat.Prime 307)
  rw [count_prime_307] at h2; exact h2

theorem nth_prime_num_63 : nth Nat.Prime 63 = 311 := by
  have h2 := nth_count (by decide : Nat.Prime 311)
  rw [count_prime_311] at h2; exact h2

theorem nth_prime_num_64 : nth Nat.Prime 64 = 313 := by
  have h2 := nth_count (by decide : Nat.Prime 313)
  rw [count_prime_313] at h2; exact h2

theorem nth_prime_num_65 : nth Nat.Prime 65 = 317 := by
  have h2 := nth_count (by decide : Nat.Prime 317)
  rw [count_prime_317] at h2; exact h2

theorem nth_prime_num_66 : nth Nat.Prime 66 = 331 := by
  have h2 := nth_count (by decide : Nat.Prime 331)
  rw [count_prime_331] at h2; exact h2

theorem nth_prime_num_67 : nth Nat.Prime 67 = 337 := by
  have h2 := nth_count (by decide : Nat.Prime 337)
  rw [count_prime_337] at h2; exact h2

theorem nth_prime_num_68 : nth Nat.Prime 68 = 347 := by
  have h2 := nth_count (by decide : Nat.Prime 347)
  rw [count_prime_347] at h2; exact h2

theorem nth_prime_num_69 : nth Nat.Prime 69 = 349 := by
  have h2 := nth_count (by decide : Nat.Prime 349)
  rw [count_prime_349] at h2; exact h2

theorem nth_prime_num_70 : nth Nat.Prime 70 = 353 := by
  have h2 := nth_count (by decide : Nat.Prime 353)
  rw [count_prime_353] at h2; exact h2

theorem nth_prime_num_71 : nth Nat.Prime 71 = 359 := by
  have h2 := nth_count (by decide : Nat.Prime 359)
  rw [count_prime_359] at h2; exact h2

theorem nth_prime_num_72 : nth Nat.Prime 72 = 367 := by
  have h2 := nth_count (by decide : Nat.Prime 367)
  rw [count_prime_367] at h2; exact h2

theorem nth_prime_num_73 : nth Nat.Prime 73 = 373 := by
  have h2 := nth_count (by decide : Nat.Prime 373)
  rw [count_prime_373] at h2; exact h2

theorem nth_prime_num_74 : nth Nat.Prime 74 = 379 := by
  have h2 := nth_count (by decide : Nat.Prime 379)
  rw [count_prime_379] at h2; exact h2

theorem nth_prime_num_75 : nth Nat.Prime 75 = 383 := by
  have h2 := nth_count (by decide : Nat.Prime 383)
  rw [count_prime_383] at h2; exact h2

theorem nth_prime_num_76 : nth Nat.Prime 76 = 389 := by
  have h2 := nth_count (by decide : Nat.Prime 389)
  rw [count_prime_389] at h2; exact h2

theorem nth_prime_num_77 : nth Nat.Prime 77 = 397 := by
  have h2 := nth_count (by decide : Nat.Prime 397)
  rw [count_prime_397] at h2; exact h2

theorem nth_prime_num_78 : nth Nat.Prime 78 = 401 := by
  have h2 := nth_count (by decide : Nat.Prime 401)
  rw [count_prime_401] at h2; exact h2

theorem nth_prime_num_79 : nth Nat.Prime 79 = 409 := by
  have h2 := nth_count (by decide : Nat.Prime 409)
  rw [count_prime_409] at h2; exact h2

theorem nth_prime_num_80 : nth Nat.Prime 80 = 419 := by
  have h2 := nth_count (by decide : Nat.Prime 419)
  rw [count_prime_419] at h2; exact h2

theorem nth_prime_num_81 : nth Nat.Prime 81 = 421 := by
  have h2 := nth_count (by decide : Nat.Prime 421)
  rw [count_prime_421] at h2; exact h2

theorem nth_prime_num_82 : nth Nat.Prime 82 = 431 := by
  have h2 := nth_count (by decide : Nat.Prime 431)
  rw [count_prime_431] at h2; exact h2

theorem nth_prime_num_83 : nth Nat.Prime 83 = 433 := by
  have h2 := nth_count (by decide : Nat.Prime 433)
  rw [count_prime_433] at h2; exact h2

theorem nth_prime_num_84 : nth Nat.Prime 84 = 439 := by
  have h2 := nth_count (by decide : Nat.Prime 439)
  rw [count_prime_439] at h2; exact h2

theorem nth_prime_num_85 : nth Nat.Prime 85 = 443 := by
  have h2 := nth_count (by decide : Nat.Prime 443)
  rw [count_prime_443] at h2; exact h2

theorem nth_prime_num_86 : nth Nat.Prime 86 = 449 := by
  have h2 := nth_count (by decide : Nat.Prime 449)
  rw [count_prime_449] at h2; exact h2

theorem nth_prime_num_87 : nth Nat.Prime 87 = 457 := by
  have h2 := nth_count (by decide : Nat.Prime 457)
  rw [count_prime_457] at h2; exact h2

theorem nth_prime_num_88 : nth Nat.Prime 88 = 461 := by
  have h2 := nth_count (by decide : Nat.Prime 461)
  rw [count_prime_461] at h2; exact h2

theorem nth_prime_num_89 : nth Nat.Prime 89 = 463 := by
  have h2 := nth_count (by decide : Nat.Prime 463)
  rw [count_prime_463] at h2; exact h2

theorem nth_prime_num_90 : nth Nat.Prime 90 = 467 := by
  have h2 := nth_count (by decide : Nat.Prime 467)
  rw [count_prime_467] at h2; exact h2

theorem nth_prime_num_91 : nth Nat.Prime 91 = 479 := by
  have h2 := nth_count (by decide : Nat.Prime 479)
  rw [count_prime_479] at h2; exact h2

theorem nth_prime_num_92 : nth Nat.Prime 92 = 487 := by
  have h2 := nth_count (by decide : Nat.Prime 487)
  rw [count_prime_487] at h2; exact h2

theorem nth_prime_num_93 : nth Nat.Prime 93 = 491 := by
  have h2 := nth_count (by decide : Nat.Prime 491)
  rw [count_prime_491] at h2; exact h2

theorem nth_prime_num_94 : nth Nat.Prime 94 = 499 := by
  have h2 := nth_count (by decide : Nat.Prime 499)
  rw [count_prime_499] at h2; exact h2

theorem nth_prime_num_95 : nth Nat.Prime 95 = 503 := by
  have h2 := nth_count (by decide : Nat.Prime 503)
  rw [count_prime_503] at h2; exact h2

theorem nth_prime_num_96 : nth Nat.Prime 96 = 509 := by
  have h2 := nth_count (by decide : Nat.Prime 509)
  rw [count_prime_509] at h2; exact h2

theorem nth_prime_num_97 : nth Nat.Prime 97 = 521 := by
  have h2 := nth_count (by decide : Nat.Prime 521)
  rw [count_prime_521] at h2; exact h2

theorem nth_prime_num_98 : nth Nat.Prime 98 = 523 := by
  have h2 := nth_count (by decide : Nat.Prime 523)
  rw [count_prime_523] at h2; exact h2

theorem nth_prime_num_99 : nth Nat.Prime 99 = 541 := by
  have h2 := nth_count (by decide : Nat.Prime 541)
  rw [count_prime_541] at h2; exact h2

theorem nth_prime_num_100 : nth Nat.Prime 100 = 547 := by
  have h2 := nth_count (by decide : Nat.Prime 547)
  rw [count_prime_547] at h2; exact h2

theorem nth_prime_num_101 : nth Nat.Prime 101 = 557 := by
  have h2 := nth_count (by decide : Nat.Prime 557)
  rw [count_prime_557] at h2; exact h2

theorem nth_prime_num_102 : nth Nat.Prime 102 = 563 := by
  have h2 := nth_count (by decide : Nat.Prime 563)
  rw [count_prime_563] at h2; exact h2

theorem nth_prime_num_103 : nth Nat.Prime 103 = 569 := by
  have h2 := nth_count (by decide : Nat.Prime 569)
  rw [count_prime_569] at h2; exact h2

theorem nth_prime_num_104 : nth Nat.Prime 104 = 571 := by
  have h2 := nth_count (by decide : Nat.Prime 571)
  rw [count_prime_571] at h2; exact h2

theorem nth_prime_num_105 : nth Nat.Prime 105 = 577 := by
  have h2 := nth_count (by decide : Nat.Prime 577)
  rw [count_prime_577] at h2; exact h2

theorem nth_prime_num_106 : nth Nat.Prime 106 = 587 := by
  have h2 := nth_count (by decide : Nat.Prime 587)
  rw [count_prime_587] at h2; exact h2

theorem nth_prime_num_107 : nth Nat.Prime 107 = 593 := by
  have h2 := nth_count (by decide : Nat.Prime 593)
  rw [count_prime_593] at h2; exact h2

theorem nth_prime_num_108 : nth Nat.Prime 108 = 599 := by
  have h2 := nth_count (by decide : Nat.Prime 599)
  rw [count_prime_599] at h2; exact h2

theorem nth_prime_num_109 : nth Nat.Prime 109 = 601 := by
  have h2 := nth_count (by decide : Nat.Prime 601)
  rw [count_prime_601] at h2; exact h2

theorem nth_prime_num_110 : nth Nat.Prime 110 = 607 := by
  have h2 := nth_count (by decide : Nat.Prime 607)
  rw [count_prime_607] at h2; exact h2

theorem nth_prime_num_111 : nth Nat.Prime 111 = 613 := by
  have h2 := nth_count (by decide : Nat.Prime 613)
  rw [count_prime_613] at h2; exact h2

theorem nth_prime_num_112 : nth Nat.Prime 112 = 617 := by
  have h2 := nth_count (by decide : Nat.Prime 617)
  rw [count_prime_617] at h2; exact h2

theorem nth_prime_num_113 : nth Nat.Prime 113 = 619 := by
  have h2 := nth_count (by decide : Nat.Prime 619)
  rw [count_prime_619] at h2; exact h2

theorem nth_prime_num_114 : nth Nat.Prime 114 = 631 := by
  have h2 := nth_count (by decide : Nat.Prime 631)
  rw [count_prime_631] at h2; exact h2

theorem nth_prime_num_115 : nth Nat.Prime 115 = 641 := by
  have h2 := nth_count (by decide : Nat.Prime 641)
  rw [count_prime_641] at h2; exact h2

theorem nth_prime_num_116 : nth Nat.Prime 116 = 643 := by
  have h2 := nth_count (by decide : Nat.Prime 643)
  rw [count_prime_643] at h2; exact h2

theorem nth_prime_num_117 : nth Nat.Prime 117 = 647 := by
  have h2 := nth_count (by decide : Nat.Prime 647)
  rw [count_prime_647] at h2; exact h2

theorem nth_prime_num_118 : nth Nat.Prime 118 = 653 := by
  have h2 := nth_count (by decide : Nat.Prime 653)
  rw [count_prime_653] at h2; exact h2

theorem nth_prime_num_119 : nth Nat.Prime 119 = 659 := by
  have h2 := nth_count (by decide : Nat.Prime 659)
  rw [count_prime_659] at h2; exact h2

theorem nth_prime_num_120 : nth Nat.Prime 120 = 661 := by
  have h2 := nth_count (by decide : Nat.Prime 661)
  rw [count_prime_661] at h2; exact h2

theorem A130911_0 : A130911 0 = 0 := by rfl

theorem A130911_1 : A130911 1 = 1 := by
  rw [A130911_step 0, A130911_0, nth_prime_zero_eq_two]
  simp

theorem A130911_2 : A130911 2 = 0 := by
  rw [A130911_step 1, A130911_1, nth_prime_one_eq_three]
  simp

theorem A130911_3 : A130911 3 = -1 := by
  rw [A130911_step 2, A130911_2, nth_prime_two_eq_five]
  simp

theorem A130911_4 : A130911 4 = 0 := by
  rw [A130911_step 3, A130911_3, nth_prime_three_eq_seven]
  simp

theorem A130911_5 : A130911 5 = 1 := by
  rw [A130911_step 4, A130911_4, nth_prime_four_eq_eleven]
  simp

theorem A130911_6 : A130911 6 = 2 := by
  rw [A130911_step 5, A130911_5, nth_prime_num_5]
  simp

theorem A130911_7 : A130911 7 = 1 := by
  rw [A130911_step 6, A130911_6, nth_prime_num_6]
  simp

theorem A130911_8 : A130911 8 = 2 := by
  rw [A130911_step 7, A130911_7, nth_prime_num_7]
  simp

theorem A130911_9 : A130911 9 = 1 := by
  rw [A130911_step 8, A130911_8, nth_prime_num_8]
  simp

theorem A130911_10 : A130911 10 = 0 := by
  rw [A130911_step 9, A130911_9, nth_prime_num_9]
  simp

theorem A130911_11 : A130911 11 = 1 := by
  rw [A130911_step 10, A130911_10, nth_prime_num_10]
  simp

theorem A130911_12 : A130911 12 = 2 := by
  rw [A130911_step 11, A130911_11, nth_prime_num_11]
  simp

theorem A130911_13 : A130911 13 = 3 := by
  rw [A130911_step 12, A130911_12, nth_prime_num_12]
  simp

theorem A130911_14 : A130911 14 = 2 := by
  rw [A130911_step 13, A130911_13, nth_prime_num_13]
  simp

theorem A130911_15 : A130911 15 = 3 := by
  rw [A130911_step 14, A130911_14, nth_prime_num_14]
  simp

theorem A130911_16 : A130911 16 = 2 := by
  rw [A130911_step 15, A130911_15, nth_prime_num_15]
  simp

theorem A130911_17 : A130911 17 = 3 := by
  rw [A130911_step 16, A130911_16, nth_prime_num_16]
  simp

theorem A130911_18 : A130911 18 = 4 := by
  rw [A130911_step 17, A130911_17, nth_prime_num_17]
  simp

theorem A130911_19 : A130911 19 = 5 := by
  rw [A130911_step 18, A130911_18, nth_prime_num_18]
  simp

theorem A130911_20 : A130911 20 = 4 := by
  rw [A130911_step 19, A130911_19, nth_prime_num_19]
  simp

theorem A130911_21 : A130911 21 = 5 := by
  rw [A130911_step 20, A130911_20, nth_prime_num_20]
  simp

theorem A130911_22 : A130911 22 = 6 := by
  rw [A130911_step 21, A130911_21, nth_prime_num_21]
  simp

theorem A130911_23 : A130911 23 = 5 := by
  rw [A130911_step 22, A130911_22, nth_prime_num_22]
  simp

theorem A130911_24 : A130911 24 = 4 := by
  rw [A130911_step 23, A130911_23, nth_prime_num_23]
  simp

theorem A130911_25 : A130911 25 = 5 := by
  rw [A130911_step 24, A130911_24, nth_prime_num_24]
  simp

theorem A130911_26 : A130911 26 = 4 := by
  rw [A130911_step 25, A130911_25, nth_prime_num_25]
  simp

theorem A130911_27 : A130911 27 = 5 := by
  rw [A130911_step 26, A130911_26, nth_prime_num_26]
  simp

theorem A130911_28 : A130911 28 = 6 := by
  rw [A130911_step 27, A130911_27, nth_prime_num_27]
  simp

theorem A130911_29 : A130911 29 = 7 := by
  rw [A130911_step 28, A130911_28, nth_prime_num_28]
  simp

theorem A130911_30 : A130911 30 = 6 := by
  rw [A130911_step 29, A130911_29, nth_prime_num_29]
  simp

theorem A130911_31 : A130911 31 = 7 := by
  rw [A130911_step 30, A130911_30, nth_prime_num_30]
  simp

theorem A130911_32 : A130911 32 = 8 := by
  rw [A130911_step 31, A130911_31, nth_prime_num_31]
  simp

theorem A130911_33 : A130911 33 = 9 := by
  rw [A130911_step 32, A130911_32, nth_prime_num_32]
  simp

theorem A130911_34 : A130911 34 = 8 := by
  rw [A130911_step 33, A130911_33, nth_prime_num_33]
  simp

theorem A130911_35 : A130911 35 = 7 := by
  rw [A130911_step 34, A130911_34, nth_prime_num_34]
  simp

theorem A130911_36 : A130911 36 = 8 := by
  rw [A130911_step 35, A130911_35, nth_prime_num_35]
  simp

theorem A130911_37 : A130911 37 = 9 := by
  rw [A130911_step 36, A130911_36, nth_prime_num_36]
  simp

theorem A130911_38 : A130911 38 = 8 := by
  rw [A130911_step 37, A130911_37, nth_prime_num_37]
  simp

theorem A130911_39 : A130911 39 = 9 := by
  rw [A130911_step 38, A130911_38, nth_prime_num_38]
  simp

theorem A130911_40 : A130911 40 = 10 := by
  rw [A130911_step 39, A130911_39, nth_prime_num_39]
  simp

theorem A130911_41 : A130911 41 = 11 := by
  rw [A130911_step 40, A130911_40, nth_prime_num_40]
  simp

theorem A130911_42 : A130911 42 = 12 := by
  rw [A130911_step 41, A130911_41, nth_prime_num_41]
  simp

theorem A130911_43 : A130911 43 = 13 := by
  rw [A130911_step 42, A130911_42, nth_prime_num_42]
  simp

theorem A130911_44 : A130911 44 = 14 := by
  rw [A130911_step 43, A130911_43, nth_prime_num_43]
  simp

theorem A130911_45 : A130911 45 = 13 := by
  rw [A130911_step 44, A130911_44, nth_prime_num_44]
  simp

theorem A130911_46 : A130911 46 = 14 := by
  rw [A130911_step 45, A130911_45, nth_prime_num_45]
  simp

theorem A130911_47 : A130911 47 = 15 := by
  rw [A130911_step 46, A130911_46, nth_prime_num_46]
  simp

theorem A130911_48 : A130911 48 = 16 := by
  rw [A130911_step 47, A130911_47, nth_prime_num_47]
  simp

theorem A130911_49 : A130911 49 = 17 := by
  rw [A130911_step 48, A130911_48, nth_prime_num_48]
  simp

theorem A130911_50 : A130911 50 = 18 := by
  rw [A130911_step 49, A130911_49, nth_prime_num_49]
  simp

theorem A130911_51 : A130911 51 = 19 := by
  rw [A130911_step 50, A130911_50, nth_prime_num_50]
  simp

theorem A130911_52 : A130911 52 = 20 := by
  rw [A130911_step 51, A130911_51, nth_prime_num_51]
  simp

theorem A130911_53 : A130911 53 = 21 := by
  rw [A130911_step 52, A130911_52, nth_prime_num_52]
  simp

theorem A130911_54 : A130911 54 = 22 := by
  rw [A130911_step 53, A130911_53, nth_prime_num_53]
  simp

theorem A130911_55 : A130911 55 = 21 := by
  rw [A130911_step 54, A130911_54, nth_prime_num_54]
  simp

theorem A130911_56 : A130911 56 = 20 := by
  rw [A130911_step 55, A130911_55, nth_prime_num_55]
  simp

theorem A130911_57 : A130911 57 = 19 := by
  rw [A130911_step 56, A130911_56, nth_prime_num_56]
  simp

theorem A130911_58 : A130911 58 = 20 := by
  rw [A130911_step 57, A130911_57, nth_prime_num_57]
  simp

theorem A130911_59 : A130911 59 = 19 := by
  rw [A130911_step 58, A130911_58, nth_prime_num_58]
  simp

theorem A130911_60 : A130911 60 = 18 := by
  rw [A130911_step 59, A130911_59, nth_prime_num_59]
  simp

theorem A130911_61 : A130911 61 = 19 := by
  rw [A130911_step 60, A130911_60, nth_prime_num_60]
  simp

theorem A130911_62 : A130911 62 = 18 := by
  rw [A130911_step 61, A130911_61, nth_prime_num_61]
  simp

theorem A130911_63 : A130911 63 = 19 := by
  rw [A130911_step 62, A130911_62, nth_prime_num_62]
  simp

theorem A130911_64 : A130911 64 = 18 := by
  rw [A130911_step 63, A130911_63, nth_prime_num_63]
  simp

theorem A130911_65 : A130911 65 = 19 := by
  rw [A130911_step 64, A130911_64, nth_prime_num_64]
  simp

theorem A130911_66 : A130911 66 = 18 := by
  rw [A130911_step 65, A130911_65, nth_prime_num_65]
  simp

theorem A130911_67 : A130911 67 = 19 := by
  rw [A130911_step 66, A130911_66, nth_prime_num_66]
  simp

theorem A130911_68 : A130911 68 = 18 := by
  rw [A130911_step 67, A130911_67, nth_prime_num_67]
  simp

theorem A130911_69 : A130911 69 = 17 := by
  rw [A130911_step 68, A130911_68, nth_prime_num_68]
  simp

theorem A130911_70 : A130911 70 = 16 := by
  rw [A130911_step 69, A130911_69, nth_prime_num_69]
  simp

theorem A130911_71 : A130911 71 = 15 := by
  rw [A130911_step 70, A130911_70, nth_prime_num_70]
  simp

theorem A130911_72 : A130911 72 = 14 := by
  rw [A130911_step 71, A130911_71, nth_prime_num_71]
  simp

theorem A130911_73 : A130911 73 = 15 := by
  rw [A130911_step 72, A130911_72, nth_prime_num_72]
  simp

theorem A130911_74 : A130911 74 = 14 := by
  rw [A130911_step 73, A130911_73, nth_prime_num_73]
  simp

theorem A130911_75 : A130911 75 = 15 := by
  rw [A130911_step 74, A130911_74, nth_prime_num_74]
  simp

theorem A130911_76 : A130911 76 = 14 := by
  rw [A130911_step 75, A130911_75, nth_prime_num_75]
  simp

theorem A130911_77 : A130911 77 = 13 := by
  rw [A130911_step 76, A130911_76, nth_prime_num_76]
  simp

theorem A130911_78 : A130911 78 = 14 := by
  rw [A130911_step 77, A130911_77, nth_prime_num_77]
  simp

theorem A130911_79 : A130911 79 = 13 := by
  rw [A130911_step 78, A130911_78, nth_prime_num_78]
  simp

theorem A130911_80 : A130911 80 = 14 := by
  rw [A130911_step 79, A130911_79, nth_prime_num_79]
  simp

theorem A130911_81 : A130911 81 = 15 := by
  rw [A130911_step 80, A130911_80, nth_prime_num_80]
  simp

theorem A130911_82 : A130911 82 = 16 := by
  rw [A130911_step 81, A130911_81, nth_prime_num_81]
  simp

theorem A130911_83 : A130911 83 = 17 := by
  rw [A130911_step 82, A130911_82, nth_prime_num_82]
  simp

theorem A130911_84 : A130911 84 = 18 := by
  rw [A130911_step 83, A130911_83, nth_prime_num_83]
  simp

theorem A130911_85 : A130911 85 = 19 := by
  rw [A130911_step 84, A130911_84, nth_prime_num_84]
  simp

theorem A130911_86 : A130911 86 = 20 := by
  rw [A130911_step 85, A130911_85, nth_prime_num_85]
  simp

theorem A130911_87 : A130911 87 = 19 := by
  rw [A130911_step 86, A130911_86, nth_prime_num_86]
  simp

theorem A130911_88 : A130911 88 = 20 := by
  rw [A130911_step 87, A130911_87, nth_prime_num_87]
  simp

theorem A130911_89 : A130911 89 = 19 := by
  rw [A130911_step 88, A130911_88, nth_prime_num_88]
  simp

theorem A130911_90 : A130911 90 = 20 := by
  rw [A130911_step 89, A130911_89, nth_prime_num_89]
  simp

theorem A130911_91 : A130911 91 = 19 := by
  rw [A130911_step 90, A130911_90, nth_prime_num_90]
  simp

theorem A130911_92 : A130911 92 = 18 := by
  rw [A130911_step 91, A130911_91, nth_prime_num_91]
  simp

theorem A130911_93 : A130911 93 = 19 := by
  rw [A130911_step 92, A130911_92, nth_prime_num_92]
  simp

theorem A130911_94 : A130911 94 = 20 := by
  rw [A130911_step 93, A130911_93, nth_prime_num_93]
  simp

theorem A130911_95 : A130911 95 = 21 := by
  rw [A130911_step 94, A130911_94, nth_prime_num_94]
  simp

theorem A130911_96 : A130911 96 = 20 := by
  rw [A130911_step 95, A130911_95, nth_prime_num_95]
  simp

theorem A130911_97 : A130911 97 = 19 := by
  rw [A130911_step 96, A130911_96, nth_prime_num_96]
  simp

theorem A130911_98 : A130911 98 = 20 := by
  rw [A130911_step 97, A130911_97, nth_prime_num_97]
  simp

theorem A130911_99 : A130911 99 = 19 := by
  rw [A130911_step 98, A130911_98, nth_prime_num_98]
  simp

theorem A130911_100 : A130911 100 = 20 := by
  rw [A130911_step 99, A130911_99, nth_prime_num_99]
  simp

theorem A130911_101 : A130911 101 = 19 := by
  rw [A130911_step 100, A130911_100, nth_prime_num_100]
  simp

theorem A130911_102 : A130911 102 = 20 := by
  rw [A130911_step 101, A130911_101, nth_prime_num_101]
  simp

theorem A130911_103 : A130911 103 = 21 := by
  rw [A130911_step 102, A130911_102, nth_prime_num_102]
  simp

theorem A130911_104 : A130911 104 = 22 := by
  rw [A130911_step 103, A130911_103, nth_prime_num_103]
  simp

theorem A130911_105 : A130911 105 = 21 := by
  rw [A130911_step 104, A130911_104, nth_prime_num_104]
  simp

theorem A130911_106 : A130911 106 = 22 := by
  rw [A130911_step 105, A130911_105, nth_prime_num_105]
  simp

theorem A130911_107 : A130911 107 = 23 := by
  rw [A130911_step 106, A130911_106, nth_prime_num_106]
  simp

theorem A130911_108 : A130911 108 = 22 := by
  rw [A130911_step 107, A130911_107, nth_prime_num_107]
  simp

theorem A130911_109 : A130911 109 = 21 := by
  rw [A130911_step 108, A130911_108, nth_prime_num_108]
  simp

theorem A130911_110 : A130911 110 = 22 := by
  rw [A130911_step 109, A130911_109, nth_prime_num_109]
  simp

theorem A130911_111 : A130911 111 = 23 := by
  rw [A130911_step 110, A130911_110, nth_prime_num_110]
  simp

theorem A130911_112 : A130911 112 = 24 := by
  rw [A130911_step 111, A130911_111, nth_prime_num_111]
  simp

theorem A130911_113 : A130911 113 = 25 := by
  rw [A130911_step 112, A130911_112, nth_prime_num_112]
  simp

theorem A130911_114 : A130911 114 = 24 := by
  rw [A130911_step 113, A130911_113, nth_prime_num_113]
  simp

theorem A130911_115 : A130911 115 = 25 := by
  rw [A130911_step 114, A130911_114, nth_prime_num_114]
  simp

theorem A130911_116 : A130911 116 = 26 := by
  rw [A130911_step 115, A130911_115, nth_prime_num_115]
  simp

theorem A130911_117 : A130911 117 = 25 := by
  rw [A130911_step 116, A130911_116, nth_prime_num_116]
  simp

theorem A130911_118 : A130911 118 = 26 := by
  rw [A130911_step 117, A130911_117, nth_prime_num_117]
  simp

theorem A130911_119 : A130911 119 = 27 := by
  rw [A130911_step 118, A130911_118, nth_prime_num_118]
  simp

theorem A130911_120 : A130911 120 = 28 := by
  rw [A130911_step 119, A130911_119, nth_prime_num_119]
  simp

theorem sgn_not_minus_11 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 11)) = -1) : False := by
  have h_sgn11 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 11)) = 1 := by
    rw [nth_prime_num_11]; simp [digits_zero]
  rw [h_sgn11] at h_sgn; contradiction

theorem sgn_not_minus_12 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 12)) = -1) : False := by
  have h_sgn12 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 12)) = 1 := by
    rw [nth_prime_num_12]; simp [digits_zero]
  rw [h_sgn12] at h_sgn; contradiction

theorem sgn_not_plus_13 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 13)) = 1) : False := by
  have h_sgn13 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 13)) = -1 := by
    rw [nth_prime_num_13]; simp [digits_zero]
  rw [h_sgn13] at h_sgn; contradiction

theorem sgn_not_minus_14 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 14)) = -1) : False := by
  have h_sgn14 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 14)) = 1 := by
    rw [nth_prime_num_14]; simp [digits_zero]
  rw [h_sgn14] at h_sgn; contradiction

theorem sgn_not_plus_15 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 15)) = 1) : False := by
  have h_sgn15 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 15)) = -1 := by
    rw [nth_prime_num_15]; simp [digits_zero]
  rw [h_sgn15] at h_sgn; contradiction

theorem sgn_not_minus_16 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 16)) = -1) : False := by
  have h_sgn16 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 16)) = 1 := by
    rw [nth_prime_num_16]; simp [digits_zero]
  rw [h_sgn16] at h_sgn; contradiction

theorem sgn_not_minus_17 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 17)) = -1) : False := by
  have h_sgn17 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 17)) = 1 := by
    rw [nth_prime_num_17]; simp [digits_zero]
  rw [h_sgn17] at h_sgn; contradiction

theorem sgn_not_minus_18 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 18)) = -1) : False := by
  have h_sgn18 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 18)) = 1 := by
    rw [nth_prime_num_18]; simp [digits_zero]
  rw [h_sgn18] at h_sgn; contradiction

theorem sgn_not_plus_19 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 19)) = 1) : False := by
  have h_sgn19 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 19)) = -1 := by
    rw [nth_prime_num_19]; simp [digits_zero]
  rw [h_sgn19] at h_sgn; contradiction

theorem sgn_not_minus_20 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 20)) = -1) : False := by
  have h_sgn20 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 20)) = 1 := by
    rw [nth_prime_num_20]; simp [digits_zero]
  rw [h_sgn20] at h_sgn; contradiction

theorem sgn_not_minus_21 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 21)) = -1) : False := by
  have h_sgn21 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 21)) = 1 := by
    rw [nth_prime_num_21]; simp [digits_zero]
  rw [h_sgn21] at h_sgn; contradiction

theorem sgn_not_plus_22 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 22)) = 1) : False := by
  have h_sgn22 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 22)) = -1 := by
    rw [nth_prime_num_22]; simp [digits_zero]
  rw [h_sgn22] at h_sgn; contradiction

theorem sgn_not_plus_23 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 23)) = 1) : False := by
  have h_sgn23 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 23)) = -1 := by
    rw [nth_prime_num_23]; simp [digits_zero]
  rw [h_sgn23] at h_sgn; contradiction

theorem sgn_not_minus_24 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 24)) = -1) : False := by
  have h_sgn24 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 24)) = 1 := by
    rw [nth_prime_num_24]; simp [digits_zero]
  rw [h_sgn24] at h_sgn; contradiction

theorem sgn_not_plus_25 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 25)) = 1) : False := by
  have h_sgn25 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 25)) = -1 := by
    rw [nth_prime_num_25]; simp [digits_zero]
  rw [h_sgn25] at h_sgn; contradiction

theorem sgn_not_minus_26 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 26)) = -1) : False := by
  have h_sgn26 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 26)) = 1 := by
    rw [nth_prime_num_26]; simp [digits_zero]
  rw [h_sgn26] at h_sgn; contradiction

theorem sgn_not_minus_27 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 27)) = -1) : False := by
  have h_sgn27 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 27)) = 1 := by
    rw [nth_prime_num_27]; simp [digits_zero]
  rw [h_sgn27] at h_sgn; contradiction

theorem sgn_not_minus_28 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 28)) = -1) : False := by
  have h_sgn28 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 28)) = 1 := by
    rw [nth_prime_num_28]; simp [digits_zero]
  rw [h_sgn28] at h_sgn; contradiction

theorem sgn_not_plus_29 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 29)) = 1) : False := by
  have h_sgn29 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 29)) = -1 := by
    rw [nth_prime_num_29]; simp [digits_zero]
  rw [h_sgn29] at h_sgn; contradiction

theorem sgn_not_minus_30 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 30)) = -1) : False := by
  have h_sgn30 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 30)) = 1 := by
    rw [nth_prime_num_30]; simp [digits_zero]
  rw [h_sgn30] at h_sgn; contradiction

theorem sgn_not_minus_31 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 31)) = -1) : False := by
  have h_sgn31 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 31)) = 1 := by
    rw [nth_prime_num_31]; simp [digits_zero]
  rw [h_sgn31] at h_sgn; contradiction

theorem sgn_not_minus_32 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 32)) = -1) : False := by
  have h_sgn32 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 32)) = 1 := by
    rw [nth_prime_num_32]; simp [digits_zero]
  rw [h_sgn32] at h_sgn; contradiction

theorem sgn_not_plus_33 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 33)) = 1) : False := by
  have h_sgn33 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 33)) = -1 := by
    rw [nth_prime_num_33]; simp [digits_zero]
  rw [h_sgn33] at h_sgn; contradiction

theorem sgn_not_plus_34 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 34)) = 1) : False := by
  have h_sgn34 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 34)) = -1 := by
    rw [nth_prime_num_34]; simp [digits_zero]
  rw [h_sgn34] at h_sgn; contradiction

theorem sgn_not_minus_35 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 35)) = -1) : False := by
  have h_sgn35 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 35)) = 1 := by
    rw [nth_prime_num_35]; simp [digits_zero]
  rw [h_sgn35] at h_sgn; contradiction

theorem sgn_not_minus_36 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 36)) = -1) : False := by
  have h_sgn36 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 36)) = 1 := by
    rw [nth_prime_num_36]; simp [digits_zero]
  rw [h_sgn36] at h_sgn; contradiction

theorem sgn_not_plus_37 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 37)) = 1) : False := by
  have h_sgn37 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 37)) = -1 := by
    rw [nth_prime_num_37]; simp [digits_zero]
  rw [h_sgn37] at h_sgn; contradiction

theorem sgn_not_minus_38 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 38)) = -1) : False := by
  have h_sgn38 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 38)) = 1 := by
    rw [nth_prime_num_38]; simp [digits_zero]
  rw [h_sgn38] at h_sgn; contradiction

theorem sgn_not_minus_39 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 39)) = -1) : False := by
  have h_sgn39 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 39)) = 1 := by
    rw [nth_prime_num_39]; simp [digits_zero]
  rw [h_sgn39] at h_sgn; contradiction

theorem sgn_not_minus_40 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 40)) = -1) : False := by
  have h_sgn40 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 40)) = 1 := by
    rw [nth_prime_num_40]; simp [digits_zero]
  rw [h_sgn40] at h_sgn; contradiction

theorem sgn_not_minus_41 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 41)) = -1) : False := by
  have h_sgn41 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 41)) = 1 := by
    rw [nth_prime_num_41]; simp [digits_zero]
  rw [h_sgn41] at h_sgn; contradiction

theorem sgn_not_minus_42 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 42)) = -1) : False := by
  have h_sgn42 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 42)) = 1 := by
    rw [nth_prime_num_42]; simp [digits_zero]
  rw [h_sgn42] at h_sgn; contradiction

theorem sgn_not_minus_43 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 43)) = -1) : False := by
  have h_sgn43 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 43)) = 1 := by
    rw [nth_prime_num_43]; simp [digits_zero]
  rw [h_sgn43] at h_sgn; contradiction

theorem sgn_not_plus_44 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 44)) = 1) : False := by
  have h_sgn44 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 44)) = -1 := by
    rw [nth_prime_num_44]; simp [digits_zero]
  rw [h_sgn44] at h_sgn; contradiction

theorem sgn_not_minus_45 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 45)) = -1) : False := by
  have h_sgn45 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 45)) = 1 := by
    rw [nth_prime_num_45]; simp [digits_zero]
  rw [h_sgn45] at h_sgn; contradiction

theorem sgn_not_minus_46 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 46)) = -1) : False := by
  have h_sgn46 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 46)) = 1 := by
    rw [nth_prime_num_46]; simp [digits_zero]
  rw [h_sgn46] at h_sgn; contradiction

theorem sgn_not_minus_47 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 47)) = -1) : False := by
  have h_sgn47 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 47)) = 1 := by
    rw [nth_prime_num_47]; simp [digits_zero]
  rw [h_sgn47] at h_sgn; contradiction

theorem sgn_not_minus_48 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 48)) = -1) : False := by
  have h_sgn48 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 48)) = 1 := by
    rw [nth_prime_num_48]; simp [digits_zero]
  rw [h_sgn48] at h_sgn; contradiction

theorem sgn_not_minus_49 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 49)) = -1) : False := by
  have h_sgn49 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 49)) = 1 := by
    rw [nth_prime_num_49]; simp [digits_zero]
  rw [h_sgn49] at h_sgn; contradiction

theorem sgn_not_minus_50 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 50)) = -1) : False := by
  have h_sgn50 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 50)) = 1 := by
    rw [nth_prime_num_50]; simp [digits_zero]
  rw [h_sgn50] at h_sgn; contradiction

theorem sgn_not_minus_51 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 51)) = -1) : False := by
  have h_sgn51 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 51)) = 1 := by
    rw [nth_prime_num_51]; simp [digits_zero]
  rw [h_sgn51] at h_sgn; contradiction

theorem sgn_not_minus_52 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 52)) = -1) : False := by
  have h_sgn52 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 52)) = 1 := by
    rw [nth_prime_num_52]; simp [digits_zero]
  rw [h_sgn52] at h_sgn; contradiction

theorem sgn_not_minus_53 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 53)) = -1) : False := by
  have h_sgn53 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 53)) = 1 := by
    rw [nth_prime_num_53]; simp [digits_zero]
  rw [h_sgn53] at h_sgn; contradiction

theorem sgn_not_plus_54 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 54)) = 1) : False := by
  have h_sgn54 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 54)) = -1 := by
    rw [nth_prime_num_54]; simp [digits_zero]
  rw [h_sgn54] at h_sgn; contradiction

theorem sgn_not_plus_55 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 55)) = 1) : False := by
  have h_sgn55 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 55)) = -1 := by
    rw [nth_prime_num_55]; simp [digits_zero]
  rw [h_sgn55] at h_sgn; contradiction

theorem sgn_not_plus_56 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 56)) = 1) : False := by
  have h_sgn56 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 56)) = -1 := by
    rw [nth_prime_num_56]; simp [digits_zero]
  rw [h_sgn56] at h_sgn; contradiction

theorem sgn_not_minus_57 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 57)) = -1) : False := by
  have h_sgn57 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 57)) = 1 := by
    rw [nth_prime_num_57]; simp [digits_zero]
  rw [h_sgn57] at h_sgn; contradiction

theorem sgn_not_plus_58 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 58)) = 1) : False := by
  have h_sgn58 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 58)) = -1 := by
    rw [nth_prime_num_58]; simp [digits_zero]
  rw [h_sgn58] at h_sgn; contradiction

theorem sgn_not_plus_59 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 59)) = 1) : False := by
  have h_sgn59 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 59)) = -1 := by
    rw [nth_prime_num_59]; simp [digits_zero]
  rw [h_sgn59] at h_sgn; contradiction

theorem sgn_not_minus_60 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 60)) = -1) : False := by
  have h_sgn60 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 60)) = 1 := by
    rw [nth_prime_num_60]; simp [digits_zero]
  rw [h_sgn60] at h_sgn; contradiction

theorem sgn_not_plus_61 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 61)) = 1) : False := by
  have h_sgn61 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 61)) = -1 := by
    rw [nth_prime_num_61]; simp [digits_zero]
  rw [h_sgn61] at h_sgn; contradiction

theorem sgn_not_minus_62 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 62)) = -1) : False := by
  have h_sgn62 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 62)) = 1 := by
    rw [nth_prime_num_62]; simp [digits_zero]
  rw [h_sgn62] at h_sgn; contradiction

theorem sgn_not_plus_63 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 63)) = 1) : False := by
  have h_sgn63 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 63)) = -1 := by
    rw [nth_prime_num_63]; simp [digits_zero]
  rw [h_sgn63] at h_sgn; contradiction

theorem sgn_not_minus_64 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 64)) = -1) : False := by
  have h_sgn64 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 64)) = 1 := by
    rw [nth_prime_num_64]; simp [digits_zero]
  rw [h_sgn64] at h_sgn; contradiction

theorem sgn_not_plus_65 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 65)) = 1) : False := by
  have h_sgn65 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 65)) = -1 := by
    rw [nth_prime_num_65]; simp [digits_zero]
  rw [h_sgn65] at h_sgn; contradiction

theorem sgn_not_minus_66 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 66)) = -1) : False := by
  have h_sgn66 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 66)) = 1 := by
    rw [nth_prime_num_66]; simp [digits_zero]
  rw [h_sgn66] at h_sgn; contradiction

theorem sgn_not_plus_67 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 67)) = 1) : False := by
  have h_sgn67 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 67)) = -1 := by
    rw [nth_prime_num_67]; simp [digits_zero]
  rw [h_sgn67] at h_sgn; contradiction

theorem sgn_not_plus_68 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 68)) = 1) : False := by
  have h_sgn68 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 68)) = -1 := by
    rw [nth_prime_num_68]; simp [digits_zero]
  rw [h_sgn68] at h_sgn; contradiction

theorem sgn_not_plus_69 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 69)) = 1) : False := by
  have h_sgn69 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 69)) = -1 := by
    rw [nth_prime_num_69]; simp [digits_zero]
  rw [h_sgn69] at h_sgn; contradiction

theorem sgn_not_plus_70 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 70)) = 1) : False := by
  have h_sgn70 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 70)) = -1 := by
    rw [nth_prime_num_70]; simp [digits_zero]
  rw [h_sgn70] at h_sgn; contradiction

theorem sgn_not_plus_71 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 71)) = 1) : False := by
  have h_sgn71 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 71)) = -1 := by
    rw [nth_prime_num_71]; simp [digits_zero]
  rw [h_sgn71] at h_sgn; contradiction

theorem sgn_not_minus_72 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 72)) = -1) : False := by
  have h_sgn72 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 72)) = 1 := by
    rw [nth_prime_num_72]; simp [digits_zero]
  rw [h_sgn72] at h_sgn; contradiction

theorem sgn_not_plus_73 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 73)) = 1) : False := by
  have h_sgn73 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 73)) = -1 := by
    rw [nth_prime_num_73]; simp [digits_zero]
  rw [h_sgn73] at h_sgn; contradiction

theorem sgn_not_minus_74 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 74)) = -1) : False := by
  have h_sgn74 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 74)) = 1 := by
    rw [nth_prime_num_74]; simp [digits_zero]
  rw [h_sgn74] at h_sgn; contradiction

theorem sgn_not_plus_75 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 75)) = 1) : False := by
  have h_sgn75 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 75)) = -1 := by
    rw [nth_prime_num_75]; simp [digits_zero]
  rw [h_sgn75] at h_sgn; contradiction

theorem sgn_not_plus_76 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 76)) = 1) : False := by
  have h_sgn76 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 76)) = -1 := by
    rw [nth_prime_num_76]; simp [digits_zero]
  rw [h_sgn76] at h_sgn; contradiction

theorem sgn_not_minus_77 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 77)) = -1) : False := by
  have h_sgn77 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 77)) = 1 := by
    rw [nth_prime_num_77]; simp [digits_zero]
  rw [h_sgn77] at h_sgn; contradiction

theorem sgn_not_plus_78 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 78)) = 1) : False := by
  have h_sgn78 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 78)) = -1 := by
    rw [nth_prime_num_78]; simp [digits_zero]
  rw [h_sgn78] at h_sgn; contradiction

theorem sgn_not_minus_79 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 79)) = -1) : False := by
  have h_sgn79 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 79)) = 1 := by
    rw [nth_prime_num_79]; simp [digits_zero]
  rw [h_sgn79] at h_sgn; contradiction

theorem sgn_not_minus_80 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 80)) = -1) : False := by
  have h_sgn80 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 80)) = 1 := by
    rw [nth_prime_num_80]; simp [digits_zero]
  rw [h_sgn80] at h_sgn; contradiction

theorem sgn_not_minus_81 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 81)) = -1) : False := by
  have h_sgn81 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 81)) = 1 := by
    rw [nth_prime_num_81]; simp [digits_zero]
  rw [h_sgn81] at h_sgn; contradiction

theorem sgn_not_minus_82 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 82)) = -1) : False := by
  have h_sgn82 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 82)) = 1 := by
    rw [nth_prime_num_82]; simp [digits_zero]
  rw [h_sgn82] at h_sgn; contradiction

theorem sgn_not_minus_83 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 83)) = -1) : False := by
  have h_sgn83 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 83)) = 1 := by
    rw [nth_prime_num_83]; simp [digits_zero]
  rw [h_sgn83] at h_sgn; contradiction

theorem sgn_not_minus_84 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 84)) = -1) : False := by
  have h_sgn84 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 84)) = 1 := by
    rw [nth_prime_num_84]; simp [digits_zero]
  rw [h_sgn84] at h_sgn; contradiction

theorem sgn_not_minus_85 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 85)) = -1) : False := by
  have h_sgn85 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 85)) = 1 := by
    rw [nth_prime_num_85]; simp [digits_zero]
  rw [h_sgn85] at h_sgn; contradiction

theorem sgn_not_plus_86 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 86)) = 1) : False := by
  have h_sgn86 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 86)) = -1 := by
    rw [nth_prime_num_86]; simp [digits_zero]
  rw [h_sgn86] at h_sgn; contradiction

theorem sgn_not_minus_87 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 87)) = -1) : False := by
  have h_sgn87 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 87)) = 1 := by
    rw [nth_prime_num_87]; simp [digits_zero]
  rw [h_sgn87] at h_sgn; contradiction

theorem sgn_not_plus_88 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 88)) = 1) : False := by
  have h_sgn88 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 88)) = -1 := by
    rw [nth_prime_num_88]; simp [digits_zero]
  rw [h_sgn88] at h_sgn; contradiction

theorem sgn_not_minus_89 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 89)) = -1) : False := by
  have h_sgn89 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 89)) = 1 := by
    rw [nth_prime_num_89]; simp [digits_zero]
  rw [h_sgn89] at h_sgn; contradiction

theorem sgn_not_plus_90 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 90)) = 1) : False := by
  have h_sgn90 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 90)) = -1 := by
    rw [nth_prime_num_90]; simp [digits_zero]
  rw [h_sgn90] at h_sgn; contradiction

theorem sgn_not_plus_91 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 91)) = 1) : False := by
  have h_sgn91 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 91)) = -1 := by
    rw [nth_prime_num_91]; simp [digits_zero]
  rw [h_sgn91] at h_sgn; contradiction

theorem sgn_not_minus_92 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 92)) = -1) : False := by
  have h_sgn92 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 92)) = 1 := by
    rw [nth_prime_num_92]; simp [digits_zero]
  rw [h_sgn92] at h_sgn; contradiction

theorem sgn_not_minus_93 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 93)) = -1) : False := by
  have h_sgn93 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 93)) = 1 := by
    rw [nth_prime_num_93]; simp [digits_zero]
  rw [h_sgn93] at h_sgn; contradiction

theorem sgn_not_minus_94 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 94)) = -1) : False := by
  have h_sgn94 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 94)) = 1 := by
    rw [nth_prime_num_94]; simp [digits_zero]
  rw [h_sgn94] at h_sgn; contradiction

theorem sgn_not_plus_95 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 95)) = 1) : False := by
  have h_sgn95 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 95)) = -1 := by
    rw [nth_prime_num_95]; simp [digits_zero]
  rw [h_sgn95] at h_sgn; contradiction

theorem sgn_not_plus_96 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 96)) = 1) : False := by
  have h_sgn96 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 96)) = -1 := by
    rw [nth_prime_num_96]; simp [digits_zero]
  rw [h_sgn96] at h_sgn; contradiction

theorem sgn_not_minus_97 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 97)) = -1) : False := by
  have h_sgn97 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 97)) = 1 := by
    rw [nth_prime_num_97]; simp [digits_zero]
  rw [h_sgn97] at h_sgn; contradiction

theorem sgn_not_plus_98 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 98)) = 1) : False := by
  have h_sgn98 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 98)) = -1 := by
    rw [nth_prime_num_98]; simp [digits_zero]
  rw [h_sgn98] at h_sgn; contradiction

theorem sgn_not_minus_99 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 99)) = -1) : False := by
  have h_sgn99 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 99)) = 1 := by
    rw [nth_prime_num_99]; simp [digits_zero]
  rw [h_sgn99] at h_sgn; contradiction

theorem sgn_not_plus_100 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 100)) = 1) : False := by
  have h_sgn100 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 100)) = -1 := by
    rw [nth_prime_num_100]; simp [digits_zero]
  rw [h_sgn100] at h_sgn; contradiction

theorem sgn_not_minus_101 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 101)) = -1) : False := by
  have h_sgn101 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 101)) = 1 := by
    rw [nth_prime_num_101]; simp [digits_zero]
  rw [h_sgn101] at h_sgn; contradiction

theorem sgn_not_minus_102 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 102)) = -1) : False := by
  have h_sgn102 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 102)) = 1 := by
    rw [nth_prime_num_102]; simp [digits_zero]
  rw [h_sgn102] at h_sgn; contradiction

theorem sgn_not_minus_103 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 103)) = -1) : False := by
  have h_sgn103 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 103)) = 1 := by
    rw [nth_prime_num_103]; simp [digits_zero]
  rw [h_sgn103] at h_sgn; contradiction

theorem sgn_not_plus_104 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 104)) = 1) : False := by
  have h_sgn104 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 104)) = -1 := by
    rw [nth_prime_num_104]; simp [digits_zero]
  rw [h_sgn104] at h_sgn; contradiction

theorem sgn_not_minus_105 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 105)) = -1) : False := by
  have h_sgn105 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 105)) = 1 := by
    rw [nth_prime_num_105]; simp [digits_zero]
  rw [h_sgn105] at h_sgn; contradiction

theorem sgn_not_minus_106 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 106)) = -1) : False := by
  have h_sgn106 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 106)) = 1 := by
    rw [nth_prime_num_106]; simp [digits_zero]
  rw [h_sgn106] at h_sgn; contradiction

theorem sgn_not_plus_107 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 107)) = 1) : False := by
  have h_sgn107 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 107)) = -1 := by
    rw [nth_prime_num_107]; simp [digits_zero]
  rw [h_sgn107] at h_sgn; contradiction

theorem sgn_not_plus_108 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 108)) = 1) : False := by
  have h_sgn108 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 108)) = -1 := by
    rw [nth_prime_num_108]; simp [digits_zero]
  rw [h_sgn108] at h_sgn; contradiction

theorem sgn_not_minus_109 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 109)) = -1) : False := by
  have h_sgn109 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 109)) = 1 := by
    rw [nth_prime_num_109]; simp [digits_zero]
  rw [h_sgn109] at h_sgn; contradiction

theorem sgn_not_minus_110 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 110)) = -1) : False := by
  have h_sgn110 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 110)) = 1 := by
    rw [nth_prime_num_110]; simp [digits_zero]
  rw [h_sgn110] at h_sgn; contradiction

theorem sgn_not_minus_111 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 111)) = -1) : False := by
  have h_sgn111 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 111)) = 1 := by
    rw [nth_prime_num_111]; simp [digits_zero]
  rw [h_sgn111] at h_sgn; contradiction

theorem sgn_not_minus_112 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 112)) = -1) : False := by
  have h_sgn112 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 112)) = 1 := by
    rw [nth_prime_num_112]; simp [digits_zero]
  rw [h_sgn112] at h_sgn; contradiction

theorem sgn_not_plus_113 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 113)) = 1) : False := by
  have h_sgn113 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 113)) = -1 := by
    rw [nth_prime_num_113]; simp [digits_zero]
  rw [h_sgn113] at h_sgn; contradiction

theorem sgn_not_minus_114 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 114)) = -1) : False := by
  have h_sgn114 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 114)) = 1 := by
    rw [nth_prime_num_114]; simp [digits_zero]
  rw [h_sgn114] at h_sgn; contradiction

theorem sgn_not_minus_115 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 115)) = -1) : False := by
  have h_sgn115 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 115)) = 1 := by
    rw [nth_prime_num_115]; simp [digits_zero]
  rw [h_sgn115] at h_sgn; contradiction

theorem sgn_not_plus_116 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 116)) = 1) : False := by
  have h_sgn116 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 116)) = -1 := by
    rw [nth_prime_num_116]; simp [digits_zero]
  rw [h_sgn116] at h_sgn; contradiction

theorem sgn_not_minus_117 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 117)) = -1) : False := by
  have h_sgn117 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 117)) = 1 := by
    rw [nth_prime_num_117]; simp [digits_zero]
  rw [h_sgn117] at h_sgn; contradiction

theorem sgn_not_minus_118 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 118)) = -1) : False := by
  have h_sgn118 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 118)) = 1 := by
    rw [nth_prime_num_118]; simp [digits_zero]
  rw [h_sgn118] at h_sgn; contradiction

theorem sgn_not_minus_119 (h_sgn : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
  weight_parity_sign (Nat.nth Nat.Prime 119)) = -1) : False := by
  have h_sgn119 : (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
    let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
    weight_parity_sign (Nat.nth Nat.Prime 119)) = 1 := by
    rw [nth_prime_num_119]; simp [digits_zero]
  rw [h_sgn119] at h_sgn; contradiction

def P (n : ℕ) : Prop :=
  A130911 n ≥ 1 ∧
  (A130911 n = 1 → n = 11) ∧
  (A130911 n = 2 → n = 12 ∨ n = 14 ∨ n = 16) ∧
  (A130911 n = 3 → n = 13 ∨ n = 15 ∨ n = 17) ∧
  (A130911 n = 4 → n = 18 ∨ n = 20 ∨ n = 24 ∨ n = 26) ∧
  (A130911 n = 5 → n = 19 ∨ n = 21 ∨ n = 23 ∨ n = 25 ∨ n = 27) ∧
  (A130911 n = 6 → n = 22 ∨ n = 28 ∨ n = 30) ∧
  (A130911 n = 7 → n = 29 ∨ n = 31 ∨ n = 35) ∧
  (A130911 n = 8 → n = 32 ∨ n = 34 ∨ n = 36 ∨ n = 38) ∧
  (A130911 n = 9 → n = 33 ∨ n = 37 ∨ n = 39) ∧
  (A130911 n = 10 → n = 40) ∧
  (A130911 n = 11 → n = 41) ∧
  (A130911 n = 12 → n = 42) ∧
  (A130911 n = 13 → n = 43 ∨ n = 45 ∨ n = 77 ∨ n = 79) ∧
  (A130911 n = 14 → n = 44 ∨ n = 46 ∨ n = 72 ∨ n = 74 ∨ n = 76 ∨ n = 78 ∨ n = 80) ∧
  (A130911 n = 15 → n = 47 ∨ n = 71 ∨ n = 73 ∨ n = 75 ∨ n = 81) ∧
  (A130911 n = 16 → n = 48 ∨ n = 70 ∨ n = 82) ∧
  (A130911 n = 17 → n = 49 ∨ n = 69 ∨ n = 83) ∧
  (A130911 n = 18 → n = 50 ∨ n = 60 ∨ n = 62 ∨ n = 64 ∨ n = 66 ∨ n = 68 ∨ n = 84 ∨ n = 92) ∧
  (A130911 n = 19 → n = 51 ∨ n = 57 ∨ n = 59 ∨ n = 61 ∨ n = 63 ∨ n = 65 ∨ n = 67 ∨ n = 85 ∨ n = 87 ∨ n = 89 ∨ n = 91 ∨ n = 93 ∨ n = 97 ∨ n = 99 ∨ n = 101) ∧
  (A130911 n = 20 → n = 52 ∨ n = 56 ∨ n = 58 ∨ n = 86 ∨ n = 88 ∨ n = 90 ∨ n = 94 ∨ n = 96 ∨ n = 98 ∨ n = 100 ∨ n = 102) ∧
  (A130911 n = 21 → n = 53 ∨ n = 55 ∨ n = 95 ∨ n = 103 ∨ n = 105 ∨ n = 109) ∧
  (A130911 n = 22 → n = 54 ∨ n = 104 ∨ n = 106 ∨ n = 108 ∨ n = 110) ∧
  (A130911 n = 23 → n = 107 ∨ n = 111) ∧
  (A130911 n = 24 → n = 112 ∨ n = 114) ∧
  (A130911 n = 25 → n = 113 ∨ n = 115 ∨ n = 117) ∧
  (A130911 n = 26 → n = 116 ∨ n = 118) ∧
  (A130911 n = 27 → n = 119) ∧
  (A130911 n = 28 → n = 120) ∧
  (A130911 n = 29 → n = 121) ∧
  (A130911 n ≥ 30 → False)

theorem A130911_ge_one (n : ℕ) : n ≥ 11 → P n := by
  induction' n with n ih
  · intro h; omega
  · intro h
    by_cases hn : n ≥ 11
    · have h_ih := ih hn
      have h_ih_1 := h_ih.1
      have h_ih_2 := h_ih.2.1
      have h_ih_3 := h_ih.2.2.1
      have h_ih_4 := h_ih.2.2.2.1
      have h_ih_5 := h_ih.2.2.2.2.1
      have h_ih_6 := h_ih.2.2.2.2.2.1
      have h_ih_7 := h_ih.2.2.2.2.2.2.1
      have h_ih_8 := h_ih.2.2.2.2.2.2.2.1
      have h_ih_9 := h_ih.2.2.2.2.2.2.2.2.1
      have h_ih_10 := h_ih.2.2.2.2.2.2.2.2.2.1
      have h_ih_11 := h_ih.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_12 := h_ih.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_13 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_14 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_15 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_16 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_17 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_18 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_19 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_20 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_21 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_22 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_23 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_24 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_25 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_26 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_27 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_28 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_29 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_30 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h_ih_31 := h_ih.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

      have h_step : A130911 (n + 1) = A130911 n +
        (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
         let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
         weight_parity_sign (Nat.nth Nat.Prime n)) := by
         dsimp [A130911]
         rw [sum_range_succ]
      have sgn_values :
        (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
         let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
         weight_parity_sign (Nat.nth Nat.Prime n)) = 1 ∨
        (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
         let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
         weight_parity_sign (Nat.nth Nat.Prime n)) = -1 := by
         dsimp; split <;> omega
      rcases sgn_values with h_sgn | h_sgn
      · -- sgn = 1
        rw [h_sgn] at h_step
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        intro h_eq_1; omega
        -- 2. A(n+1) = 2 -> n+1 in [12, 14, 16]
        intro h_eq_2; have : A130911 n = 1 := by omega
        have hn_or := h_ih_2 this
        have h_eq := hn_or
        · subst h_eq; left; rfl
        -- 3. A(n+1) = 3 -> n+1 in [13, 15, 17]
        intro h_eq_3; have : A130911 n = 2 := by omega
        have hn_or := h_ih_3 this
        rcases hn_or with h_eq_12|h_eq_14|h_eq_16
        · subst h_eq_12; left; rfl
        · subst h_eq_14; right; left; rfl
        · subst h_eq_16; right; right; rfl
        -- 4. A(n+1) = 4 -> n+1 in [18, 20, 24, 26]
        intro h_eq_4; have : A130911 n = 3 := by omega
        have hn_or := h_ih_4 this
        rcases hn_or with h_eq_13|h_eq_15|h_eq_17
        · subst h_eq_13; exact (sgn_not_plus_13 h_sgn).elim
        · subst h_eq_15; exact (sgn_not_plus_15 h_sgn).elim
        · subst h_eq_17; left; rfl
        -- 5. A(n+1) = 5 -> n+1 in [19, 21, 23, 25, 27]
        intro h_eq_5; have : A130911 n = 4 := by omega
        have hn_or := h_ih_5 this
        rcases hn_or with h_eq_18|h_eq_20|h_eq_24|h_eq_26
        · subst h_eq_18; left; rfl
        · subst h_eq_20; right; left; rfl
        · subst h_eq_24; right; right; right; left; rfl
        · subst h_eq_26; right; right; right; right; rfl
        -- 6. A(n+1) = 6 -> n+1 in [22, 28, 30]
        intro h_eq_6; have : A130911 n = 5 := by omega
        have hn_or := h_ih_6 this
        rcases hn_or with h_eq_19|h_eq_21|h_eq_23|h_eq_25|h_eq_27
        · subst h_eq_19; exact (sgn_not_plus_19 h_sgn).elim
        · subst h_eq_21; left; rfl
        · subst h_eq_23; exact (sgn_not_plus_23 h_sgn).elim
        · subst h_eq_25; exact (sgn_not_plus_25 h_sgn).elim
        · subst h_eq_27; right; left; rfl
        -- 7. A(n+1) = 7 -> n+1 in [29, 31, 35]
        intro h_eq_7; have : A130911 n = 6 := by omega
        have hn_or := h_ih_7 this
        rcases hn_or with h_eq_22|h_eq_28|h_eq_30
        · subst h_eq_22; exact (sgn_not_plus_22 h_sgn).elim
        · subst h_eq_28; left; rfl
        · subst h_eq_30; right; left; rfl
        -- 8. A(n+1) = 8 -> n+1 in [32, 34, 36, 38]
        intro h_eq_8; have : A130911 n = 7 := by omega
        have hn_or := h_ih_8 this
        rcases hn_or with h_eq_29|h_eq_31|h_eq_35
        · subst h_eq_29; exact (sgn_not_plus_29 h_sgn).elim
        · subst h_eq_31; left; rfl
        · subst h_eq_35; right; right; left; rfl
        -- 9. A(n+1) = 9 -> n+1 in [33, 37, 39]
        intro h_eq_9; have : A130911 n = 8 := by omega
        have hn_or := h_ih_9 this
        rcases hn_or with h_eq_32|h_eq_34|h_eq_36|h_eq_38
        · subst h_eq_32; left; rfl
        · subst h_eq_34; exact (sgn_not_plus_34 h_sgn).elim
        · subst h_eq_36; right; left; rfl
        · subst h_eq_38; right; right; rfl
        -- 10. A(n+1) = 10 -> n+1 in [40]
        intro h_eq_10; have : A130911 n = 9 := by omega
        have hn_or := h_ih_10 this
        rcases hn_or with h_eq_33|h_eq_37|h_eq_39
        · subst h_eq_33; exact (sgn_not_plus_33 h_sgn).elim
        · subst h_eq_37; exact (sgn_not_plus_37 h_sgn).elim
        · subst h_eq_39; rfl
        -- 11. A(n+1) = 11 -> n+1 in [41]
        intro h_eq_11; have : A130911 n = 10 := by omega
        have hn_or := h_ih_11 this
        have h_eq := hn_or
        · subst h_eq; rfl
        -- 12. A(n+1) = 12 -> n+1 in [42]
        intro h_eq_12; have : A130911 n = 11 := by omega
        have hn_or := h_ih_12 this
        have h_eq := hn_or
        · subst h_eq; rfl
        -- 13. A(n+1) = 13 -> n+1 in [43, 45, 77, 79]
        intro h_eq_13; have : A130911 n = 12 := by omega
        have hn_or := h_ih_13 this
        have h_eq := hn_or
        · subst h_eq; left; rfl
        -- 14. A(n+1) = 14 -> n+1 in [44, 46, 72, 74, 76, 78, 80]
        intro h_eq_14; have : A130911 n = 13 := by omega
        have hn_or := h_ih_14 this
        rcases hn_or with h_eq_43|h_eq_45|h_eq_77|h_eq_79
        · subst h_eq_43; left; rfl
        · subst h_eq_45; right; left; rfl
        · subst h_eq_77; right; right; right; right; right; left; rfl
        · subst h_eq_79; right; right; right; right; right; right; rfl
        -- 15. A(n+1) = 15 -> n+1 in [47, 71, 73, 75, 81]
        intro h_eq_15; have : A130911 n = 14 := by omega
        have hn_or := h_ih_15 this
        rcases hn_or with h_eq_44|h_eq_46|h_eq_72|h_eq_74|h_eq_76|h_eq_78|h_eq_80
        · subst h_eq_44; exact (sgn_not_plus_44 h_sgn).elim
        · subst h_eq_46; left; rfl
        · subst h_eq_72; right; right; left; rfl
        · subst h_eq_74; right; right; right; left; rfl
        · subst h_eq_76; exact (sgn_not_plus_76 h_sgn).elim
        · subst h_eq_78; exact (sgn_not_plus_78 h_sgn).elim
        · subst h_eq_80; right; right; right; right; rfl
        -- 16. A(n+1) = 16 -> n+1 in [48, 70, 82]
        intro h_eq_16; have : A130911 n = 15 := by omega
        have hn_or := h_ih_16 this
        rcases hn_or with h_eq_47|h_eq_71|h_eq_73|h_eq_75|h_eq_81
        · subst h_eq_47; left; rfl
        · subst h_eq_71; exact (sgn_not_plus_71 h_sgn).elim
        · subst h_eq_73; exact (sgn_not_plus_73 h_sgn).elim
        · subst h_eq_75; exact (sgn_not_plus_75 h_sgn).elim
        · subst h_eq_81; right; right; rfl
        -- 17. A(n+1) = 17 -> n+1 in [49, 69, 83]
        intro h_eq_17; have : A130911 n = 16 := by omega
        have hn_or := h_ih_17 this
        rcases hn_or with h_eq_48|h_eq_70|h_eq_82
        · subst h_eq_48; left; rfl
        · subst h_eq_70; exact (sgn_not_plus_70 h_sgn).elim
        · subst h_eq_82; right; right; rfl
        -- 18. A(n+1) = 18 -> n+1 in [50, 60, 62, 64, 66, 68, 84, 92]
        intro h_eq_18; have : A130911 n = 17 := by omega
        have hn_or := h_ih_18 this
        rcases hn_or with h_eq_49|h_eq_69|h_eq_83
        · subst h_eq_49; left; rfl
        · subst h_eq_69; exact (sgn_not_plus_69 h_sgn).elim
        · subst h_eq_83; right; right; right; right; right; right; left; rfl
        -- 19. A(n+1) = 19 -> n+1 in [51, 57, 59, 61, 63, 65, 67, 85, 87, 89, 91, 93, 97, 99, 101]
        intro h_eq_19; have : A130911 n = 18 := by omega
        have hn_or := h_ih_19 this
        rcases hn_or with h_eq_50|h_eq_60|h_eq_62|h_eq_64|h_eq_66|h_eq_68|h_eq_84|h_eq_92
        · subst h_eq_50; left; rfl
        · subst h_eq_60; right; right; right; left; rfl
        · subst h_eq_62; right; right; right; right; left; rfl
        · subst h_eq_64; right; right; right; right; right; left; rfl
        · subst h_eq_66; right; right; right; right; right; right; left; rfl
        · subst h_eq_68; exact (sgn_not_plus_68 h_sgn).elim
        · subst h_eq_84; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_92; right; right; right; right; right; right; right; right; right; right; right; left; rfl
        -- 20. A(n+1) = 20 -> n+1 in [52, 56, 58, 86, 88, 90, 94, 96, 98, 100, 102]
        intro h_eq_20; have : A130911 n = 19 := by omega
        have hn_or := h_ih_20 this
        rcases hn_or with h_eq_51|h_eq_57|h_eq_59|h_eq_61|h_eq_63|h_eq_65|h_eq_67|h_eq_85|h_eq_87|h_eq_89|h_eq_91|h_eq_93|h_eq_97|h_eq_99|h_eq_101
        · subst h_eq_51; left; rfl
        · subst h_eq_57; right; right; left; rfl
        · subst h_eq_59; exact (sgn_not_plus_59 h_sgn).elim
        · subst h_eq_61; exact (sgn_not_plus_61 h_sgn).elim
        · subst h_eq_63; exact (sgn_not_plus_63 h_sgn).elim
        · subst h_eq_65; exact (sgn_not_plus_65 h_sgn).elim
        · subst h_eq_67; exact (sgn_not_plus_67 h_sgn).elim
        · subst h_eq_85; right; right; right; left; rfl
        · subst h_eq_87; right; right; right; right; left; rfl
        · subst h_eq_89; right; right; right; right; right; left; rfl
        · subst h_eq_91; exact (sgn_not_plus_91 h_sgn).elim
        · subst h_eq_93; right; right; right; right; right; right; left; rfl
        · subst h_eq_97; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_99; right; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_101; right; right; right; right; right; right; right; right; right; right; rfl
        -- 21. A(n+1) = 21 -> n+1 in [53, 55, 95, 103, 105, 109]
        intro h_eq_21; have : A130911 n = 20 := by omega
        have hn_or := h_ih_21 this
        rcases hn_or with h_eq_52|h_eq_56|h_eq_58|h_eq_86|h_eq_88|h_eq_90|h_eq_94|h_eq_96|h_eq_98|h_eq_100|h_eq_102
        · subst h_eq_52; left; rfl
        · subst h_eq_56; exact (sgn_not_plus_56 h_sgn).elim
        · subst h_eq_58; exact (sgn_not_plus_58 h_sgn).elim
        · subst h_eq_86; exact (sgn_not_plus_86 h_sgn).elim
        · subst h_eq_88; exact (sgn_not_plus_88 h_sgn).elim
        · subst h_eq_90; exact (sgn_not_plus_90 h_sgn).elim
        · subst h_eq_94; right; right; left; rfl
        · subst h_eq_96; exact (sgn_not_plus_96 h_sgn).elim
        · subst h_eq_98; exact (sgn_not_plus_98 h_sgn).elim
        · subst h_eq_100; exact (sgn_not_plus_100 h_sgn).elim
        · subst h_eq_102; right; right; right; left; rfl
        -- 22. A(n+1) = 22 -> n+1 in [54, 104, 106, 108, 110]
        intro h_eq_22; have : A130911 n = 21 := by omega
        have hn_or := h_ih_22 this
        rcases hn_or with h_eq_53|h_eq_55|h_eq_95|h_eq_103|h_eq_105|h_eq_109
        · subst h_eq_53; left; rfl
        · subst h_eq_55; exact (sgn_not_plus_55 h_sgn).elim
        · subst h_eq_95; exact (sgn_not_plus_95 h_sgn).elim
        · subst h_eq_103; right; left; rfl
        · subst h_eq_105; right; right; left; rfl
        · subst h_eq_109; right; right; right; right; rfl
        -- 23. A(n+1) = 23 -> n+1 in [107, 111]
        intro h_eq_23; have : A130911 n = 22 := by omega
        have hn_or := h_ih_23 this
        rcases hn_or with h_eq_54|h_eq_104|h_eq_106|h_eq_108|h_eq_110
        · subst h_eq_54; exact (sgn_not_plus_54 h_sgn).elim
        · subst h_eq_104; exact (sgn_not_plus_104 h_sgn).elim
        · subst h_eq_106; left; rfl
        · subst h_eq_108; exact (sgn_not_plus_108 h_sgn).elim
        · subst h_eq_110; right; rfl
        -- 24. A(n+1) = 24 -> n+1 in [112, 114]
        intro h_eq_24; have : A130911 n = 23 := by omega
        have hn_or := h_ih_24 this
        rcases hn_or with h_eq_107|h_eq_111
        · subst h_eq_107; exact (sgn_not_plus_107 h_sgn).elim
        · subst h_eq_111; left; rfl
        -- 25. A(n+1) = 25 -> n+1 in [113, 115, 117]
        intro h_eq_25; have : A130911 n = 24 := by omega
        have hn_or := h_ih_25 this
        rcases hn_or with h_eq_112|h_eq_114
        · subst h_eq_112; left; rfl
        · subst h_eq_114; right; left; rfl
        -- 26. A(n+1) = 26 -> n+1 in [116, 118]
        intro h_eq_26; have : A130911 n = 25 := by omega
        have hn_or := h_ih_26 this
        rcases hn_or with h_eq_113|h_eq_115|h_eq_117
        · subst h_eq_113; exact (sgn_not_plus_113 h_sgn).elim
        · subst h_eq_115; left; rfl
        · subst h_eq_117; right; rfl
        -- 27. A(n+1) = 27 -> n+1 in [119]
        intro h_eq_27; have : A130911 n = 26 := by omega
        have hn_or := h_ih_27 this
        rcases hn_or with h_eq_116|h_eq_118
        · subst h_eq_116; exact (sgn_not_plus_116 h_sgn).elim
        · subst h_eq_118; rfl
        -- 28. A(n+1) = 28 -> n+1 in [120]
        intro h_eq_28; have : A130911 n = 27 := by omega
        have hn_or := h_ih_28 this
        have h_eq := hn_or
        · subst h_eq; rfl
        -- 29. A(n+1) = 29 -> n+1 in [121]
        intro h_eq_29; have : A130911 n = 28 := by omega
        have hn_or := h_ih_29 this
        have h_eq := hn_or
        · subst h_eq; rfl
        -- 30. A(n+1) >= 30 -> False
        intro h_ge30
        have hn_ge29 : A130911 n ≥ 29 := by omega
        have hn_eq29_or : A130911 n = 29 ∨ A130911 n ≥ 30 := by omega
        rcases hn_eq29_or with h_eq29 | h_ge30_n
        · have hn_or := h_ih_30 h_eq29
          exact hn_or.elim
        · exact h_ih_31 h_ge30_n

      · -- sgn = -1
        rw [h_sgn] at h_step
        have h_ge2 : A130911 n ≥ 2 := by
          by_cases hn11 : n = 11
          · subst hn11; exact (sgn_not_minus_11 h_sgn).elim
          · have : A130911 n ≠ 1 := by
                intro h_eq1
                have := h_ih_2 h_eq1
                subst this
                contradiction
            omega
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        -- 1. A(n+1) = 1 -> n+1 in [11]
        intro h_eq_1; have : A130911 n = 2 := by omega
        have hn_or := h_ih_3 this
        rcases hn_or with h_eq_12|h_eq_14|h_eq_16
        · subst h_eq_12; exact (sgn_not_minus_12 h_sgn).elim
        · subst h_eq_14; exact (sgn_not_minus_14 h_sgn).elim
        · subst h_eq_16; exact (sgn_not_minus_16 h_sgn).elim
        -- 2. A(n+1) = 2 -> n+1 in [12, 14, 16]
        intro h_eq_2; have : A130911 n = 3 := by omega
        have hn_or := h_ih_4 this
        rcases hn_or with h_eq_13|h_eq_15|h_eq_17
        · subst h_eq_13; right; left; rfl
        · subst h_eq_15; right; right; rfl
        · subst h_eq_17; exact (sgn_not_minus_17 h_sgn).elim
        -- 3. A(n+1) = 3 -> n+1 in [13, 15, 17]
        intro h_eq_3; have : A130911 n = 4 := by omega
        have hn_or := h_ih_5 this
        rcases hn_or with h_eq_18|h_eq_20|h_eq_24|h_eq_26
        · subst h_eq_18; exact (sgn_not_minus_18 h_sgn).elim
        · subst h_eq_20; exact (sgn_not_minus_20 h_sgn).elim
        · subst h_eq_24; exact (sgn_not_minus_24 h_sgn).elim
        · subst h_eq_26; exact (sgn_not_minus_26 h_sgn).elim
        -- 4. A(n+1) = 4 -> n+1 in [18, 20, 24, 26]
        intro h_eq_4; have : A130911 n = 5 := by omega
        have hn_or := h_ih_6 this
        rcases hn_or with h_eq_19|h_eq_21|h_eq_23|h_eq_25|h_eq_27
        · subst h_eq_19; right; left; rfl
        · subst h_eq_21; exact (sgn_not_minus_21 h_sgn).elim
        · subst h_eq_23; right; right; left; rfl
        · subst h_eq_25; right; right; right; rfl
        · subst h_eq_27; exact (sgn_not_minus_27 h_sgn).elim
        -- 5. A(n+1) = 5 -> n+1 in [19, 21, 23, 25, 27]
        intro h_eq_5; have : A130911 n = 6 := by omega
        have hn_or := h_ih_7 this
        rcases hn_or with h_eq_22|h_eq_28|h_eq_30
        · subst h_eq_22; right; right; left; rfl
        · subst h_eq_28; exact (sgn_not_minus_28 h_sgn).elim
        · subst h_eq_30; exact (sgn_not_minus_30 h_sgn).elim
        -- 6. A(n+1) = 6 -> n+1 in [22, 28, 30]
        intro h_eq_6; have : A130911 n = 7 := by omega
        have hn_or := h_ih_8 this
        rcases hn_or with h_eq_29|h_eq_31|h_eq_35
        · subst h_eq_29; right; right; rfl
        · subst h_eq_31; exact (sgn_not_minus_31 h_sgn).elim
        · subst h_eq_35; exact (sgn_not_minus_35 h_sgn).elim
        -- 7. A(n+1) = 7 -> n+1 in [29, 31, 35]
        intro h_eq_7; have : A130911 n = 8 := by omega
        have hn_or := h_ih_9 this
        rcases hn_or with h_eq_32|h_eq_34|h_eq_36|h_eq_38
        · subst h_eq_32; exact (sgn_not_minus_32 h_sgn).elim
        · subst h_eq_34; right; right; rfl
        · subst h_eq_36; exact (sgn_not_minus_36 h_sgn).elim
        · subst h_eq_38; exact (sgn_not_minus_38 h_sgn).elim
        -- 8. A(n+1) = 8 -> n+1 in [32, 34, 36, 38]
        intro h_eq_8; have : A130911 n = 9 := by omega
        have hn_or := h_ih_10 this
        rcases hn_or with h_eq_33|h_eq_37|h_eq_39
        · subst h_eq_33; right; left; rfl
        · subst h_eq_37; right; right; right; rfl
        · subst h_eq_39; exact (sgn_not_minus_39 h_sgn).elim
        -- 9. A(n+1) = 9 -> n+1 in [33, 37, 39]
        intro h_eq_9; have : A130911 n = 10 := by omega
        have hn_or := h_ih_11 this
        have h_eq := hn_or
        · subst h_eq; exact (sgn_not_minus_40 h_sgn).elim
        -- 10. A(n+1) = 10 -> n+1 in [40]
        intro h_eq_10; have : A130911 n = 11 := by omega
        have hn_or := h_ih_12 this
        have h_eq := hn_or
        · subst h_eq; exact (sgn_not_minus_41 h_sgn).elim
        -- 11. A(n+1) = 11 -> n+1 in [41]
        intro h_eq_11; have : A130911 n = 12 := by omega
        have hn_or := h_ih_13 this
        have h_eq := hn_or
        · subst h_eq; exact (sgn_not_minus_42 h_sgn).elim
        -- 12. A(n+1) = 12 -> n+1 in [42]
        intro h_eq_12; have : A130911 n = 13 := by omega
        have hn_or := h_ih_14 this
        rcases hn_or with h_eq_43|h_eq_45|h_eq_77|h_eq_79
        · subst h_eq_43; exact (sgn_not_minus_43 h_sgn).elim
        · subst h_eq_45; exact (sgn_not_minus_45 h_sgn).elim
        · subst h_eq_77; exact (sgn_not_minus_77 h_sgn).elim
        · subst h_eq_79; exact (sgn_not_minus_79 h_sgn).elim
        -- 13. A(n+1) = 13 -> n+1 in [43, 45, 77, 79]
        intro h_eq_13; have : A130911 n = 14 := by omega
        have hn_or := h_ih_15 this
        rcases hn_or with h_eq_44|h_eq_46|h_eq_72|h_eq_74|h_eq_76|h_eq_78|h_eq_80
        · subst h_eq_44; right; left; rfl
        · subst h_eq_46; exact (sgn_not_minus_46 h_sgn).elim
        · subst h_eq_72; exact (sgn_not_minus_72 h_sgn).elim
        · subst h_eq_74; exact (sgn_not_minus_74 h_sgn).elim
        · subst h_eq_76; right; right; left; rfl
        · subst h_eq_78; right; right; right; rfl
        · subst h_eq_80; exact (sgn_not_minus_80 h_sgn).elim
        -- 14. A(n+1) = 14 -> n+1 in [44, 46, 72, 74, 76, 78, 80]
        intro h_eq_14; have : A130911 n = 15 := by omega
        have hn_or := h_ih_16 this
        rcases hn_or with h_eq_47|h_eq_71|h_eq_73|h_eq_75|h_eq_81
        · subst h_eq_47; exact (sgn_not_minus_47 h_sgn).elim
        · subst h_eq_71; right; right; left; rfl
        · subst h_eq_73; right; right; right; left; rfl
        · subst h_eq_75; right; right; right; right; left; rfl
        · subst h_eq_81; exact (sgn_not_minus_81 h_sgn).elim
        -- 15. A(n+1) = 15 -> n+1 in [47, 71, 73, 75, 81]
        intro h_eq_15; have : A130911 n = 16 := by omega
        have hn_or := h_ih_17 this
        rcases hn_or with h_eq_48|h_eq_70|h_eq_82
        · subst h_eq_48; exact (sgn_not_minus_48 h_sgn).elim
        · subst h_eq_70; right; left; rfl
        · subst h_eq_82; exact (sgn_not_minus_82 h_sgn).elim
        -- 16. A(n+1) = 16 -> n+1 in [48, 70, 82]
        intro h_eq_16; have : A130911 n = 17 := by omega
        have hn_or := h_ih_18 this
        rcases hn_or with h_eq_49|h_eq_69|h_eq_83
        · subst h_eq_49; exact (sgn_not_minus_49 h_sgn).elim
        · subst h_eq_69; right; left; rfl
        · subst h_eq_83; exact (sgn_not_minus_83 h_sgn).elim
        -- 17. A(n+1) = 17 -> n+1 in [49, 69, 83]
        intro h_eq_17; have : A130911 n = 18 := by omega
        have hn_or := h_ih_19 this
        rcases hn_or with h_eq_50|h_eq_60|h_eq_62|h_eq_64|h_eq_66|h_eq_68|h_eq_84|h_eq_92
        · subst h_eq_50; exact (sgn_not_minus_50 h_sgn).elim
        · subst h_eq_60; exact (sgn_not_minus_60 h_sgn).elim
        · subst h_eq_62; exact (sgn_not_minus_62 h_sgn).elim
        · subst h_eq_64; exact (sgn_not_minus_64 h_sgn).elim
        · subst h_eq_66; exact (sgn_not_minus_66 h_sgn).elim
        · subst h_eq_68; right; left; rfl
        · subst h_eq_84; exact (sgn_not_minus_84 h_sgn).elim
        · subst h_eq_92; exact (sgn_not_minus_92 h_sgn).elim
        -- 18. A(n+1) = 18 -> n+1 in [50, 60, 62, 64, 66, 68, 84, 92]
        intro h_eq_18; have : A130911 n = 19 := by omega
        have hn_or := h_ih_20 this
        rcases hn_or with h_eq_51|h_eq_57|h_eq_59|h_eq_61|h_eq_63|h_eq_65|h_eq_67|h_eq_85|h_eq_87|h_eq_89|h_eq_91|h_eq_93|h_eq_97|h_eq_99|h_eq_101
        · subst h_eq_51; exact (sgn_not_minus_51 h_sgn).elim
        · subst h_eq_57; exact (sgn_not_minus_57 h_sgn).elim
        · subst h_eq_59; right; left; rfl
        · subst h_eq_61; right; right; left; rfl
        · subst h_eq_63; right; right; right; left; rfl
        · subst h_eq_65; right; right; right; right; left; rfl
        · subst h_eq_67; right; right; right; right; right; left; rfl
        · subst h_eq_85; exact (sgn_not_minus_85 h_sgn).elim
        · subst h_eq_87; exact (sgn_not_minus_87 h_sgn).elim
        · subst h_eq_89; exact (sgn_not_minus_89 h_sgn).elim
        · subst h_eq_91; right; right; right; right; right; right; right; rfl
        · subst h_eq_93; exact (sgn_not_minus_93 h_sgn).elim
        · subst h_eq_97; exact (sgn_not_minus_97 h_sgn).elim
        · subst h_eq_99; exact (sgn_not_minus_99 h_sgn).elim
        · subst h_eq_101; exact (sgn_not_minus_101 h_sgn).elim
        -- 19. A(n+1) = 19 -> n+1 in [51, 57, 59, 61, 63, 65, 67, 85, 87, 89, 91, 93, 97, 99, 101]
        intro h_eq_19; have : A130911 n = 20 := by omega
        have hn_or := h_ih_21 this
        rcases hn_or with h_eq_52|h_eq_56|h_eq_58|h_eq_86|h_eq_88|h_eq_90|h_eq_94|h_eq_96|h_eq_98|h_eq_100|h_eq_102
        · subst h_eq_52; exact (sgn_not_minus_52 h_sgn).elim
        · subst h_eq_56; right; left; rfl
        · subst h_eq_58; right; right; left; rfl
        · subst h_eq_86; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_88; right; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_90; right; right; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_94; exact (sgn_not_minus_94 h_sgn).elim
        · subst h_eq_96; right; right; right; right; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_98; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_100; right; right; right; right; right; right; right; right; right; right; right; right; right; right; rfl
        · subst h_eq_102; exact (sgn_not_minus_102 h_sgn).elim
        -- 20. A(n+1) = 20 -> n+1 in [52, 56, 58, 86, 88, 90, 94, 96, 98, 100, 102]
        intro h_eq_20; have : A130911 n = 21 := by omega
        have hn_or := h_ih_22 this
        rcases hn_or with h_eq_53|h_eq_55|h_eq_95|h_eq_103|h_eq_105|h_eq_109
        · subst h_eq_53; exact (sgn_not_minus_53 h_sgn).elim
        · subst h_eq_55; right; left; rfl
        · subst h_eq_95; right; right; right; right; right; right; right; left; rfl
        · subst h_eq_103; exact (sgn_not_minus_103 h_sgn).elim
        · subst h_eq_105; exact (sgn_not_minus_105 h_sgn).elim
        · subst h_eq_109; exact (sgn_not_minus_109 h_sgn).elim
        -- 21. A(n+1) = 21 -> n+1 in [53, 55, 95, 103, 105, 109]
        intro h_eq_21; have : A130911 n = 22 := by omega
        have hn_or := h_ih_23 this
        rcases hn_or with h_eq_54|h_eq_104|h_eq_106|h_eq_108|h_eq_110
        · subst h_eq_54; right; left; rfl
        · subst h_eq_104; right; right; right; right; left; rfl
        · subst h_eq_106; exact (sgn_not_minus_106 h_sgn).elim
        · subst h_eq_108; right; right; right; right; right; rfl
        · subst h_eq_110; exact (sgn_not_minus_110 h_sgn).elim
        -- 22. A(n+1) = 22 -> n+1 in [54, 104, 106, 108, 110]
        intro h_eq_22; have : A130911 n = 23 := by omega
        have hn_or := h_ih_24 this
        rcases hn_or with h_eq_107|h_eq_111
        · subst h_eq_107; right; right; right; left; rfl
        · subst h_eq_111; exact (sgn_not_minus_111 h_sgn).elim
        -- 23. A(n+1) = 23 -> n+1 in [107, 111]
        intro h_eq_23; have : A130911 n = 24 := by omega
        have hn_or := h_ih_25 this
        rcases hn_or with h_eq_112|h_eq_114
        · subst h_eq_112; exact (sgn_not_minus_112 h_sgn).elim
        · subst h_eq_114; exact (sgn_not_minus_114 h_sgn).elim
        -- 24. A(n+1) = 24 -> n+1 in [112, 114]
        intro h_eq_24; have : A130911 n = 25 := by omega
        have hn_or := h_ih_26 this
        rcases hn_or with h_eq_113|h_eq_115|h_eq_117
        · subst h_eq_113; right; rfl
        · subst h_eq_115; exact (sgn_not_minus_115 h_sgn).elim
        · subst h_eq_117; exact (sgn_not_minus_117 h_sgn).elim
        -- 25. A(n+1) = 25 -> n+1 in [113, 115, 117]
        intro h_eq_25; have : A130911 n = 26 := by omega
        have hn_or := h_ih_27 this
        rcases hn_or with h_eq_116|h_eq_118
        · subst h_eq_116; right; right; rfl
        · subst h_eq_118; exact (sgn_not_minus_118 h_sgn).elim
        -- 26. A(n+1) = 26 -> n+1 in [116, 118]
        intro h_eq_26; have : A130911 n = 27 := by omega
        have hn_or := h_ih_28 this
        have h_eq := hn_or
        · subst h_eq; exact (sgn_not_minus_119 h_sgn).elim
        -- 27. A(n+1) = 27 -> n+1 in [119]
        intro h_eq_27; have : A130911 n = 28 := by omega
        have hn_or := h_ih_29 this
        have h_eq := hn_or
        · subst h_eq; exact (sgn_not_minus_120 h_sgn).elim
