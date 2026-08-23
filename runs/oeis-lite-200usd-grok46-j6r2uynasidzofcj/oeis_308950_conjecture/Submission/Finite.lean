import FormalConjectures.Util.ProblemImports
open Nat
set_option maxHeartbeats 80000000

def SunGood (n : ℕ) : Prop :=
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
  ∨
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))

lemma g2 : SunGood 2 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g3 : SunGood 3 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g4 : SunGood 4 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g5 : SunGood 5 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g6 : SunGood 6 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g7 : SunGood 7 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g8 : SunGood 8 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g9 : SunGood 9 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g10 : SunGood 10 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g11 : SunGood 11 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g12 : SunGood 12 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g13 : SunGood 13 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g14 : SunGood 14 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g15 : SunGood 15 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g16 : SunGood 16 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g17 : SunGood 17 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g18 : SunGood 18 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g19 : SunGood 19 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g20 : SunGood 20 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g21 : SunGood 21 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g22 : SunGood 22 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g23 : SunGood 23 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g24 : SunGood 24 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g25 : SunGood 25 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g26 : SunGood 26 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g27 : SunGood 27 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g28 : SunGood 28 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g29 : SunGood 29 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g30 : SunGood 30 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g31 : SunGood 31 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g32 : SunGood 32 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g33 : SunGood 33 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g34 : SunGood 34 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g35 : SunGood 35 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g36 : SunGood 36 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g37 : SunGood 37 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g38 : SunGood 38 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g39 : SunGood 39 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g40 : SunGood 40 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g41 : SunGood 41 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g42 : SunGood 42 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g43 : SunGood 43 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g44 : SunGood 44 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g45 : SunGood 45 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g46 : SunGood 46 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g47 : SunGood 47 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g48 : SunGood 48 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g49 : SunGood 49 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g50 : SunGood 50 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g51 : SunGood 51 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g52 : SunGood 52 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g53 : SunGood 53 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g54 : SunGood 54 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g55 : SunGood 55 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g56 : SunGood 56 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g57 : SunGood 57 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g58 : SunGood 58 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g59 : SunGood 59 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g60 : SunGood 60 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g61 : SunGood 61 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g62 : SunGood 62 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g63 : SunGood 63 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g64 : SunGood 64 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g65 : SunGood 65 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g66 : SunGood 66 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g67 : SunGood 67 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g68 : SunGood 68 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g69 : SunGood 69 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g70 : SunGood 70 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g71 : SunGood 71 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g72 : SunGood 72 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g73 : SunGood 73 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g74 : SunGood 74 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g75 : SunGood 75 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g76 : SunGood 76 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g77 : SunGood 77 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g78 : SunGood 78 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g79 : SunGood 79 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g80 : SunGood 80 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g81 : SunGood 81 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g82 : SunGood 82 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g83 : SunGood 83 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g84 : SunGood 84 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g85 : SunGood 85 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g86 : SunGood 86 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g87 : SunGood 87 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g88 : SunGood 88 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g89 : SunGood 89 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g90 : SunGood 90 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g91 : SunGood 91 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g92 : SunGood 92 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g93 : SunGood 93 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g94 : SunGood 94 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g95 : SunGood 95 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g96 : SunGood 96 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g97 : SunGood 97 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g98 : SunGood 98 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g99 : SunGood 99 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g100 : SunGood 100 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g101 : SunGood 101 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g102 : SunGood 102 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g103 : SunGood 103 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g104 : SunGood 104 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g105 : SunGood 105 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g106 : SunGood 106 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g107 : SunGood 107 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g108 : SunGood 108 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g109 : SunGood 109 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g110 : SunGood 110 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g111 : SunGood 111 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g112 : SunGood 112 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g113 : SunGood 113 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g114 : SunGood 114 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g115 : SunGood 115 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g116 : SunGood 116 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g117 : SunGood 117 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g118 : SunGood 118 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g119 : SunGood 119 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g120 : SunGood 120 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g121 : SunGood 121 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g122 : SunGood 122 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g123 : SunGood 123 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g124 : SunGood 124 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g125 : SunGood 125 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g126 : SunGood 126 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g127 : SunGood 127 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g128 : SunGood 128 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g129 : SunGood 129 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g130 : SunGood 130 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g131 : SunGood 131 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g132 : SunGood 132 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g133 : SunGood 133 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g134 : SunGood 134 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g135 : SunGood 135 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g136 : SunGood 136 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g137 : SunGood 137 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g138 : SunGood 138 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g139 : SunGood 139 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g140 : SunGood 140 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g141 : SunGood 141 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g142 : SunGood 142 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g143 : SunGood 143 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g144 : SunGood 144 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g145 : SunGood 145 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g146 : SunGood 146 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g147 : SunGood 147 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g148 : SunGood 148 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g149 : SunGood 149 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g150 : SunGood 150 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g151 : SunGood 151 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g152 : SunGood 152 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g153 : SunGood 153 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g154 : SunGood 154 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g155 : SunGood 155 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g156 : SunGood 156 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g157 : SunGood 157 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g158 : SunGood 158 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g159 : SunGood 159 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g160 : SunGood 160 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g161 : SunGood 161 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g162 : SunGood 162 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g163 : SunGood 163 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g164 : SunGood 164 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g165 : SunGood 165 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g166 : SunGood 166 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g167 : SunGood 167 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g168 : SunGood 168 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g169 : SunGood 169 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g170 : SunGood 170 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g171 : SunGood 171 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g172 : SunGood 172 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g173 : SunGood 173 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g174 : SunGood 174 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g175 : SunGood 175 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g176 : SunGood 176 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g177 : SunGood 177 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g178 : SunGood 178 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g179 : SunGood 179 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g180 : SunGood 180 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g181 : SunGood 181 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g182 : SunGood 182 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g183 : SunGood 183 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g184 : SunGood 184 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g185 : SunGood 185 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g186 : SunGood 186 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g187 : SunGood 187 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g188 : SunGood 188 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g189 : SunGood 189 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g190 : SunGood 190 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g191 : SunGood 191 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g192 : SunGood 192 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g193 : SunGood 193 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g194 : SunGood 194 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g195 : SunGood 195 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g196 : SunGood 196 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g197 : SunGood 197 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g198 : SunGood 198 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g199 : SunGood 199 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g200 : SunGood 200 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g201 : SunGood 201 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g202 : SunGood 202 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g203 : SunGood 203 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g204 : SunGood 204 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g205 : SunGood 205 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g206 : SunGood 206 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g207 : SunGood 207 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g208 : SunGood 208 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g209 : SunGood 209 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g210 : SunGood 210 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g211 : SunGood 211 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g212 : SunGood 212 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g213 : SunGood 213 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g214 : SunGood 214 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g215 : SunGood 215 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g216 : SunGood 216 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g217 : SunGood 217 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g218 : SunGood 218 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g219 : SunGood 219 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g220 : SunGood 220 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g221 : SunGood 221 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g222 : SunGood 222 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g223 : SunGood 223 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g224 : SunGood 224 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g225 : SunGood 225 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g226 : SunGood 226 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g227 : SunGood 227 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g228 : SunGood 228 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g229 : SunGood 229 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g230 : SunGood 230 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g231 : SunGood 231 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g232 : SunGood 232 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g233 : SunGood 233 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g234 : SunGood 234 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g235 : SunGood 235 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g236 : SunGood 236 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g237 : SunGood 237 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g238 : SunGood 238 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g239 : SunGood 239 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g240 : SunGood 240 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g241 : SunGood 241 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g242 : SunGood 242 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g243 : SunGood 243 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g244 : SunGood 244 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g245 : SunGood 245 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g246 : SunGood 246 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g247 : SunGood 247 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g248 : SunGood 248 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g249 : SunGood 249 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g250 : SunGood 250 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g251 : SunGood 251 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g252 : SunGood 252 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g253 : SunGood 253 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g254 : SunGood 254 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g255 : SunGood 255 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g256 : SunGood 256 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g257 : SunGood 257 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g258 : SunGood 258 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g259 : SunGood 259 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g260 : SunGood 260 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g261 : SunGood 261 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g262 : SunGood 262 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g263 : SunGood 263 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g264 : SunGood 264 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g265 : SunGood 265 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g266 : SunGood 266 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g267 : SunGood 267 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g268 : SunGood 268 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g269 : SunGood 269 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g270 : SunGood 270 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g271 : SunGood 271 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g272 : SunGood 272 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g273 : SunGood 273 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g274 : SunGood 274 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g275 : SunGood 275 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g276 : SunGood 276 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g277 : SunGood 277 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g278 : SunGood 278 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g279 : SunGood 279 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g280 : SunGood 280 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g281 : SunGood 281 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g282 : SunGood 282 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g283 : SunGood 283 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g284 : SunGood 284 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g285 : SunGood 285 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g286 : SunGood 286 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g287 : SunGood 287 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g288 : SunGood 288 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g289 : SunGood 289 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g290 : SunGood 290 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g291 : SunGood 291 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g292 : SunGood 292 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g293 : SunGood 293 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g294 : SunGood 294 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g295 : SunGood 295 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g296 : SunGood 296 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g297 : SunGood 297 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g298 : SunGood 298 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g299 : SunGood 299 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g300 : SunGood 300 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g301 : SunGood 301 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g302 : SunGood 302 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g303 : SunGood 303 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g304 : SunGood 304 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g305 : SunGood 305 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g306 : SunGood 306 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g307 : SunGood 307 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g308 : SunGood 308 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g309 : SunGood 309 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g310 : SunGood 310 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g311 : SunGood 311 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g312 : SunGood 312 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g313 : SunGood 313 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g314 : SunGood 314 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g315 : SunGood 315 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g316 : SunGood 316 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g317 : SunGood 317 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g318 : SunGood 318 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g319 : SunGood 319 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g320 : SunGood 320 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g321 : SunGood 321 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g322 : SunGood 322 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g323 : SunGood 323 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g324 : SunGood 324 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g325 : SunGood 325 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g326 : SunGood 326 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g327 : SunGood 327 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g328 : SunGood 328 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g329 : SunGood 329 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g330 : SunGood 330 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g331 : SunGood 331 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g332 : SunGood 332 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g333 : SunGood 333 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g334 : SunGood 334 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g335 : SunGood 335 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g336 : SunGood 336 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g337 : SunGood 337 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g338 : SunGood 338 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g339 : SunGood 339 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g340 : SunGood 340 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g341 : SunGood 341 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g342 : SunGood 342 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g343 : SunGood 343 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g344 : SunGood 344 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g345 : SunGood 345 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g346 : SunGood 346 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g347 : SunGood 347 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g348 : SunGood 348 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g349 : SunGood 349 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g350 : SunGood 350 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g351 : SunGood 351 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g352 : SunGood 352 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g353 : SunGood 353 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g354 : SunGood 354 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g355 : SunGood 355 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g356 : SunGood 356 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g357 : SunGood 357 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g358 : SunGood 358 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g359 : SunGood 359 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g360 : SunGood 360 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g361 : SunGood 361 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g362 : SunGood 362 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g363 : SunGood 363 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g364 : SunGood 364 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g365 : SunGood 365 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g366 : SunGood 366 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g367 : SunGood 367 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g368 : SunGood 368 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g369 : SunGood 369 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g370 : SunGood 370 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g371 : SunGood 371 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g372 : SunGood 372 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g373 : SunGood 373 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g374 : SunGood 374 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g375 : SunGood 375 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g376 : SunGood 376 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g377 : SunGood 377 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g378 : SunGood 378 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g379 : SunGood 379 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g380 : SunGood 380 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g381 : SunGood 381 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g382 : SunGood 382 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g383 : SunGood 383 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g384 : SunGood 384 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g385 : SunGood 385 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g386 : SunGood 386 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g387 : SunGood 387 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g388 : SunGood 388 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g389 : SunGood 389 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g390 : SunGood 390 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g391 : SunGood 391 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g392 : SunGood 392 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g393 : SunGood 393 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g394 : SunGood 394 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g395 : SunGood 395 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g396 : SunGood 396 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g397 : SunGood 397 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g398 : SunGood 398 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g399 : SunGood 399 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g400 : SunGood 400 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g401 : SunGood 401 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g402 : SunGood 402 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g403 : SunGood 403 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g404 : SunGood 404 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g405 : SunGood 405 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g406 : SunGood 406 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g407 : SunGood 407 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g408 : SunGood 408 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g409 : SunGood 409 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g410 : SunGood 410 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g411 : SunGood 411 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g412 : SunGood 412 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g413 : SunGood 413 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g414 : SunGood 414 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g415 : SunGood 415 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g416 : SunGood 416 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g417 : SunGood 417 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g418 : SunGood 418 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g419 : SunGood 419 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g420 : SunGood 420 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g421 : SunGood 421 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g422 : SunGood 422 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g423 : SunGood 423 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g424 : SunGood 424 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g425 : SunGood 425 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g426 : SunGood 426 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g427 : SunGood 427 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g428 : SunGood 428 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g429 : SunGood 429 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g430 : SunGood 430 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g431 : SunGood 431 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g432 : SunGood 432 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g433 : SunGood 433 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g434 : SunGood 434 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g435 : SunGood 435 := Or.inr ⟨5, 0, by norm_num, by norm_num⟩
lemma g436 : SunGood 436 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g437 : SunGood 437 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g438 : SunGood 438 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g439 : SunGood 439 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g440 : SunGood 440 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g441 : SunGood 441 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g442 : SunGood 442 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g443 : SunGood 443 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g444 : SunGood 444 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g445 : SunGood 445 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g446 : SunGood 446 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g447 : SunGood 447 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g448 : SunGood 448 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g449 : SunGood 449 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g450 : SunGood 450 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g451 : SunGood 451 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g452 : SunGood 452 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g453 : SunGood 453 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g454 : SunGood 454 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g455 : SunGood 455 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g456 : SunGood 456 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g457 : SunGood 457 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g458 : SunGood 458 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g459 : SunGood 459 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g460 : SunGood 460 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g461 : SunGood 461 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g462 : SunGood 462 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g463 : SunGood 463 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g464 : SunGood 464 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g465 : SunGood 465 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g466 : SunGood 466 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g467 : SunGood 467 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g468 : SunGood 468 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g469 : SunGood 469 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g470 : SunGood 470 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g471 : SunGood 471 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g472 : SunGood 472 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g473 : SunGood 473 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g474 : SunGood 474 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g475 : SunGood 475 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g476 : SunGood 476 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g477 : SunGood 477 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g478 : SunGood 478 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g479 : SunGood 479 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g480 : SunGood 480 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g481 : SunGood 481 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g482 : SunGood 482 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g483 : SunGood 483 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g484 : SunGood 484 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g485 : SunGood 485 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g486 : SunGood 486 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g487 : SunGood 487 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g488 : SunGood 488 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g489 : SunGood 489 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g490 : SunGood 490 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g491 : SunGood 491 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g492 : SunGood 492 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g493 : SunGood 493 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g494 : SunGood 494 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g495 : SunGood 495 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g496 : SunGood 496 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g497 : SunGood 497 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g498 : SunGood 498 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g499 : SunGood 499 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g500 : SunGood 500 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g501 : SunGood 501 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g502 : SunGood 502 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g503 : SunGood 503 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g504 : SunGood 504 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g505 : SunGood 505 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g506 : SunGood 506 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g507 : SunGood 507 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g508 : SunGood 508 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g509 : SunGood 509 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g510 : SunGood 510 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g511 : SunGood 511 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g512 : SunGood 512 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g513 : SunGood 513 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g514 : SunGood 514 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g515 : SunGood 515 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g516 : SunGood 516 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g517 : SunGood 517 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g518 : SunGood 518 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g519 : SunGood 519 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g520 : SunGood 520 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g521 : SunGood 521 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g522 : SunGood 522 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g523 : SunGood 523 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g524 : SunGood 524 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g525 : SunGood 525 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g526 : SunGood 526 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g527 : SunGood 527 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g528 : SunGood 528 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g529 : SunGood 529 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g530 : SunGood 530 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g531 : SunGood 531 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g532 : SunGood 532 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g533 : SunGood 533 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g534 : SunGood 534 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g535 : SunGood 535 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g536 : SunGood 536 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g537 : SunGood 537 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g538 : SunGood 538 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g539 : SunGood 539 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g540 : SunGood 540 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g541 : SunGood 541 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g542 : SunGood 542 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g543 : SunGood 543 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g544 : SunGood 544 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g545 : SunGood 545 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g546 : SunGood 546 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g547 : SunGood 547 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g548 : SunGood 548 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g549 : SunGood 549 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g550 : SunGood 550 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g551 : SunGood 551 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g552 : SunGood 552 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g553 : SunGood 553 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g554 : SunGood 554 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g555 : SunGood 555 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g556 : SunGood 556 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g557 : SunGood 557 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g558 : SunGood 558 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g559 : SunGood 559 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g560 : SunGood 560 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g561 : SunGood 561 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g562 : SunGood 562 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g563 : SunGood 563 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g564 : SunGood 564 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g565 : SunGood 565 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g566 : SunGood 566 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g567 : SunGood 567 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g568 : SunGood 568 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g569 : SunGood 569 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g570 : SunGood 570 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g571 : SunGood 571 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g572 : SunGood 572 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g573 : SunGood 573 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g574 : SunGood 574 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g575 : SunGood 575 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g576 : SunGood 576 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g577 : SunGood 577 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g578 : SunGood 578 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g579 : SunGood 579 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g580 : SunGood 580 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g581 : SunGood 581 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g582 : SunGood 582 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g583 : SunGood 583 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g584 : SunGood 584 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g585 : SunGood 585 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g586 : SunGood 586 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g587 : SunGood 587 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g588 : SunGood 588 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g589 : SunGood 589 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g590 : SunGood 590 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g591 : SunGood 591 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g592 : SunGood 592 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g593 : SunGood 593 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g594 : SunGood 594 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g595 : SunGood 595 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g596 : SunGood 596 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g597 : SunGood 597 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g598 : SunGood 598 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g599 : SunGood 599 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g600 : SunGood 600 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g601 : SunGood 601 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g602 : SunGood 602 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g603 : SunGood 603 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g604 : SunGood 604 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g605 : SunGood 605 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g606 : SunGood 606 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g607 : SunGood 607 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g608 : SunGood 608 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g609 : SunGood 609 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g610 : SunGood 610 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g611 : SunGood 611 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g612 : SunGood 612 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g613 : SunGood 613 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g614 : SunGood 614 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g615 : SunGood 615 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g616 : SunGood 616 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g617 : SunGood 617 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g618 : SunGood 618 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g619 : SunGood 619 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g620 : SunGood 620 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g621 : SunGood 621 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g622 : SunGood 622 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g623 : SunGood 623 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g624 : SunGood 624 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g625 : SunGood 625 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g626 : SunGood 626 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g627 : SunGood 627 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g628 : SunGood 628 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g629 : SunGood 629 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g630 : SunGood 630 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g631 : SunGood 631 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g632 : SunGood 632 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g633 : SunGood 633 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g634 : SunGood 634 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g635 : SunGood 635 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g636 : SunGood 636 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g637 : SunGood 637 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g638 : SunGood 638 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g639 : SunGood 639 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g640 : SunGood 640 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g641 : SunGood 641 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g642 : SunGood 642 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g643 : SunGood 643 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g644 : SunGood 644 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g645 : SunGood 645 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g646 : SunGood 646 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g647 : SunGood 647 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g648 : SunGood 648 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g649 : SunGood 649 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g650 : SunGood 650 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g651 : SunGood 651 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g652 : SunGood 652 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g653 : SunGood 653 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g654 : SunGood 654 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g655 : SunGood 655 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g656 : SunGood 656 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g657 : SunGood 657 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g658 : SunGood 658 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g659 : SunGood 659 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g660 : SunGood 660 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g661 : SunGood 661 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g662 : SunGood 662 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g663 : SunGood 663 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g664 : SunGood 664 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g665 : SunGood 665 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g666 : SunGood 666 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g667 : SunGood 667 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g668 : SunGood 668 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g669 : SunGood 669 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g670 : SunGood 670 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g671 : SunGood 671 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g672 : SunGood 672 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g673 : SunGood 673 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g674 : SunGood 674 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g675 : SunGood 675 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g676 : SunGood 676 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g677 : SunGood 677 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g678 : SunGood 678 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g679 : SunGood 679 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g680 : SunGood 680 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g681 : SunGood 681 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g682 : SunGood 682 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g683 : SunGood 683 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g684 : SunGood 684 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g685 : SunGood 685 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g686 : SunGood 686 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g687 : SunGood 687 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g688 : SunGood 688 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g689 : SunGood 689 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g690 : SunGood 690 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g691 : SunGood 691 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g692 : SunGood 692 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g693 : SunGood 693 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g694 : SunGood 694 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g695 : SunGood 695 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g696 : SunGood 696 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g697 : SunGood 697 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g698 : SunGood 698 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g699 : SunGood 699 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g700 : SunGood 700 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g701 : SunGood 701 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g702 : SunGood 702 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g703 : SunGood 703 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g704 : SunGood 704 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g705 : SunGood 705 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g706 : SunGood 706 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g707 : SunGood 707 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g708 : SunGood 708 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g709 : SunGood 709 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g710 : SunGood 710 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g711 : SunGood 711 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g712 : SunGood 712 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g713 : SunGood 713 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g714 : SunGood 714 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g715 : SunGood 715 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g716 : SunGood 716 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g717 : SunGood 717 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g718 : SunGood 718 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g719 : SunGood 719 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g720 : SunGood 720 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g721 : SunGood 721 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g722 : SunGood 722 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g723 : SunGood 723 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g724 : SunGood 724 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g725 : SunGood 725 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g726 : SunGood 726 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g727 : SunGood 727 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g728 : SunGood 728 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g729 : SunGood 729 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g730 : SunGood 730 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g731 : SunGood 731 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g732 : SunGood 732 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g733 : SunGood 733 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g734 : SunGood 734 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g735 : SunGood 735 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g736 : SunGood 736 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g737 : SunGood 737 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g738 : SunGood 738 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g739 : SunGood 739 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g740 : SunGood 740 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g741 : SunGood 741 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g742 : SunGood 742 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g743 : SunGood 743 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g744 : SunGood 744 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g745 : SunGood 745 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g746 : SunGood 746 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g747 : SunGood 747 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g748 : SunGood 748 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g749 : SunGood 749 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g750 : SunGood 750 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g751 : SunGood 751 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g752 : SunGood 752 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g753 : SunGood 753 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g754 : SunGood 754 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g755 : SunGood 755 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g756 : SunGood 756 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g757 : SunGood 757 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g758 : SunGood 758 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g759 : SunGood 759 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g760 : SunGood 760 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g761 : SunGood 761 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g762 : SunGood 762 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g763 : SunGood 763 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g764 : SunGood 764 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g765 : SunGood 765 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g766 : SunGood 766 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g767 : SunGood 767 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g768 : SunGood 768 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g769 : SunGood 769 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g770 : SunGood 770 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g771 : SunGood 771 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g772 : SunGood 772 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g773 : SunGood 773 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g774 : SunGood 774 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g775 : SunGood 775 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g776 : SunGood 776 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g777 : SunGood 777 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g778 : SunGood 778 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g779 : SunGood 779 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g780 : SunGood 780 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g781 : SunGood 781 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g782 : SunGood 782 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g783 : SunGood 783 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g784 : SunGood 784 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g785 : SunGood 785 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g786 : SunGood 786 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g787 : SunGood 787 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g788 : SunGood 788 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g789 : SunGood 789 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g790 : SunGood 790 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g791 : SunGood 791 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g792 : SunGood 792 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g793 : SunGood 793 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g794 : SunGood 794 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g795 : SunGood 795 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g796 : SunGood 796 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g797 : SunGood 797 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g798 : SunGood 798 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g799 : SunGood 799 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g800 : SunGood 800 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g801 : SunGood 801 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g802 : SunGood 802 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g803 : SunGood 803 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g804 : SunGood 804 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g805 : SunGood 805 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g806 : SunGood 806 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g807 : SunGood 807 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g808 : SunGood 808 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g809 : SunGood 809 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g810 : SunGood 810 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g811 : SunGood 811 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g812 : SunGood 812 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g813 : SunGood 813 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g814 : SunGood 814 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g815 : SunGood 815 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g816 : SunGood 816 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g817 : SunGood 817 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g818 : SunGood 818 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g819 : SunGood 819 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g820 : SunGood 820 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g821 : SunGood 821 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g822 : SunGood 822 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g823 : SunGood 823 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g824 : SunGood 824 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g825 : SunGood 825 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g826 : SunGood 826 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g827 : SunGood 827 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g828 : SunGood 828 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g829 : SunGood 829 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g830 : SunGood 830 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g831 : SunGood 831 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g832 : SunGood 832 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g833 : SunGood 833 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g834 : SunGood 834 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g835 : SunGood 835 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g836 : SunGood 836 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g837 : SunGood 837 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g838 : SunGood 838 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g839 : SunGood 839 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g840 : SunGood 840 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g841 : SunGood 841 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g842 : SunGood 842 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g843 : SunGood 843 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g844 : SunGood 844 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g845 : SunGood 845 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g846 : SunGood 846 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g847 : SunGood 847 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g848 : SunGood 848 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g849 : SunGood 849 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g850 : SunGood 850 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g851 : SunGood 851 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g852 : SunGood 852 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g853 : SunGood 853 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g854 : SunGood 854 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g855 : SunGood 855 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g856 : SunGood 856 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g857 : SunGood 857 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g858 : SunGood 858 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g859 : SunGood 859 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g860 : SunGood 860 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g861 : SunGood 861 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g862 : SunGood 862 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g863 : SunGood 863 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g864 : SunGood 864 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g865 : SunGood 865 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g866 : SunGood 866 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g867 : SunGood 867 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g868 : SunGood 868 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g869 : SunGood 869 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g870 : SunGood 870 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g871 : SunGood 871 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g872 : SunGood 872 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g873 : SunGood 873 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g874 : SunGood 874 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g875 : SunGood 875 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g876 : SunGood 876 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g877 : SunGood 877 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g878 : SunGood 878 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g879 : SunGood 879 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g880 : SunGood 880 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g881 : SunGood 881 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g882 : SunGood 882 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g883 : SunGood 883 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g884 : SunGood 884 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g885 : SunGood 885 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g886 : SunGood 886 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g887 : SunGood 887 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g888 : SunGood 888 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g889 : SunGood 889 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g890 : SunGood 890 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g891 : SunGood 891 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g892 : SunGood 892 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g893 : SunGood 893 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g894 : SunGood 894 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g895 : SunGood 895 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g896 : SunGood 896 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g897 : SunGood 897 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g898 : SunGood 898 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g899 : SunGood 899 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g900 : SunGood 900 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g901 : SunGood 901 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g902 : SunGood 902 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g903 : SunGood 903 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g904 : SunGood 904 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g905 : SunGood 905 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g906 : SunGood 906 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g907 : SunGood 907 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g908 : SunGood 908 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g909 : SunGood 909 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g910 : SunGood 910 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g911 : SunGood 911 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g912 : SunGood 912 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g913 : SunGood 913 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g914 : SunGood 914 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g915 : SunGood 915 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g916 : SunGood 916 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g917 : SunGood 917 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g918 : SunGood 918 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g919 : SunGood 919 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g920 : SunGood 920 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g921 : SunGood 921 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g922 : SunGood 922 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g923 : SunGood 923 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g924 : SunGood 924 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g925 : SunGood 925 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g926 : SunGood 926 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g927 : SunGood 927 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g928 : SunGood 928 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g929 : SunGood 929 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g930 : SunGood 930 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g931 : SunGood 931 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g932 : SunGood 932 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g933 : SunGood 933 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g934 : SunGood 934 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g935 : SunGood 935 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g936 : SunGood 936 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g937 : SunGood 937 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g938 : SunGood 938 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g939 : SunGood 939 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g940 : SunGood 940 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g941 : SunGood 941 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g942 : SunGood 942 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g943 : SunGood 943 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g944 : SunGood 944 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g945 : SunGood 945 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g946 : SunGood 946 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g947 : SunGood 947 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g948 : SunGood 948 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g949 : SunGood 949 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g950 : SunGood 950 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g951 : SunGood 951 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g952 : SunGood 952 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g953 : SunGood 953 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g954 : SunGood 954 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g955 : SunGood 955 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g956 : SunGood 956 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g957 : SunGood 957 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g958 : SunGood 958 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g959 : SunGood 959 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g960 : SunGood 960 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g961 : SunGood 961 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g962 : SunGood 962 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g963 : SunGood 963 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g964 : SunGood 964 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g965 : SunGood 965 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g966 : SunGood 966 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g967 : SunGood 967 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g968 : SunGood 968 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g969 : SunGood 969 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g970 : SunGood 970 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g971 : SunGood 971 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g972 : SunGood 972 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g973 : SunGood 973 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g974 : SunGood 974 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g975 : SunGood 975 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g976 : SunGood 976 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g977 : SunGood 977 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g978 : SunGood 978 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g979 : SunGood 979 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g980 : SunGood 980 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g981 : SunGood 981 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g982 : SunGood 982 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g983 : SunGood 983 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g984 : SunGood 984 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g985 : SunGood 985 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g986 : SunGood 986 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g987 : SunGood 987 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g988 : SunGood 988 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g989 : SunGood 989 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g990 : SunGood 990 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g991 : SunGood 991 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g992 : SunGood 992 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g993 : SunGood 993 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g994 : SunGood 994 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g995 : SunGood 995 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g996 : SunGood 996 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g997 : SunGood 997 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g998 : SunGood 998 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g999 : SunGood 999 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1000 : SunGood 1000 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1001 : SunGood 1001 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1002 : SunGood 1002 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1003 : SunGood 1003 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1004 : SunGood 1004 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1005 : SunGood 1005 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1006 : SunGood 1006 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1007 : SunGood 1007 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1008 : SunGood 1008 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1009 : SunGood 1009 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1010 : SunGood 1010 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1011 : SunGood 1011 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1012 : SunGood 1012 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1013 : SunGood 1013 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1014 : SunGood 1014 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1015 : SunGood 1015 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1016 : SunGood 1016 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1017 : SunGood 1017 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1018 : SunGood 1018 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1019 : SunGood 1019 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1020 : SunGood 1020 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1021 : SunGood 1021 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1022 : SunGood 1022 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1023 : SunGood 1023 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1024 : SunGood 1024 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1025 : SunGood 1025 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1026 : SunGood 1026 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1027 : SunGood 1027 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1028 : SunGood 1028 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1029 : SunGood 1029 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1030 : SunGood 1030 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1031 : SunGood 1031 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1032 : SunGood 1032 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1033 : SunGood 1033 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1034 : SunGood 1034 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1035 : SunGood 1035 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1036 : SunGood 1036 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1037 : SunGood 1037 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1038 : SunGood 1038 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1039 : SunGood 1039 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1040 : SunGood 1040 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1041 : SunGood 1041 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1042 : SunGood 1042 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1043 : SunGood 1043 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1044 : SunGood 1044 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1045 : SunGood 1045 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1046 : SunGood 1046 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1047 : SunGood 1047 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1048 : SunGood 1048 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1049 : SunGood 1049 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1050 : SunGood 1050 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1051 : SunGood 1051 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1052 : SunGood 1052 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1053 : SunGood 1053 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1054 : SunGood 1054 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1055 : SunGood 1055 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1056 : SunGood 1056 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1057 : SunGood 1057 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1058 : SunGood 1058 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1059 : SunGood 1059 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1060 : SunGood 1060 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1061 : SunGood 1061 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1062 : SunGood 1062 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1063 : SunGood 1063 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1064 : SunGood 1064 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1065 : SunGood 1065 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1066 : SunGood 1066 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1067 : SunGood 1067 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1068 : SunGood 1068 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1069 : SunGood 1069 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1070 : SunGood 1070 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1071 : SunGood 1071 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1072 : SunGood 1072 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1073 : SunGood 1073 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1074 : SunGood 1074 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1075 : SunGood 1075 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1076 : SunGood 1076 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1077 : SunGood 1077 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1078 : SunGood 1078 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1079 : SunGood 1079 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1080 : SunGood 1080 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1081 : SunGood 1081 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1082 : SunGood 1082 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1083 : SunGood 1083 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1084 : SunGood 1084 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1085 : SunGood 1085 := Or.inr ⟨5, 0, by norm_num, by norm_num⟩
lemma g1086 : SunGood 1086 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1087 : SunGood 1087 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1088 : SunGood 1088 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1089 : SunGood 1089 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1090 : SunGood 1090 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1091 : SunGood 1091 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1092 : SunGood 1092 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1093 : SunGood 1093 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1094 : SunGood 1094 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1095 : SunGood 1095 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1096 : SunGood 1096 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1097 : SunGood 1097 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1098 : SunGood 1098 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1099 : SunGood 1099 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1100 : SunGood 1100 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1101 : SunGood 1101 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1102 : SunGood 1102 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1103 : SunGood 1103 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1104 : SunGood 1104 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1105 : SunGood 1105 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1106 : SunGood 1106 := Or.inl ⟨7, 0, by norm_num, by norm_num⟩
lemma g1107 : SunGood 1107 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1108 : SunGood 1108 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1109 : SunGood 1109 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1110 : SunGood 1110 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1111 : SunGood 1111 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1112 : SunGood 1112 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1113 : SunGood 1113 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1114 : SunGood 1114 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1115 : SunGood 1115 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1116 : SunGood 1116 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1117 : SunGood 1117 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1118 : SunGood 1118 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1119 : SunGood 1119 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1120 : SunGood 1120 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1121 : SunGood 1121 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1122 : SunGood 1122 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1123 : SunGood 1123 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1124 : SunGood 1124 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1125 : SunGood 1125 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1126 : SunGood 1126 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1127 : SunGood 1127 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1128 : SunGood 1128 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1129 : SunGood 1129 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1130 : SunGood 1130 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1131 : SunGood 1131 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1132 : SunGood 1132 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1133 : SunGood 1133 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1134 : SunGood 1134 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1135 : SunGood 1135 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1136 : SunGood 1136 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1137 : SunGood 1137 := Or.inr ⟨7, 0, by norm_num, by norm_num⟩
lemma g1138 : SunGood 1138 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1139 : SunGood 1139 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1140 : SunGood 1140 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1141 : SunGood 1141 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1142 : SunGood 1142 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1143 : SunGood 1143 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1144 : SunGood 1144 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1145 : SunGood 1145 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1146 : SunGood 1146 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1147 : SunGood 1147 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1148 : SunGood 1148 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1149 : SunGood 1149 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1150 : SunGood 1150 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1151 : SunGood 1151 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1152 : SunGood 1152 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1153 : SunGood 1153 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1154 : SunGood 1154 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1155 : SunGood 1155 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1156 : SunGood 1156 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1157 : SunGood 1157 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1158 : SunGood 1158 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1159 : SunGood 1159 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1160 : SunGood 1160 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1161 : SunGood 1161 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1162 : SunGood 1162 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1163 : SunGood 1163 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1164 : SunGood 1164 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1165 : SunGood 1165 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1166 : SunGood 1166 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1167 : SunGood 1167 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1168 : SunGood 1168 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1169 : SunGood 1169 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1170 : SunGood 1170 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1171 : SunGood 1171 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1172 : SunGood 1172 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1173 : SunGood 1173 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1174 : SunGood 1174 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1175 : SunGood 1175 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1176 : SunGood 1176 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1177 : SunGood 1177 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1178 : SunGood 1178 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1179 : SunGood 1179 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1180 : SunGood 1180 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1181 : SunGood 1181 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1182 : SunGood 1182 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1183 : SunGood 1183 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1184 : SunGood 1184 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1185 : SunGood 1185 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1186 : SunGood 1186 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1187 : SunGood 1187 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1188 : SunGood 1188 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1189 : SunGood 1189 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1190 : SunGood 1190 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1191 : SunGood 1191 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1192 : SunGood 1192 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1193 : SunGood 1193 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1194 : SunGood 1194 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1195 : SunGood 1195 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1196 : SunGood 1196 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1197 : SunGood 1197 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1198 : SunGood 1198 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1199 : SunGood 1199 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1200 : SunGood 1200 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1201 : SunGood 1201 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1202 : SunGood 1202 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1203 : SunGood 1203 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1204 : SunGood 1204 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1205 : SunGood 1205 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1206 : SunGood 1206 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1207 : SunGood 1207 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1208 : SunGood 1208 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1209 : SunGood 1209 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1210 : SunGood 1210 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1211 : SunGood 1211 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1212 : SunGood 1212 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1213 : SunGood 1213 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1214 : SunGood 1214 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1215 : SunGood 1215 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1216 : SunGood 1216 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1217 : SunGood 1217 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1218 : SunGood 1218 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1219 : SunGood 1219 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1220 : SunGood 1220 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1221 : SunGood 1221 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1222 : SunGood 1222 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1223 : SunGood 1223 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1224 : SunGood 1224 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1225 : SunGood 1225 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1226 : SunGood 1226 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1227 : SunGood 1227 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1228 : SunGood 1228 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1229 : SunGood 1229 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1230 : SunGood 1230 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1231 : SunGood 1231 := Or.inr ⟨5, 0, by norm_num, by norm_num⟩
lemma g1232 : SunGood 1232 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1233 : SunGood 1233 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1234 : SunGood 1234 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1235 : SunGood 1235 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g1236 : SunGood 1236 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1237 : SunGood 1237 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1238 : SunGood 1238 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1239 : SunGood 1239 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1240 : SunGood 1240 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1241 : SunGood 1241 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1242 : SunGood 1242 := Or.inl ⟨6, 0, by norm_num, by norm_num⟩
lemma g1243 : SunGood 1243 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1244 : SunGood 1244 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1245 : SunGood 1245 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1246 : SunGood 1246 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1247 : SunGood 1247 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1248 : SunGood 1248 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1249 : SunGood 1249 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1250 : SunGood 1250 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1251 : SunGood 1251 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1252 : SunGood 1252 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1253 : SunGood 1253 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1254 : SunGood 1254 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1255 : SunGood 1255 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1256 : SunGood 1256 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1257 : SunGood 1257 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1258 : SunGood 1258 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1259 : SunGood 1259 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1260 : SunGood 1260 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1261 : SunGood 1261 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1262 : SunGood 1262 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1263 : SunGood 1263 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1264 : SunGood 1264 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1265 : SunGood 1265 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1266 : SunGood 1266 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1267 : SunGood 1267 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1268 : SunGood 1268 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1269 : SunGood 1269 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1270 : SunGood 1270 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1271 : SunGood 1271 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1272 : SunGood 1272 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1273 : SunGood 1273 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1274 : SunGood 1274 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1275 : SunGood 1275 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1276 : SunGood 1276 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1277 : SunGood 1277 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1278 : SunGood 1278 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1279 : SunGood 1279 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1280 : SunGood 1280 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1281 : SunGood 1281 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1282 : SunGood 1282 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1283 : SunGood 1283 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1284 : SunGood 1284 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1285 : SunGood 1285 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1286 : SunGood 1286 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1287 : SunGood 1287 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1288 : SunGood 1288 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1289 : SunGood 1289 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1290 : SunGood 1290 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1291 : SunGood 1291 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1292 : SunGood 1292 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1293 : SunGood 1293 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1294 : SunGood 1294 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1295 : SunGood 1295 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1296 : SunGood 1296 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1297 : SunGood 1297 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1298 : SunGood 1298 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1299 : SunGood 1299 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1300 : SunGood 1300 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1301 : SunGood 1301 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1302 : SunGood 1302 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1303 : SunGood 1303 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1304 : SunGood 1304 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1305 : SunGood 1305 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1306 : SunGood 1306 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1307 : SunGood 1307 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1308 : SunGood 1308 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1309 : SunGood 1309 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1310 : SunGood 1310 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1311 : SunGood 1311 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1312 : SunGood 1312 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1313 : SunGood 1313 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1314 : SunGood 1314 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1315 : SunGood 1315 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1316 : SunGood 1316 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1317 : SunGood 1317 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1318 : SunGood 1318 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1319 : SunGood 1319 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1320 : SunGood 1320 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1321 : SunGood 1321 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1322 : SunGood 1322 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1323 : SunGood 1323 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1324 : SunGood 1324 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1325 : SunGood 1325 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1326 : SunGood 1326 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1327 : SunGood 1327 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1328 : SunGood 1328 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1329 : SunGood 1329 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1330 : SunGood 1330 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1331 : SunGood 1331 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1332 : SunGood 1332 := Or.inr ⟨6, 0, by norm_num, by norm_num⟩
lemma g1333 : SunGood 1333 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1334 : SunGood 1334 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1335 : SunGood 1335 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1336 : SunGood 1336 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1337 : SunGood 1337 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1338 : SunGood 1338 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1339 : SunGood 1339 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1340 : SunGood 1340 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1341 : SunGood 1341 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1342 : SunGood 1342 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1343 : SunGood 1343 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1344 : SunGood 1344 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1345 : SunGood 1345 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1346 : SunGood 1346 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1347 : SunGood 1347 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1348 : SunGood 1348 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1349 : SunGood 1349 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1350 : SunGood 1350 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1351 : SunGood 1351 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1352 : SunGood 1352 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1353 : SunGood 1353 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1354 : SunGood 1354 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1355 : SunGood 1355 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1356 : SunGood 1356 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1357 : SunGood 1357 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1358 : SunGood 1358 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1359 : SunGood 1359 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1360 : SunGood 1360 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1361 : SunGood 1361 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1362 : SunGood 1362 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1363 : SunGood 1363 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1364 : SunGood 1364 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1365 : SunGood 1365 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1366 : SunGood 1366 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1367 : SunGood 1367 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1368 : SunGood 1368 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1369 : SunGood 1369 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1370 : SunGood 1370 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1371 : SunGood 1371 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1372 : SunGood 1372 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1373 : SunGood 1373 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1374 : SunGood 1374 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1375 : SunGood 1375 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1376 : SunGood 1376 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1377 : SunGood 1377 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1378 : SunGood 1378 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1379 : SunGood 1379 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1380 : SunGood 1380 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1381 : SunGood 1381 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1382 : SunGood 1382 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1383 : SunGood 1383 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1384 : SunGood 1384 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1385 : SunGood 1385 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1386 : SunGood 1386 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1387 : SunGood 1387 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1388 : SunGood 1388 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1389 : SunGood 1389 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1390 : SunGood 1390 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1391 : SunGood 1391 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1392 : SunGood 1392 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1393 : SunGood 1393 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1394 : SunGood 1394 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1395 : SunGood 1395 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1396 : SunGood 1396 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1397 : SunGood 1397 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1398 : SunGood 1398 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1399 : SunGood 1399 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1400 : SunGood 1400 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1401 : SunGood 1401 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g1402 : SunGood 1402 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1403 : SunGood 1403 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1404 : SunGood 1404 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1405 : SunGood 1405 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1406 : SunGood 1406 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1407 : SunGood 1407 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1408 : SunGood 1408 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1409 : SunGood 1409 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1410 : SunGood 1410 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1411 : SunGood 1411 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1412 : SunGood 1412 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1413 : SunGood 1413 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1414 : SunGood 1414 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1415 : SunGood 1415 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1416 : SunGood 1416 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1417 : SunGood 1417 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g1418 : SunGood 1418 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1419 : SunGood 1419 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1420 : SunGood 1420 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1421 : SunGood 1421 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1422 : SunGood 1422 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1423 : SunGood 1423 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1424 : SunGood 1424 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1425 : SunGood 1425 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1426 : SunGood 1426 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1427 : SunGood 1427 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1428 : SunGood 1428 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1429 : SunGood 1429 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1430 : SunGood 1430 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1431 : SunGood 1431 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1432 : SunGood 1432 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1433 : SunGood 1433 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1434 : SunGood 1434 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1435 : SunGood 1435 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1436 : SunGood 1436 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1437 : SunGood 1437 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1438 : SunGood 1438 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1439 : SunGood 1439 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1440 : SunGood 1440 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1441 : SunGood 1441 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1442 : SunGood 1442 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1443 : SunGood 1443 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1444 : SunGood 1444 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1445 : SunGood 1445 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1446 : SunGood 1446 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1447 : SunGood 1447 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1448 : SunGood 1448 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1449 : SunGood 1449 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1450 : SunGood 1450 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1451 : SunGood 1451 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1452 : SunGood 1452 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1453 : SunGood 1453 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1454 : SunGood 1454 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1455 : SunGood 1455 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1456 : SunGood 1456 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1457 : SunGood 1457 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1458 : SunGood 1458 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1459 : SunGood 1459 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1460 : SunGood 1460 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1461 : SunGood 1461 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1462 : SunGood 1462 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1463 : SunGood 1463 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1464 : SunGood 1464 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1465 : SunGood 1465 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1466 : SunGood 1466 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1467 : SunGood 1467 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1468 : SunGood 1468 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1469 : SunGood 1469 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1470 : SunGood 1470 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1471 : SunGood 1471 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1472 : SunGood 1472 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1473 : SunGood 1473 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1474 : SunGood 1474 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1475 : SunGood 1475 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1476 : SunGood 1476 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1477 : SunGood 1477 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1478 : SunGood 1478 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1479 : SunGood 1479 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1480 : SunGood 1480 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1481 : SunGood 1481 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1482 : SunGood 1482 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1483 : SunGood 1483 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1484 : SunGood 1484 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1485 : SunGood 1485 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1486 : SunGood 1486 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1487 : SunGood 1487 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g1488 : SunGood 1488 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1489 : SunGood 1489 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1490 : SunGood 1490 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1491 : SunGood 1491 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1492 : SunGood 1492 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1493 : SunGood 1493 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1494 : SunGood 1494 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1495 : SunGood 1495 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1496 : SunGood 1496 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1497 : SunGood 1497 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1498 : SunGood 1498 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1499 : SunGood 1499 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1500 : SunGood 1500 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1501 : SunGood 1501 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1502 : SunGood 1502 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1503 : SunGood 1503 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1504 : SunGood 1504 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1505 : SunGood 1505 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1506 : SunGood 1506 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1507 : SunGood 1507 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1508 : SunGood 1508 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1509 : SunGood 1509 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1510 : SunGood 1510 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1511 : SunGood 1511 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1512 : SunGood 1512 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1513 : SunGood 1513 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1514 : SunGood 1514 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1515 : SunGood 1515 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1516 : SunGood 1516 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1517 : SunGood 1517 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1518 : SunGood 1518 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1519 : SunGood 1519 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1520 : SunGood 1520 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1521 : SunGood 1521 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1522 : SunGood 1522 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1523 : SunGood 1523 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1524 : SunGood 1524 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1525 : SunGood 1525 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1526 : SunGood 1526 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1527 : SunGood 1527 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1528 : SunGood 1528 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1529 : SunGood 1529 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1530 : SunGood 1530 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1531 : SunGood 1531 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1532 : SunGood 1532 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1533 : SunGood 1533 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1534 : SunGood 1534 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1535 : SunGood 1535 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1536 : SunGood 1536 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1537 : SunGood 1537 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1538 : SunGood 1538 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1539 : SunGood 1539 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1540 : SunGood 1540 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1541 : SunGood 1541 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1542 : SunGood 1542 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1543 : SunGood 1543 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1544 : SunGood 1544 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1545 : SunGood 1545 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1546 : SunGood 1546 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1547 : SunGood 1547 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1548 : SunGood 1548 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1549 : SunGood 1549 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1550 : SunGood 1550 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1551 : SunGood 1551 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1552 : SunGood 1552 := Or.inl ⟨6, 0, by norm_num, by norm_num⟩
lemma g1553 : SunGood 1553 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1554 : SunGood 1554 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1555 : SunGood 1555 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1556 : SunGood 1556 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1557 : SunGood 1557 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1558 : SunGood 1558 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1559 : SunGood 1559 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1560 : SunGood 1560 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1561 : SunGood 1561 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1562 : SunGood 1562 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1563 : SunGood 1563 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1564 : SunGood 1564 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1565 : SunGood 1565 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1566 : SunGood 1566 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1567 : SunGood 1567 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1568 : SunGood 1568 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1569 : SunGood 1569 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1570 : SunGood 1570 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1571 : SunGood 1571 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1572 : SunGood 1572 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1573 : SunGood 1573 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1574 : SunGood 1574 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1575 : SunGood 1575 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1576 : SunGood 1576 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1577 : SunGood 1577 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1578 : SunGood 1578 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1579 : SunGood 1579 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1580 : SunGood 1580 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1581 : SunGood 1581 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1582 : SunGood 1582 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1583 : SunGood 1583 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1584 : SunGood 1584 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1585 : SunGood 1585 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1586 : SunGood 1586 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1587 : SunGood 1587 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1588 : SunGood 1588 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1589 : SunGood 1589 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1590 : SunGood 1590 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1591 : SunGood 1591 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1592 : SunGood 1592 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1593 : SunGood 1593 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1594 : SunGood 1594 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1595 : SunGood 1595 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1596 : SunGood 1596 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1597 : SunGood 1597 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1598 : SunGood 1598 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1599 : SunGood 1599 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1600 : SunGood 1600 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1601 : SunGood 1601 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1602 : SunGood 1602 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1603 : SunGood 1603 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1604 : SunGood 1604 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1605 : SunGood 1605 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1606 : SunGood 1606 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1607 : SunGood 1607 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1608 : SunGood 1608 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1609 : SunGood 1609 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1610 : SunGood 1610 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1611 : SunGood 1611 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1612 : SunGood 1612 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1613 : SunGood 1613 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1614 : SunGood 1614 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1615 : SunGood 1615 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1616 : SunGood 1616 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1617 : SunGood 1617 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1618 : SunGood 1618 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1619 : SunGood 1619 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1620 : SunGood 1620 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1621 : SunGood 1621 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1622 : SunGood 1622 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1623 : SunGood 1623 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1624 : SunGood 1624 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1625 : SunGood 1625 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1626 : SunGood 1626 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1627 : SunGood 1627 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1628 : SunGood 1628 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1629 : SunGood 1629 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1630 : SunGood 1630 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1631 : SunGood 1631 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1632 : SunGood 1632 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1633 : SunGood 1633 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1634 : SunGood 1634 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1635 : SunGood 1635 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1636 : SunGood 1636 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1637 : SunGood 1637 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1638 : SunGood 1638 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1639 : SunGood 1639 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1640 : SunGood 1640 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1641 : SunGood 1641 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1642 : SunGood 1642 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1643 : SunGood 1643 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1644 : SunGood 1644 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1645 : SunGood 1645 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1646 : SunGood 1646 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1647 : SunGood 1647 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1648 : SunGood 1648 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1649 : SunGood 1649 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1650 : SunGood 1650 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1651 : SunGood 1651 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1652 : SunGood 1652 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1653 : SunGood 1653 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1654 : SunGood 1654 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1655 : SunGood 1655 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1656 : SunGood 1656 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1657 : SunGood 1657 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1658 : SunGood 1658 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1659 : SunGood 1659 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1660 : SunGood 1660 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1661 : SunGood 1661 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1662 : SunGood 1662 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1663 : SunGood 1663 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1664 : SunGood 1664 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1665 : SunGood 1665 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1666 : SunGood 1666 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1667 : SunGood 1667 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g1668 : SunGood 1668 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g1669 : SunGood 1669 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1670 : SunGood 1670 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1671 : SunGood 1671 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g1672 : SunGood 1672 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1673 : SunGood 1673 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1674 : SunGood 1674 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1675 : SunGood 1675 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1676 : SunGood 1676 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1677 : SunGood 1677 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1678 : SunGood 1678 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1679 : SunGood 1679 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1680 : SunGood 1680 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1681 : SunGood 1681 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1682 : SunGood 1682 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1683 : SunGood 1683 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1684 : SunGood 1684 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1685 : SunGood 1685 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1686 : SunGood 1686 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1687 : SunGood 1687 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1688 : SunGood 1688 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1689 : SunGood 1689 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1690 : SunGood 1690 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1691 : SunGood 1691 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1692 : SunGood 1692 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1693 : SunGood 1693 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1694 : SunGood 1694 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1695 : SunGood 1695 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1696 : SunGood 1696 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1697 : SunGood 1697 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1698 : SunGood 1698 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1699 : SunGood 1699 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1700 : SunGood 1700 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1701 : SunGood 1701 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1702 : SunGood 1702 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1703 : SunGood 1703 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1704 : SunGood 1704 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1705 : SunGood 1705 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1706 : SunGood 1706 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1707 : SunGood 1707 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1708 : SunGood 1708 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1709 : SunGood 1709 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1710 : SunGood 1710 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1711 : SunGood 1711 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1712 : SunGood 1712 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1713 : SunGood 1713 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1714 : SunGood 1714 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1715 : SunGood 1715 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1716 : SunGood 1716 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1717 : SunGood 1717 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1718 : SunGood 1718 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1719 : SunGood 1719 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1720 : SunGood 1720 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1721 : SunGood 1721 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1722 : SunGood 1722 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1723 : SunGood 1723 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1724 : SunGood 1724 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1725 : SunGood 1725 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1726 : SunGood 1726 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1727 : SunGood 1727 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1728 : SunGood 1728 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1729 : SunGood 1729 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1730 : SunGood 1730 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1731 : SunGood 1731 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1732 : SunGood 1732 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1733 : SunGood 1733 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1734 : SunGood 1734 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1735 : SunGood 1735 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1736 : SunGood 1736 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1737 : SunGood 1737 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1738 : SunGood 1738 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g1739 : SunGood 1739 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1740 : SunGood 1740 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1741 : SunGood 1741 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1742 : SunGood 1742 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1743 : SunGood 1743 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1744 : SunGood 1744 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1745 : SunGood 1745 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1746 : SunGood 1746 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1747 : SunGood 1747 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1748 : SunGood 1748 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1749 : SunGood 1749 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1750 : SunGood 1750 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1751 : SunGood 1751 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1752 : SunGood 1752 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1753 : SunGood 1753 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1754 : SunGood 1754 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1755 : SunGood 1755 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1756 : SunGood 1756 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1757 : SunGood 1757 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1758 : SunGood 1758 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1759 : SunGood 1759 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1760 : SunGood 1760 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1761 : SunGood 1761 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1762 : SunGood 1762 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1763 : SunGood 1763 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1764 : SunGood 1764 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1765 : SunGood 1765 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1766 : SunGood 1766 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1767 : SunGood 1767 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1768 : SunGood 1768 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1769 : SunGood 1769 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1770 : SunGood 1770 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1771 : SunGood 1771 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1772 : SunGood 1772 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1773 : SunGood 1773 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1774 : SunGood 1774 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1775 : SunGood 1775 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1776 : SunGood 1776 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1777 : SunGood 1777 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1778 : SunGood 1778 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1779 : SunGood 1779 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1780 : SunGood 1780 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1781 : SunGood 1781 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1782 : SunGood 1782 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1783 : SunGood 1783 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1784 : SunGood 1784 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1785 : SunGood 1785 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1786 : SunGood 1786 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1787 : SunGood 1787 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1788 : SunGood 1788 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1789 : SunGood 1789 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1790 : SunGood 1790 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1791 : SunGood 1791 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1792 : SunGood 1792 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1793 : SunGood 1793 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1794 : SunGood 1794 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1795 : SunGood 1795 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1796 : SunGood 1796 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1797 : SunGood 1797 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1798 : SunGood 1798 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1799 : SunGood 1799 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1800 : SunGood 1800 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1801 : SunGood 1801 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1802 : SunGood 1802 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1803 : SunGood 1803 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1804 : SunGood 1804 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1805 : SunGood 1805 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1806 : SunGood 1806 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1807 : SunGood 1807 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1808 : SunGood 1808 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1809 : SunGood 1809 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1810 : SunGood 1810 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1811 : SunGood 1811 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1812 : SunGood 1812 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1813 : SunGood 1813 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1814 : SunGood 1814 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1815 : SunGood 1815 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1816 : SunGood 1816 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1817 : SunGood 1817 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1818 : SunGood 1818 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1819 : SunGood 1819 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1820 : SunGood 1820 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1821 : SunGood 1821 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1822 : SunGood 1822 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1823 : SunGood 1823 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1824 : SunGood 1824 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1825 : SunGood 1825 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1826 : SunGood 1826 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1827 : SunGood 1827 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1828 : SunGood 1828 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1829 : SunGood 1829 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1830 : SunGood 1830 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1831 : SunGood 1831 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1832 : SunGood 1832 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1833 : SunGood 1833 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1834 : SunGood 1834 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1835 : SunGood 1835 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1836 : SunGood 1836 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1837 : SunGood 1837 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1838 : SunGood 1838 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1839 : SunGood 1839 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1840 : SunGood 1840 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1841 : SunGood 1841 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1842 : SunGood 1842 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1843 : SunGood 1843 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1844 : SunGood 1844 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1845 : SunGood 1845 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1846 : SunGood 1846 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1847 : SunGood 1847 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1848 : SunGood 1848 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1849 : SunGood 1849 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1850 : SunGood 1850 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1851 : SunGood 1851 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1852 : SunGood 1852 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1853 : SunGood 1853 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1854 : SunGood 1854 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1855 : SunGood 1855 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1856 : SunGood 1856 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1857 : SunGood 1857 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1858 : SunGood 1858 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma g1859 : SunGood 1859 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1860 : SunGood 1860 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1861 : SunGood 1861 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1862 : SunGood 1862 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1863 : SunGood 1863 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1864 : SunGood 1864 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1865 : SunGood 1865 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1866 : SunGood 1866 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1867 : SunGood 1867 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1868 : SunGood 1868 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1869 : SunGood 1869 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g1870 : SunGood 1870 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1871 : SunGood 1871 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1872 : SunGood 1872 := Or.inr ⟨6, 0, by norm_num, by norm_num⟩
lemma g1873 : SunGood 1873 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1874 : SunGood 1874 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1875 : SunGood 1875 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1876 : SunGood 1876 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1877 : SunGood 1877 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1878 : SunGood 1878 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1879 : SunGood 1879 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1880 : SunGood 1880 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1881 : SunGood 1881 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1882 : SunGood 1882 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1883 : SunGood 1883 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1884 : SunGood 1884 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1885 : SunGood 1885 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1886 : SunGood 1886 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1887 : SunGood 1887 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1888 : SunGood 1888 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1889 : SunGood 1889 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1890 : SunGood 1890 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1891 : SunGood 1891 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1892 : SunGood 1892 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1893 : SunGood 1893 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1894 : SunGood 1894 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1895 : SunGood 1895 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1896 : SunGood 1896 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1897 : SunGood 1897 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1898 : SunGood 1898 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1899 : SunGood 1899 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1900 : SunGood 1900 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1901 : SunGood 1901 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1902 : SunGood 1902 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1903 : SunGood 1903 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1904 : SunGood 1904 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1905 : SunGood 1905 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1906 : SunGood 1906 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1907 : SunGood 1907 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1908 : SunGood 1908 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1909 : SunGood 1909 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1910 : SunGood 1910 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1911 : SunGood 1911 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1912 : SunGood 1912 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1913 : SunGood 1913 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1914 : SunGood 1914 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1915 : SunGood 1915 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1916 : SunGood 1916 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1917 : SunGood 1917 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1918 : SunGood 1918 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1919 : SunGood 1919 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1920 : SunGood 1920 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1921 : SunGood 1921 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1922 : SunGood 1922 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1923 : SunGood 1923 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1924 : SunGood 1924 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1925 : SunGood 1925 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1926 : SunGood 1926 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1927 : SunGood 1927 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1928 : SunGood 1928 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma g1929 : SunGood 1929 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1930 : SunGood 1930 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1931 : SunGood 1931 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1932 : SunGood 1932 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1933 : SunGood 1933 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1934 : SunGood 1934 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1935 : SunGood 1935 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1936 : SunGood 1936 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1937 : SunGood 1937 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1938 : SunGood 1938 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1939 : SunGood 1939 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1940 : SunGood 1940 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1941 : SunGood 1941 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1942 : SunGood 1942 := Or.inr ⟨7, 0, by norm_num, by norm_num⟩
lemma g1943 : SunGood 1943 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma g1944 : SunGood 1944 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1945 : SunGood 1945 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1946 : SunGood 1946 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1947 : SunGood 1947 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1948 : SunGood 1948 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1949 : SunGood 1949 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1950 : SunGood 1950 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1951 : SunGood 1951 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1952 : SunGood 1952 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1953 : SunGood 1953 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma g1954 : SunGood 1954 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1955 : SunGood 1955 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1956 : SunGood 1956 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1957 : SunGood 1957 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1958 : SunGood 1958 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1959 : SunGood 1959 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1960 : SunGood 1960 := Or.inl ⟨7, 0, by norm_num, by norm_num⟩
lemma g1961 : SunGood 1961 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1962 : SunGood 1962 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma g1963 : SunGood 1963 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma g1964 : SunGood 1964 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1965 : SunGood 1965 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1966 : SunGood 1966 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1967 : SunGood 1967 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1968 : SunGood 1968 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1969 : SunGood 1969 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1970 : SunGood 1970 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1971 : SunGood 1971 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1972 : SunGood 1972 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1973 : SunGood 1973 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1974 : SunGood 1974 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1975 : SunGood 1975 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1976 : SunGood 1976 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1977 : SunGood 1977 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1978 : SunGood 1978 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1979 : SunGood 1979 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1980 : SunGood 1980 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1981 : SunGood 1981 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma g1982 : SunGood 1982 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1983 : SunGood 1983 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1984 : SunGood 1984 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1985 : SunGood 1985 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1986 : SunGood 1986 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1987 : SunGood 1987 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma g1988 : SunGood 1988 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1989 : SunGood 1989 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1990 : SunGood 1990 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1991 : SunGood 1991 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1992 : SunGood 1992 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1993 : SunGood 1993 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1994 : SunGood 1994 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1995 : SunGood 1995 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1996 : SunGood 1996 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma g1997 : SunGood 1997 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma g1998 : SunGood 1998 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g1999 : SunGood 1999 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma g2000 : SunGood 2000 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩

lemma sunGood_block_2_201 {n : ℕ} (hlo : 2 ≤ n) (hhi : n ≤ 201) : SunGood n := by
  interval_cases n
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6
  · exact g7
  · exact g8
  · exact g9
  · exact g10
  · exact g11
  · exact g12
  · exact g13
  · exact g14
  · exact g15
  · exact g16
  · exact g17
  · exact g18
  · exact g19
  · exact g20
  · exact g21
  · exact g22
  · exact g23
  · exact g24
  · exact g25
  · exact g26
  · exact g27
  · exact g28
  · exact g29
  · exact g30
  · exact g31
  · exact g32
  · exact g33
  · exact g34
  · exact g35
  · exact g36
  · exact g37
  · exact g38
  · exact g39
  · exact g40
  · exact g41
  · exact g42
  · exact g43
  · exact g44
  · exact g45
  · exact g46
  · exact g47
  · exact g48
  · exact g49
  · exact g50
  · exact g51
  · exact g52
  · exact g53
  · exact g54
  · exact g55
  · exact g56
  · exact g57
  · exact g58
  · exact g59
  · exact g60
  · exact g61
  · exact g62
  · exact g63
  · exact g64
  · exact g65
  · exact g66
  · exact g67
  · exact g68
  · exact g69
  · exact g70
  · exact g71
  · exact g72
  · exact g73
  · exact g74
  · exact g75
  · exact g76
  · exact g77
  · exact g78
  · exact g79
  · exact g80
  · exact g81
  · exact g82
  · exact g83
  · exact g84
  · exact g85
  · exact g86
  · exact g87
  · exact g88
  · exact g89
  · exact g90
  · exact g91
  · exact g92
  · exact g93
  · exact g94
  · exact g95
  · exact g96
  · exact g97
  · exact g98
  · exact g99
  · exact g100
  · exact g101
  · exact g102
  · exact g103
  · exact g104
  · exact g105
  · exact g106
  · exact g107
  · exact g108
  · exact g109
  · exact g110
  · exact g111
  · exact g112
  · exact g113
  · exact g114
  · exact g115
  · exact g116
  · exact g117
  · exact g118
  · exact g119
  · exact g120
  · exact g121
  · exact g122
  · exact g123
  · exact g124
  · exact g125
  · exact g126
  · exact g127
  · exact g128
  · exact g129
  · exact g130
  · exact g131
  · exact g132
  · exact g133
  · exact g134
  · exact g135
  · exact g136
  · exact g137
  · exact g138
  · exact g139
  · exact g140
  · exact g141
  · exact g142
  · exact g143
  · exact g144
  · exact g145
  · exact g146
  · exact g147
  · exact g148
  · exact g149
  · exact g150
  · exact g151
  · exact g152
  · exact g153
  · exact g154
  · exact g155
  · exact g156
  · exact g157
  · exact g158
  · exact g159
  · exact g160
  · exact g161
  · exact g162
  · exact g163
  · exact g164
  · exact g165
  · exact g166
  · exact g167
  · exact g168
  · exact g169
  · exact g170
  · exact g171
  · exact g172
  · exact g173
  · exact g174
  · exact g175
  · exact g176
  · exact g177
  · exact g178
  · exact g179
  · exact g180
  · exact g181
  · exact g182
  · exact g183
  · exact g184
  · exact g185
  · exact g186
  · exact g187
  · exact g188
  · exact g189
  · exact g190
  · exact g191
  · exact g192
  · exact g193
  · exact g194
  · exact g195
  · exact g196
  · exact g197
  · exact g198
  · exact g199
  · exact g200
  · exact g201

lemma sunGood_block_202_401 {n : ℕ} (hlo : 202 ≤ n) (hhi : n ≤ 401) : SunGood n := by
  interval_cases n
  · exact g202
  · exact g203
  · exact g204
  · exact g205
  · exact g206
  · exact g207
  · exact g208
  · exact g209
  · exact g210
  · exact g211
  · exact g212
  · exact g213
  · exact g214
  · exact g215
  · exact g216
  · exact g217
  · exact g218
  · exact g219
  · exact g220
  · exact g221
  · exact g222
  · exact g223
  · exact g224
  · exact g225
  · exact g226
  · exact g227
  · exact g228
  · exact g229
  · exact g230
  · exact g231
  · exact g232
  · exact g233
  · exact g234
  · exact g235
  · exact g236
  · exact g237
  · exact g238
  · exact g239
  · exact g240
  · exact g241
  · exact g242
  · exact g243
  · exact g244
  · exact g245
  · exact g246
  · exact g247
  · exact g248
  · exact g249
  · exact g250
  · exact g251
  · exact g252
  · exact g253
  · exact g254
  · exact g255
  · exact g256
  · exact g257
  · exact g258
  · exact g259
  · exact g260
  · exact g261
  · exact g262
  · exact g263
  · exact g264
  · exact g265
  · exact g266
  · exact g267
  · exact g268
  · exact g269
  · exact g270
  · exact g271
  · exact g272
  · exact g273
  · exact g274
  · exact g275
  · exact g276
  · exact g277
  · exact g278
  · exact g279
  · exact g280
  · exact g281
  · exact g282
  · exact g283
  · exact g284
  · exact g285
  · exact g286
  · exact g287
  · exact g288
  · exact g289
  · exact g290
  · exact g291
  · exact g292
  · exact g293
  · exact g294
  · exact g295
  · exact g296
  · exact g297
  · exact g298
  · exact g299
  · exact g300
  · exact g301
  · exact g302
  · exact g303
  · exact g304
  · exact g305
  · exact g306
  · exact g307
  · exact g308
  · exact g309
  · exact g310
  · exact g311
  · exact g312
  · exact g313
  · exact g314
  · exact g315
  · exact g316
  · exact g317
  · exact g318
  · exact g319
  · exact g320
  · exact g321
  · exact g322
  · exact g323
  · exact g324
  · exact g325
  · exact g326
  · exact g327
  · exact g328
  · exact g329
  · exact g330
  · exact g331
  · exact g332
  · exact g333
  · exact g334
  · exact g335
  · exact g336
  · exact g337
  · exact g338
  · exact g339
  · exact g340
  · exact g341
  · exact g342
  · exact g343
  · exact g344
  · exact g345
  · exact g346
  · exact g347
  · exact g348
  · exact g349
  · exact g350
  · exact g351
  · exact g352
  · exact g353
  · exact g354
  · exact g355
  · exact g356
  · exact g357
  · exact g358
  · exact g359
  · exact g360
  · exact g361
  · exact g362
  · exact g363
  · exact g364
  · exact g365
  · exact g366
  · exact g367
  · exact g368
  · exact g369
  · exact g370
  · exact g371
  · exact g372
  · exact g373
  · exact g374
  · exact g375
  · exact g376
  · exact g377
  · exact g378
  · exact g379
  · exact g380
  · exact g381
  · exact g382
  · exact g383
  · exact g384
  · exact g385
  · exact g386
  · exact g387
  · exact g388
  · exact g389
  · exact g390
  · exact g391
  · exact g392
  · exact g393
  · exact g394
  · exact g395
  · exact g396
  · exact g397
  · exact g398
  · exact g399
  · exact g400
  · exact g401

lemma sunGood_block_402_601 {n : ℕ} (hlo : 402 ≤ n) (hhi : n ≤ 601) : SunGood n := by
  interval_cases n
  · exact g402
  · exact g403
  · exact g404
  · exact g405
  · exact g406
  · exact g407
  · exact g408
  · exact g409
  · exact g410
  · exact g411
  · exact g412
  · exact g413
  · exact g414
  · exact g415
  · exact g416
  · exact g417
  · exact g418
  · exact g419
  · exact g420
  · exact g421
  · exact g422
  · exact g423
  · exact g424
  · exact g425
  · exact g426
  · exact g427
  · exact g428
  · exact g429
  · exact g430
  · exact g431
  · exact g432
  · exact g433
  · exact g434
  · exact g435
  · exact g436
  · exact g437
  · exact g438
  · exact g439
  · exact g440
  · exact g441
  · exact g442
  · exact g443
  · exact g444
  · exact g445
  · exact g446
  · exact g447
  · exact g448
  · exact g449
  · exact g450
  · exact g451
  · exact g452
  · exact g453
  · exact g454
  · exact g455
  · exact g456
  · exact g457
  · exact g458
  · exact g459
  · exact g460
  · exact g461
  · exact g462
  · exact g463
  · exact g464
  · exact g465
  · exact g466
  · exact g467
  · exact g468
  · exact g469
  · exact g470
  · exact g471
  · exact g472
  · exact g473
  · exact g474
  · exact g475
  · exact g476
  · exact g477
  · exact g478
  · exact g479
  · exact g480
  · exact g481
  · exact g482
  · exact g483
  · exact g484
  · exact g485
  · exact g486
  · exact g487
  · exact g488
  · exact g489
  · exact g490
  · exact g491
  · exact g492
  · exact g493
  · exact g494
  · exact g495
  · exact g496
  · exact g497
  · exact g498
  · exact g499
  · exact g500
  · exact g501
  · exact g502
  · exact g503
  · exact g504
  · exact g505
  · exact g506
  · exact g507
  · exact g508
  · exact g509
  · exact g510
  · exact g511
  · exact g512
  · exact g513
  · exact g514
  · exact g515
  · exact g516
  · exact g517
  · exact g518
  · exact g519
  · exact g520
  · exact g521
  · exact g522
  · exact g523
  · exact g524
  · exact g525
  · exact g526
  · exact g527
  · exact g528
  · exact g529
  · exact g530
  · exact g531
  · exact g532
  · exact g533
  · exact g534
  · exact g535
  · exact g536
  · exact g537
  · exact g538
  · exact g539
  · exact g540
  · exact g541
  · exact g542
  · exact g543
  · exact g544
  · exact g545
  · exact g546
  · exact g547
  · exact g548
  · exact g549
  · exact g550
  · exact g551
  · exact g552
  · exact g553
  · exact g554
  · exact g555
  · exact g556
  · exact g557
  · exact g558
  · exact g559
  · exact g560
  · exact g561
  · exact g562
  · exact g563
  · exact g564
  · exact g565
  · exact g566
  · exact g567
  · exact g568
  · exact g569
  · exact g570
  · exact g571
  · exact g572
  · exact g573
  · exact g574
  · exact g575
  · exact g576
  · exact g577
  · exact g578
  · exact g579
  · exact g580
  · exact g581
  · exact g582
  · exact g583
  · exact g584
  · exact g585
  · exact g586
  · exact g587
  · exact g588
  · exact g589
  · exact g590
  · exact g591
  · exact g592
  · exact g593
  · exact g594
  · exact g595
  · exact g596
  · exact g597
  · exact g598
  · exact g599
  · exact g600
  · exact g601

lemma sunGood_block_602_801 {n : ℕ} (hlo : 602 ≤ n) (hhi : n ≤ 801) : SunGood n := by
  interval_cases n
  · exact g602
  · exact g603
  · exact g604
  · exact g605
  · exact g606
  · exact g607
  · exact g608
  · exact g609
  · exact g610
  · exact g611
  · exact g612
  · exact g613
  · exact g614
  · exact g615
  · exact g616
  · exact g617
  · exact g618
  · exact g619
  · exact g620
  · exact g621
  · exact g622
  · exact g623
  · exact g624
  · exact g625
  · exact g626
  · exact g627
  · exact g628
  · exact g629
  · exact g630
  · exact g631
  · exact g632
  · exact g633
  · exact g634
  · exact g635
  · exact g636
  · exact g637
  · exact g638
  · exact g639
  · exact g640
  · exact g641
  · exact g642
  · exact g643
  · exact g644
  · exact g645
  · exact g646
  · exact g647
  · exact g648
  · exact g649
  · exact g650
  · exact g651
  · exact g652
  · exact g653
  · exact g654
  · exact g655
  · exact g656
  · exact g657
  · exact g658
  · exact g659
  · exact g660
  · exact g661
  · exact g662
  · exact g663
  · exact g664
  · exact g665
  · exact g666
  · exact g667
  · exact g668
  · exact g669
  · exact g670
  · exact g671
  · exact g672
  · exact g673
  · exact g674
  · exact g675
  · exact g676
  · exact g677
  · exact g678
  · exact g679
  · exact g680
  · exact g681
  · exact g682
  · exact g683
  · exact g684
  · exact g685
  · exact g686
  · exact g687
  · exact g688
  · exact g689
  · exact g690
  · exact g691
  · exact g692
  · exact g693
  · exact g694
  · exact g695
  · exact g696
  · exact g697
  · exact g698
  · exact g699
  · exact g700
  · exact g701
  · exact g702
  · exact g703
  · exact g704
  · exact g705
  · exact g706
  · exact g707
  · exact g708
  · exact g709
  · exact g710
  · exact g711
  · exact g712
  · exact g713
  · exact g714
  · exact g715
  · exact g716
  · exact g717
  · exact g718
  · exact g719
  · exact g720
  · exact g721
  · exact g722
  · exact g723
  · exact g724
  · exact g725
  · exact g726
  · exact g727
  · exact g728
  · exact g729
  · exact g730
  · exact g731
  · exact g732
  · exact g733
  · exact g734
  · exact g735
  · exact g736
  · exact g737
  · exact g738
  · exact g739
  · exact g740
  · exact g741
  · exact g742
  · exact g743
  · exact g744
  · exact g745
  · exact g746
  · exact g747
  · exact g748
  · exact g749
  · exact g750
  · exact g751
  · exact g752
  · exact g753
  · exact g754
  · exact g755
  · exact g756
  · exact g757
  · exact g758
  · exact g759
  · exact g760
  · exact g761
  · exact g762
  · exact g763
  · exact g764
  · exact g765
  · exact g766
  · exact g767
  · exact g768
  · exact g769
  · exact g770
  · exact g771
  · exact g772
  · exact g773
  · exact g774
  · exact g775
  · exact g776
  · exact g777
  · exact g778
  · exact g779
  · exact g780
  · exact g781
  · exact g782
  · exact g783
  · exact g784
  · exact g785
  · exact g786
  · exact g787
  · exact g788
  · exact g789
  · exact g790
  · exact g791
  · exact g792
  · exact g793
  · exact g794
  · exact g795
  · exact g796
  · exact g797
  · exact g798
  · exact g799
  · exact g800
  · exact g801

lemma sunGood_block_802_1001 {n : ℕ} (hlo : 802 ≤ n) (hhi : n ≤ 1001) : SunGood n := by
  interval_cases n
  · exact g802
  · exact g803
  · exact g804
  · exact g805
  · exact g806
  · exact g807
  · exact g808
  · exact g809
  · exact g810
  · exact g811
  · exact g812
  · exact g813
  · exact g814
  · exact g815
  · exact g816
  · exact g817
  · exact g818
  · exact g819
  · exact g820
  · exact g821
  · exact g822
  · exact g823
  · exact g824
  · exact g825
  · exact g826
  · exact g827
  · exact g828
  · exact g829
  · exact g830
  · exact g831
  · exact g832
  · exact g833
  · exact g834
  · exact g835
  · exact g836
  · exact g837
  · exact g838
  · exact g839
  · exact g840
  · exact g841
  · exact g842
  · exact g843
  · exact g844
  · exact g845
  · exact g846
  · exact g847
  · exact g848
  · exact g849
  · exact g850
  · exact g851
  · exact g852
  · exact g853
  · exact g854
  · exact g855
  · exact g856
  · exact g857
  · exact g858
  · exact g859
  · exact g860
  · exact g861
  · exact g862
  · exact g863
  · exact g864
  · exact g865
  · exact g866
  · exact g867
  · exact g868
  · exact g869
  · exact g870
  · exact g871
  · exact g872
  · exact g873
  · exact g874
  · exact g875
  · exact g876
  · exact g877
  · exact g878
  · exact g879
  · exact g880
  · exact g881
  · exact g882
  · exact g883
  · exact g884
  · exact g885
  · exact g886
  · exact g887
  · exact g888
  · exact g889
  · exact g890
  · exact g891
  · exact g892
  · exact g893
  · exact g894
  · exact g895
  · exact g896
  · exact g897
  · exact g898
  · exact g899
  · exact g900
  · exact g901
  · exact g902
  · exact g903
  · exact g904
  · exact g905
  · exact g906
  · exact g907
  · exact g908
  · exact g909
  · exact g910
  · exact g911
  · exact g912
  · exact g913
  · exact g914
  · exact g915
  · exact g916
  · exact g917
  · exact g918
  · exact g919
  · exact g920
  · exact g921
  · exact g922
  · exact g923
  · exact g924
  · exact g925
  · exact g926
  · exact g927
  · exact g928
  · exact g929
  · exact g930
  · exact g931
  · exact g932
  · exact g933
  · exact g934
  · exact g935
  · exact g936
  · exact g937
  · exact g938
  · exact g939
  · exact g940
  · exact g941
  · exact g942
  · exact g943
  · exact g944
  · exact g945
  · exact g946
  · exact g947
  · exact g948
  · exact g949
  · exact g950
  · exact g951
  · exact g952
  · exact g953
  · exact g954
  · exact g955
  · exact g956
  · exact g957
  · exact g958
  · exact g959
  · exact g960
  · exact g961
  · exact g962
  · exact g963
  · exact g964
  · exact g965
  · exact g966
  · exact g967
  · exact g968
  · exact g969
  · exact g970
  · exact g971
  · exact g972
  · exact g973
  · exact g974
  · exact g975
  · exact g976
  · exact g977
  · exact g978
  · exact g979
  · exact g980
  · exact g981
  · exact g982
  · exact g983
  · exact g984
  · exact g985
  · exact g986
  · exact g987
  · exact g988
  · exact g989
  · exact g990
  · exact g991
  · exact g992
  · exact g993
  · exact g994
  · exact g995
  · exact g996
  · exact g997
  · exact g998
  · exact g999
  · exact g1000
  · exact g1001

lemma sunGood_block_1002_1201 {n : ℕ} (hlo : 1002 ≤ n) (hhi : n ≤ 1201) : SunGood n := by
  interval_cases n
  · exact g1002
  · exact g1003
  · exact g1004
  · exact g1005
  · exact g1006
  · exact g1007
  · exact g1008
  · exact g1009
  · exact g1010
  · exact g1011
  · exact g1012
  · exact g1013
  · exact g1014
  · exact g1015
  · exact g1016
  · exact g1017
  · exact g1018
  · exact g1019
  · exact g1020
  · exact g1021
  · exact g1022
  · exact g1023
  · exact g1024
  · exact g1025
  · exact g1026
  · exact g1027
  · exact g1028
  · exact g1029
  · exact g1030
  · exact g1031
  · exact g1032
  · exact g1033
  · exact g1034
  · exact g1035
  · exact g1036
  · exact g1037
  · exact g1038
  · exact g1039
  · exact g1040
  · exact g1041
  · exact g1042
  · exact g1043
  · exact g1044
  · exact g1045
  · exact g1046
  · exact g1047
  · exact g1048
  · exact g1049
  · exact g1050
  · exact g1051
  · exact g1052
  · exact g1053
  · exact g1054
  · exact g1055
  · exact g1056
  · exact g1057
  · exact g1058
  · exact g1059
  · exact g1060
  · exact g1061
  · exact g1062
  · exact g1063
  · exact g1064
  · exact g1065
  · exact g1066
  · exact g1067
  · exact g1068
  · exact g1069
  · exact g1070
  · exact g1071
  · exact g1072
  · exact g1073
  · exact g1074
  · exact g1075
  · exact g1076
  · exact g1077
  · exact g1078
  · exact g1079
  · exact g1080
  · exact g1081
  · exact g1082
  · exact g1083
  · exact g1084
  · exact g1085
  · exact g1086
  · exact g1087
  · exact g1088
  · exact g1089
  · exact g1090
  · exact g1091
  · exact g1092
  · exact g1093
  · exact g1094
  · exact g1095
  · exact g1096
  · exact g1097
  · exact g1098
  · exact g1099
  · exact g1100
  · exact g1101
  · exact g1102
  · exact g1103
  · exact g1104
  · exact g1105
  · exact g1106
  · exact g1107
  · exact g1108
  · exact g1109
  · exact g1110
  · exact g1111
  · exact g1112
  · exact g1113
  · exact g1114
  · exact g1115
  · exact g1116
  · exact g1117
  · exact g1118
  · exact g1119
  · exact g1120
  · exact g1121
  · exact g1122
  · exact g1123
  · exact g1124
  · exact g1125
  · exact g1126
  · exact g1127
  · exact g1128
  · exact g1129
  · exact g1130
  · exact g1131
  · exact g1132
  · exact g1133
  · exact g1134
  · exact g1135
  · exact g1136
  · exact g1137
  · exact g1138
  · exact g1139
  · exact g1140
  · exact g1141
  · exact g1142
  · exact g1143
  · exact g1144
  · exact g1145
  · exact g1146
  · exact g1147
  · exact g1148
  · exact g1149
  · exact g1150
  · exact g1151
  · exact g1152
  · exact g1153
  · exact g1154
  · exact g1155
  · exact g1156
  · exact g1157
  · exact g1158
  · exact g1159
  · exact g1160
  · exact g1161
  · exact g1162
  · exact g1163
  · exact g1164
  · exact g1165
  · exact g1166
  · exact g1167
  · exact g1168
  · exact g1169
  · exact g1170
  · exact g1171
  · exact g1172
  · exact g1173
  · exact g1174
  · exact g1175
  · exact g1176
  · exact g1177
  · exact g1178
  · exact g1179
  · exact g1180
  · exact g1181
  · exact g1182
  · exact g1183
  · exact g1184
  · exact g1185
  · exact g1186
  · exact g1187
  · exact g1188
  · exact g1189
  · exact g1190
  · exact g1191
  · exact g1192
  · exact g1193
  · exact g1194
  · exact g1195
  · exact g1196
  · exact g1197
  · exact g1198
  · exact g1199
  · exact g1200
  · exact g1201

lemma sunGood_block_1202_1401 {n : ℕ} (hlo : 1202 ≤ n) (hhi : n ≤ 1401) : SunGood n := by
  interval_cases n
  · exact g1202
  · exact g1203
  · exact g1204
  · exact g1205
  · exact g1206
  · exact g1207
  · exact g1208
  · exact g1209
  · exact g1210
  · exact g1211
  · exact g1212
  · exact g1213
  · exact g1214
  · exact g1215
  · exact g1216
  · exact g1217
  · exact g1218
  · exact g1219
  · exact g1220
  · exact g1221
  · exact g1222
  · exact g1223
  · exact g1224
  · exact g1225
  · exact g1226
  · exact g1227
  · exact g1228
  · exact g1229
  · exact g1230
  · exact g1231
  · exact g1232
  · exact g1233
  · exact g1234
  · exact g1235
  · exact g1236
  · exact g1237
  · exact g1238
  · exact g1239
  · exact g1240
  · exact g1241
  · exact g1242
  · exact g1243
  · exact g1244
  · exact g1245
  · exact g1246
  · exact g1247
  · exact g1248
  · exact g1249
  · exact g1250
  · exact g1251
  · exact g1252
  · exact g1253
  · exact g1254
  · exact g1255
  · exact g1256
  · exact g1257
  · exact g1258
  · exact g1259
  · exact g1260
  · exact g1261
  · exact g1262
  · exact g1263
  · exact g1264
  · exact g1265
  · exact g1266
  · exact g1267
  · exact g1268
  · exact g1269
  · exact g1270
  · exact g1271
  · exact g1272
  · exact g1273
  · exact g1274
  · exact g1275
  · exact g1276
  · exact g1277
  · exact g1278
  · exact g1279
  · exact g1280
  · exact g1281
  · exact g1282
  · exact g1283
  · exact g1284
  · exact g1285
  · exact g1286
  · exact g1287
  · exact g1288
  · exact g1289
  · exact g1290
  · exact g1291
  · exact g1292
  · exact g1293
  · exact g1294
  · exact g1295
  · exact g1296
  · exact g1297
  · exact g1298
  · exact g1299
  · exact g1300
  · exact g1301
  · exact g1302
  · exact g1303
  · exact g1304
  · exact g1305
  · exact g1306
  · exact g1307
  · exact g1308
  · exact g1309
  · exact g1310
  · exact g1311
  · exact g1312
  · exact g1313
  · exact g1314
  · exact g1315
  · exact g1316
  · exact g1317
  · exact g1318
  · exact g1319
  · exact g1320
  · exact g1321
  · exact g1322
  · exact g1323
  · exact g1324
  · exact g1325
  · exact g1326
  · exact g1327
  · exact g1328
  · exact g1329
  · exact g1330
  · exact g1331
  · exact g1332
  · exact g1333
  · exact g1334
  · exact g1335
  · exact g1336
  · exact g1337
  · exact g1338
  · exact g1339
  · exact g1340
  · exact g1341
  · exact g1342
  · exact g1343
  · exact g1344
  · exact g1345
  · exact g1346
  · exact g1347
  · exact g1348
  · exact g1349
  · exact g1350
  · exact g1351
  · exact g1352
  · exact g1353
  · exact g1354
  · exact g1355
  · exact g1356
  · exact g1357
  · exact g1358
  · exact g1359
  · exact g1360
  · exact g1361
  · exact g1362
  · exact g1363
  · exact g1364
  · exact g1365
  · exact g1366
  · exact g1367
  · exact g1368
  · exact g1369
  · exact g1370
  · exact g1371
  · exact g1372
  · exact g1373
  · exact g1374
  · exact g1375
  · exact g1376
  · exact g1377
  · exact g1378
  · exact g1379
  · exact g1380
  · exact g1381
  · exact g1382
  · exact g1383
  · exact g1384
  · exact g1385
  · exact g1386
  · exact g1387
  · exact g1388
  · exact g1389
  · exact g1390
  · exact g1391
  · exact g1392
  · exact g1393
  · exact g1394
  · exact g1395
  · exact g1396
  · exact g1397
  · exact g1398
  · exact g1399
  · exact g1400
  · exact g1401

lemma sunGood_block_1402_1601 {n : ℕ} (hlo : 1402 ≤ n) (hhi : n ≤ 1601) : SunGood n := by
  interval_cases n
  · exact g1402
  · exact g1403
  · exact g1404
  · exact g1405
  · exact g1406
  · exact g1407
  · exact g1408
  · exact g1409
  · exact g1410
  · exact g1411
  · exact g1412
  · exact g1413
  · exact g1414
  · exact g1415
  · exact g1416
  · exact g1417
  · exact g1418
  · exact g1419
  · exact g1420
  · exact g1421
  · exact g1422
  · exact g1423
  · exact g1424
  · exact g1425
  · exact g1426
  · exact g1427
  · exact g1428
  · exact g1429
  · exact g1430
  · exact g1431
  · exact g1432
  · exact g1433
  · exact g1434
  · exact g1435
  · exact g1436
  · exact g1437
  · exact g1438
  · exact g1439
  · exact g1440
  · exact g1441
  · exact g1442
  · exact g1443
  · exact g1444
  · exact g1445
  · exact g1446
  · exact g1447
  · exact g1448
  · exact g1449
  · exact g1450
  · exact g1451
  · exact g1452
  · exact g1453
  · exact g1454
  · exact g1455
  · exact g1456
  · exact g1457
  · exact g1458
  · exact g1459
  · exact g1460
  · exact g1461
  · exact g1462
  · exact g1463
  · exact g1464
  · exact g1465
  · exact g1466
  · exact g1467
  · exact g1468
  · exact g1469
  · exact g1470
  · exact g1471
  · exact g1472
  · exact g1473
  · exact g1474
  · exact g1475
  · exact g1476
  · exact g1477
  · exact g1478
  · exact g1479
  · exact g1480
  · exact g1481
  · exact g1482
  · exact g1483
  · exact g1484
  · exact g1485
  · exact g1486
  · exact g1487
  · exact g1488
  · exact g1489
  · exact g1490
  · exact g1491
  · exact g1492
  · exact g1493
  · exact g1494
  · exact g1495
  · exact g1496
  · exact g1497
  · exact g1498
  · exact g1499
  · exact g1500
  · exact g1501
  · exact g1502
  · exact g1503
  · exact g1504
  · exact g1505
  · exact g1506
  · exact g1507
  · exact g1508
  · exact g1509
  · exact g1510
  · exact g1511
  · exact g1512
  · exact g1513
  · exact g1514
  · exact g1515
  · exact g1516
  · exact g1517
  · exact g1518
  · exact g1519
  · exact g1520
  · exact g1521
  · exact g1522
  · exact g1523
  · exact g1524
  · exact g1525
  · exact g1526
  · exact g1527
  · exact g1528
  · exact g1529
  · exact g1530
  · exact g1531
  · exact g1532
  · exact g1533
  · exact g1534
  · exact g1535
  · exact g1536
  · exact g1537
  · exact g1538
  · exact g1539
  · exact g1540
  · exact g1541
  · exact g1542
  · exact g1543
  · exact g1544
  · exact g1545
  · exact g1546
  · exact g1547
  · exact g1548
  · exact g1549
  · exact g1550
  · exact g1551
  · exact g1552
  · exact g1553
  · exact g1554
  · exact g1555
  · exact g1556
  · exact g1557
  · exact g1558
  · exact g1559
  · exact g1560
  · exact g1561
  · exact g1562
  · exact g1563
  · exact g1564
  · exact g1565
  · exact g1566
  · exact g1567
  · exact g1568
  · exact g1569
  · exact g1570
  · exact g1571
  · exact g1572
  · exact g1573
  · exact g1574
  · exact g1575
  · exact g1576
  · exact g1577
  · exact g1578
  · exact g1579
  · exact g1580
  · exact g1581
  · exact g1582
  · exact g1583
  · exact g1584
  · exact g1585
  · exact g1586
  · exact g1587
  · exact g1588
  · exact g1589
  · exact g1590
  · exact g1591
  · exact g1592
  · exact g1593
  · exact g1594
  · exact g1595
  · exact g1596
  · exact g1597
  · exact g1598
  · exact g1599
  · exact g1600
  · exact g1601

lemma sunGood_block_1602_1801 {n : ℕ} (hlo : 1602 ≤ n) (hhi : n ≤ 1801) : SunGood n := by
  interval_cases n
  · exact g1602
  · exact g1603
  · exact g1604
  · exact g1605
  · exact g1606
  · exact g1607
  · exact g1608
  · exact g1609
  · exact g1610
  · exact g1611
  · exact g1612
  · exact g1613
  · exact g1614
  · exact g1615
  · exact g1616
  · exact g1617
  · exact g1618
  · exact g1619
  · exact g1620
  · exact g1621
  · exact g1622
  · exact g1623
  · exact g1624
  · exact g1625
  · exact g1626
  · exact g1627
  · exact g1628
  · exact g1629
  · exact g1630
  · exact g1631
  · exact g1632
  · exact g1633
  · exact g1634
  · exact g1635
  · exact g1636
  · exact g1637
  · exact g1638
  · exact g1639
  · exact g1640
  · exact g1641
  · exact g1642
  · exact g1643
  · exact g1644
  · exact g1645
  · exact g1646
  · exact g1647
  · exact g1648
  · exact g1649
  · exact g1650
  · exact g1651
  · exact g1652
  · exact g1653
  · exact g1654
  · exact g1655
  · exact g1656
  · exact g1657
  · exact g1658
  · exact g1659
  · exact g1660
  · exact g1661
  · exact g1662
  · exact g1663
  · exact g1664
  · exact g1665
  · exact g1666
  · exact g1667
  · exact g1668
  · exact g1669
  · exact g1670
  · exact g1671
  · exact g1672
  · exact g1673
  · exact g1674
  · exact g1675
  · exact g1676
  · exact g1677
  · exact g1678
  · exact g1679
  · exact g1680
  · exact g1681
  · exact g1682
  · exact g1683
  · exact g1684
  · exact g1685
  · exact g1686
  · exact g1687
  · exact g1688
  · exact g1689
  · exact g1690
  · exact g1691
  · exact g1692
  · exact g1693
  · exact g1694
  · exact g1695
  · exact g1696
  · exact g1697
  · exact g1698
  · exact g1699
  · exact g1700
  · exact g1701
  · exact g1702
  · exact g1703
  · exact g1704
  · exact g1705
  · exact g1706
  · exact g1707
  · exact g1708
  · exact g1709
  · exact g1710
  · exact g1711
  · exact g1712
  · exact g1713
  · exact g1714
  · exact g1715
  · exact g1716
  · exact g1717
  · exact g1718
  · exact g1719
  · exact g1720
  · exact g1721
  · exact g1722
  · exact g1723
  · exact g1724
  · exact g1725
  · exact g1726
  · exact g1727
  · exact g1728
  · exact g1729
  · exact g1730
  · exact g1731
  · exact g1732
  · exact g1733
  · exact g1734
  · exact g1735
  · exact g1736
  · exact g1737
  · exact g1738
  · exact g1739
  · exact g1740
  · exact g1741
  · exact g1742
  · exact g1743
  · exact g1744
  · exact g1745
  · exact g1746
  · exact g1747
  · exact g1748
  · exact g1749
  · exact g1750
  · exact g1751
  · exact g1752
  · exact g1753
  · exact g1754
  · exact g1755
  · exact g1756
  · exact g1757
  · exact g1758
  · exact g1759
  · exact g1760
  · exact g1761
  · exact g1762
  · exact g1763
  · exact g1764
  · exact g1765
  · exact g1766
  · exact g1767
  · exact g1768
  · exact g1769
  · exact g1770
  · exact g1771
  · exact g1772
  · exact g1773
  · exact g1774
  · exact g1775
  · exact g1776
  · exact g1777
  · exact g1778
  · exact g1779
  · exact g1780
  · exact g1781
  · exact g1782
  · exact g1783
  · exact g1784
  · exact g1785
  · exact g1786
  · exact g1787
  · exact g1788
  · exact g1789
  · exact g1790
  · exact g1791
  · exact g1792
  · exact g1793
  · exact g1794
  · exact g1795
  · exact g1796
  · exact g1797
  · exact g1798
  · exact g1799
  · exact g1800
  · exact g1801

lemma sunGood_block_1802_2000 {n : ℕ} (hlo : 1802 ≤ n) (hhi : n ≤ 2000) : SunGood n := by
  interval_cases n
  · exact g1802
  · exact g1803
  · exact g1804
  · exact g1805
  · exact g1806
  · exact g1807
  · exact g1808
  · exact g1809
  · exact g1810
  · exact g1811
  · exact g1812
  · exact g1813
  · exact g1814
  · exact g1815
  · exact g1816
  · exact g1817
  · exact g1818
  · exact g1819
  · exact g1820
  · exact g1821
  · exact g1822
  · exact g1823
  · exact g1824
  · exact g1825
  · exact g1826
  · exact g1827
  · exact g1828
  · exact g1829
  · exact g1830
  · exact g1831
  · exact g1832
  · exact g1833
  · exact g1834
  · exact g1835
  · exact g1836
  · exact g1837
  · exact g1838
  · exact g1839
  · exact g1840
  · exact g1841
  · exact g1842
  · exact g1843
  · exact g1844
  · exact g1845
  · exact g1846
  · exact g1847
  · exact g1848
  · exact g1849
  · exact g1850
  · exact g1851
  · exact g1852
  · exact g1853
  · exact g1854
  · exact g1855
  · exact g1856
  · exact g1857
  · exact g1858
  · exact g1859
  · exact g1860
  · exact g1861
  · exact g1862
  · exact g1863
  · exact g1864
  · exact g1865
  · exact g1866
  · exact g1867
  · exact g1868
  · exact g1869
  · exact g1870
  · exact g1871
  · exact g1872
  · exact g1873
  · exact g1874
  · exact g1875
  · exact g1876
  · exact g1877
  · exact g1878
  · exact g1879
  · exact g1880
  · exact g1881
  · exact g1882
  · exact g1883
  · exact g1884
  · exact g1885
  · exact g1886
  · exact g1887
  · exact g1888
  · exact g1889
  · exact g1890
  · exact g1891
  · exact g1892
  · exact g1893
  · exact g1894
  · exact g1895
  · exact g1896
  · exact g1897
  · exact g1898
  · exact g1899
  · exact g1900
  · exact g1901
  · exact g1902
  · exact g1903
  · exact g1904
  · exact g1905
  · exact g1906
  · exact g1907
  · exact g1908
  · exact g1909
  · exact g1910
  · exact g1911
  · exact g1912
  · exact g1913
  · exact g1914
  · exact g1915
  · exact g1916
  · exact g1917
  · exact g1918
  · exact g1919
  · exact g1920
  · exact g1921
  · exact g1922
  · exact g1923
  · exact g1924
  · exact g1925
  · exact g1926
  · exact g1927
  · exact g1928
  · exact g1929
  · exact g1930
  · exact g1931
  · exact g1932
  · exact g1933
  · exact g1934
  · exact g1935
  · exact g1936
  · exact g1937
  · exact g1938
  · exact g1939
  · exact g1940
  · exact g1941
  · exact g1942
  · exact g1943
  · exact g1944
  · exact g1945
  · exact g1946
  · exact g1947
  · exact g1948
  · exact g1949
  · exact g1950
  · exact g1951
  · exact g1952
  · exact g1953
  · exact g1954
  · exact g1955
  · exact g1956
  · exact g1957
  · exact g1958
  · exact g1959
  · exact g1960
  · exact g1961
  · exact g1962
  · exact g1963
  · exact g1964
  · exact g1965
  · exact g1966
  · exact g1967
  · exact g1968
  · exact g1969
  · exact g1970
  · exact g1971
  · exact g1972
  · exact g1973
  · exact g1974
  · exact g1975
  · exact g1976
  · exact g1977
  · exact g1978
  · exact g1979
  · exact g1980
  · exact g1981
  · exact g1982
  · exact g1983
  · exact g1984
  · exact g1985
  · exact g1986
  · exact g1987
  · exact g1988
  · exact g1989
  · exact g1990
  · exact g1991
  · exact g1992
  · exact g1993
  · exact g1994
  · exact g1995
  · exact g1996
  · exact g1997
  · exact g1998
  · exact g1999
  · exact g2000

lemma sunGood_of_le_2000 {n : ℕ} (hn : 1 < n) (hN : n ≤ 2000) : SunGood n := by
  rcases le_or_gt n 201 with h | h
  · exact sunGood_block_2_201 (by omega) h
  rcases le_or_gt n 401 with h | h
  · exact sunGood_block_202_401 (by omega) h
  rcases le_or_gt n 601 with h | h
  · exact sunGood_block_402_601 (by omega) h
  rcases le_or_gt n 801 with h | h
  · exact sunGood_block_602_801 (by omega) h
  rcases le_or_gt n 1001 with h | h
  · exact sunGood_block_802_1001 (by omega) h
  rcases le_or_gt n 1201 with h | h
  · exact sunGood_block_1002_1201 (by omega) h
  rcases le_or_gt n 1401 with h | h
  · exact sunGood_block_1202_1401 (by omega) h
  rcases le_or_gt n 1601 with h | h
  · exact sunGood_block_1402_1601 (by omega) h
  rcases le_or_gt n 1801 with h | h
  · exact sunGood_block_1602_1801 (by omega) h
  exact sunGood_block_1802_2000 (by omega) hN
