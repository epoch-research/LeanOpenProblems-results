import FormalConjectures.Util.ProblemImports
open Nat
set_option maxHeartbeats 40000000

def SunGood (n : ℕ) : Prop :=
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
  ∨
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))

lemma good2 : SunGood 2 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good3 : SunGood 3 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good4 : SunGood 4 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good5 : SunGood 5 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good6 : SunGood 6 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good7 : SunGood 7 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good8 : SunGood 8 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good9 : SunGood 9 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good10 : SunGood 10 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good11 : SunGood 11 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good12 : SunGood 12 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good13 : SunGood 13 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good14 : SunGood 14 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good15 : SunGood 15 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good16 : SunGood 16 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good17 : SunGood 17 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good18 : SunGood 18 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good19 : SunGood 19 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good20 : SunGood 20 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good21 : SunGood 21 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good22 : SunGood 22 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good23 : SunGood 23 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good24 : SunGood 24 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good25 : SunGood 25 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good26 : SunGood 26 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good27 : SunGood 27 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good28 : SunGood 28 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good29 : SunGood 29 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good30 : SunGood 30 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good31 : SunGood 31 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good32 : SunGood 32 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good33 : SunGood 33 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good34 : SunGood 34 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good35 : SunGood 35 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good36 : SunGood 36 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good37 : SunGood 37 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good38 : SunGood 38 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good39 : SunGood 39 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good40 : SunGood 40 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good41 : SunGood 41 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good42 : SunGood 42 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good43 : SunGood 43 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good44 : SunGood 44 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good45 : SunGood 45 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good46 : SunGood 46 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good47 : SunGood 47 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good48 : SunGood 48 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good49 : SunGood 49 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good50 : SunGood 50 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good51 : SunGood 51 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good52 : SunGood 52 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good53 : SunGood 53 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good54 : SunGood 54 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good55 : SunGood 55 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good56 : SunGood 56 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good57 : SunGood 57 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good58 : SunGood 58 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good59 : SunGood 59 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good60 : SunGood 60 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good61 : SunGood 61 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good62 : SunGood 62 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good63 : SunGood 63 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good64 : SunGood 64 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good65 : SunGood 65 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good66 : SunGood 66 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good67 : SunGood 67 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good68 : SunGood 68 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good69 : SunGood 69 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good70 : SunGood 70 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good71 : SunGood 71 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good72 : SunGood 72 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good73 : SunGood 73 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good74 : SunGood 74 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good75 : SunGood 75 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good76 : SunGood 76 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good77 : SunGood 77 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good78 : SunGood 78 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good79 : SunGood 79 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good80 : SunGood 80 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good81 : SunGood 81 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good82 : SunGood 82 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good83 : SunGood 83 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good84 : SunGood 84 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good85 : SunGood 85 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good86 : SunGood 86 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good87 : SunGood 87 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good88 : SunGood 88 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good89 : SunGood 89 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good90 : SunGood 90 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good91 : SunGood 91 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good92 : SunGood 92 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good93 : SunGood 93 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good94 : SunGood 94 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good95 : SunGood 95 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good96 : SunGood 96 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good97 : SunGood 97 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good98 : SunGood 98 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good99 : SunGood 99 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good100 : SunGood 100 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good101 : SunGood 101 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good102 : SunGood 102 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good103 : SunGood 103 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good104 : SunGood 104 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good105 : SunGood 105 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good106 : SunGood 106 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good107 : SunGood 107 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good108 : SunGood 108 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good109 : SunGood 109 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good110 : SunGood 110 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good111 : SunGood 111 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good112 : SunGood 112 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good113 : SunGood 113 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good114 : SunGood 114 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good115 : SunGood 115 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good116 : SunGood 116 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good117 : SunGood 117 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good118 : SunGood 118 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good119 : SunGood 119 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good120 : SunGood 120 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good121 : SunGood 121 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good122 : SunGood 122 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good123 : SunGood 123 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good124 : SunGood 124 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good125 : SunGood 125 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good126 : SunGood 126 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good127 : SunGood 127 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good128 : SunGood 128 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good129 : SunGood 129 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good130 : SunGood 130 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good131 : SunGood 131 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good132 : SunGood 132 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good133 : SunGood 133 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good134 : SunGood 134 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good135 : SunGood 135 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good136 : SunGood 136 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good137 : SunGood 137 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good138 : SunGood 138 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good139 : SunGood 139 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good140 : SunGood 140 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good141 : SunGood 141 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good142 : SunGood 142 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good143 : SunGood 143 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good144 : SunGood 144 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good145 : SunGood 145 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good146 : SunGood 146 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good147 : SunGood 147 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good148 : SunGood 148 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good149 : SunGood 149 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good150 : SunGood 150 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good151 : SunGood 151 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good152 : SunGood 152 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good153 : SunGood 153 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good154 : SunGood 154 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good155 : SunGood 155 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good156 : SunGood 156 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good157 : SunGood 157 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good158 : SunGood 158 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good159 : SunGood 159 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good160 : SunGood 160 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good161 : SunGood 161 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good162 : SunGood 162 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good163 : SunGood 163 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good164 : SunGood 164 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good165 : SunGood 165 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good166 : SunGood 166 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good167 : SunGood 167 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good168 : SunGood 168 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good169 : SunGood 169 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good170 : SunGood 170 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good171 : SunGood 171 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good172 : SunGood 172 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good173 : SunGood 173 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good174 : SunGood 174 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good175 : SunGood 175 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good176 : SunGood 176 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good177 : SunGood 177 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good178 : SunGood 178 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good179 : SunGood 179 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good180 : SunGood 180 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good181 : SunGood 181 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good182 : SunGood 182 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good183 : SunGood 183 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good184 : SunGood 184 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good185 : SunGood 185 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good186 : SunGood 186 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good187 : SunGood 187 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good188 : SunGood 188 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good189 : SunGood 189 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good190 : SunGood 190 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good191 : SunGood 191 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good192 : SunGood 192 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good193 : SunGood 193 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good194 : SunGood 194 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good195 : SunGood 195 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good196 : SunGood 196 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good197 : SunGood 197 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good198 : SunGood 198 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good199 : SunGood 199 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good200 : SunGood 200 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good201 : SunGood 201 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good202 : SunGood 202 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good203 : SunGood 203 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good204 : SunGood 204 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good205 : SunGood 205 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good206 : SunGood 206 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good207 : SunGood 207 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good208 : SunGood 208 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good209 : SunGood 209 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good210 : SunGood 210 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good211 : SunGood 211 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good212 : SunGood 212 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good213 : SunGood 213 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good214 : SunGood 214 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good215 : SunGood 215 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good216 : SunGood 216 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good217 : SunGood 217 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good218 : SunGood 218 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good219 : SunGood 219 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good220 : SunGood 220 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good221 : SunGood 221 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good222 : SunGood 222 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good223 : SunGood 223 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good224 : SunGood 224 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good225 : SunGood 225 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good226 : SunGood 226 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good227 : SunGood 227 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma good228 : SunGood 228 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good229 : SunGood 229 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good230 : SunGood 230 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good231 : SunGood 231 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good232 : SunGood 232 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good233 : SunGood 233 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good234 : SunGood 234 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good235 : SunGood 235 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good236 : SunGood 236 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good237 : SunGood 237 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good238 : SunGood 238 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good239 : SunGood 239 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good240 : SunGood 240 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good241 : SunGood 241 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good242 : SunGood 242 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good243 : SunGood 243 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good244 : SunGood 244 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good245 : SunGood 245 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good246 : SunGood 246 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good247 : SunGood 247 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good248 : SunGood 248 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good249 : SunGood 249 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good250 : SunGood 250 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good251 : SunGood 251 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good252 : SunGood 252 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good253 : SunGood 253 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good254 : SunGood 254 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good255 : SunGood 255 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good256 : SunGood 256 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good257 : SunGood 257 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good258 : SunGood 258 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good259 : SunGood 259 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good260 : SunGood 260 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good261 : SunGood 261 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good262 : SunGood 262 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good263 : SunGood 263 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good264 : SunGood 264 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good265 : SunGood 265 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good266 : SunGood 266 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good267 : SunGood 267 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good268 : SunGood 268 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good269 : SunGood 269 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good270 : SunGood 270 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good271 : SunGood 271 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good272 : SunGood 272 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good273 : SunGood 273 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good274 : SunGood 274 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good275 : SunGood 275 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good276 : SunGood 276 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good277 : SunGood 277 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good278 : SunGood 278 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good279 : SunGood 279 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good280 : SunGood 280 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good281 : SunGood 281 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good282 : SunGood 282 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good283 : SunGood 283 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good284 : SunGood 284 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good285 : SunGood 285 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good286 : SunGood 286 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good287 : SunGood 287 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good288 : SunGood 288 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good289 : SunGood 289 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good290 : SunGood 290 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good291 : SunGood 291 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good292 : SunGood 292 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good293 : SunGood 293 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good294 : SunGood 294 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good295 : SunGood 295 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good296 : SunGood 296 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good297 : SunGood 297 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good298 : SunGood 298 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good299 : SunGood 299 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good300 : SunGood 300 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good301 : SunGood 301 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good302 : SunGood 302 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good303 : SunGood 303 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good304 : SunGood 304 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good305 : SunGood 305 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good306 : SunGood 306 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good307 : SunGood 307 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good308 : SunGood 308 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good309 : SunGood 309 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good310 : SunGood 310 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good311 : SunGood 311 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good312 : SunGood 312 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good313 : SunGood 313 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good314 : SunGood 314 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good315 : SunGood 315 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good316 : SunGood 316 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good317 : SunGood 317 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good318 : SunGood 318 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good319 : SunGood 319 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good320 : SunGood 320 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good321 : SunGood 321 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good322 : SunGood 322 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good323 : SunGood 323 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good324 : SunGood 324 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good325 : SunGood 325 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good326 : SunGood 326 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good327 : SunGood 327 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good328 : SunGood 328 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma good329 : SunGood 329 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good330 : SunGood 330 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good331 : SunGood 331 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good332 : SunGood 332 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good333 : SunGood 333 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good334 : SunGood 334 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good335 : SunGood 335 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good336 : SunGood 336 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good337 : SunGood 337 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good338 : SunGood 338 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good339 : SunGood 339 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good340 : SunGood 340 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good341 : SunGood 341 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good342 : SunGood 342 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good343 : SunGood 343 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good344 : SunGood 344 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good345 : SunGood 345 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good346 : SunGood 346 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good347 : SunGood 347 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good348 : SunGood 348 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good349 : SunGood 349 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good350 : SunGood 350 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good351 : SunGood 351 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good352 : SunGood 352 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good353 : SunGood 353 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good354 : SunGood 354 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good355 : SunGood 355 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good356 : SunGood 356 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good357 : SunGood 357 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good358 : SunGood 358 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good359 : SunGood 359 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good360 : SunGood 360 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good361 : SunGood 361 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good362 : SunGood 362 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good363 : SunGood 363 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good364 : SunGood 364 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good365 : SunGood 365 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good366 : SunGood 366 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma good367 : SunGood 367 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good368 : SunGood 368 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good369 : SunGood 369 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good370 : SunGood 370 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good371 : SunGood 371 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good372 : SunGood 372 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good373 : SunGood 373 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good374 : SunGood 374 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good375 : SunGood 375 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good376 : SunGood 376 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good377 : SunGood 377 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good378 : SunGood 378 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good379 : SunGood 379 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good380 : SunGood 380 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good381 : SunGood 381 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good382 : SunGood 382 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good383 : SunGood 383 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good384 : SunGood 384 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good385 : SunGood 385 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good386 : SunGood 386 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good387 : SunGood 387 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good388 : SunGood 388 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good389 : SunGood 389 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good390 : SunGood 390 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good391 : SunGood 391 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good392 : SunGood 392 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good393 : SunGood 393 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good394 : SunGood 394 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good395 : SunGood 395 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good396 : SunGood 396 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good397 : SunGood 397 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good398 : SunGood 398 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good399 : SunGood 399 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good400 : SunGood 400 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good401 : SunGood 401 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good402 : SunGood 402 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good403 : SunGood 403 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good404 : SunGood 404 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good405 : SunGood 405 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good406 : SunGood 406 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good407 : SunGood 407 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good408 : SunGood 408 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good409 : SunGood 409 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good410 : SunGood 410 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good411 : SunGood 411 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good412 : SunGood 412 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good413 : SunGood 413 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good414 : SunGood 414 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good415 : SunGood 415 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good416 : SunGood 416 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good417 : SunGood 417 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good418 : SunGood 418 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good419 : SunGood 419 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good420 : SunGood 420 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good421 : SunGood 421 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good422 : SunGood 422 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good423 : SunGood 423 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good424 : SunGood 424 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good425 : SunGood 425 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good426 : SunGood 426 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good427 : SunGood 427 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good428 : SunGood 428 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good429 : SunGood 429 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good430 : SunGood 430 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good431 : SunGood 431 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good432 : SunGood 432 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good433 : SunGood 433 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good434 : SunGood 434 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good435 : SunGood 435 := Or.inr ⟨5, 0, by norm_num, by norm_num⟩
lemma good436 : SunGood 436 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good437 : SunGood 437 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good438 : SunGood 438 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good439 : SunGood 439 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good440 : SunGood 440 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good441 : SunGood 441 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good442 : SunGood 442 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good443 : SunGood 443 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good444 : SunGood 444 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good445 : SunGood 445 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good446 : SunGood 446 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good447 : SunGood 447 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good448 : SunGood 448 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good449 : SunGood 449 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good450 : SunGood 450 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good451 : SunGood 451 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good452 : SunGood 452 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good453 : SunGood 453 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good454 : SunGood 454 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good455 : SunGood 455 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good456 : SunGood 456 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good457 : SunGood 457 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good458 : SunGood 458 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good459 : SunGood 459 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good460 : SunGood 460 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good461 : SunGood 461 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good462 : SunGood 462 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good463 : SunGood 463 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good464 : SunGood 464 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good465 : SunGood 465 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good466 : SunGood 466 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good467 : SunGood 467 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good468 : SunGood 468 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good469 : SunGood 469 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good470 : SunGood 470 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good471 : SunGood 471 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good472 : SunGood 472 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good473 : SunGood 473 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good474 : SunGood 474 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good475 : SunGood 475 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good476 : SunGood 476 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good477 : SunGood 477 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good478 : SunGood 478 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good479 : SunGood 479 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good480 : SunGood 480 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good481 : SunGood 481 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good482 : SunGood 482 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good483 : SunGood 483 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good484 : SunGood 484 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good485 : SunGood 485 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good486 : SunGood 486 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good487 : SunGood 487 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good488 : SunGood 488 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good489 : SunGood 489 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good490 : SunGood 490 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good491 : SunGood 491 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good492 : SunGood 492 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good493 : SunGood 493 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good494 : SunGood 494 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good495 : SunGood 495 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good496 : SunGood 496 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good497 : SunGood 497 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good498 : SunGood 498 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good499 : SunGood 499 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good500 : SunGood 500 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good501 : SunGood 501 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good502 : SunGood 502 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good503 : SunGood 503 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good504 : SunGood 504 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good505 : SunGood 505 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good506 : SunGood 506 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good507 : SunGood 507 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good508 : SunGood 508 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good509 : SunGood 509 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good510 : SunGood 510 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good511 : SunGood 511 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good512 : SunGood 512 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good513 : SunGood 513 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good514 : SunGood 514 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good515 : SunGood 515 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good516 : SunGood 516 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good517 : SunGood 517 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good518 : SunGood 518 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good519 : SunGood 519 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good520 : SunGood 520 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good521 : SunGood 521 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good522 : SunGood 522 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good523 : SunGood 523 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good524 : SunGood 524 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good525 : SunGood 525 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good526 : SunGood 526 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good527 : SunGood 527 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good528 : SunGood 528 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good529 : SunGood 529 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good530 : SunGood 530 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good531 : SunGood 531 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good532 : SunGood 532 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good533 : SunGood 533 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good534 : SunGood 534 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good535 : SunGood 535 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good536 : SunGood 536 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good537 : SunGood 537 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good538 : SunGood 538 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good539 : SunGood 539 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good540 : SunGood 540 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good541 : SunGood 541 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good542 : SunGood 542 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good543 : SunGood 543 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good544 : SunGood 544 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good545 : SunGood 545 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good546 : SunGood 546 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good547 : SunGood 547 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good548 : SunGood 548 := Or.inr ⟨4, 0, by norm_num, by norm_num⟩
lemma good549 : SunGood 549 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good550 : SunGood 550 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good551 : SunGood 551 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good552 : SunGood 552 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good553 : SunGood 553 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good554 : SunGood 554 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good555 : SunGood 555 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good556 : SunGood 556 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good557 : SunGood 557 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good558 : SunGood 558 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good559 : SunGood 559 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good560 : SunGood 560 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good561 : SunGood 561 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good562 : SunGood 562 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good563 : SunGood 563 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good564 : SunGood 564 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good565 : SunGood 565 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good566 : SunGood 566 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good567 : SunGood 567 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good568 : SunGood 568 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good569 : SunGood 569 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good570 : SunGood 570 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good571 : SunGood 571 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good572 : SunGood 572 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good573 : SunGood 573 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good574 : SunGood 574 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good575 : SunGood 575 := Or.inl ⟨5, 0, by norm_num, by norm_num⟩
lemma good576 : SunGood 576 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good577 : SunGood 577 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good578 : SunGood 578 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good579 : SunGood 579 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good580 : SunGood 580 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good581 : SunGood 581 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good582 : SunGood 582 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good583 : SunGood 583 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good584 : SunGood 584 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good585 : SunGood 585 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good586 : SunGood 586 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good587 : SunGood 587 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good588 : SunGood 588 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good589 : SunGood 589 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good590 : SunGood 590 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good591 : SunGood 591 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good592 : SunGood 592 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good593 : SunGood 593 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good594 : SunGood 594 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good595 : SunGood 595 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good596 : SunGood 596 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good597 : SunGood 597 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good598 : SunGood 598 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good599 : SunGood 599 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good600 : SunGood 600 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good601 : SunGood 601 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good602 : SunGood 602 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good603 : SunGood 603 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good604 : SunGood 604 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good605 : SunGood 605 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good606 : SunGood 606 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good607 : SunGood 607 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good608 : SunGood 608 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good609 : SunGood 609 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good610 : SunGood 610 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good611 : SunGood 611 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good612 : SunGood 612 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good613 : SunGood 613 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good614 : SunGood 614 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good615 : SunGood 615 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good616 : SunGood 616 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good617 : SunGood 617 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good618 : SunGood 618 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good619 : SunGood 619 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good620 : SunGood 620 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good621 : SunGood 621 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good622 : SunGood 622 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good623 : SunGood 623 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good624 : SunGood 624 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good625 : SunGood 625 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good626 : SunGood 626 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good627 : SunGood 627 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good628 : SunGood 628 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good629 : SunGood 629 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good630 : SunGood 630 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good631 : SunGood 631 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good632 : SunGood 632 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good633 : SunGood 633 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good634 : SunGood 634 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good635 : SunGood 635 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good636 : SunGood 636 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good637 : SunGood 637 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good638 : SunGood 638 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good639 : SunGood 639 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good640 : SunGood 640 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good641 : SunGood 641 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good642 : SunGood 642 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good643 : SunGood 643 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good644 : SunGood 644 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good645 : SunGood 645 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good646 : SunGood 646 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good647 : SunGood 647 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good648 : SunGood 648 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good649 : SunGood 649 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good650 : SunGood 650 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good651 : SunGood 651 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good652 : SunGood 652 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good653 : SunGood 653 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good654 : SunGood 654 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good655 : SunGood 655 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good656 : SunGood 656 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good657 : SunGood 657 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good658 : SunGood 658 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good659 : SunGood 659 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good660 : SunGood 660 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good661 : SunGood 661 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good662 : SunGood 662 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good663 : SunGood 663 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good664 : SunGood 664 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma good665 : SunGood 665 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good666 : SunGood 666 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good667 : SunGood 667 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good668 : SunGood 668 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good669 : SunGood 669 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good670 : SunGood 670 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good671 : SunGood 671 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good672 : SunGood 672 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good673 : SunGood 673 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good674 : SunGood 674 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good675 : SunGood 675 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good676 : SunGood 676 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good677 : SunGood 677 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good678 : SunGood 678 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good679 : SunGood 679 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good680 : SunGood 680 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good681 : SunGood 681 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good682 : SunGood 682 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good683 : SunGood 683 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good684 : SunGood 684 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good685 : SunGood 685 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good686 : SunGood 686 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good687 : SunGood 687 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good688 : SunGood 688 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good689 : SunGood 689 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good690 : SunGood 690 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good691 : SunGood 691 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good692 : SunGood 692 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good693 : SunGood 693 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good694 : SunGood 694 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good695 : SunGood 695 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good696 : SunGood 696 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good697 : SunGood 697 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good698 : SunGood 698 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good699 : SunGood 699 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma good700 : SunGood 700 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good701 : SunGood 701 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good702 : SunGood 702 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good703 : SunGood 703 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good704 : SunGood 704 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good705 : SunGood 705 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good706 : SunGood 706 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good707 : SunGood 707 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good708 : SunGood 708 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good709 : SunGood 709 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good710 : SunGood 710 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good711 : SunGood 711 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good712 : SunGood 712 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good713 : SunGood 713 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good714 : SunGood 714 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good715 : SunGood 715 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good716 : SunGood 716 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good717 : SunGood 717 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good718 : SunGood 718 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good719 : SunGood 719 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good720 : SunGood 720 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good721 : SunGood 721 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma good722 : SunGood 722 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good723 : SunGood 723 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good724 : SunGood 724 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good725 : SunGood 725 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good726 : SunGood 726 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good727 : SunGood 727 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good728 : SunGood 728 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good729 : SunGood 729 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good730 : SunGood 730 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good731 : SunGood 731 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good732 : SunGood 732 := Or.inl ⟨4, 0, by norm_num, by norm_num⟩
lemma good733 : SunGood 733 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good734 : SunGood 734 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good735 : SunGood 735 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good736 : SunGood 736 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good737 : SunGood 737 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good738 : SunGood 738 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good739 : SunGood 739 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good740 : SunGood 740 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good741 : SunGood 741 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good742 : SunGood 742 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good743 : SunGood 743 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good744 : SunGood 744 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good745 : SunGood 745 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good746 : SunGood 746 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good747 : SunGood 747 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good748 : SunGood 748 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good749 : SunGood 749 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good750 : SunGood 750 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good751 : SunGood 751 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good752 : SunGood 752 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good753 : SunGood 753 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good754 : SunGood 754 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good755 : SunGood 755 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good756 : SunGood 756 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good757 : SunGood 757 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good758 : SunGood 758 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good759 : SunGood 759 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good760 : SunGood 760 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good761 : SunGood 761 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good762 : SunGood 762 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good763 : SunGood 763 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good764 : SunGood 764 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good765 : SunGood 765 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good766 : SunGood 766 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good767 : SunGood 767 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good768 : SunGood 768 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good769 : SunGood 769 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good770 : SunGood 770 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good771 : SunGood 771 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good772 : SunGood 772 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good773 : SunGood 773 := Or.inl ⟨3, 0, by norm_num, by norm_num⟩
lemma good774 : SunGood 774 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good775 : SunGood 775 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good776 : SunGood 776 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good777 : SunGood 777 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good778 : SunGood 778 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good779 : SunGood 779 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good780 : SunGood 780 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good781 : SunGood 781 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good782 : SunGood 782 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good783 : SunGood 783 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good784 : SunGood 784 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good785 : SunGood 785 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good786 : SunGood 786 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good787 : SunGood 787 := Or.inr ⟨3, 0, by norm_num, by norm_num⟩
lemma good788 : SunGood 788 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good789 : SunGood 789 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good790 : SunGood 790 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good791 : SunGood 791 := Or.inr ⟨1, 0, by norm_num, by norm_num⟩
lemma good792 : SunGood 792 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good793 : SunGood 793 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩
lemma good794 : SunGood 794 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good795 : SunGood 795 := Or.inl ⟨1, 0, by norm_num, by norm_num⟩
lemma good796 : SunGood 796 := Or.inr ⟨2, 0, by norm_num, by norm_num⟩
lemma good797 : SunGood 797 := Or.inl ⟨2, 0, by norm_num, by norm_num⟩
lemma good798 : SunGood 798 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good799 : SunGood 799 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩
lemma good800 : SunGood 800 := Or.inr ⟨0, 0, by norm_num, by norm_num⟩

lemma sunGood_of_le_800 (n : ℕ) (hn : 1 < n) (hN : n ≤ 800) : SunGood n := by
  interval_cases n
  · exact good2
  · exact good3
  · exact good4
  · exact good5
  · exact good6
  · exact good7
  · exact good8
  · exact good9
  · exact good10
  · exact good11
  · exact good12
  · exact good13
  · exact good14
  · exact good15
  · exact good16
  · exact good17
  · exact good18
  · exact good19
  · exact good20
  · exact good21
  · exact good22
  · exact good23
  · exact good24
  · exact good25
  · exact good26
  · exact good27
  · exact good28
  · exact good29
  · exact good30
  · exact good31
  · exact good32
  · exact good33
  · exact good34
  · exact good35
  · exact good36
  · exact good37
  · exact good38
  · exact good39
  · exact good40
  · exact good41
  · exact good42
  · exact good43
  · exact good44
  · exact good45
  · exact good46
  · exact good47
  · exact good48
  · exact good49
  · exact good50
  · exact good51
  · exact good52
  · exact good53
  · exact good54
  · exact good55
  · exact good56
  · exact good57
  · exact good58
  · exact good59
  · exact good60
  · exact good61
  · exact good62
  · exact good63
  · exact good64
  · exact good65
  · exact good66
  · exact good67
  · exact good68
  · exact good69
  · exact good70
  · exact good71
  · exact good72
  · exact good73
  · exact good74
  · exact good75
  · exact good76
  · exact good77
  · exact good78
  · exact good79
  · exact good80
  · exact good81
  · exact good82
  · exact good83
  · exact good84
  · exact good85
  · exact good86
  · exact good87
  · exact good88
  · exact good89
  · exact good90
  · exact good91
  · exact good92
  · exact good93
  · exact good94
  · exact good95
  · exact good96
  · exact good97
  · exact good98
  · exact good99
  · exact good100
  · exact good101
  · exact good102
  · exact good103
  · exact good104
  · exact good105
  · exact good106
  · exact good107
  · exact good108
  · exact good109
  · exact good110
  · exact good111
  · exact good112
  · exact good113
  · exact good114
  · exact good115
  · exact good116
  · exact good117
  · exact good118
  · exact good119
  · exact good120
  · exact good121
  · exact good122
  · exact good123
  · exact good124
  · exact good125
  · exact good126
  · exact good127
  · exact good128
  · exact good129
  · exact good130
  · exact good131
  · exact good132
  · exact good133
  · exact good134
  · exact good135
  · exact good136
  · exact good137
  · exact good138
  · exact good139
  · exact good140
  · exact good141
  · exact good142
  · exact good143
  · exact good144
  · exact good145
  · exact good146
  · exact good147
  · exact good148
  · exact good149
  · exact good150
  · exact good151
  · exact good152
  · exact good153
  · exact good154
  · exact good155
  · exact good156
  · exact good157
  · exact good158
  · exact good159
  · exact good160
  · exact good161
  · exact good162
  · exact good163
  · exact good164
  · exact good165
  · exact good166
  · exact good167
  · exact good168
  · exact good169
  · exact good170
  · exact good171
  · exact good172
  · exact good173
  · exact good174
  · exact good175
  · exact good176
  · exact good177
  · exact good178
  · exact good179
  · exact good180
  · exact good181
  · exact good182
  · exact good183
  · exact good184
  · exact good185
  · exact good186
  · exact good187
  · exact good188
  · exact good189
  · exact good190
  · exact good191
  · exact good192
  · exact good193
  · exact good194
  · exact good195
  · exact good196
  · exact good197
  · exact good198
  · exact good199
  · exact good200
  · exact good201
  · exact good202
  · exact good203
  · exact good204
  · exact good205
  · exact good206
  · exact good207
  · exact good208
  · exact good209
  · exact good210
  · exact good211
  · exact good212
  · exact good213
  · exact good214
  · exact good215
  · exact good216
  · exact good217
  · exact good218
  · exact good219
  · exact good220
  · exact good221
  · exact good222
  · exact good223
  · exact good224
  · exact good225
  · exact good226
  · exact good227
  · exact good228
  · exact good229
  · exact good230
  · exact good231
  · exact good232
  · exact good233
  · exact good234
  · exact good235
  · exact good236
  · exact good237
  · exact good238
  · exact good239
  · exact good240
  · exact good241
  · exact good242
  · exact good243
  · exact good244
  · exact good245
  · exact good246
  · exact good247
  · exact good248
  · exact good249
  · exact good250
  · exact good251
  · exact good252
  · exact good253
  · exact good254
  · exact good255
  · exact good256
  · exact good257
  · exact good258
  · exact good259
  · exact good260
  · exact good261
  · exact good262
  · exact good263
  · exact good264
  · exact good265
  · exact good266
  · exact good267
  · exact good268
  · exact good269
  · exact good270
  · exact good271
  · exact good272
  · exact good273
  · exact good274
  · exact good275
  · exact good276
  · exact good277
  · exact good278
  · exact good279
  · exact good280
  · exact good281
  · exact good282
  · exact good283
  · exact good284
  · exact good285
  · exact good286
  · exact good287
  · exact good288
  · exact good289
  · exact good290
  · exact good291
  · exact good292
  · exact good293
  · exact good294
  · exact good295
  · exact good296
  · exact good297
  · exact good298
  · exact good299
  · exact good300
  · exact good301
  · exact good302
  · exact good303
  · exact good304
  · exact good305
  · exact good306
  · exact good307
  · exact good308
  · exact good309
  · exact good310
  · exact good311
  · exact good312
  · exact good313
  · exact good314
  · exact good315
  · exact good316
  · exact good317
  · exact good318
  · exact good319
  · exact good320
  · exact good321
  · exact good322
  · exact good323
  · exact good324
  · exact good325
  · exact good326
  · exact good327
  · exact good328
  · exact good329
  · exact good330
  · exact good331
  · exact good332
  · exact good333
  · exact good334
  · exact good335
  · exact good336
  · exact good337
  · exact good338
  · exact good339
  · exact good340
  · exact good341
  · exact good342
  · exact good343
  · exact good344
  · exact good345
  · exact good346
  · exact good347
  · exact good348
  · exact good349
  · exact good350
  · exact good351
  · exact good352
  · exact good353
  · exact good354
  · exact good355
  · exact good356
  · exact good357
  · exact good358
  · exact good359
  · exact good360
  · exact good361
  · exact good362
  · exact good363
  · exact good364
  · exact good365
  · exact good366
  · exact good367
  · exact good368
  · exact good369
  · exact good370
  · exact good371
  · exact good372
  · exact good373
  · exact good374
  · exact good375
  · exact good376
  · exact good377
  · exact good378
  · exact good379
  · exact good380
  · exact good381
  · exact good382
  · exact good383
  · exact good384
  · exact good385
  · exact good386
  · exact good387
  · exact good388
  · exact good389
  · exact good390
  · exact good391
  · exact good392
  · exact good393
  · exact good394
  · exact good395
  · exact good396
  · exact good397
  · exact good398
  · exact good399
  · exact good400
  · exact good401
  · exact good402
  · exact good403
  · exact good404
  · exact good405
  · exact good406
  · exact good407
  · exact good408
  · exact good409
  · exact good410
  · exact good411
  · exact good412
  · exact good413
  · exact good414
  · exact good415
  · exact good416
  · exact good417
  · exact good418
  · exact good419
  · exact good420
  · exact good421
  · exact good422
  · exact good423
  · exact good424
  · exact good425
  · exact good426
  · exact good427
  · exact good428
  · exact good429
  · exact good430
  · exact good431
  · exact good432
  · exact good433
  · exact good434
  · exact good435
  · exact good436
  · exact good437
  · exact good438
  · exact good439
  · exact good440
  · exact good441
  · exact good442
  · exact good443
  · exact good444
  · exact good445
  · exact good446
  · exact good447
  · exact good448
  · exact good449
  · exact good450
  · exact good451
  · exact good452
  · exact good453
  · exact good454
  · exact good455
  · exact good456
  · exact good457
  · exact good458
  · exact good459
  · exact good460
  · exact good461
  · exact good462
  · exact good463
  · exact good464
  · exact good465
  · exact good466
  · exact good467
  · exact good468
  · exact good469
  · exact good470
  · exact good471
  · exact good472
  · exact good473
  · exact good474
  · exact good475
  · exact good476
  · exact good477
  · exact good478
  · exact good479
  · exact good480
  · exact good481
  · exact good482
  · exact good483
  · exact good484
  · exact good485
  · exact good486
  · exact good487
  · exact good488
  · exact good489
  · exact good490
  · exact good491
  · exact good492
  · exact good493
  · exact good494
  · exact good495
  · exact good496
  · exact good497
  · exact good498
  · exact good499
  · exact good500
  · exact good501
  · exact good502
  · exact good503
  · exact good504
  · exact good505
  · exact good506
  · exact good507
  · exact good508
  · exact good509
  · exact good510
  · exact good511
  · exact good512
  · exact good513
  · exact good514
  · exact good515
  · exact good516
  · exact good517
  · exact good518
  · exact good519
  · exact good520
  · exact good521
  · exact good522
  · exact good523
  · exact good524
  · exact good525
  · exact good526
  · exact good527
  · exact good528
  · exact good529
  · exact good530
  · exact good531
  · exact good532
  · exact good533
  · exact good534
  · exact good535
  · exact good536
  · exact good537
  · exact good538
  · exact good539
  · exact good540
  · exact good541
  · exact good542
  · exact good543
  · exact good544
  · exact good545
  · exact good546
  · exact good547
  · exact good548
  · exact good549
  · exact good550
  · exact good551
  · exact good552
  · exact good553
  · exact good554
  · exact good555
  · exact good556
  · exact good557
  · exact good558
  · exact good559
  · exact good560
  · exact good561
  · exact good562
  · exact good563
  · exact good564
  · exact good565
  · exact good566
  · exact good567
  · exact good568
  · exact good569
  · exact good570
  · exact good571
  · exact good572
  · exact good573
  · exact good574
  · exact good575
  · exact good576
  · exact good577
  · exact good578
  · exact good579
  · exact good580
  · exact good581
  · exact good582
  · exact good583
  · exact good584
  · exact good585
  · exact good586
  · exact good587
  · exact good588
  · exact good589
  · exact good590
  · exact good591
  · exact good592
  · exact good593
  · exact good594
  · exact good595
  · exact good596
  · exact good597
  · exact good598
  · exact good599
  · exact good600
  · exact good601
  · exact good602
  · exact good603
  · exact good604
  · exact good605
  · exact good606
  · exact good607
  · exact good608
  · exact good609
  · exact good610
  · exact good611
  · exact good612
  · exact good613
  · exact good614
  · exact good615
  · exact good616
  · exact good617
  · exact good618
  · exact good619
  · exact good620
  · exact good621
  · exact good622
  · exact good623
  · exact good624
  · exact good625
  · exact good626
  · exact good627
  · exact good628
  · exact good629
  · exact good630
  · exact good631
  · exact good632
  · exact good633
  · exact good634
  · exact good635
  · exact good636
  · exact good637
  · exact good638
  · exact good639
  · exact good640
  · exact good641
  · exact good642
  · exact good643
  · exact good644
  · exact good645
  · exact good646
  · exact good647
  · exact good648
  · exact good649
  · exact good650
  · exact good651
  · exact good652
  · exact good653
  · exact good654
  · exact good655
  · exact good656
  · exact good657
  · exact good658
  · exact good659
  · exact good660
  · exact good661
  · exact good662
  · exact good663
  · exact good664
  · exact good665
  · exact good666
  · exact good667
  · exact good668
  · exact good669
  · exact good670
  · exact good671
  · exact good672
  · exact good673
  · exact good674
  · exact good675
  · exact good676
  · exact good677
  · exact good678
  · exact good679
  · exact good680
  · exact good681
  · exact good682
  · exact good683
  · exact good684
  · exact good685
  · exact good686
  · exact good687
  · exact good688
  · exact good689
  · exact good690
  · exact good691
  · exact good692
  · exact good693
  · exact good694
  · exact good695
  · exact good696
  · exact good697
  · exact good698
  · exact good699
  · exact good700
  · exact good701
  · exact good702
  · exact good703
  · exact good704
  · exact good705
  · exact good706
  · exact good707
  · exact good708
  · exact good709
  · exact good710
  · exact good711
  · exact good712
  · exact good713
  · exact good714
  · exact good715
  · exact good716
  · exact good717
  · exact good718
  · exact good719
  · exact good720
  · exact good721
  · exact good722
  · exact good723
  · exact good724
  · exact good725
  · exact good726
  · exact good727
  · exact good728
  · exact good729
  · exact good730
  · exact good731
  · exact good732
  · exact good733
  · exact good734
  · exact good735
  · exact good736
  · exact good737
  · exact good738
  · exact good739
  · exact good740
  · exact good741
  · exact good742
  · exact good743
  · exact good744
  · exact good745
  · exact good746
  · exact good747
  · exact good748
  · exact good749
  · exact good750
  · exact good751
  · exact good752
  · exact good753
  · exact good754
  · exact good755
  · exact good756
  · exact good757
  · exact good758
  · exact good759
  · exact good760
  · exact good761
  · exact good762
  · exact good763
  · exact good764
  · exact good765
  · exact good766
  · exact good767
  · exact good768
  · exact good769
  · exact good770
  · exact good771
  · exact good772
  · exact good773
  · exact good774
  · exact good775
  · exact good776
  · exact good777
  · exact good778
  · exact good779
  · exact good780
  · exact good781
  · exact good782
  · exact good783
  · exact good784
  · exact good785
  · exact good786
  · exact good787
  · exact good788
  · exact good789
  · exact good790
  · exact good791
  · exact good792
  · exact good793
  · exact good794
  · exact good795
  · exact good796
  · exact good797
  · exact good798
  · exact good799
  · exact good800
