import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

unsafe def A301376_conjecture (n : ℕ) (hn : n > 0) : a n > 0 :=
  A301376_conjecture n hn
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · exact (h_even (by decide : Even 0)).elim
    · apply a_pos_of_exists 1 1 0 0 0 0 <;> decide
    · exact (h_even (by decide : Even 2)).elim
    · apply a_pos_of_exists 3 1 0 2 2 0 <;> decide
    · exact (h_even (by decide : Even 4)).elim
    · apply a_pos_of_exists 5 4 0 0 3 2 <;> decide
    · exact (h_even (by decide : Even 6)).elim
    · apply a_pos_of_exists 7 2 0 3 6 1 <;> decide
    · exact (h_even (by decide : Even 8)).elim
    · apply a_pos_of_exists 9 1 0 4 8 0 <;> decide
    · exact (h_even (by decide : Even 10)).elim
    · apply a_pos_of_exists 11 2 0 6 9 1 <;> decide
    · exact (h_even (by decide : Even 12)).elim
    · apply a_pos_of_exists 13 4 0 3 12 2 <;> decide
    · exact (h_even (by decide : Even 14)).elim
    · apply a_pos_of_exists 15 2 0 5 14 1 <;> decide
    · exact (h_even (by decide : Even 16)).elim
    · apply a_pos_of_exists 17 1 0 12 12 0 <;> decide
    · exact (h_even (by decide : Even 18)).elim
    · apply a_pos_of_exists 19 1 0 6 18 0 <;> decide
    · exact (h_even (by decide : Even 20)).elim
    · apply a_pos_of_exists 21 4 0 5 20 2 <;> decide
    · exact (h_even (by decide : Even 22)).elim
    · apply a_pos_of_exists 23 10 2 5 20 3 <;> decide
    · exact (h_even (by decide : Even 24)).elim
    · apply a_pos_of_exists 25 10 2 11 20 3 <;> decide
    · exact (h_even (by decide : Even 26)).elim
    · apply a_pos_of_exists 27 2 0 7 26 1 <;> decide
    · exact (h_even (by decide : Even 28)).elim
    · apply a_pos_of_exists 29 16 0 3 24 4 <;> decide
    · exact (h_even (by decide : Even 30)).elim
    · apply a_pos_of_exists 31 10 2 4 29 3 <;> decide
    · exact (h_even (by decide : Even 32)).elim
    · apply a_pos_of_exists 33 1 0 8 32 0 <;> decide
    · exact (h_even (by decide : Even 34)).elim
    · apply a_pos_of_exists 35 1 0 18 30 0 <;> decide
    · exact (h_even (by decide : Even 36)).elim
    · apply a_pos_of_exists 37 8 0 3 36 3 <;> decide
    · exact (h_even (by decide : Even 38)).elim
    · apply a_pos_of_exists 39 2 0 19 34 1 <;> decide
    · exact (h_even (by decide : Even 40)).elim
    · apply a_pos_of_exists 41 4 0 12 39 2 <;> decide
    · exact (h_even (by decide : Even 42)).elim
    · apply a_pos_of_exists 43 2 0 9 42 1 <;> decide
    · exact (h_even (by decide : Even 44)).elim
    · apply a_pos_of_exists 45 4 0 28 35 2 <;> decide
    · exact (h_even (by decide : Even 46)).elim
    · apply a_pos_of_exists 47 2 0 21 42 1 <;> decide
    · exact (h_even (by decide : Even 48)).elim
    · apply a_pos_of_exists 49 4 0 9 48 2 <;> decide
    · exact (h_even (by decide : Even 50)).elim
    · apply a_pos_of_exists 51 1 0 10 50 0 <;> decide
    · exact (h_even (by decide : Even 52)).elim
    · apply a_pos_of_exists 53 8 0 12 51 3 <;> decide
    · exact (h_even (by decide : Even 54)).elim
    · apply a_pos_of_exists 55 20 4 20 47 4 <;> decide
    · exact (h_even (by decide : Even 56)).elim
    · apply a_pos_of_exists 57 4 0 23 52 2 <;> decide
    · exact (h_even (by decide : Even 58)).elim
    · apply a_pos_of_exists 59 20 4 16 53 4 <;> decide
    · exact (h_even (by decide : Even 60)).elim
    · apply a_pos_of_exists 61 10 2 41 44 3 <;> decide
    · exact (h_even (by decide : Even 62)).elim
    · apply a_pos_of_exists 63 2 0 11 62 1 <;> decide
    · exact (h_even (by decide : Even 64)).elim
    · apply a_pos_of_exists 65 10 2 5 64 3 <;> decide
    · exact (h_even (by decide : Even 66)).elim
    · apply a_pos_of_exists 67 10 2 17 64 3 <;> decide
    · exact (h_even (by decide : Even 68)).elim
    · apply a_pos_of_exists 69 4 0 11 68 2 <;> decide
    · exact (h_even (by decide : Even 70)).elim
    · apply a_pos_of_exists 71 10 2 29 64 3 <;> decide
    · exact (h_even (by decide : Even 72)).elim
    · apply a_pos_of_exists 73 1 0 12 72 0 <;> decide
    · exact (h_even (by decide : Even 74)).elim
    · apply a_pos_of_exists 75 10 2 36 65 3 <;> decide
    · exact (h_even (by decide : Even 76)).elim
    · apply a_pos_of_exists 77 4 0 27 72 2 <;> decide
    · exact (h_even (by decide : Even 78)).elim
    · apply a_pos_of_exists 79 10 2 19 76 3 <;> decide
    · exact (h_even (by decide : Even 80)).elim
    · apply a_pos_of_exists 81 1 0 28 76 0 <;> decide
    · exact (h_even (by decide : Even 82)).elim
    · apply a_pos_of_exists 83 2 0 18 81 1 <;> decide
    · exact (h_even (by decide : Even 84)).elim
    · apply a_pos_of_exists 85 4 0 45 72 2 <;> decide
    · exact (h_even (by decide : Even 86)).elim
    · apply a_pos_of_exists 87 2 0 13 86 1 <;> decide
    · exact (h_even (by decide : Even 88)).elim
    · apply a_pos_of_exists 89 8 0 36 81 3 <;> decide
    · exact (h_even (by decide : Even 90)).elim
    · apply a_pos_of_exists 91 10 2 16 89 3 <;> decide
    · exact (h_even (by decide : Even 92)).elim
    · apply a_pos_of_exists 93 4 0 13 92 2 <;> decide
    · exact (h_even (by decide : Even 94)).elim
    · apply a_pos_of_exists 95 20 4 47 80 4 <;> decide
    · exact (h_even (by decide : Even 96)).elim
    · apply a_pos_of_exists 97 10 2 29 92 3 <;> decide
    · exact (h_even (by decide : Even 98)).elim
    · apply a_pos_of_exists 99 1 0 14 98 0 <;> decide
    · exact (h_even (by decide : Even 100)).elim
    · apply a_pos_of_exists 101 16 0 12 99 4 <;> decide
    · exact (h_even (by decide : Even 102)).elim
    · apply a_pos_of_exists 103 20 4 28 97 4 <;> decide
    · exact (h_even (by decide : Even 104)).elim
    · apply a_pos_of_exists 105 1 0 32 100 0 <;> decide
    · exact (h_even (by decide : Even 106)).elim
    · apply a_pos_of_exists 107 10 2 23 104 3 <;> decide
    · exact (h_even (by decide : Even 108)).elim
    · apply a_pos_of_exists 109 8 0 51 96 3 <;> decide
    · exact (h_even (by decide : Even 110)).elim
    · apply a_pos_of_exists 111 2 0 46 101 1 <;> decide
    · exact (h_even (by decide : Even 112)).elim
    · apply a_pos_of_exists 113 4 0 33 108 2 <;> decide
    · exact (h_even (by decide : Even 114)).elim
    · apply a_pos_of_exists 115 2 0 15 114 1 <;> decide
    · exact (h_even (by decide : Even 116)).elim
    · apply a_pos_of_exists 117 4 0 77 88 2 <;> decide
    · exact (h_even (by decide : Even 118)).elim
    · apply a_pos_of_exists 119 2 0 66 99 1 <;> decide
    · exact (h_even (by decide : Even 120)).elim
    · apply a_pos_of_exists 121 4 0 15 120 2 <;> decide
    · exact (h_even (by decide : Even 122)).elim
    · apply a_pos_of_exists 123 2 0 22 121 1 <;> decide
    · exact (h_even (by decide : Even 124)).elim
    · apply a_pos_of_exists 125 34 10 40 113 4 <;> decide
    · exact (h_even (by decide : Even 126)).elim
    · apply a_pos_of_exists 127 10 2 20 125 3 <;> decide
    · exact (h_even (by decide : Even 128)).elim
    · apply a_pos_of_exists 129 1 0 16 128 0 <;> decide
    · exact (h_even (by decide : Even 130)).elim
    · apply a_pos_of_exists 131 10 2 41 124 3 <;> decide
    · exact (h_even (by decide : Even 132)).elim
    · apply a_pos_of_exists 133 10 2 47 124 3 <;> decide
    · exact (h_even (by decide : Even 134)).elim
    · apply a_pos_of_exists 135 10 2 61 120 3 <;> decide
    · exact (h_even (by decide : Even 136)).elim
    · apply a_pos_of_exists 137 10 2 13 136 3 <;> decide
    · exact (h_even (by decide : Even 138)).elim
    · apply a_pos_of_exists 139 34 10 41 128 4 <;> decide
    · exact (h_even (by decide : Even 140)).elim
    · apply a_pos_of_exists 141 4 0 37 136 2 <;> decide
    · exact (h_even (by decide : Even 142)).elim
    · apply a_pos_of_exists 143 10 2 32 139 3 <;> decide
    · exact (h_even (by decide : Even 144)).elim
    · apply a_pos_of_exists 145 1 0 60 132 0 <;> decide
    · exact (h_even (by decide : Even 146)).elim
    · apply a_pos_of_exists 147 1 0 38 142 0 <;> decide
    · exact (h_even (by decide : Even 148)).elim
    · apply a_pos_of_exists 149 4 0 24 147 2 <;> decide
    · exact (h_even (by decide : Even 150)).elim
    · apply a_pos_of_exists 151 2 0 54 141 1 <;> decide
    · exact (h_even (by decide : Even 152)).elim
    · apply a_pos_of_exists 153 4 0 17 152 2 <;> decide
    · exact (h_even (by decide : Even 154)).elim
    · apply a_pos_of_exists 155 2 0 39 150 1 <;> decide
    · exact (h_even (by decide : Even 156)).elim
    · apply a_pos_of_exists 157 10 2 64 143 3 <;> decide
    · exact (h_even (by decide : Even 158)).elim
    · apply a_pos_of_exists 159 10 2 29 156 3 <;> decide
    · exact (h_even (by decide : Even 160)).elim
    · apply a_pos_of_exists 161 1 0 72 144 0 <;> decide
    · exact (h_even (by decide : Even 162)).elim
    · apply a_pos_of_exists 163 1 0 18 162 0 <;> decide
    · exact (h_even (by decide : Even 164)).elim
    · apply a_pos_of_exists 165 8 0 56 155 3 <;> decide
    · exact (h_even (by decide : Even 166)).elim
    · apply a_pos_of_exists 167 10 2 56 157 3 <;> decide
    · exact (h_even (by decide : Even 168)).elim
    · apply a_pos_of_exists 169 16 0 9 168 4 <;> decide
    · exact (h_even (by decide : Even 170)).elim
    · apply a_pos_of_exists 171 2 0 26 169 1 <;> decide
    · exact (h_even (by decide : Even 172)).elim
    · apply a_pos_of_exists 173 10 2 44 167 3 <;> decide
    · exact (h_even (by decide : Even 174)).elim
    · apply a_pos_of_exists 175 20 4 25 172 4 <;> decide
    · exact (h_even (by decide : Even 176)).elim
    · apply a_pos_of_exists 177 4 0 97 148 2 <;> decide
    · exact (h_even (by decide : Even 178)).elim
    · apply a_pos_of_exists 179 1 0 42 174 0 <;> decide
    · exact (h_even (by decide : Even 180)).elim
    · apply a_pos_of_exists 181 10 2 41 176 3 <;> decide
    · exact (h_even (by decide : Even 182)).elim
    · apply a_pos_of_exists 183 2 0 19 182 1 <;> decide
    · exact (h_even (by decide : Even 184)).elim
    · apply a_pos_of_exists 185 10 2 85 164 3 <;> decide
    · exact (h_even (by decide : Even 186)).elim
    · apply a_pos_of_exists 187 20 4 68 173 4 <;> decide
    · exact (h_even (by decide : Even 188)).elim
    · apply a_pos_of_exists 189 4 0 19 188 2 <;> decide
    · exact (h_even (by decide : Even 190)).elim
    · apply a_pos_of_exists 191 20 4 47 184 4 <;> decide
    · exact (h_even (by decide : Even 192)).elim
    · apply a_pos_of_exists 193 20 4 128 143 4 <;> decide
    · exact (h_even (by decide : Even 194)).elim
    · apply a_pos_of_exists 195 1 0 70 182 0 <;> decide
    · exact (h_even (by decide : Even 196)).elim
    · apply a_pos_of_exists 197 10 2 17 196 3 <;> decide
    · exact (h_even (by decide : Even 198)).elim
    · apply a_pos_of_exists 199 20 4 44 193 4 <;> decide
    · exact (h_even (by decide : Even 200)).elim
    · apply a_pos_of_exists 201 1 0 20 200 0 <;> decide
    · exact (h_even (by decide : Even 202)).elim
    · apply a_pos_of_exists 203 10 2 68 191 3 <;> decide
    · exact (h_even (by decide : Even 204)).elim
    · apply a_pos_of_exists 205 20 4 20 203 4 <;> decide
    · exact (h_even (by decide : Even 206)).elim
    · apply a_pos_of_exists 207 20 4 72 193 4 <;> decide
    · exact (h_even (by decide : Even 208)).elim
    · apply a_pos_of_exists 209 10 2 104 181 3 <;> decide
    · exact (h_even (by decide : Even 210)).elim
    · apply a_pos_of_exists 211 10 2 136 161 3 <;> decide
    · exact (h_even (by decide : Even 212)).elim
    · apply a_pos_of_exists 213 8 0 19 212 3 <;> decide
    · exact (h_even (by decide : Even 214)).elim
    · apply a_pos_of_exists 215 10 2 40 211 3 <;> decide
    · exact (h_even (by decide : Even 216)).elim
    · apply a_pos_of_exists 217 10 2 61 208 3 <;> decide
    · exact (h_even (by decide : Even 218)).elim
    · apply a_pos_of_exists 219 10 2 79 204 3 <;> decide
    · exact (h_even (by decide : Even 220)).elim
    · apply a_pos_of_exists 221 20 4 5 220 4 <;> decide
    · exact (h_even (by decide : Even 222)).elim
    · apply a_pos_of_exists 223 2 0 21 222 1 <;> decide
    · exact (h_even (by decide : Even 224)).elim
    · apply a_pos_of_exists 225 4 0 47 220 2 <;> decide
    · exact (h_even (by decide : Even 226)).elim
    · apply a_pos_of_exists 227 2 0 30 225 1 <;> decide
    · exact (h_even (by decide : Even 228)).elim
    · apply a_pos_of_exists 229 4 0 21 228 2 <;> decide
    · exact (h_even (by decide : Even 230)).elim
    · apply a_pos_of_exists 231 2 0 94 211 1 <;> decide
    · exact (h_even (by decide : Even 232)).elim
    · apply a_pos_of_exists 233 1 0 48 228 0 <;> decide
    · exact (h_even (by decide : Even 234)).elim
    · apply a_pos_of_exists 235 34 10 88 215 4 <;> decide
    · exact (h_even (by decide : Even 236)).elim
    · apply a_pos_of_exists 237 4 0 68 227 2 <;> decide
    · exact (h_even (by decide : Even 238)).elim
    · apply a_pos_of_exists 239 34 10 13 236 4 <;> decide
    · exact (h_even (by decide : Even 240)).elim
    · apply a_pos_of_exists 241 10 2 116 211 3 <;> decide
    · exact (h_even (by decide : Even 242)).elim
    · apply a_pos_of_exists 243 1 0 22 242 0 <;> decide
    · exact (h_even (by decide : Even 244)).elim
    · apply a_pos_of_exists 245 10 2 65 236 3 <;> decide
    · exact (h_even (by decide : Even 246)).elim
    · apply a_pos_of_exists 247 10 2 37 244 3 <;> decide
    · exact (h_even (by decide : Even 248)).elim
    · apply a_pos_of_exists 249 8 0 49 244 3 <;> decide
    · exact (h_even (by decide : Even 250)).elim
    · apply a_pos_of_exists 251 10 2 76 239 3 <;> decide
    · exact (h_even (by decide : Even 252)).elim
    · apply a_pos_of_exists 253 8 0 21 252 3 <;> decide
    · exact (h_even (by decide : Even 254)).elim
    · apply a_pos_of_exists 255 10 2 164 195 3 <;> decide
    · exact (h_even (by decide : Even 256)).elim
    · apply a_pos_of_exists 257 10 2 44 253 3 <;> decide
    · exact (h_even (by decide : Even 258)).elim
    · apply a_pos_of_exists 259 2 0 81 246 1 <;> decide
    · exact (h_even (by decide : Even 260)).elim
    · apply a_pos_of_exists 261 4 0 32 259 2 <;> decide
    · exact (h_even (by decide : Even 262)).elim
    · apply a_pos_of_exists 263 2 0 51 258 1 <;> decide
    · exact (h_even (by decide : Even 264)).elim
    · apply a_pos_of_exists 265 4 0 72 255 2 <;> decide
    · exact (h_even (by decide : Even 266)).elim
    · apply a_pos_of_exists 267 2 0 23 266 1 <;> decide
    · exact (h_even (by decide : Even 268)).elim
    · apply a_pos_of_exists 269 8 0 51 264 3 <;> decide
    · exact (h_even (by decide : Even 270)).elim
    · apply a_pos_of_exists 271 34 10 19 268 4 <;> decide
    · exact (h_even (by decide : Even 272)).elim
    · apply a_pos_of_exists 273 1 0 52 268 0 <;> decide
    · exact (h_even (by decide : Even 274)).elim
    · apply a_pos_of_exists 275 10 2 89 260 3 <;> decide
    · exact (h_even (by decide : Even 276)).elim
    · apply a_pos_of_exists 277 10 2 80 265 3 <;> decide
    · exact (h_even (by decide : Even 278)).elim
    · apply a_pos_of_exists 279 2 0 74 269 1 <;> decide
    · exact (h_even (by decide : Even 280)).elim
    · apply a_pos_of_exists 281 10 2 139 244 3 <;> decide
    · exact (h_even (by decide : Even 282)).elim
    · apply a_pos_of_exists 283 10 2 32 281 3 <;> decide
    · exact (h_even (by decide : Even 284)).elim
    · apply a_pos_of_exists 285 4 0 53 280 2 <;> decide
    · exact (h_even (by decide : Even 286)).elim
    · apply a_pos_of_exists 287 10 2 91 272 3 <;> decide
    · exact (h_even (by decide : Even 288)).elim
    · apply a_pos_of_exists 289 1 0 24 288 0 <;> decide
    · exact (h_even (by decide : Even 290)).elim
    · apply a_pos_of_exists 291 1 0 86 278 0 <;> decide
    · exact (h_even (by decide : Even 292)).elim
    · apply a_pos_of_exists 293 20 4 13 292 4 <;> decide
    · exact (h_even (by decide : Even 294)).elim
    · apply a_pos_of_exists 295 10 2 139 260 3 <;> decide
    · exact (h_even (by decide : Even 296)).elim
    · apply a_pos_of_exists 297 1 0 128 268 0 <;> decide
    · exact (h_even (by decide : Even 298)).elim
    · apply a_pos_of_exists 299 10 2 41 296 3 <;> decide
    · sorry
