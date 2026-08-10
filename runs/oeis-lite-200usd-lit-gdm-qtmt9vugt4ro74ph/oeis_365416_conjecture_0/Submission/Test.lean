import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Nat
lemma coprime_252_of_prime (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :
    q % 252 ≠ 0 ∧ Nat.Coprime q 252 := by
  have h_gcd : q.gcd 252 = 1 := by
    by_contra hc
    have h_dvd : q.gcd 252 ∣ q := q.gcd_dvd_left 252
    have h_dvd2 : q.gcd 252 ∣ 252 := q.gcd_dvd_right 252
    rcases hq.eq_one_or_self_of_dvd _ h_dvd with h1 | h2
    · exact hc h1
    · have hq_dvd_252 : q ∣ 252 := h2 ▸ h_dvd2
      have hq252 : q ≤ 252 := Nat.le_of_dvd (by decide) hq_dvd_252
      interval_cases q
      · exact (show ¬ Nat.Prime 0 by decide) hq
      · exact (show ¬ Nat.Prime 1 by decide) hq
      · exact hq2 rfl
      · exact hq3 rfl
      · exact (show ¬ Nat.Prime 4 by decide) hq
      · exact (show ¬ 5 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 6 by decide) hq
      · exact hq7 rfl
      · exact (show ¬ Nat.Prime 8 by decide) hq
      · exact (show ¬ Nat.Prime 9 by decide) hq
      · exact (show ¬ Nat.Prime 10 by decide) hq
      · exact (show ¬ 11 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 12 by decide) hq
      · exact (show ¬ 13 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 14 by decide) hq
      · exact (show ¬ Nat.Prime 15 by decide) hq
      · exact (show ¬ Nat.Prime 16 by decide) hq
      · exact (show ¬ 17 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 18 by decide) hq
      · exact (show ¬ 19 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 20 by decide) hq
      · exact (show ¬ Nat.Prime 21 by decide) hq
      · exact (show ¬ Nat.Prime 22 by decide) hq
      · exact (show ¬ 23 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 24 by decide) hq
      · exact (show ¬ Nat.Prime 25 by decide) hq
      · exact (show ¬ Nat.Prime 26 by decide) hq
      · exact (show ¬ Nat.Prime 27 by decide) hq
      · exact (show ¬ Nat.Prime 28 by decide) hq
      · exact (show ¬ 29 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 30 by decide) hq
      · exact (show ¬ 31 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 32 by decide) hq
      · exact (show ¬ Nat.Prime 33 by decide) hq
      · exact (show ¬ Nat.Prime 34 by decide) hq
      · exact (show ¬ Nat.Prime 35 by decide) hq
      · exact (show ¬ Nat.Prime 36 by decide) hq
      · exact (show ¬ 37 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 38 by decide) hq
      · exact (show ¬ Nat.Prime 39 by decide) hq
      · exact (show ¬ Nat.Prime 40 by decide) hq
      · exact (show ¬ 41 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 42 by decide) hq
      · exact (show ¬ 43 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 44 by decide) hq
      · exact (show ¬ Nat.Prime 45 by decide) hq
      · exact (show ¬ Nat.Prime 46 by decide) hq
      · exact (show ¬ 47 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 48 by decide) hq
      · exact (show ¬ Nat.Prime 49 by decide) hq
      · exact (show ¬ Nat.Prime 50 by decide) hq
      · exact (show ¬ Nat.Prime 51 by decide) hq
      · exact (show ¬ Nat.Prime 52 by decide) hq
      · exact (show ¬ 53 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 54 by decide) hq
      · exact (show ¬ Nat.Prime 55 by decide) hq
      · exact (show ¬ Nat.Prime 56 by decide) hq
      · exact (show ¬ Nat.Prime 57 by decide) hq
      · exact (show ¬ Nat.Prime 58 by decide) hq
      · exact (show ¬ 59 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 60 by decide) hq
      · exact (show ¬ 61 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 62 by decide) hq
      · exact (show ¬ Nat.Prime 63 by decide) hq
      · exact (show ¬ Nat.Prime 64 by decide) hq
      · exact (show ¬ Nat.Prime 65 by decide) hq
      · exact (show ¬ Nat.Prime 66 by decide) hq
      · exact (show ¬ 67 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 68 by decide) hq
      · exact (show ¬ Nat.Prime 69 by decide) hq
      · exact (show ¬ Nat.Prime 70 by decide) hq
      · exact (show ¬ 71 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 72 by decide) hq
      · exact (show ¬ 73 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 74 by decide) hq
      · exact (show ¬ Nat.Prime 75 by decide) hq
      · exact (show ¬ Nat.Prime 76 by decide) hq
      · exact (show ¬ Nat.Prime 77 by decide) hq
      · exact (show ¬ Nat.Prime 78 by decide) hq
      · exact (show ¬ 79 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 80 by decide) hq
      · exact (show ¬ Nat.Prime 81 by decide) hq
      · exact (show ¬ Nat.Prime 82 by decide) hq
      · exact (show ¬ 83 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 84 by decide) hq
      · exact (show ¬ Nat.Prime 85 by decide) hq
      · exact (show ¬ Nat.Prime 86 by decide) hq
      · exact (show ¬ Nat.Prime 87 by decide) hq
      · exact (show ¬ Nat.Prime 88 by decide) hq
      · exact (show ¬ 89 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 90 by decide) hq
      · exact (show ¬ Nat.Prime 91 by decide) hq
      · exact (show ¬ Nat.Prime 92 by decide) hq
      · exact (show ¬ Nat.Prime 93 by decide) hq
      · exact (show ¬ Nat.Prime 94 by decide) hq
      · exact (show ¬ Nat.Prime 95 by decide) hq
      · exact (show ¬ Nat.Prime 96 by decide) hq
      · exact (show ¬ 97 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 98 by decide) hq
      · exact (show ¬ Nat.Prime 99 by decide) hq
      · exact (show ¬ Nat.Prime 100 by decide) hq
      · exact (show ¬ 101 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 102 by decide) hq
      · exact (show ¬ 103 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 104 by decide) hq
      · exact (show ¬ Nat.Prime 105 by decide) hq
      · exact (show ¬ Nat.Prime 106 by decide) hq
      · exact (show ¬ 107 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 108 by decide) hq
      · exact (show ¬ 109 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 110 by decide) hq
      · exact (show ¬ Nat.Prime 111 by decide) hq
      · exact (show ¬ Nat.Prime 112 by decide) hq
      · exact (show ¬ 113 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 114 by decide) hq
      · exact (show ¬ Nat.Prime 115 by decide) hq
      · exact (show ¬ Nat.Prime 116 by decide) hq
      · exact (show ¬ Nat.Prime 117 by decide) hq
      · exact (show ¬ Nat.Prime 118 by decide) hq
      · exact (show ¬ Nat.Prime 119 by decide) hq
      · exact (show ¬ Nat.Prime 120 by decide) hq
      · exact (show ¬ Nat.Prime 121 by decide) hq
      · exact (show ¬ Nat.Prime 122 by decide) hq
      · exact (show ¬ Nat.Prime 123 by decide) hq
      · exact (show ¬ Nat.Prime 124 by decide) hq
      · exact (show ¬ Nat.Prime 125 by decide) hq
      · exact (show ¬ Nat.Prime 126 by decide) hq
      · exact (show ¬ 127 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 128 by decide) hq
      · exact (show ¬ Nat.Prime 129 by decide) hq
      · exact (show ¬ Nat.Prime 130 by decide) hq
      · exact (show ¬ 131 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 132 by decide) hq
      · exact (show ¬ Nat.Prime 133 by decide) hq
      · exact (show ¬ Nat.Prime 134 by decide) hq
      · exact (show ¬ Nat.Prime 135 by decide) hq
      · exact (show ¬ Nat.Prime 136 by decide) hq
      · exact (show ¬ 137 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 138 by decide) hq
      · exact (show ¬ 139 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 140 by decide) hq
      · exact (show ¬ Nat.Prime 141 by decide) hq
      · exact (show ¬ Nat.Prime 142 by decide) hq
      · exact (show ¬ Nat.Prime 143 by decide) hq
      · exact (show ¬ Nat.Prime 144 by decide) hq
      · exact (show ¬ Nat.Prime 145 by decide) hq
      · exact (show ¬ Nat.Prime 146 by decide) hq
      · exact (show ¬ Nat.Prime 147 by decide) hq
      · exact (show ¬ Nat.Prime 148 by decide) hq
      · exact (show ¬ 149 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 150 by decide) hq
      · exact (show ¬ 151 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 152 by decide) hq
      · exact (show ¬ Nat.Prime 153 by decide) hq
      · exact (show ¬ Nat.Prime 154 by decide) hq
      · exact (show ¬ Nat.Prime 155 by decide) hq
      · exact (show ¬ Nat.Prime 156 by decide) hq
      · exact (show ¬ 157 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 158 by decide) hq
      · exact (show ¬ Nat.Prime 159 by decide) hq
      · exact (show ¬ Nat.Prime 160 by decide) hq
      · exact (show ¬ Nat.Prime 161 by decide) hq
      · exact (show ¬ Nat.Prime 162 by decide) hq
      · exact (show ¬ 163 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 164 by decide) hq
      · exact (show ¬ Nat.Prime 165 by decide) hq
      · exact (show ¬ Nat.Prime 166 by decide) hq
      · exact (show ¬ 167 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 168 by decide) hq
      · exact (show ¬ Nat.Prime 169 by decide) hq
      · exact (show ¬ Nat.Prime 170 by decide) hq
      · exact (show ¬ Nat.Prime 171 by decide) hq
      · exact (show ¬ Nat.Prime 172 by decide) hq
      · exact (show ¬ 173 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 174 by decide) hq
      · exact (show ¬ Nat.Prime 175 by decide) hq
      · exact (show ¬ Nat.Prime 176 by decide) hq
      · exact (show ¬ Nat.Prime 177 by decide) hq
      · exact (show ¬ Nat.Prime 178 by decide) hq
      · exact (show ¬ 179 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 180 by decide) hq
      · exact (show ¬ 181 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 182 by decide) hq
      · exact (show ¬ Nat.Prime 183 by decide) hq
      · exact (show ¬ Nat.Prime 184 by decide) hq
      · exact (show ¬ Nat.Prime 185 by decide) hq
      · exact (show ¬ Nat.Prime 186 by decide) hq
      · exact (show ¬ Nat.Prime 187 by decide) hq
      · exact (show ¬ Nat.Prime 188 by decide) hq
      · exact (show ¬ Nat.Prime 189 by decide) hq
      · exact (show ¬ Nat.Prime 190 by decide) hq
      · exact (show ¬ 191 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 192 by decide) hq
      · exact (show ¬ 193 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 194 by decide) hq
      · exact (show ¬ Nat.Prime 195 by decide) hq
      · exact (show ¬ Nat.Prime 196 by decide) hq
      · exact (show ¬ 197 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 198 by decide) hq
      · exact (show ¬ 199 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 200 by decide) hq
      · exact (show ¬ Nat.Prime 201 by decide) hq
      · exact (show ¬ Nat.Prime 202 by decide) hq
      · exact (show ¬ Nat.Prime 203 by decide) hq
      · exact (show ¬ Nat.Prime 204 by decide) hq
      · exact (show ¬ Nat.Prime 205 by decide) hq
      · exact (show ¬ Nat.Prime 206 by decide) hq
      · exact (show ¬ Nat.Prime 207 by decide) hq
      · exact (show ¬ Nat.Prime 208 by decide) hq
      · exact (show ¬ Nat.Prime 209 by decide) hq
      · exact (show ¬ Nat.Prime 210 by decide) hq
      · exact (show ¬ 211 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 212 by decide) hq
      · exact (show ¬ Nat.Prime 213 by decide) hq
      · exact (show ¬ Nat.Prime 214 by decide) hq
      · exact (show ¬ Nat.Prime 215 by decide) hq
      · exact (show ¬ Nat.Prime 216 by decide) hq
      · exact (show ¬ Nat.Prime 217 by decide) hq
      · exact (show ¬ Nat.Prime 218 by decide) hq
      · exact (show ¬ Nat.Prime 219 by decide) hq
      · exact (show ¬ Nat.Prime 220 by decide) hq
      · exact (show ¬ Nat.Prime 221 by decide) hq
      · exact (show ¬ Nat.Prime 222 by decide) hq
      · exact (show ¬ 223 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 224 by decide) hq
      · exact (show ¬ Nat.Prime 225 by decide) hq
      · exact (show ¬ Nat.Prime 226 by decide) hq
      · exact (show ¬ 227 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 228 by decide) hq
      · exact (show ¬ 229 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 230 by decide) hq
      · exact (show ¬ Nat.Prime 231 by decide) hq
      · exact (show ¬ Nat.Prime 232 by decide) hq
      · exact (show ¬ 233 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 234 by decide) hq
      · exact (show ¬ Nat.Prime 235 by decide) hq
      · exact (show ¬ Nat.Prime 236 by decide) hq
      · exact (show ¬ Nat.Prime 237 by decide) hq
      · exact (show ¬ Nat.Prime 238 by decide) hq
      · exact (show ¬ 239 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 240 by decide) hq
      · exact (show ¬ 241 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 242 by decide) hq
      · exact (show ¬ Nat.Prime 243 by decide) hq
      · exact (show ¬ Nat.Prime 244 by decide) hq
      · exact (show ¬ Nat.Prime 245 by decide) hq
      · exact (show ¬ Nat.Prime 246 by decide) hq
      · exact (show ¬ Nat.Prime 247 by decide) hq
      · exact (show ¬ Nat.Prime 248 by decide) hq
      · exact (show ¬ Nat.Prime 249 by decide) hq
      · exact (show ¬ Nat.Prime 250 by decide) hq
      · exact (show ¬ 251 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 252 by decide) hq
  have h_mod : q % 252 ≠ 0 := by
    intro hc
    have : 252 ∣ q := Nat.dvd_of_mod_eq_zero hc
    have : q.gcd 252 = 252 := Nat.gcd_eq_right this
    omega
  exact ⟨h_mod, h_gcd⟩
lemma pow_six_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) : (q : ZMod 252) ^ 6 = 1 := by
  set r := q % 252
  have hr_lt : r < 252 := Nat.mod_lt q (by decide)
  have q_mod : q % 252 = r := rfl
  interval_cases r
  · exfalso
    have h_gcd_dvd : 252 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 252 ∣ 252 := by decide
      have h_g_dvd_r : 252 ∣ 0 := by decide
      have h_g_dvd_q : 252 ∣ q := by
        have : q = 252 * (q / 252) + 0 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 252 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 1 := by
      have : q % 252 = 1 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 2 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 2 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 3 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 3 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 4 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 4 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 5 := by
      have : q % 252 = 5 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 6 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 6 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 7 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 7 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 8 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 8 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 9 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 9 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 10 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 10 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 11 := by
      have : q % 252 = 11 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 12 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 12 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 13 := by
      have : q % 252 = 13 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 14 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 14 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 15 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 15 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 16 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 16 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 17 := by
      have : q % 252 = 17 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 18 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 18 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 19 := by
      have : q % 252 = 19 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 20 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 20 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 21 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 21 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 22 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 22 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 23 := by
      have : q % 252 = 23 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 24 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 24 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 25 := by
      have : q % 252 = 25 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 26 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 26 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 27 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 27 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 28 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 28 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 29 := by
      have : q % 252 = 29 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 30 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 30 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 31 := by
      have : q % 252 = 31 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 32 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 32 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 33 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 33 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 34 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 34 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 35 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 35 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 36 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 36 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 37 := by
      have : q % 252 = 37 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 38 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 38 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 39 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 39 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 40 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 40 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 41 := by
      have : q % 252 = 41 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 42 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 42 ∣ 252 := by decide
      have h_g_dvd_r : 42 ∣ 42 := by decide
      have h_g_dvd_q : 42 ∣ q := by
        have : q = 252 * (q / 252) + 42 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 42 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 43 := by
      have : q % 252 = 43 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 44 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 44 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 45 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 45 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 46 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 46 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 47 := by
      have : q % 252 = 47 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 48 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 48 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 49 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 49 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 50 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 50 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 51 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 51 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 52 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 52 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 53 := by
      have : q % 252 = 53 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 54 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 54 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 55 := by
      have : q % 252 = 55 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 56 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 56 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 57 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 57 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 58 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 58 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 59 := by
      have : q % 252 = 59 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 60 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 60 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 61 := by
      have : q % 252 = 61 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 62 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 62 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 63 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 63 ∣ 252 := by decide
      have h_g_dvd_r : 63 ∣ 63 := by decide
      have h_g_dvd_q : 63 ∣ q := by
        have : q = 252 * (q / 252) + 63 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 63 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 64 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 64 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 65 := by
      have : q % 252 = 65 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 66 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 66 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 67 := by
      have : q % 252 = 67 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 68 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 68 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 69 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 69 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 70 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 70 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 71 := by
      have : q % 252 = 71 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 72 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 72 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 73 := by
      have : q % 252 = 73 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 74 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 74 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 75 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 75 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 76 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 76 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 77 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 77 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 78 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 78 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 79 := by
      have : q % 252 = 79 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 80 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 80 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 81 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 81 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 82 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 82 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 83 := by
      have : q % 252 = 83 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 84 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 84 ∣ 252 := by decide
      have h_g_dvd_r : 84 ∣ 84 := by decide
      have h_g_dvd_q : 84 ∣ q := by
        have : q = 252 * (q / 252) + 84 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 84 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 85 := by
      have : q % 252 = 85 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 86 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 86 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 87 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 87 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 88 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 88 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 89 := by
      have : q % 252 = 89 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 90 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 90 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 91 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 91 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 92 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 92 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 93 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 93 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 94 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 94 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 95 := by
      have : q % 252 = 95 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 96 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 96 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 97 := by
      have : q % 252 = 97 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 98 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 98 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 99 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 99 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 100 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 100 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 101 := by
      have : q % 252 = 101 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 102 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 102 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 103 := by
      have : q % 252 = 103 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 104 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 104 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 105 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 105 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 106 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 106 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 107 := by
      have : q % 252 = 107 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 108 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 108 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 109 := by
      have : q % 252 = 109 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 110 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 110 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 111 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 111 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 112 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 112 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 113 := by
      have : q % 252 = 113 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 114 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 114 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 115 := by
      have : q % 252 = 115 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 116 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 116 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 117 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 117 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 118 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 118 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 119 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 119 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 120 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 120 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 121 := by
      have : q % 252 = 121 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 122 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 122 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 123 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 123 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 124 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 124 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 125 := by
      have : q % 252 = 125 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 126 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 126 ∣ 252 := by decide
      have h_g_dvd_r : 126 ∣ 126 := by decide
      have h_g_dvd_q : 126 ∣ q := by
        have : q = 252 * (q / 252) + 126 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 126 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 127 := by
      have : q % 252 = 127 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 128 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 128 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 129 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 129 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 130 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 130 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 131 := by
      have : q % 252 = 131 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 132 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 132 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 133 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 133 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 134 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 134 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 135 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 135 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 136 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 136 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 137 := by
      have : q % 252 = 137 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 138 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 138 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 139 := by
      have : q % 252 = 139 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 140 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 140 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 141 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 141 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 142 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 142 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 143 := by
      have : q % 252 = 143 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 144 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 144 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 145 := by
      have : q % 252 = 145 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 146 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 146 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 147 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 147 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 148 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 148 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 149 := by
      have : q % 252 = 149 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 150 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 150 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 151 := by
      have : q % 252 = 151 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 152 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 152 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 153 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 153 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 154 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 154 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 155 := by
      have : q % 252 = 155 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 156 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 156 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 157 := by
      have : q % 252 = 157 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 158 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 158 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 159 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 159 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 160 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 160 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 161 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 161 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 162 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 162 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 163 := by
      have : q % 252 = 163 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 164 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 164 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 165 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 165 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 166 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 166 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 167 := by
      have : q % 252 = 167 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 84 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 84 ∣ 252 := by decide
      have h_g_dvd_r : 84 ∣ 168 := by decide
      have h_g_dvd_q : 84 ∣ q := by
        have : q = 252 * (q / 252) + 168 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 84 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 169 := by
      have : q % 252 = 169 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 170 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 170 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 171 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 171 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 172 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 172 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 173 := by
      have : q % 252 = 173 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 174 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 174 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 175 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 175 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 176 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 176 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 177 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 177 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 178 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 178 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 179 := by
      have : q % 252 = 179 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 180 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 180 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 181 := by
      have : q % 252 = 181 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 182 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 182 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 183 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 183 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 184 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 184 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 185 := by
      have : q % 252 = 185 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 186 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 186 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 187 := by
      have : q % 252 = 187 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 188 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 188 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 63 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 63 ∣ 252 := by decide
      have h_g_dvd_r : 63 ∣ 189 := by decide
      have h_g_dvd_q : 63 ∣ q := by
        have : q = 252 * (q / 252) + 189 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 63 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 190 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 190 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 191 := by
      have : q % 252 = 191 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 192 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 192 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 193 := by
      have : q % 252 = 193 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 194 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 194 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 195 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 195 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 196 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 196 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 197 := by
      have : q % 252 = 197 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 198 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 198 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 199 := by
      have : q % 252 = 199 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 200 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 200 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 201 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 201 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 202 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 202 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 203 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 203 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 204 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 204 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 205 := by
      have : q % 252 = 205 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 206 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 206 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 207 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 207 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 208 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 208 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 209 := by
      have : q % 252 = 209 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 42 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 42 ∣ 252 := by decide
      have h_g_dvd_r : 42 ∣ 210 := by decide
      have h_g_dvd_q : 42 ∣ q := by
        have : q = 252 * (q / 252) + 210 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 42 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 211 := by
      have : q % 252 = 211 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 212 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 212 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 213 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 213 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 214 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 214 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 215 := by
      have : q % 252 = 215 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 216 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 216 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 217 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 217 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 218 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 218 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 219 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 219 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 220 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 220 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 221 := by
      have : q % 252 = 221 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 222 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 222 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 223 := by
      have : q % 252 = 223 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 224 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 224 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 225 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 225 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 226 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 226 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 227 := by
      have : q % 252 = 227 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 228 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 228 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 229 := by
      have : q % 252 = 229 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 230 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 230 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 231 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 231 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 232 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 232 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 233 := by
      have : q % 252 = 233 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 234 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 234 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 235 := by
      have : q % 252 = 235 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 236 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 236 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 237 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 237 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 238 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 238 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 239 := by
      have : q % 252 = 239 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 240 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 240 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 241 := by
      have : q % 252 = 241 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 242 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 242 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 243 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 243 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 244 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 244 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 245 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 245 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 246 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 246 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 247 := by
      have : q % 252 = 247 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 248 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 248 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 249 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 249 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 250 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 250 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 251 := by
      have : q % 252 = 251 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
lemma pow_unit_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) (f : ℕ) :
    (q : ZMod 252) ^ f = (q : ZMod 252) ^ (f % 6) := by
  have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul, pow_six_zmod_252 q hq_coprime, one_pow, one_mul]
lemma pillai_diff_two_3_7 (e f : ℕ) (he : 1 < e) (h : 7 ^ f - 3 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (7 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
    have h_ge : 7 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((7 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h3e : (3 : ZMod 9) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (3 : ZMod 9) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h3e, sub_zero] at h_zmod
  have h7f : (7 : ZMod 9) ^ f = (7 : ZMod 9) ^ (f % 3) := by
    have h_eq : f = 3 * (f / 3) + f % 3 := (Nat.div_add_mod f 3).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (7 : ZMod 9) ^ 3 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h7f] at h_zmod
  have h_mod : f % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 3 <;> revert h_zmod <;> decide

lemma pillai_diff_two_5_7 (e f : ℕ) (he : 1 < e) (h : 7 ^ f - 5 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (7 : ZMod 25) ^ f - (5 : ZMod 25) ^ e = 2 := by
    have h_ge : 7 ^ f ≥ 5 ^ e := by omega
    have h_cast : ((7 ^ f - 5 ^ e : ℕ) : ZMod 25) = ((2 : ℕ) : ZMod 25) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h5e : (5 : ZMod 25) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (5 : ZMod 25) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h5e, sub_zero] at h_zmod
  have h7f : (7 : ZMod 25) ^ f = (7 : ZMod 25) ^ (f % 4) := by
    have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (7 : ZMod 25) ^ 4 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h7f] at h_zmod
  have h_mod : f % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 4 <;> revert h_zmod <;> decide

lemma pillai_diff_two_7_5 (e f : ℕ) (h : 5 ^ f - 7 ^ e = 2) : False := by
  have h_zmod : (5 : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
    have h_ge : 5 ^ f ≥ 7 ^ e := by omega
    have h_cast : ((5 ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h5 : (5 : ZMod 3) = 2 := rfl
  have h7 : (7 : ZMod 3) = 1 := rfl
  rw [h5, h7, one_pow] at h_zmod
  have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
    have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul]
  rw [h2f] at h_zmod
  have h_mod : f % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 2 <;> revert h_zmod <;> decide

lemma pow_three_helper_999 (k : ℕ) : (3 : ZMod 999) ^ (18 * k + 3) = (3 : ZMod 999) ^ 3 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : 18 * (k + 1) + 3 = 18 * k + 3 + 18 := by omega
    rw [this, pow_add, ih]
    rfl

lemma pow_three_zmod_999 (f : ℕ) (hf : f ≥ 3) :
    (3 : ZMod 999) ^ f = (3 : ZMod 999) ^ ((f - 3) % 18 + 3) := by
  have h_eq : f = 18 * ((f - 3) / 18) + 3 + (f - 3) % 18 := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_three_helper_999, ← pow_add]
  have : 3 + (f - 3) % 18 = (f - 3) % 18 + 3 := by omega
  rw [this]

lemma pow_seven_zmod_999 (e : ℕ) (he : e ≥ 2) :
    (7 : ZMod 999) ^ e = (7 : ZMod 999) ^ ((e - 2) % 9 + 2) := by
  have h_eq : e = 9 * ((e - 2) / 9) + ((e - 2) % 9 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul]
  have : (7 : ZMod 999) ^ 9 = 1 := by rfl
  rw [this, one_pow, one_mul]

lemma pillai_diff_two_7_3 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 3 ^ f - 7 ^ e = 2) : False := by
  have hf3 : f ≥ 3 := by
    by_contra hc
    have : f = 2 := by omega
    subst this
    have : 3 ^ 2 - 7 ^ e = 2 := h
    have h_pow : 7 ^ e ≥ 49 := Nat.pow_le_pow_right (show 0 < 7 by decide) he
    omega
  have he2 : e ≥ 2 := he
  have h_zmod : (3 : ZMod 999) ^ f - (7 : ZMod 999) ^ e = 2 := by
    have h_ge : 3 ^ f ≥ 7 ^ e := by omega
    have h_cast : ((3 ^ f - 7 ^ e : ℕ) : ZMod 999) = ((2 : ℕ) : ZMod 999) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  rw [pow_three_zmod_999 f hf3, pow_seven_zmod_999 e he2] at h_zmod
  have h_mod_f : (f - 3) % 18 < 18 := Nat.mod_lt _ (by decide)
  have h_mod_e : (e - 2) % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : (f - 3) % 18 <;> interval_cases he_mod : (e - 2) % 9 <;> revert h_zmod <;> decide

lemma pillai_diff_two_3_11 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 11 ^ f - 3 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (11 : ZMod 121) ^ f - (3 : ZMod 121) ^ e = 2 := by
    have h_ge : 11 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((11 ^ f - 3 ^ e : ℕ) : ZMod 121) = ((2 : ℕ) : ZMod 121) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h11f : (11 : ZMod 121) ^ f = 0 := by
    have hf_eq : f = (f - 2) + 2 := by omega
    rw [hf_eq, pow_add]
    have : (11 : ZMod 121) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h11f, zero_sub] at h_zmod
  have h_cast2 : (3 : ZMod 121) ^ e = 119 := by
    calc (3 : ZMod 121) ^ e = - (- (3 : ZMod 121) ^ e) := by ring
    _ = -2 := by rw [h_zmod]
    _ = 119 := rfl
  have h3e : (3 : ZMod 121) ^ e = (3 : ZMod 121) ^ (e % 110) := by
    have h_eq : e = 110 * (e / 110) + e % 110 := (Nat.div_add_mod e 110).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 121) ^ 110 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h3e] at h_cast2
  have h_mod : e % 110 < 110 := Nat.mod_lt _ (by decide)
  interval_cases he_mod : e % 110 <;> revert h_cast2 <;> decide

lemma pow_seven_helper_252 (k : ℕ) : (7 : ZMod 252) ^ (6 * k + 2) = (7 : ZMod 252) ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : 6 * (k + 1) + 2 = 6 * k + 2 + 6 := by omega
    rw [this, pow_add, ih]
    rfl

lemma pow_seven_zmod_252 (e : ℕ) (he : e ≥ 2) :
    (7 : ZMod 252) ^ e = (7 : ZMod 252) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + 2 + (e - 2) % 6 := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_seven_helper_252, ← pow_add]
  have : 2 + (e - 2) % 6 = (e - 2) % 6 + 2 := by omega
  rw [this]

