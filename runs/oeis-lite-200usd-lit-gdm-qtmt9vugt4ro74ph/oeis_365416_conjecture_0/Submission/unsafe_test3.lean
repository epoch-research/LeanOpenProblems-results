import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000

open Nat

lemma odd_sq_mod_eight (y : ℕ) (hy : y % 2 = 1) : 8 ∣ y ^ 2 - 1 := by
  have h_mod : y % 8 < 8 := Nat.mod_lt _ (by decide)
  set k := y / 8
  interval_cases y_mod : y % 8
  · have : y % 2 = 0 := by
      have : y = 8 * k + 0 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 1 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 2 * k) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 2 * k) + 1 - 1 = 8 * (8 * k ^ 2 + 2 * k) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 2 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 3 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 6 * k + 1) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 6 * k + 1) + 1 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 4 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 5 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 10 * k + 3) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 10 * k + 3) + 1 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 6 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 7 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 14 * k + 6) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 14 * k + 6) + 1 - 1 = 8 * (8 * k ^ 2 + 14 * k + 6) := by omega
    rw [this]
    exact dvd_mul_right 8 _


lemma pow_five_zmod_eight (e : ℕ) : (5 : ZMod 8) ^ e = 1 ∨ (5 : ZMod 8) ^ e = 5 := by
  induction e with
  | zero => left; rfl
  | succ e ih =>
    rcases ih with h1 | h2
    · right; rw [pow_succ, h1, one_mul]
    · left; rw [pow_succ, h2]
      decide


lemma hy_odd_proof (q f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (hf : f % 2 = 0) (hf_pos : f > 0) :
    (q ^ (f / 2)) % 2 = 1 := by
  set y := q ^ (f / 2)
  by_contra hc
  have hc_even : y % 2 = 0 := by omega
  have h_even_y : 2 ∣ y := Nat.dvd_of_mod_eq_zero hc_even
  have h_even_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even_y
  rcases hq.eq_one_or_self_of_dvd 2 h_even_q with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma f_even_contradiction (e f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_sq : q ^ f = 5 ^ e + 2) (hf_even : f % 2 = 0) (hf_pos : f > 0) : False := by
  have hf_eq : f = (f / 2) * 2 := by omega
  set y := q ^ (f / 2)
  have h_fy : q ^ f = y ^ 2 := by
    rw [hf_eq, pow_mul]
  have h_sq_y : y ^ 2 = 5 ^ e + 2 := by
    rw [← h_fy, h_sq]
  have hy_odd : y % 2 = 1 := hy_odd_proof q f hq hq_ne_2 hf_even hf_pos
  have h_dvd : 8 ∣ y ^ 2 - 1 := odd_sq_mod_eight y hy_odd
  have h_dvd_five : 8 ∣ 5 ^ e + 1 := by
    have h_sub : y ^ 2 - 1 = 5 ^ e + 1 := by
      generalize 5 ^ e = V at h_sq_y ⊢
      rw [h_sq_y]
      omega
    rw [h_sub] at h_dvd
    exact h_dvd
  have h_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = 0 := by
    rcases h_dvd_five with ⟨c, hc⟩
    have hc_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = ((8 * c : ℕ) : ZMod 8) := congrArg Nat.cast hc
    rw [hc_cast]
    push_cast
    have : (8 : ZMod 8) = 0 := rfl
    rw [this, zero_mul]
  have h_five_zmod : (5 : ZMod 8) ^ e = -1 := by
    have h_cast_push : (5 : ZMod 8) ^ e + 1 = 0 := by
      calc (5 : ZMod 8) ^ e + 1 = ((5 ^ e + 1 : ℕ) : ZMod 8) := by push_cast; rfl
      _ = 0 := h_cast
    calc (5 : ZMod 8) ^ e = (5 : ZMod 8) ^ e + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h_cast_push]
    _ = -1 := by ring
  have h_pow_cases := pow_five_zmod_eight e
  rcases h_pow_cases with h1 | h2
  · rw [h1] at h_five_zmod
    have : (1 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide
  · rw [h2] at h_five_zmod
    have : (5 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide

lemma pow_two_zmod_three_odd (e : ℕ) (he_odd : e % 2 = 1) : (2 : ZMod 3) ^ e = 2 := by
  have h_eq : e = 2 * (e / 2) + 1 := by omega
  rw [h_eq]
  have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
    rw [pow_succ, pow_mul]
  rw [this]
  have : (2 : ZMod 3) ^ 2 = 1 := rfl
  rw [this, one_pow, one_mul]

lemma q_mod_3_contradiction (e f q : ℕ) (hq_mod : q % 3 = 2) (he_odd : e % 2 = 1) (h : q ^ f = 5 ^ e + 2) : f % 2 = 0 := by
  by_contra hf_odd_hc
  have hf_odd : f % 2 = 1 := by omega
  have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((5 ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h
  push_cast at h_cast
  have hq_cast : (q : ZMod 3) = 2 := by
    have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hq_mod]
    rfl
  have h5_cast : (5 : ZMod 3) = 2 := rfl
  rw [hq_cast, h5_cast] at h_cast
  have hq_pow : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
  have h5_pow : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
  rw [hq_pow, h5_pow] at h_cast
  have : (2 : ZMod 3) = 2 + 2 := h_cast
  revert this
  decide

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
    have : q ≥ 252 := Nat.le_of_dvd hq.pos this
    have : q.gcd 252 = 252 := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hc)
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
            have : q = 252 * (q / m) + 0 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 2 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 3 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 4 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 6 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 7 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 8 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 9 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 10 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 12 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 14 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 15 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 16 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 18 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 20 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 21 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 22 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 24 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 26 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 27 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 28 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 30 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 32 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 33 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 34 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 35 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 36 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 38 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 39 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 40 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 42 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 44 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 45 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 46 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 48 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 49 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 50 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 51 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 52 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 54 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 56 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 57 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 58 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 60 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 62 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 63 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 64 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 66 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 68 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 69 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 70 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 72 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 74 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 75 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 76 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 77 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 78 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 80 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 81 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 82 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 84 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 86 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 87 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 88 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 90 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 91 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 92 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 93 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 94 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 96 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 98 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 99 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 100 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 102 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 104 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 105 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 106 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 108 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 110 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 111 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 112 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 114 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 116 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 117 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 118 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 119 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 120 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 122 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 123 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 124 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 126 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 128 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 129 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 130 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 132 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 133 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 134 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 135 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 136 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 138 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 140 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 141 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 142 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 144 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 146 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 147 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 148 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 150 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 152 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 153 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 154 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 156 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 158 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 159 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 160 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 161 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 162 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 164 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 165 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 166 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 168 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 170 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 171 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 172 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 174 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 175 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 176 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 177 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 178 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 180 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 182 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 183 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 184 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 186 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 188 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 189 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 190 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 192 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 194 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 195 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 196 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 198 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 200 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 201 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 202 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 203 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 204 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 206 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 207 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 208 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 210 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 212 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 213 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 214 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 216 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 217 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 218 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 219 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 220 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 222 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 224 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 225 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 226 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 228 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 230 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 231 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 232 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 234 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 236 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 237 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 238 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 240 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 242 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 243 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 244 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 245 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 246 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 248 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 249 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
            have : q = 252 * (q / m) + 250 := (Nat.div_add_mod q m).symm.trans (by omega)
            rw [this]
            exact dvd_add (dvd_mul_of_dvd_right h_g_dvd_252 _) h_g_dvd_r
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
